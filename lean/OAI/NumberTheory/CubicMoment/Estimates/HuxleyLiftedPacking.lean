import OAI.NumberTheory.CubicMoment.Estimates.HuxleyFractionSeparation

namespace OAI

/-! Local multiplicity of the reduced fractions and all their lattice translates. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

@[ext] structure HuxleyLift where
  denominator : Eisenstein
  numerator : Eisenstein
  shift : Eisenstein
  deriving DecidableEq

def HuxleyLift.frequency (i : HuxleyLift) : ℂ :=
  (i.numerator:ℂ)/(i.denominator:ℂ)+(i.shift:ℂ)

def HuxleyLift.reduced (Q : ℝ) (i : HuxleyLift) : Prop :=
  i.denominator ≠ 0 ∧ norm i.denominator ≤ Q ∧
    IsCoprime i.denominator i.numerator ∧
    residueRepresentative i.denominator (Ideal.Quotient.mk (modulus i.denominator) i.numerator) =
      i.numerator

lemma huxleyLift_actual {q : Eisenstein} (hq : q ≠ 0) {Q : ℝ} (hQ : norm q ≤ Q)
    (x : Residues q) (hx : IsUnit x) (z : Eisenstein) :
    HuxleyLift.reduced Q ⟨q,residueRepresentative q x,z⟩ := by
  refine ⟨hq,hQ,?_,?_⟩
  · exact isCoprime_of_residue_isUnit (by rwa [residueRepresentative_spec])
  · dsimp
    rw [residueRepresentative_spec]

lemma huxleyLift_eq_of_frequency_of_denominator {Q : ℝ} {i j : HuxleyLift}
    (hi : i.reduced Q) (hj : j.reduced Q)
    (hq : i.denominator = j.denominator) (hf : i.frequency = j.frequency) : i = j := by
  rcases i with ⟨q,a,u⟩
  rcases j with ⟨r,b,v⟩
  dsimp at hq
  subst r
  have hq0 : q ≠ 0 := hi.1
  have hqc : (q:ℂ) ≠ 0 := fun h => hq0 (Subtype.ext h)
  have he : a-b-(v-u)*q = 0 := by
    apply Subtype.ext
    change (a:ℂ)-(b:ℂ)-((v:ℂ)-(u:ℂ))*(q:ℂ) = 0
    dsimp [HuxleyLift.frequency] at hf
    field_simp at hf
    linear_combination hf
  have heq := congrArg (Ideal.Quotient.mk (modulus q)) he
  have hqz : Ideal.Quotient.mk (modulus q) q = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl q))
  simp only [map_sub,map_mul,map_zero,hqz,mul_zero,sub_zero,sub_eq_zero] at heq
  have hab : a = b := hi.2.2.2.symm.trans ((congrArg (residueRepresentative q) heq).trans hj.2.2.2)
  subst b
  have huv : u = v := by
    apply Subtype.ext
    dsimp [HuxleyLift.frequency] at hf
    exact add_left_cancel hf
  subst v
  rfl

lemma huxleyLift_eq_frequency_of_close {Q : ℝ} {i j : HuxleyLift}
    (hi : i.reduced Q) (hj : j.reduced Q)
    (hclose : ‖i.frequency-j.frequency‖^2 < 1/Q^2) :
    i.frequency = j.frequency :=
  translated_fraction_eq_of_close hi.1 hj.1 hi.2.1 hj.2.1
    i.numerator j.numerator i.shift j.shift hclose

lemma huxleyLift_associated_of_close {Q : ℝ} {i j : HuxleyLift}
    (hi : i.reduced Q) (hj : j.reduced Q)
    (hclose : ‖i.frequency-j.frequency‖^2 < 1/Q^2) :
    Associated i.denominator j.denominator := by
  apply reduced_fraction_associated_denominators hi.2.2.1 hj.2.2.1
  by_contra hne
  have hsep := eisenstein_fraction_separation hi.1 hj.1 hi.2.1 hj.2.1
    i.numerator j.numerator (j.shift-i.shift) hne
  have he : (i.numerator:ℂ)/(i.denominator:ℂ)-(j.numerator:ℂ)/(j.denominator:ℂ)-
      ((j.shift-i.shift:Eisenstein):ℂ) = i.frequency-j.frequency := by
    dsimp [HuxleyLift.frequency]
    ring
  rw [he] at hsep
  exact (not_le_of_gt hclose) hsep

/-- A small disk contains at most eighteen lifted reduced fractions, counting
all associate denominators and all lattice translations. -/
lemma huxleyLift_local_count (Q : ℝ) (hQ : 0 < Q) (z : ℂ) (S : Finset HuxleyLift)
    (hred : ∀ i ∈ S, i.reduced Q)
    (hclose : ∀ i ∈ S, ‖i.frequency-z‖ < 1/(3*Q)) :
    (S.card:ℝ) ≤ 18 := by
  classical
  by_cases hs : S.Nonempty
  · obtain ⟨i0,hi0⟩ := hs
    have hpair (i : HuxleyLift) (hi : i ∈ S) :
        ‖i.frequency-i0.frequency‖^2 < 1/Q^2 := by
      have ht := dist_triangle i.frequency z i0.frequency
      simp only [dist_eq_norm] at ht
      rw [norm_sub_rev z i0.frequency] at ht
      have hh : ‖i.frequency-i0.frequency‖ < 1/Q := by
        have hi' := hclose i hi
        have h0' := hclose i0 hi0
        have hdiv : 1/(3*Q)+1/(3*Q) < 1/Q := by
          field_simp
          linarith
        linarith
      have hd : 0 ≤ 1/Q := (one_div_pos.mpr hQ).le
      have hsq := (sq_lt_sq₀ (_root_.norm_nonneg _) hd).mpr hh
      simpa only [one_div_pow,one_pow] using hsq
    have hinj : Set.InjOn HuxleyLift.denominator (↑S : Set HuxleyLift) := by
      intro i hi j hj hij
      apply huxleyLift_eq_of_frequency_of_denominator (hred i hi) (hred j hj) hij
      exact (huxleyLift_eq_frequency_of_close (hred i hi) (hred i0 hi0) (hpair i hi)).trans
        (huxleyLift_eq_frequency_of_close (hred j hj) (hred i0 hi0) (hpair j hj)).symm
    have hsub : S.image HuxleyLift.denominator ⊆
        (S.image HuxleyLift.denominator).filter (fun q => Associated i0.denominator q) := by
      intro q hq
      refine Finset.mem_filter.mpr ⟨hq,?_⟩
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
      exact (huxleyLift_associated_of_close (hred i hi) (hred i0 hi0) (hpair i hi)).symm
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_iff.mpr hinj] at hc
    exact (show (S.card:ℝ) ≤
      (((S.image HuxleyLift.denominator).filter (fun q => Associated i0.denominator q)).card:ℝ)
      by exact_mod_cast hc).trans (associated_denominator_count _ _)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [he]

end CubicFirstMoment

end

end OAI
