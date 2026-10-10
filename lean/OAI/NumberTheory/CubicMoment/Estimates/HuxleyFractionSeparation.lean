import OAI.NumberTheory.CubicMoment.Estimates.PublishedAdditiveSieve
import OAI.NumberTheory.CubicMoment.Estimates.ConductorLocal

namespace OAI

/-! Separation of the actual reduced Eisenstein fractions in the additive sieve. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma eisenstein_fraction_cross_norm {q r : Eisenstein} (hq : q ≠ 0) (hr : r ≠ 0)
    (a b z : Eisenstein) :
    norm (a*r-b*q-z*q*r) = norm q*norm r*
      ‖(a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-(z:ℂ)‖^2 := by
  have hqc : (q:ℂ) ≠ 0 := fun h => hq (Subtype.ext h)
  have hrc : (r:ℂ) ≠ 0 := fun h => hr (Subtype.ext h)
  have he : ((a*r-b*q-z*q*r:Eisenstein):ℂ) =
      (q:ℂ)*(r:ℂ)*((a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-(z:ℂ)) := by
    push_cast
    field_simp
  simp only [norm,Complex.normSq_eq_norm_sq]
  rw [he,_root_.norm_mul,_root_.norm_mul,mul_pow,mul_pow]

lemma eisenstein_fraction_separation {q r : Eisenstein} (hq : q ≠ 0) (hr : r ≠ 0)
    {Q : ℝ} (hqQ : norm q ≤ Q) (hrQ : norm r ≤ Q)
    (a b z : Eisenstein) (hgap : a*r-b*q-z*q*r ≠ 0) :
    1/Q^2 ≤ ‖(a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-(z:ℂ)‖^2 := by
  have hq0 := norm_pos_of_ne_zero hq
  have hr0 := norm_pos_of_ne_zero hr
  have hQ : 0 < Q := hq0.trans_le hqQ
  have hprod : norm q*norm r ≤ Q^2 := by
    simpa only [pow_two] using mul_le_mul hqQ hrQ hr0.le hQ.le
  have hcross := one_le_norm hgap
  rw [eisenstein_fraction_cross_norm hq hr a b z] at hcross
  apply (div_le_iff₀ (sq_pos_of_pos hQ)).mpr
  calc
    1 ≤ norm q*norm r*‖(a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-(z:ℂ)‖^2 := hcross
    _ ≤ _ := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hprod (sq_nonneg _)

lemma reduced_fraction_associated_denominators {q r a b z : Eisenstein}
    (hqa : IsCoprime q a) (hrb : IsCoprime r b)
    (he : a*r-b*q-z*q*r = 0) : Associated q r := by
  have hqr : q ∣ r := by
    apply hqa.dvd_of_dvd_mul_left
    refine ⟨b+z*r,?_⟩
    linear_combination he
  have hrq : r ∣ q := by
    apply hrb.dvd_of_dvd_mul_left
    refine ⟨a-z*q,?_⟩
    linear_combination -he
  exact associated_of_dvd_dvd hqr hrq

lemma reduced_fraction_nonassociated_separation {q r a b : Eisenstein}
    (hq : q ≠ 0) (hr : r ≠ 0) (hqa : IsCoprime q a) (hrb : IsCoprime r b)
    (hnot : ¬Associated q r) {Q : ℝ} (hqQ : norm q ≤ Q) (hrQ : norm r ≤ Q)
    (z : Eisenstein) :
    1/Q^2 ≤ ‖(a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-(z:ℂ)‖^2 := by
  exact eisenstein_fraction_separation hq hr hqQ hrQ a b z
    (fun he => hnot (reduced_fraction_associated_denominators hqa hrb he))

/-- Distinct residue classes at the same denominator stay separated modulo the lattice. -/
lemma residue_fraction_separation {q : Eisenstein} (hq : q ≠ 0)
    {x y : Residues q} (hxy : x ≠ y) {Q : ℝ} (hqQ : norm q ≤ Q) (z : Eisenstein) :
    1/Q^2 ≤ ‖(residueRepresentative q x:ℂ)/(q:ℂ)-
      (residueRepresentative q y:ℂ)/(q:ℂ)-(z:ℂ)‖^2 := by
  apply eisenstein_fraction_separation hq hq hqQ hqQ
  intro he
  have he' : (residueRepresentative q x-residueRepresentative q y-z*q)*q = 0 := by
    linear_combination he
  have hz : residueRepresentative q x-residueRepresentative q y-z*q = 0 :=
    (mul_eq_zero.mp he').resolve_right hq
  have hquot := congrArg (Ideal.Quotient.mk (modulus q)) hz
  simp only [map_sub,map_mul,residueRepresentative_spec,map_zero] at hquot
  have hqzero : Ideal.Quotient.mk (modulus q) q = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (Set.mem_singleton q)
  rw [hqzero,mul_zero,sub_zero,sub_eq_zero] at hquot
  exact hxy hquot

/-- The unit conditions in Huxley's literal residue sum are exactly the coprimality
conditions used in the cross-determinant separation proof. -/
lemma huxley_reduced_fraction_separation {q r : Eisenstein}
    (hq : q ≠ 0) (hr : r ≠ 0) (x : Residues q) (y : Residues r)
    (hx : IsUnit x) (hy : IsUnit y) (hnot : ¬Associated q r)
    {Q : ℝ} (hqQ : norm q ≤ Q) (hrQ : norm r ≤ Q) (z : Eisenstein) :
    1/Q^2 ≤ ‖(residueRepresentative q x:ℂ)/(q:ℂ)-
      (residueRepresentative r y:ℂ)/(r:ℂ)-(z:ℂ)‖^2 := by
  apply reduced_fraction_nonassociated_separation hq hr _ _ hnot hqQ hrQ z
  · exact isCoprime_of_residue_isUnit (by rwa [residueRepresentative_spec])
  · exact isCoprime_of_residue_isUnit (by rwa [residueRepresentative_spec])

lemma eisenstein_fraction_eq_of_close {q r : Eisenstein} (hq : q ≠ 0) (hr : r ≠ 0)
    {Q : ℝ} (hqQ : norm q ≤ Q) (hrQ : norm r ≤ Q) (a b z : Eisenstein)
    (hclose : ‖(a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-(z:ℂ)‖^2 < 1/Q^2) :
    (a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ) = (z:ℂ) := by
  have hg : a*r-b*q-z*q*r = 0 := by
    by_contra hne
    exact (not_le_of_gt hclose) (eisenstein_fraction_separation hq hr hqQ hrQ a b z hne)
  have hn := eisenstein_fraction_cross_norm hq hr a b z
  rw [hg,show norm (0:Eisenstein) = 0 by simp [norm]] at hn
  have hq0 := norm_pos_of_ne_zero hq
  have hr0 := norm_pos_of_ne_zero hr
  have hsq : ‖(a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-(z:ℂ)‖^2 = 0 := by
    exact (mul_eq_zero.mp hn.symm).resolve_left (mul_pos hq0 hr0).ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))

lemma translated_fraction_eq_of_close {q r : Eisenstein} (hq : q ≠ 0) (hr : r ≠ 0)
    {Q : ℝ} (hqQ : norm q ≤ Q) (hrQ : norm r ≤ Q)
    (a b u v : Eisenstein)
    (hclose : ‖((a:ℂ)/(q:ℂ)+(u:ℂ))-((b:ℂ)/(r:ℂ)+(v:ℂ))‖^2 < 1/Q^2) :
    (a:ℂ)/(q:ℂ)+(u:ℂ) = (b:ℂ)/(r:ℂ)+(v:ℂ) := by
  have he : (a:ℂ)/(q:ℂ)-(b:ℂ)/(r:ℂ)-((v-u:Eisenstein):ℂ) =
      ((a:ℂ)/(q:ℂ)+(u:ℂ))-((b:ℂ)/(r:ℂ)+(v:ℂ)) := by push_cast; ring
  have h := eisenstein_fraction_eq_of_close hq hr hqQ hrQ a b (v-u) (by rwa [he])
  push_cast at h
  linear_combination h

/-- All associates have a uniformly bounded multiplicity; an explicit lattice
bound suffices, so the large sieve does not require classifying the six units. -/
lemma associated_denominator_count (S : Finset Eisenstein) (q : Eisenstein) :
    ((S.filter (fun r => Associated q r)).card:ℝ) ≤ 18 := by
  classical
  have hsub : S.filter (fun r => Associated q r) ⊆
      (nonzeroNormBall 1).image (fun u => q*u) := by
    intro r hr
    obtain ⟨u,hu⟩ := (Finset.mem_filter.mp hr).2
    apply Finset.mem_image.mpr
    refine ⟨(u:Eisenstein),?_,hu⟩
    exact mem_nonzeroNormBall.mpr ⟨(norm_of_isUnit u.isUnit).le,u.ne_zero⟩
  have hc := Finset.card_le_card hsub
  have hi := Finset.card_image_le (s := nonzeroNormBall 1) (f := fun u => q*u)
  have hn : ((nonzeroNormBall 1).card:ℝ) ≤ 18 := by
    simpa only [mul_one] using nonzeroNormBall_card_le (show (0:ℝ) ≤ 1 by norm_num)
  have hnat : (S.filter (fun r => Associated q r)).card ≤ (nonzeroNormBall 1).card := hc.trans hi
  exact (show ((S.filter (fun r => Associated q r)).card:ℝ) ≤
    ((nonzeroNormBall 1).card:ℝ) by exact_mod_cast hnat).trans hn

end CubicFirstMoment

end

end OAI
