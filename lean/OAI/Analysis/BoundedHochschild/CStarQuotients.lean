import Mathlib
import OAI.Analysis.BoundedHochschild.BlockSpans

namespace OAI

/-! C-star quotients by star-closed ideals. -/

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric

namespace HochschildCStarQuotient
variable {A : Type*} [CStarAlgebra A]

class StarClosed (I : Ideal A) : Prop where
  star_mem {x : A} : x ∈ I → star x ∈ I

variable (I : Ideal A) [I.IsTwoSided]

lemma norm_mk_le (x : A) : ‖Ideal.Quotient.mk I x‖ ≤ ‖x‖ :=
  Submodule.Quotient.norm_mk_le I x

lemma norm_mk_lt (x : A ⧸ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, Ideal.Quotient.mk I a = x ∧ ‖a‖ < ‖x‖ + ε :=
  QuotientAddGroup.exists_norm_mk_lt x hε

instance quotientSeminormedRing : SeminormedRing (A ⧸ I) where
  dist_eq := dist_eq_norm_neg_add
  norm_mul_le x y := le_of_forall_pos_le_add fun ε hε => by
    have := ((nhds_basis_ball.prod_nhds nhds_basis_ball).tendsto_iff nhds_basis_ball).mp
      (continuous_mul.tendsto (‖x‖, ‖y‖)) ε hε
    simp only [Set.mem_prod, Metric.mem_ball, and_imp, Prod.forall, Prod.exists] at this
    rcases this with ⟨ε₁, ε₂, ⟨h₁, h₂⟩, h⟩
    obtain ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩ := norm_mk_lt I x h₁, norm_mk_lt I y h₂
    simp only [dist, abs_sub_lt_iff] at h
    specialize h ‖a‖ ‖b‖ ⟨by linarith, by linarith [norm_mk_le I a]⟩
      ⟨by linarith, by linarith [norm_mk_le I b]⟩
    calc
      _ ≤ ‖a‖ * ‖b‖ := (norm_mk_le I (a*b)).trans (norm_mul_le a b)
      _ ≤ _ := (sub_lt_iff_lt_add'.mp h.1).le

instance quotientNormedRing [IsClosed (I : Set A)] : NormedRing (A ⧸ I) :=
  { quotientSeminormedRing I, Submodule.Quotient.normedAddCommGroup I with }

instance quotientNormedAlgebra : NormedAlgebra ℂ (A ⧸ I) :=
  { Submodule.Quotient.normedSpace I ℂ, Ideal.Quotient.algebra ℂ with }

variable [StarClosed I]

instance quotientStar : Star (A ⧸ I) where
  star := Quotient.map' star fun a b hab => by
    rw [Submodule.quotientRel_def] at hab ⊢
    simpa only [star_sub] using StarClosed.star_mem (I := I) hab

@[simp] lemma star_mk (a : A) : star (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (star a) := rfl

instance quotientStarRing : StarRing (A ⧸ I) where
  star_involutive x := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    simp
  star_mul x y := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [← map_mul, star_mk, star_mul]
  star_add x y := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [← map_add, star_mk, star_add]

instance quotientStarModule : StarModule ℂ (A ⧸ I) where
  star_smul r x := by
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk I (star (r • a)) = Ideal.Quotient.mk I (star r • star a)
    rw [star_smul]

lemma norm_star_le (x : A ⧸ I) : ‖star x‖ ≤ ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a,rfl,ha⟩ := norm_mk_lt I x hε
  exact (norm_mk_le I (star a)).trans (by simpa only [norm_star] using ha.le)

instance quotientNormedStarGroup : NormedStarGroup (A ⧸ I) where
  norm_star_le := norm_star_le I

 
def starSubalgebra : NonUnitalStarSubalgebra ℂ A where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  mul_mem' := fun _ hy => I.mul_mem_left _ hy
  smul_mem' := fun r x hx => by
    change r • x ∈ I
    rw [Algebra.smul_def]
    exact I.mul_mem_left _ hx
  star_mem' := StarClosed.star_mem

instance starSubalgebra_closed [h : IsClosed (I : Set A)] :
    IsClosed (starSubalgebra I : Set A) := h

omit [I.IsTwoSided] in
 
lemma exists_cut [IsClosed (I : Set A)] (b : A) (hb : b ∈ I) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : A, e ∈ I ∧ star e = e ∧ ‖1-e‖ ≤ 1 ∧ ‖b-b*e‖ < ε := by
  let oa := CStarAlgebra.spectralOrder A
  let osa := CStarAlgebra.spectralOrderedRing A
  let S := starSubalgebra I
  let os := CStarAlgebra.spectralOrder S
  let oss := CStarAlgebra.spectralOrderedRing S
  let b' : S := ⟨b,hb⟩
  have hi := CStarAlgebra.increasingApproximateUnit S
  have hd : ∀ᶠ e : S in CStarAlgebra.approximateUnit S, ‖b'-b'*e‖ < ε := by
    have ht := ((tendsto_const_nhds (x := b')).sub (hi.tendsto_mul_left b')).norm
    simpa only [sub_self, norm_zero] using ht.eventually (gt_mem_nhds (by simpa only [sub_self, norm_zero] using hε))
  obtain ⟨e,he₀,he₁,he₂⟩ := (hi.eventually_nonneg.and (hi.eventually_norm.and hd)).exists
  have hepos : 0 ≤ (e:A) := by
    simpa using (@NonUnitalStarRingHom.map_le_map_of_map_star S A _ os _ oss _ oa _ osa
      (NonUnitalStarRingHom.ofClass (NonUnitalStarSubalgebraClass.subtype S)) 0 e he₀)
  have henorm : ‖(e:A)‖ ≤ 1 := he₁
  have heone : (e:A) ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hepos).mp henorm
  refine ⟨e,e.property,hepos.isSelfAdjoint.star_eq,?_,he₂⟩
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg (1-(e:A)) (sub_nonneg.mpr heone)).mpr
    (sub_le_self _ hepos)

lemma quotient_cstar [IsClosed (I : Set A)] (x : A ⧸ I) :
    ‖x‖ * ‖x‖ ≤ ‖star x*x‖ := by
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [star_mk, ← map_mul]
  apply QuotientAddGroup.le_norm_iff.mpr
  intro t ht
  apply le_of_forall_pos_le_add
  intro ε hε
  have hb : t-star a*a ∈ I := (Ideal.Quotient.eq).mp ht
  obtain ⟨e,he,hes,hen,heb⟩ := exists_cut I (t-star a*a) hb hε
  have hqe : Ideal.Quotient.mk I e = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr he
  have hx : Ideal.Quotient.mk I (a*(1-e)) = Ideal.Quotient.mk I a := by
    simp only [map_mul,map_sub,map_one,hqe,sub_zero,mul_one]
  calc
    ‖Ideal.Quotient.mk I a‖ * ‖Ideal.Quotient.mk I a‖ ≤ ‖a*(1-e)‖ * ‖a*(1-e)‖ := by
      apply mul_self_le_mul_self (norm_nonneg _)
      rw [← hx]
      exact norm_mk_le I _
    _ = ‖(1-e)*(star a*a)*(1-e)‖ := by
      rw [← CStarRing.norm_star_mul_self]
      simp only [star_mul,star_sub,star_one,hes,mul_assoc]
    _ = ‖(1-e)*t*(1-e)-(1-e)*((t-star a*a)-(t-star a*a)*e)‖ := by
      congr 1
      noncomm_ring
    _ ≤ ‖(1-e)*t*(1-e)‖ + ‖(1-e)*((t-star a*a)-(t-star a*a)*e)‖ := norm_sub_le _ _
    _ ≤ ‖t‖ + ε := by
      apply add_le_add
      · calc
          _ ≤ ‖1-e‖*‖t‖*‖1-e‖ := (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ 1*‖t‖*1 := by gcongr
          _ = _ := by ring
      · calc
          _ ≤ ‖1-e‖*‖(t-star a*a)-(t-star a*a)*e‖ := norm_mul_le _ _
          _ ≤ 1*‖(t-star a*a)-(t-star a*a)*e‖ :=
            mul_le_mul_of_nonneg_right hen (norm_nonneg _)
          _ ≤ ε := by simpa using heb.le

instance quotientCStarAlgebra [IsClosed (I : Set A)] : CStarAlgebra (A ⧸ I) where
  norm_mul_self_le := quotient_cstar I

end HochschildCStarQuotient
end

end OAI
