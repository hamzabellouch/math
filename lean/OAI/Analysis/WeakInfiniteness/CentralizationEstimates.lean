import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra

section UnitalEstimate

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

lemma norm_commutator_sq_le_unital (v a : B) (hv : ‖v‖ ≤ 1) :
    ‖a*v-v*a‖^2 ≤ ‖star v*(star a*a)*v-star a*a‖ +
      2*‖a‖*‖star v*a*v-a‖ := by
  have hvv : star v*v ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg v)).mp
    rw [CStarRing.norm_star_mul_self]
    exact (mul_le_mul hv hv (norm_nonneg _) zero_le_one).trans (by norm_num)
  let d := a*v-v*a
  let e := a-star v*a*v
  let R := (star v*(star a*a)*v-star a*a)+star a*e+star e*a
  have hR : star d*d ≤ R := by
    apply sub_nonneg.mp
    have he : R-star d*d=star a*(1-star v*v)*a := by
      dsimp only [R,e,d]
      simp only [star_sub,star_mul,star_star]
      noncomm_ring
    rw [he]
    exact star_left_conjugate_nonneg (sub_nonneg.mpr hvv) a
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg hR (star_mul_self_nonneg d)
  rw [CStarRing.norm_star_mul_self] at hn
  have hRn : ‖R‖ ≤ ‖star v*(star a*a)*v-star a*a‖+2*‖a‖*‖e‖ := by
    calc
      _ ≤ ‖star v*(star a*a)*v-star a*a‖+‖star a*e‖+‖star e*a‖ := norm_add₃_le
      _ ≤ ‖star v*(star a*a)*v-star a*a‖+‖star a‖*‖e‖+‖star e‖*‖a‖ := by
        gcongr <;> exact norm_mul_le _ _
      _ = _ := by rw [norm_star,norm_star]; ring
  have he : ‖e‖=‖star v*a*v-a‖ := norm_sub_rev _ _
  rw [he] at hRn
  exact (by simpa only [pow_two] using hn.trans hRn)

end UnitalEstimate

section NonUnitalEstimate

variable {A : Type*} [NonUnitalCStarAlgebra A]

lemma norm_commutator_sq_le (v a : A) (hv : ‖v‖ ≤ 1) :
    ‖a*v-v*a‖^2 ≤ ‖star v*(star a*a)*v-star a*a‖ +
      2*‖a‖*‖star v*a*v-a‖ := by
  have h := norm_commutator_sq_le_unital (v : Unitization ℂ A) (a : Unitization ℂ A)
    (by simpa only [Unitization.norm_inr] using hv)
  simpa only [← Unitization.inr_mul,← Unitization.inr_star,← Unitization.inr_sub,
    Unitization.norm_inr] using h

lemma norm_relative_initial_defect_le (v a : A) (hv : ‖v‖ ≤ 1) :
    ‖(star v*v)*a-a‖ ≤ ‖a*v-v*a‖+‖star v*a*v-a‖ := by
  have he : (star v*v)*a-a= -star v*(a*v-v*a)+(star v*a*v-a) := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖-star v*(a*v-v*a)‖+‖star v*a*v-a‖ := norm_add_le _ _
    _ ≤ ‖-star v‖*‖a*v-v*a‖+‖star v*a*v-a‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ _ := by simpa only [norm_neg,norm_star,one_mul] using
      add_le_add (mul_le_mul_of_nonneg_right hv (norm_nonneg (a*v-v*a))) (le_refl ‖star v*a*v-a‖)

lemma norm_relative_cross_defect_le (s t a : A) (hs : ‖s‖ ≤ 1) :
    ‖(star s*t)*a‖ ≤ ‖a*t-t*a‖+‖star s*a*t‖ := by
  have he : (star s*t)*a= -star s*(a*t-t*a)+star s*a*t := by noncomm_ring
  rw [he]
  calc
    _ ≤ ‖-star s*(a*t-t*a)‖+‖star s*a*t‖ := norm_add_le _ _
    _ ≤ ‖-star s‖*‖a*t-t*a‖+‖star s*a*t‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ _ := by simpa only [norm_neg,norm_star,one_mul] using
      add_le_add (mul_le_mul_of_nonneg_right hs (norm_nonneg (a*t-t*a))) (le_refl ‖star s*a*t‖)

def ContractiveIdentityDiagonalization (A : Type*) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ (F : Finset A) (ε : ℝ),0 < ε →∃ s t : A,‖s‖≤1 ∧ ‖t‖≤1 ∧
    ∀ a ∈ F,‖star s*a*s-a‖<ε ∧ ‖star t*a*t-a‖<ε ∧ ‖star s*a*t‖<ε

def LocalCentralCuntzPair (A : Type*) [NonUnitalCStarAlgebra A] : Prop :=
  ∀ (F : Finset A) (ε : ℝ),0 < ε →∃ s t : A,‖s‖≤1 ∧ ‖t‖≤1 ∧
    ∀ a ∈ F,‖a*s-s*a‖<ε ∧ ‖a*t-t*a‖<ε ∧
      ‖(star s*s)*a-a‖<ε ∧ ‖(star t*t)*a-a‖<ε ∧ ‖(star s*t)*a‖<ε

lemma ContractiveIdentityDiagonalization.localCentralCuntzPair
    (h : ContractiveIdentityDiagonalization A) : LocalCentralCuntzPair A := by
  classical
  intro F ε hε
  let M : ℝ := 1+∑ a ∈ F,‖a‖
  have hM : 0 < M := by dsimp only [M]; positivity
  have haM (a : A) (ha : a ∈ F) : ‖a‖ ≤ M := by
    have hs := Finset.single_le_sum (f := fun b : A => ‖b‖) (fun _ _ => norm_nonneg _) ha
    dsimp only [M]
    linarith
  let δ := min (ε/4) (ε^2/(16*(1+2*M)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδε : δ ≤ ε/4 := min_le_left _ _
  have hδsq : (1+2*M)*δ ≤ ε^2/16 := by
    have hle : δ ≤ ε^2/(16*(1+2*M)) := min_le_right _ _
    have hp : 0 < 16*(1+2*M) := by positivity
    have hh := (le_div_iff₀ hp).mp hle
    nlinarith
  obtain ⟨s,t,hs,ht,hF⟩ := h (F ∪ F.image (fun a => star a*a)) δ hδ
  have he (a : A) (ha : a ∈ F) := hF a (Finset.mem_union_left _ ha)
  have he2 (a : A) (ha : a ∈ F) := hF (star a*a)
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
  have hcomm (v a : A) (hv : ‖v‖≤1) (ha : a ∈ F)
      (hva : ‖star v*a*v-a‖<δ)
      (hv2 : ‖star v*(star a*a)*v-star a*a‖<δ) : ‖a*v-v*a‖<ε/2 := by
    have hn := norm_commutator_sq_le v a hv
    have hna : 0 ≤ ‖a‖ := norm_nonneg _
    have hbound : ‖a*v-v*a‖^2 ≤ (1+2*M)*δ := calc
      _ ≤ δ+2*‖a‖*δ := hn.trans (add_le_add hv2.le (mul_le_mul_of_nonneg_left hva.le (by positivity)))
      _ ≤ (1+2*M)*δ := by nlinarith [haM a ha]
    have hn0 := norm_nonneg (a*v-v*a)
    nlinarith
  refine ⟨s,t,hs,ht,?_⟩
  intro a ha
  have hsa := hcomm s a hs ha (he a ha).1 (he2 a ha).1
  have hta := hcomm t a ht ha (he a ha).2.1 (he2 a ha).2.1
  have hsi := norm_relative_initial_defect_le s a hs
  have hti := norm_relative_initial_defect_le t a ht
  have hst := norm_relative_cross_defect_le s t a hs
  have hbase := he a ha
  refine ⟨by linarith,by linarith,?_,?_,?_⟩ <;> linarith

lemma LocalCentralCuntzPair.contractiveIdentityDiagonalization
    (h : LocalCentralCuntzPair A) : ContractiveIdentityDiagonalization A := by
  intro F ε hε
  obtain ⟨s,t,hs,ht,hF⟩ := h F (ε/3) (by positivity)
  refine ⟨s,t,hs,ht,?_⟩
  intro a ha
  obtain ⟨hsa,hta,hsi,hti,hst⟩ := hF a ha
  have hcomp (v : A) (hv : ‖v‖≤1) :
      ‖star v*a*v-a‖ ≤ ‖a*v-v*a‖+‖(star v*v)*a-a‖ := by
    have he : star v*a*v-a=star v*(a*v-v*a)+((star v*v)*a-a) := by noncomm_ring
    rw [he]
    calc
      _ ≤ ‖star v*(a*v-v*a)‖+‖(star v*v)*a-a‖ := norm_add_le _ _
      _ ≤ ‖star v‖*‖a*v-v*a‖+‖(star v*v)*a-a‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ _ := by simpa only [norm_star,one_mul] using
        add_le_add (mul_le_mul_of_nonneg_right hv (norm_nonneg (a*v-v*a))) (le_refl ‖(star v*v)*a-a‖)
  have hcross : ‖star s*a*t‖ ≤ ‖a*t-t*a‖+‖(star s*t)*a‖ := by
    have he : star s*a*t=star s*(a*t-t*a)+(star s*t)*a := by noncomm_ring
    rw [he]
    calc
      _ ≤ ‖star s*(a*t-t*a)‖+‖(star s*t)*a‖ := norm_add_le _ _
      _ ≤ ‖star s‖*‖a*t-t*a‖+‖(star s*t)*a‖ := by gcongr; exact norm_mul_le _ _
      _ ≤ _ := by simpa only [norm_star,one_mul] using
        add_le_add (mul_le_mul_of_nonneg_right hs (norm_nonneg (a*t-t*a))) (le_refl ‖(star s*t)*a‖)
  refine ⟨?_,?_,?_⟩
  · have hh := hcomp s hs; linarith
  · have hh := hcomp t ht; linarith
  · linarith

lemma contractiveIdentityDiagonalization_iff_localCentralCuntzPair :
    ContractiveIdentityDiagonalization A ↔ LocalCentralCuntzPair A :=
  ⟨ContractiveIdentityDiagonalization.localCentralCuntzPair,
    LocalCentralCuntzPair.contractiveIdentityDiagonalization⟩

end NonUnitalEstimate

end

end WeakPureInfiniteness
end

end OAI
