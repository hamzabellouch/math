import Mathlib
import OAI.Analysis.WeakInfiniteness.SmallPartition
import OAI.Analysis.WeakInfiniteness.SpectralDeletion

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

open scoped BigOperators Topology CStarAlgebra

section CFCDeletion

variable {A : Type*} [CStarAlgebra A]

def ContinuouslySupported (U p : A) (S : Set ℝ) : Prop :=
  ∀ g : C(ℝ,ℝ), (∀ x ∈ S,g x=0) → p*cfc g U=0 ∧ cfc g U*p=0

lemma cfc_partition_sum (U : A) (hU : IsSelfAdjoint U)
    {ι : Type*} [Fintype ι] (f : ι → C(ℝ,ℝ))
    (hs : ∀ x ∈ spectrum ℝ U,∑ i,f i x=1) : ∑ i,cfc (f i) U=1 := by
  rw [← cfc_sum_univ (fun i => ⇑(f i)) U (fun i => (f i).continuous.continuousOn)]
  calc
    cfc (∑ i,⇑(f i)) U=cfc (fun _ : ℝ => 1) U := by
      apply cfc_congr
      intro x hx
      simpa using hs x hx
    _ = 1 := by rw [cfc_const_one ℝ U hU]

lemma cfc_mul_eq_zero_of_small_supports (U : A)
    (f g : C(ℝ,ℝ)) (c d δ : ℝ)
    (hf : tsupport f ⊆ Metric.ball c δ) (hg : tsupport g ⊆ Metric.ball d δ)
    (hcd : 2*δ ≤ dist c d) : cfc f U*cfc g U=0 := by
  rw [← cfc_mul f g U f.continuous.continuousOn g.continuous.continuousOn]
  calc
    cfc (fun x => f x*g x) U=cfc (fun _ : ℝ => 0) U := by
      apply cfc_congr
      intro x _
      by_cases hfx : f x=0
      · simp only [hfx,zero_mul]
      by_cases hgx : g x=0
      · simp only [hgx,mul_zero]
      have hx1 : dist x c < δ := hf (subset_tsupport f hfx)
      have hx2 : dist x d < δ := hg (subset_tsupport g hgx)
      have ht := dist_triangle c x d
      rw [dist_comm c x] at ht
      exfalso
      linarith
    _ = 0 := cfc_zero ℝ U

lemma vanishes_on_separated_sets (f g : C(ℝ,ℝ)) (c d δ : ℝ)
    (hf : tsupport f ⊆ Metric.ball c δ) (hg : tsupport g ⊆ Metric.ball d δ)
    (S T : Set ℝ) (hsep : ∀ x ∈ S,∀ y ∈ T,8*δ ≤ dist x y)
    (hcd : ¬4*δ < dist c d) :
    (∀ x ∈ S,f x=0) ∨ (∀ y ∈ T,g y=0) := by
  by_contra h
  push Not at h
  obtain ⟨⟨x,hx,hfx⟩,⟨y,hy,hgy⟩⟩ := h
  have hxc : dist x c < δ := hf (subset_tsupport f hfx)
  have hyd : dist y d < δ := hg (subset_tsupport g hgy)
  have ht1 := dist_triangle x c y
  have ht2 := dist_triangle c d y
  rw [dist_comm d y] at ht2
  have hs := hsep x hx y hy
  have h0 : 0 < δ := lt_of_le_of_lt (dist_nonneg) hxc
  have hc := le_of_not_gt hcd
  linarith

theorem exists_continuous_spectral_deletion (U V : A)
    (hU : IsSelfAdjoint U) (hV : IsSelfAdjoint V) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ H : A, IsSelfAdjoint H ∧ ∃ n : ℕ, ∃ e : Fin n → A,
      (∀ i,IsSelfAdjoint (e i)) ∧ (∑ i,e i=1) ∧ (∀ i,e i*H*e i=0) ∧
      ∀ (p q : A) (S T : Set ℝ), ContinuouslySupported U p S →
        ContinuouslySupported U q T → (∀ x ∈ S,∀ y ∈ T,ρ ≤ dist x y) →
        p*H*q=p*V*q := by
  classical
  let δ : ℝ := ρ/8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨n,c,f,hf,hfs,_⟩ := exists_small_partition (spectrum ℝ U)
    (ContinuousFunctionalCalculus.isCompact_spectrum U) hδ
  let e : Fin n → A := fun i => cfc (f i) U
  let R : Fin n → Fin n → Prop := fun j k => 4*δ < dist (c j) (c k)
  let H := finiteDeletion e V R
  have hesa : ∀ i,IsSelfAdjoint (e i) := fun i => cfc_predicate (f i) U
  refine ⟨H,finiteDeletion_selfAdjoint e V R hesa hV (fun j k => by
    dsimp [R]; rw [dist_comm]),n,e,hesa,cfc_partition_sum U hU f hfs,?_,?_⟩
  · apply finiteDeletion_diagonals e V R e
    intro l j k hjk
    dsimp only [R] at hjk
    by_cases hlj : 2*δ ≤ dist (c l) (c j)
    · exact Or.inl (cfc_mul_eq_zero_of_small_supports U (f l) (f j)
        (c l) (c j) δ (hf l) (hf j) hlj)
    · right
      apply cfc_mul_eq_zero_of_small_supports U (f k) (f l)
        (c k) (c l) δ (hf k) (hf l)
      have ht := dist_triangle (c j) (c l) (c k)
      rw [dist_comm (c j) (c l),dist_comm (c l) (c k)] at ht
      have hh := lt_of_not_ge hlj
      linarith
  · intro p q S T hp hq hsep
    apply finiteDeletion_preserves_corner e V p q R (cfc_partition_sum U hU f hfs)
    intro j k hjk
    have hs : ∀ x ∈ S,∀ y ∈ T,8*δ ≤ dist x y := by
      have heq : 8*δ=ρ := by dsimp [δ]; ring
      simpa only [heq] using hsep
    rcases vanishes_on_separated_sets (f j) (f k) (c j) (c k) δ
      (hf j) (hf k) S T hs hjk with hj | hk
    · exact Or.inl (hp (f j) hj).1
    · exact Or.inr (hq (f k) hk).2

end CFCDeletion

section Images

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
  [PartialOrder B] [StarOrderedRing B]

lemma both_signs_in_image_of_partition_diagonals (π : A →⋆ₐ[ℂ] B)
    {a : A} (ha : IsSelfAdjoint a) (hne : π a ≠ 0)
    {ι : Type*} [Fintype ι] (e : ι → A) (he : ∀ i,IsSelfAdjoint (e i))
    (hs : ∑ i,e i=1) (hd : ∀ i,e i*a*e i=0) :
    (π a)⁺ ≠ 0 ∧ (π a)⁻ ≠ 0 := by
  apply both_signs_of_partition_diagonals (ha.map π) hne (fun i => π (e i))
    (fun i => (he i).map π)
  · rw [← map_sum,hs,map_one]
  · intro i
    simpa only [map_mul,map_zero] using congrArg π (hd i)

end Images

end

end WeakPureInfiniteness
end

end OAI
