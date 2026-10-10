import Mathlib
import OAI.Combinatorics.SharpRamsey.Learning.PreparedResidualBounds

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset
open scoped Classical BigOperators
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedPreparedOverlapBounds_1 : Finite (Projectivization K V) := by
  let : Finite V := Module.finite_of_finite K
  infer_instance
local instance flat_JoinedPreparedOverlapBounds_2 : Fintype (Projectivization K V) := Fintype.ofFinite _
local instance flat_JoinedPreparedOverlapBounds_3 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedPreparedOverlapBounds_4 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _
local instance flat_JoinedPreparedOverlapBounds_5 : Finite (Submodule K V) := by
  let : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun W : Submodule K V => (W : Set V)) SetLike.coe_injective
local instance flat_JoinedPreparedOverlapBounds_6 : Fintype (Submodule K V) := Fintype.ofFinite _

lemma pairs_of_radial_bound (hdim : Module.finrank K V=4)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c a K₀ : ℝ)
    (hr : ((richRadials S x c a).card:ℝ)*a^100≤K₀)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule≤LinearMap.ker H.rep) :
    ((largePairs S x c a A).card:ℝ)*a^200≤K₀*((Nat.card K:ℝ)+1)^2*a^100 := by
  have hh : ((largePairs S x c a A).card:ℝ)≤
      (richRadials S x c a).card*((Nat.card K:ℝ)+1)^2 := by
    exact_mod_cast largePairs_card hdim S x c a A hA
  have h100 : 0≤a^100 := by
    have heven : Even (100 : ℕ) := by decide
    exact heven.pow_nonneg a
  have he : a^200=a^100*a^100 := by rw [← pow_add]
  calc
    ((largePairs S x c a A).card:ℝ)*a^200 =
        ((largePairs S x c a A).card:ℝ)*(a^100*a^100) := by rw [he]
    _ ≤ ((richRadials S x c a).card*((Nat.card K:ℝ)+1)^2)*(a^100*a^100) :=
      mul_le_mul_of_nonneg_right hh (mul_nonneg h100 h100)
    _ = ((richRadials S x c a).card*a^100)*(((Nat.card K:ℝ)+1)^2*a^100) := by ac_rfl
    _ ≤ K₀*(((Nat.card K:ℝ)+1)^2*a^100) :=
      mul_le_mul_of_nonneg_right hr (mul_nonneg (sq_nonneg _) h100)
    _ = K₀*((Nat.card K:ℝ)+1)^2*a^100 := by rw [mul_assoc]

lemma neighbors_empty_of_radials (hdim : Module.finrank K V=4)
    (S : Finset (Projectivization K V)) (x : Projectivization K V) (c a : ℝ)
    (hr : (richRadials S x c a).card=0)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule≤LinearMap.ker H.rep)
    (H : Projectivization K (Module.Dual K V)) (hH : H∈A) :
    largeNeighbors S x c a A H=∅ := by
  apply card_eq_zero.mp
  have hh := neighbors_card hdim S x c a A hA H (hA H hH)
  have hz : (richRadials S x c a∩lines x H).card=0 := by
    have hp := card_le_card (inter_subset_left : richRadials S x c a∩lines x H⊆richRadials S x c a)
    omega
  rw [hz,zero_mul] at hh
  omega

theorem list_overlap_exceptions (hdim : Module.finrank K V=4)
    (F : Finset (Submodule K V)) (m : ℕ)
    (S : Finset (Projectivization K V)) (bs : List (Submodule K V))
    (h : GreedyPreparation.Complete F planePoints m S bs)
    (c K₀ : ℝ) (hc : 0<c) (hK : 0≤K₀) (T : Finset I) (a : I→ℝ)
    (ha : ∀ i∈T,0<a i)
    (hJ : ∀ i∈T,K₀<c*(GreedyPreparation.removed S planePoints bs).card*a i^99 →
      2*bs.length≤⌈a i/c⌉₊)
    (hM : ∀ i∈T,K₀<c*(GreedyPreparation.removed S planePoints bs).card*a i^99 →
      4≤⌈a i/c⌉₊) :
    ∃ D : Finset (Projectivization K V),
      (D.card:ℝ)*K₀≤8*(c*(GreedyPreparation.removed S planePoints bs).card)^2*∑ i∈T,a i^98 ∧
      ∀ x,x∉D → ∀ i∈T,∀ A : Finset (Projectivization K (Module.Dual K V)),
      (∀ H∈A,x.submodule≤LinearMap.ker H.rep) →
      ((largePairs (GreedyPreparation.removed S planePoints bs \
        (GreedyPreparation.own S planePoints bs x∪{x})) x c (a i) A).card:ℝ)*a i^200≤
      K₀*((Nat.card K:ℝ)+1)^2*a i^100 := by
  let X := fun x => GreedyPreparation.removed S planePoints bs \
        (GreedyPreparation.own S planePoints bs x∪{x})
  let r := fun x i => (richRadials (X x) x c (a i)).card
  have hcrude (x : Projectivization K V) (i : I) (_hi : i∈T) :
      (r x i:ℝ)*a i≤c*(GreedyPreparation.removed S planePoints bs).card := by
    apply (richRadials_mul_le (X x) x c (a i) hc.le).trans
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (card_le_card sdiff_subset)) hc.le
  have hpair (i : I) (hi : i∈T)
      (hk : K₀<c*(GreedyPreparation.removed S planePoints bs).card*a i^99) :
      (∑ x,(r x i:ℝ))*a i^2≤8*(c*(GreedyPreparation.removed S planePoints bs).card)^2 :=
    list_radial_pairs F m S bs h c (a i) hc (ha i hi).le (hJ i hi hk) (hM i hi hk)
  obtain ⟨D,hcard,hbound⟩ := RadialExceptions.radial_exceptions T a ha r
    (c*(GreedyPreparation.removed S planePoints bs).card) K₀
    (8*(c*(GreedyPreparation.removed S planePoints bs).card)^2) hK (by positivity) hcrude hpair
  refine ⟨D,hcard,?_⟩
  intro x hx i hi A hA
  exact pairs_of_radial_bound hdim (X x) x c (a i) K₀ (hbound x hx i hi) A hA

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
