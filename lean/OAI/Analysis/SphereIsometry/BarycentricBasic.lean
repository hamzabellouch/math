import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Basic

namespace OAI

/-!
# Finite barycenters

The point attached to a nonempty face in barycentric subdivision is its
ordinary finite average. The definition also assigns zero to the empty set.
-/

noncomputable section

open scoped BigOperators

namespace Tingley

variable {V W E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

def finiteBarycenter (p : V → E) (S : Finset V) : E :=
  (S.card : ℝ)⁻¹ • ∑ v ∈ S, p v

theorem finiteBarycenter_eq_centerMass (p : V → E) (S : Finset V) :
    finiteBarycenter p S = S.centerMass (fun _ => (1 : ℝ)) p := by
  simp [finiteBarycenter, Finset.centerMass]

@[simp] theorem finiteBarycenter_empty (p : V → E) :
    finiteBarycenter p ∅ = 0 := by
  simp [finiteBarycenter]

@[simp] theorem finiteBarycenter_singleton (p : V → E) (v : V) :
    finiteBarycenter p {v} = p v := by
  simp [finiteBarycenter]

theorem finiteBarycenter_congr {p q : V → E} {S : Finset V}
    (h : ∀ v ∈ S, p v = q v) :
    finiteBarycenter p S = finiteBarycenter q S := by
  unfold finiteBarycenter
  congr 1
  exact Finset.sum_congr rfl h

theorem finiteBarycenter_mem_convex {K : Set E} (hK : Convex ℝ K)
    {p : V → E} {S : Finset V} (hs : S.Nonempty)
    (hp : ∀ v ∈ S, p v ∈ K) : finiteBarycenter p S ∈ K := by
  rw [finiteBarycenter_eq_centerMass]
  apply hK.centerMass_mem
  · intro v hv
    exact zero_le_one
  · simpa using (Nat.cast_pos.mpr (Finset.card_pos.mpr hs) : 0 < (S.card : ℝ))
  · exact hp

theorem finiteBarycenter_mem_convexHull {p : V → E} {S T : Finset V}
    (hs : S.Nonempty) (hst : S ⊆ T) :
    finiteBarycenter p S ∈ convexHull ℝ (p '' (↑T : Set V)) := by
  apply finiteBarycenter_mem_convex (convex_convexHull ℝ _) hs
  intro v hv
  exact subset_convexHull ℝ _ ⟨v, hst hv, rfl⟩

theorem map_finiteBarycenter (L : E →ₗ[ℝ] F) (p : V → E) (S : Finset V) :
    L (finiteBarycenter p S) = finiteBarycenter (L ∘ p) S := by
  simp [finiteBarycenter]

theorem finiteBarycenter_map (e : V ↪ W) (p : W → E) (S : Finset V) :
    finiteBarycenter p (S.map e) = finiteBarycenter (p ∘ e) S := by
  simp [finiteBarycenter]

theorem finiteBarycenter_map_of_eq (e : V ↪ W) (p : V → E) (q : W → E)
    (S : Finset V) (h : ∀ v ∈ S, q (e v) = p v) :
    finiteBarycenter q (S.map e) = finiteBarycenter p S := by
  rw [finiteBarycenter_map]
  exact finiteBarycenter_congr h

theorem finiteBarycenter_apply {ι : Type*} [Fintype ι]
    (p : V → ι → ℝ) (S : Finset V) (i : ι) :
    finiteBarycenter p S i = (S.card : ℝ)⁻¹ * ∑ v ∈ S, p v i := by
  simp [finiteBarycenter, Finset.sum_apply]

end Tingley

end

end OAI
