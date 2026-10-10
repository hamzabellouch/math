import OAI.Analysis.KadisonKastler.ConvexRowAverages
import OAI.Analysis.KadisonKastler.RowReplication

namespace OAI

/-! The normalized finite-row orbit is convex and invariant under row averaging. -/

namespace KadisonKastler

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem finiteRightAverage_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (r : κ → A) (F : A →ₗ[ℂ] A) :
    finiteRightAverage (r ∘ e) F = finiteRightAverage r F := by
  apply LinearMap.ext
  intro x
  exact Equiv.sum_comp e (fun j => F (x * r j) * star (r j))

def finiteRowOrbit (F : A →ₗ[ℂ] A) : Set (A →ₗ[ℂ] A) :=
  {G | ∃ (n : ℕ) (r : Fin n → A), (∑ i, r i * star (r i) = 1) ∧
    G = finiteRightAverage r F}

theorem finiteRowOrbit_self (F : A →ₗ[ℂ] A) : F ∈ finiteRowOrbit F := by
  refine ⟨1, fun _ => 1, by simp, ?_⟩
  apply LinearMap.ext
  intro x
  simp

theorem finiteRowOrbit_convex (F : A →ₗ[ℂ] A) : Convex ℝ (finiteRowOrbit F) := by
  classical
  rintro G ⟨m, r, hr, rfl⟩ K ⟨n, s, hs, rfl⟩ a b ha hb hab
  let t := convexRow a r s
  let e := (Fintype.equivFin (Fin m ⊕ Fin n)).symm
  refine ⟨Fintype.card (Fin m ⊕ Fin n), t ∘ e, ?_, ?_⟩
  · change (∑ i, t (e i) * star (t (e i))) = 1
    rw [Equiv.sum_comp e (fun j => t j * star (t j))]
    exact convexRow_normalized a ha (by linarith) r s hr hs
  · rw [finiteRightAverage_reindex e t F]
    dsimp only [t]
    rw [finiteRightAverage_convexRow a ha (by linarith), show 1 - a = b by linarith]

theorem finiteRowOrbit_invariant (F : A →ₗ[ℂ] A)
    {G : A →ₗ[ℂ] A} (hG : G ∈ finiteRowOrbit F)
    {m : ℕ} (r : Fin m → A) (hr : ∑ i, r i * star (r i) = 1) :
    finiteRightAverage r G ∈ finiteRowOrbit F := by
  classical
  obtain ⟨n, s, hs, rfl⟩ := hG
  let t : Fin m × Fin n → A := fun ij => r ij.1 * s ij.2
  let e := (Fintype.equivFin (Fin m × Fin n)).symm
  refine ⟨Fintype.card (Fin m × Fin n), t ∘ e, ?_, ?_⟩
  · change (∑ i, t (e i) * star (t (e i))) = 1
    rw [Equiv.sum_comp e (fun j => t j * star (t j))]
    exact finiteRow_product_normalized r s hr hs
  · rw [finiteRightAverage_reindex e t F, finiteRightAverage_comp]

variable [PartialOrder A] [StarOrderedRing A]

theorem finiteRowOrbit_complete_bound {F G : A →ₗ[ℂ] A} {c : ℝ}
    (hF : CompletelyBoundedBy F c) (hc : 0 ≤ c) (hG : G ∈ finiteRowOrbit F) :
    CompletelyBoundedBy G c := by
  obtain ⟨n, r, hr, rfl⟩ := hG
  exact hF.finiteRightAverage hc r hr

end

end KadisonKastler

end OAI
