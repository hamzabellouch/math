import Mathlib.MeasureTheory.Measure.Portmanteau

namespace OAI

/-! A compact spectral set has a finite small-ball cover whose boundaries
have zero mass. The centers remain in the spectral set. -/

noncomputable section
open MeasureTheory Set Metric
open scoped Topology Classical

namespace InvariantIsing

lemma spectral_null_boundary_cover (μ : Measure ℝ) [SFinite μ]
    (K : Set ℝ) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ n : ℕ, ∃ c r : Fin n → ℝ,
      (∀ i, c i∈K) ∧ (∀ i, δ/2 < r i ∧ r i < δ) ∧
      (∀ i, μ (frontier (ball (c i) (r i)))=0) ∧
      K ⊆ ⋃ i, ball (c i) (r i) := by
  have hex (x : K) : ∃ r ∈ Ioo (δ/2) δ, μ (frontier (ball (x : ℝ) r))=0 := by
    simpa only [thickening_singleton] using
      exists_null_frontier_thickening μ ({(x : ℝ)} : Set ℝ) (by linarith : δ/2 < δ)
  choose r hr hnull using hex
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℝ) (r x))
    (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,mem_ball_self (lt_trans (half_pos hδ) (hr ⟨x,hx⟩).1)⟩)
  let A := {x : K // x∈t}
  let e := Fintype.equivFin A
  let c : Fin (Fintype.card A) → ℝ := fun i => ((e.symm i).1 : ℝ)
  let r' : Fin (Fintype.card A) → ℝ := fun i => r (e.symm i).1
  refine ⟨Fintype.card A,c,r',fun i => (e.symm i).1.2,fun i => hr (e.symm i).1,
    fun i => hnull (e.symm i).1,?_⟩
  intro x hx
  obtain ⟨y,hy⟩ := mem_iUnion.mp (ht hx)
  obtain ⟨hyt,hxy⟩ := mem_iUnion.mp hy
  refine mem_iUnion.mpr ⟨e ⟨y,hyt⟩,?_⟩
  simpa only [c,r',Equiv.symm_apply_apply] using hxy

end InvariantIsing

end

end OAI
