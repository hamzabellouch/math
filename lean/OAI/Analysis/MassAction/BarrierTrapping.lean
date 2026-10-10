import OAI.Analysis.MassAction.FiniteMinimum
import OAI.Analysis.MassAction.MassActionDot
import OAI.Analysis.MassAction.PlateauGeometry

namespace OAI

universe uIota

noncomputable section

namespace Problem326.Barrier

/-- The finite affine minimum used as a barrier. All minimizing labels are
active; no tie-breaking convention is built into this definition. -/
def affineMinimum {d : ℕ} {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → Fin d → ℝ) (c : ι → ℝ) (z : Fin d → ℝ) : ℝ :=
  s.inf' hs (fun i => dot (a i) z + c i)

/-- Finite-segment trapping for a vector field with nonnegative derivatives
of every active affine branch. This theorem does not assume a global solution
or any reaction-network property: those enter only when supplying `hactive`. -/
theorem affine_minimum_traps_segment
    {d : ℕ} {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → Fin d → ℝ) (c : ι → ℝ)
    {B : Set (Fin d → ℝ)} {M T : ℝ}
    {f : (Fin d → ℝ) → (Fin d → ℝ)} {x : ℝ → (Fin d → ℝ)}
    (hT : 0 ≤ T) (hB : IsClosed B)
    (hceil : ∀ z, affineMinimum s hs a c z ≤ M)
    (hboundary : ∀ z ∈ frontier B, affineMinimum s hs a c z ≠ M)
    (hactive : ∀ z ∈ B, ∀ i ∈ s,
      dot (a i) z + c i = affineMinimum s hs a c z →
      0 ≤ dot (a i) (f z))
    (hx : ContinuousOn x (Set.Icc 0 T))
    (hxderiv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt x (f (x t)) t)
    (hx0 : x 0 ∈ interior B)
    (hF0 : affineMinimum s hs a c (x 0) = M) :
    Set.MapsTo x (Set.Icc 0 T)
      {z | z ∈ interior B ∧ affineMinimum s hs a c z = M} := by
  apply Geometry.mapsTo_plateau_of_monotone_on_box hT hB hx hx0 hceil hF0 hboundary
  intro τ hτ hseg
  change MonotoneOn
    (fun t => s.inf' hs (fun i => dot (a i) (x t) + c i)) (Set.Icc 0 τ)
  apply monotoneOn_finset_inf'_of_active_deriv_nonneg hs
  · intro i hi
    have hc : Continuous (fun z : Fin d → ℝ => dot (a i) z + c i) := by
      unfold dot
      fun_prop
    exact hc.comp_continuousOn (hx.mono (Set.Icc_subset_Icc le_rfl hτ.2))
  · intro t ht i hi hai
    refine ⟨dot (a i) (f (x t)), ?_, ?_⟩
    · exact hactive (x t) (hseg ⟨ht.1.le, ht.2.le⟩) i hi hai
    · exact hasDerivAt_affineLabel
        (hxderiv t ⟨ht.1, ht.2.trans_le hτ.2⟩) (a i) (c i)

theorem forward_solution_trapped
    {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → Fin d → ℝ) (c : ι → ℝ)
    {B : Set (Fin d → ℝ)} {M T : ℝ} {x0 : Fin d → ℝ}
    {x : ℝ → (Fin d → ℝ)} (hT : 0 ≤ T) (hB : IsClosed B)
    (hceil : ∀ z, affineMinimum s hs a c z ≤ M)
    (hboundary : ∀ z ∈ frontier B, affineMinimum s hs a c z ≠ M)
    (hactive : ∀ z ∈ B, ∀ i ∈ s,
      dot (a i) z + c i = affineMinimum s hs a c z →
      0 ≤ dot (a i) (massAction N κ z))
    (hx : IsForwardSolutionOn N κ x0 T x)
    (hx0 : x0 ∈ interior B) (hF0 : affineMinimum s hs a c x0 = M) :
    Set.MapsTo x (Set.Icc 0 T)
      {z | z ∈ interior B ∧ affineMinimum s hs a c z = M} := by
  exact affine_minimum_traps_segment s hs a c hT hB hceil hboundary hactive
    hx.2.1 hx.2.2 (hx.1.symm ▸ hx0) (hx.1.symm ▸ hF0)

end Problem326.Barrier

end

end OAI
