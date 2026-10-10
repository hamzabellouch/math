import OAI.Analysis.MassAction.Model
import OAI.Analysis.MassAction.FiniteMinimum
import OAI.Analysis.MassAction.PlateauGeometry

namespace OAI

universe uIota

noncomputable section

open Set

namespace Problem326

/-- Differentiation of a fixed linear functional along a state-space curve. -/
theorem hasDerivAt_dot_curve {d : ℕ} (a : Fin d → ℝ)
    {x : ℝ → (Fin d → ℝ)} {v : Fin d → ℝ} {t : ℝ}
    (hx : HasDerivAt x v t) :
    HasDerivAt (fun u => dot a (x u)) (dot a v) t := by
  unfold dot
  exact HasDerivAt.fun_sum fun i _ => (hasDerivAt_pi.mp hx i).const_mul (a i)

/-- Fixed affine functionals preserve continuity on a time interval. -/
theorem continuousOn_dot_curve {d : ℕ} (a : Fin d → ℝ)
    {x : ℝ → (Fin d → ℝ)} {S : Set ℝ} (hx : ContinuousOn x S) :
    ContinuousOn (fun t => dot a (x t)) S := by
  unfold dot
  fun_prop

/-- An active inward-pointing condition makes a finite affine minimum
nondecreasing along any differentiable curve in the specified region. -/
theorem affineMinimum_monotoneOn
    {d : ℕ} {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (B : Set (Fin d → ℝ))
    {x : ℝ → (Fin d → ℝ)} {u v : ℝ}
    (hx : ContinuousOn x (Icc u v))
    (hxd : ∀ t ∈ Ioo u v, HasDerivAt x (f (x t)) t)
    (hB : ∀ t ∈ Icc u v, x t ∈ B)
    (hinward : ∀ z ∈ B, ∀ i ∈ s,
      dot (a i) z + c i = s.inf' hs (fun j => dot (a j) z + c j) →
      0 ≤ dot (a i) (f z)) :
    MonotoneOn (fun t => s.inf' hs (fun i => dot (a i) (x t) + c i)) (Icc u v) := by
  apply monotoneOn_finset_inf'_of_active_deriv_nonneg hs
  · intro i hi
    exact (continuousOn_dot_curve (a i) hx).add continuousOn_const
  · intro t ht i hi hactive
    refine ⟨dot (a i) (f (x t)), hinward (x t) (hB t (Ioo_subset_Icc_self ht))
      i hi hactive, ?_⟩
    exact (hasDerivAt_dot_curve (a i) (hxd t ht)).add_const (c i)

/-- The maximum-level plateau is preserved along a solution segment in the
region where all active affine branches point inward. -/
theorem affineMinimum_eq_of_ceiling
    {d : ℕ} {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (B : Set (Fin d → ℝ))
    {x : ℝ → (Fin d → ℝ)} {u v M : ℝ}
    (hx : ContinuousOn x (Icc u v))
    (hxd : ∀ t ∈ Ioo u v, HasDerivAt x (f (x t)) t)
    (hB : ∀ t ∈ Icc u v, x t ∈ B)
    (hinward : ∀ z ∈ B, ∀ i ∈ s,
      dot (a i) z + c i = s.inf' hs (fun j => dot (a j) z + c j) →
      0 ≤ dot (a i) (f z))
    (hceiling : ∀ z ∈ B, s.inf' hs (fun i => dot (a i) z + c i) ≤ M)
    (hstart : s.inf' hs (fun i => dot (a i) (x u) + c i) = M) :
    ∀ t ∈ Icc u v, s.inf' hs (fun i => dot (a i) (x t) + c i) = M := by
  intro t ht
  apply le_antisymm (hceiling (x t) (hB t ht))
  rw [← hstart]
  exact affineMinimum_monotoneOn s hs a c f B hx hxd hB hinward
    ⟨le_rfl, ht.1.trans ht.2⟩ ht ht.1

/-- Exact finite-forward-solution specialization of affine plateau preservation. -/
theorem IsForwardSolutionOn.affineMinimum_eq
    {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    {z : Fin d → ℝ} {T : ℝ} {x : ℝ → (Fin d → ℝ)}
    (hx : IsForwardSolutionOn N κ z T x)
    {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (B : Set (Fin d → ℝ)) {M : ℝ}
    (hB : ∀ t ∈ Icc 0 T, x t ∈ B)
    (hinward : ∀ y ∈ B, ∀ i ∈ s,
      dot (a i) y + c i = s.inf' hs (fun j => dot (a j) y + c j) →
      0 ≤ dot (a i) (massAction N κ y))
    (hceiling : ∀ y ∈ B, s.inf' hs (fun i => dot (a i) y + c i) ≤ M)
    (hstart : s.inf' hs (fun i => dot (a i) z + c i) = M) :
    ∀ t ∈ Icc 0 T, s.inf' hs (fun i => dot (a i) (x t) + c i) = M := by
  apply affineMinimum_eq_of_ceiling s hs a c (massAction N κ) B
    hx.2.1 hx.2.2 hB hinward hceiling
  simpa [hx.1] using hstart

/-- A finite affine plateau traps any solution segment, without an a priori
assumption that the segment stays in the region. The first-boundary argument
uses the active inward estimate only inside the closed region. -/
theorem affineMinimum_trapped
    {d : ℕ} {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ)
    (f : (Fin d → ℝ) → (Fin d → ℝ)) (B : Set (Fin d → ℝ))
    {x : ℝ → (Fin d → ℝ)} {T M : ℝ}
    (hT : 0 ≤ T) (hclosed : IsClosed B)
    (hx : ContinuousOn x (Icc 0 T))
    (hxd : ∀ t ∈ Ioo 0 T, HasDerivAt x (f (x t)) t)
    (hx0 : x 0 ∈ interior B)
    (hinward : ∀ z ∈ B, ∀ i ∈ s,
      dot (a i) z + c i = s.inf' hs (fun j => dot (a j) z + c j) →
      0 ≤ dot (a i) (f z))
    (hceiling : ∀ z ∈ B, s.inf' hs (fun i => dot (a i) z + c i) ≤ M)
    (hstart : s.inf' hs (fun i => dot (a i) (x 0) + c i) = M)
    (hboundary : ∀ z ∈ frontier B,
      s.inf' hs (fun i => dot (a i) z + c i) ≠ M) :
    MapsTo x (Icc 0 T) (interior B) ∧
      ∀ t ∈ Icc 0 T, s.inf' hs (fun i => dot (a i) (x t) + c i) = M := by
  have hstay : MapsTo x (Icc 0 T) (interior B) := by
    apply Geometry.mapsTo_interior_of_no_first_boundary hT hclosed hx hx0
    intro τ hτ hseg hfront
    have hsub : Icc 0 τ ⊆ Icc 0 T := Icc_subset_Icc le_rfl hτ.2
    have heq := affineMinimum_eq_of_ceiling s hs a c f B (hx.mono hsub)
      (fun t ht => hxd t ⟨ht.1, ht.2.trans_le hτ.2⟩)
      hseg hinward hceiling hstart τ ⟨hτ.1, le_rfl⟩
    exact hboundary (x τ) hfront heq
  refine ⟨hstay, ?_⟩
  exact affineMinimum_eq_of_ceiling s hs a c f B hx hxd
    (fun t ht => interior_subset (hstay ht)) hinward hceiling hstart

/-- Exact mass-action specialization of the finite-interval trapping theorem. -/
theorem IsForwardSolutionOn.affineMinimum_trapped
    {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ}
    {z : Fin d → ℝ} {T : ℝ} {x : ℝ → (Fin d → ℝ)}
    (hx : IsForwardSolutionOn N κ z T x)
    {ι : Type uIota} (s : Finset ι) (hs : s.Nonempty)
    (a : ι → (Fin d → ℝ)) (c : ι → ℝ) (B : Set (Fin d → ℝ)) {M : ℝ}
    (hT : 0 ≤ T) (hclosed : IsClosed B) (hz : z ∈ interior B)
    (hinward : ∀ y ∈ B, ∀ i ∈ s,
      dot (a i) y + c i = s.inf' hs (fun j => dot (a j) y + c j) →
      0 ≤ dot (a i) (massAction N κ y))
    (hceiling : ∀ y ∈ B, s.inf' hs (fun i => dot (a i) y + c i) ≤ M)
    (hstart : s.inf' hs (fun i => dot (a i) z + c i) = M)
    (hboundary : ∀ y ∈ frontier B,
      s.inf' hs (fun i => dot (a i) y + c i) ≠ M) :
    MapsTo x (Icc 0 T) (interior B) ∧
      ∀ t ∈ Icc 0 T, s.inf' hs (fun i => dot (a i) (x t) + c i) = M := by
  apply Problem326.affineMinimum_trapped s hs a c (massAction N κ) B
    hT hclosed hx.2.1 hx.2.2
  · simpa [hx.1] using hz
  · exact hinward
  · exact hceiling
  · simpa [hx.1] using hstart
  · exact hboundary

end Problem326

end

end OAI
