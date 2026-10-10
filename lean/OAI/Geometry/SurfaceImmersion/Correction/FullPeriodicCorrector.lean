import OAI.Geometry.SurfaceImmersion.Correction.SmoothPeriodicCorrector
import OAI.Geometry.SurfaceImmersion.Primitive.SlowPeriodicDerivative

namespace OAI

/-! The three equations in the periodic corrector system of paper 094-01,
equation (periodic-corrector-system), with smooth dependence on slow parameters. -/

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicCorrector

open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- A mean-zero, jointly smooth solution of the complete periodic system.
The transverse equation follows from differentiating the pairing with `Y`. -/
theorem solve_full_smooth_family (v : A) (S : A → Submodule ℝ E) (Y C X₀ : A → E)
    (hY : ContDiff ℝ ∞ Y) (hC : ContDiff ℝ ∞ C) (hX₀ : ContDiff ℝ ∞ X₀)
    (hYC : ∀ p, fderiv ℝ Y p v = C p)
    (hdet : ∀ p, gramDet (Y p) (C p) ≠ 0)
    (hPY : ∀ p w, w ∈ S p → inner ℝ (Y p) w = 0)
    (hPC : ∀ p w, w ∈ S p → inner ℝ (C p) w = 0)
    (hPX : ∀ p w, w ∈ S p → inner ℝ (X₀ p) w = 0)
    (V : A → C(Period, E)) (hVmem : ∀ p t, V p t ∈ S p)
    (hV : ContDiff ℝ ∞ (fun z : A × ℝ => V z.1 (z.2 : Period)))
    (q : A → ℝ) (hq : ContDiff ℝ ∞ q) (hqpos : ∀ p, 0 < q p)
    (hcircle : ∀ p t, inner ℝ (V p t) (V p t) = q p)
    (h j e : A → C(Period, ℝ))
    (hhs : ContDiff ℝ ∞ (fun z : A × ℝ => h z.1 (z.2 : Period)))
    (hjs : ContDiff ℝ ∞ (fun z : A × ℝ => j z.1 (z.2 : Period)))
    (hes : ContDiff ℝ ∞ (fun z : A × ℝ => e z.1 (z.2 : Period)))
    (hmh : ∀ p, average (h p) = 0) (hmj : ∀ p, average (j p) = 0)
    (hme : ∀ p, average (e p) = 0) :
    ∃ U D : A → C(Period, E),
      ContDiff ℝ ∞ (fun z : A × ℝ => U z.1 (z.2 : Period)) ∧
      ContDiff ℝ ∞ (fun z : A × ℝ => D z.1 (z.2 : Period)) ∧
      (∀ p, average (U p) = 0) ∧
      (∀ (p : A) (t : ℝ), HasDerivAt (fun s : ℝ => U p (s : Period))
        (D p (t : Period)) t) ∧
      (∀ p t, inner ℝ (Y p) (D p t) = h p t) ∧
      (∀ p (t : ℝ), inner ℝ (Y p)
        (slowDerivative (fun z : A × ℝ => U z.1 (z.2 : Period)) v (p, t)) = j p (t : Period)) ∧
      (∀ p, fluctuation (fun t => inner ℝ (X₀ p + V p t) (D p t)) = e p) ∧
      (∀ O : Set A, IsOpen O → (∀ p ∈ O, h p = 0) →
        (∀ p ∈ O, j p = 0) → (∀ p ∈ O, e p = 0) → ∀ p ∈ O, U p = 0) := by
  let H := primitiveFamily h hhs hmh
  have hHs : ContDiff ℝ ∞ (fun z : A × ℝ => H z.1 (z.2 : Period)) :=
    primitiveFamily_smooth h hhs hmh
  have hH0 : ∀ p, average (H p) = 0 := primitiveFamily_mean_zero h hhs hmh
  let Hᵥ := slowDerivativeFamily H hHs v
  have hHᵥs : ContDiff ℝ ∞ (fun z : A × ℝ => Hᵥ z.1 (z.2 : Period)) :=
    slowDerivativeFamily_smooth H hHs v
  let K : A → C(Period, ℝ) := fun p => Hᵥ p - j p
  have hKs : ContDiff ℝ ∞ (fun z : A × ℝ => K z.1 (z.2 : Period)) := hHᵥs.sub hjs
  have hK0 (p : A) : average (K p) = 0 := by
    have hv0 : average (Hᵥ p) = 0 := slowDerivativeFamily_mean_zero H hHs hH0 v p
    change average (fun t => Hᵥ p t - j p t) = 0
    rw [average_sub (f := Hᵥ p) (g := j p) (Hᵥ p).continuous (j p).continuous,
      hv0, hmj p, sub_self]
  obtain ⟨U, D, hUs, hDs, hU0, hUd, hpair, hfluc, hUH, hzero⟩ :=
    solve_smooth_family S Y C X₀ hY hC hX₀ hdet hPY hPC hPX V hVmem hV
      q hq hqpos hcircle h K e hhs hKs hes hmh hK0 hme
  refine ⟨U, D, hUs, hDs, hU0, hUd, fun p t => (hpair p t).2, ?_, hfluc, ?_⟩
  · intro p t
    have hUt : ContDiff ℝ ∞ (fun p => U p (t : Period)) :=
      hUs.comp (contDiff_id.prodMk contDiff_const)
    have hHt : ContDiff ℝ ∞ (fun p => H p (t : Period)) :=
      hHs.comp (contDiff_id.prodMk contDiff_const)
    have he (p : A) : inner ℝ (Y p) (U p (t : Period)) = H p (t : Period) := hUH p t
    have hK : inner ℝ (C p) (U p (t : Period)) =
        fderiv ℝ (fun p => H p (t : Period)) p v - j p (t : Period) := by
      rw [fderiv_slice hHs]
      exact (hpair p (t : Period)).1
    have hd := directional_pairing_constraint
      (hY.differentiable (by simp) p) (hUt.differentiable (by simp) p)
      (hHt.differentiable (by simp) p) he (hYC p) hK
    rwa [fderiv_slice hUs] at hd
  · intro O hO hhO hjO heO p hp
    have hHO : ∀ q ∈ O, H q = 0 := fun q hq => primitiveFamily_zero_at h hhs hmh (hhO q hq)
    have hHvp : Hᵥ p = 0 := slowDerivativeFamily_zero_on H hHs hO hHO v hp
    have hKp : K p = 0 := by
      change Hᵥ p - j p = 0
      rw [hHvp, hjO p hp, sub_self]
    exact hzero p (hhO p hp) hKp (heO p hp)

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
