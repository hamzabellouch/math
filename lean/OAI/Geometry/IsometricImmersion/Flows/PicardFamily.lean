import OAI.Geometry.IsometricImmersion.Flows.FlowExistence

namespace OAI

noncomputable section
open Set Metric Function
open scoped Topology NNReal ContDiff

namespace SmoothLocal.Flow

theorem exists_confined_continuous_picard_family
    {f : ℝ → ℝ → ℝ} {tmin tmax : ℝ} {t0 : Icc tmin tmax} {x0 : ℝ}
    {a r L K : ℝ≥0} (hf : IsPicardLindelof f t0 x0 a r L K) :
    ∃ Y : ℝ → ℝ → ℝ,
      (∀ s ∈ closedBall x0 r, Y s t0 = s ∧
        ∀ t ∈ Icc tmin tmax, HasDerivWithinAt (Y s) (f t (Y s t)) (Icc tmin tmax) t) ∧
      (∀ s ∈ closedBall x0 r, ∀ t, Y s t ∈ closedBall x0 a) ∧
      (∃ J : ℝ≥0, ∀ t, LipschitzOnWith J (fun s => Y s t) (closedBall x0 r)) ∧
      ContinuousOn (uncurry Y) (closedBall x0 r ×ˢ Icc tmin tmax) ∧
      (∀ s ∈ closedBall x0 r, LipschitzOnWith L (Y s) (Icc tmin tmax)) := by
  classical
  have hex (s : ℝ) (hs : s ∈ closedBall x0 r) :=
    ODE.FunSpace.exists_isFixedPt_next hf hs
  choose alpha halpha using hex
  let Y : ℝ → ℝ → ℝ := fun s => if hs : s ∈ closedBall x0 r then
    (alpha s hs).compProj else fun _ => 0
  have hY (s : ℝ) (hs : s ∈ closedBall x0 r) : Y s = (alpha s hs).compProj := by
    simp only [Y, dite_eq_left hs]
  have hstart (s : ℝ) (hs : s ∈ closedBall x0 r) : Y s t0 = s := by
    rw [hY s hs, ODE.FunSpace.compProj_val, ← halpha s hs,
      ODE.FunSpace.next_apply₀]
  have hderiv (s : ℝ) (hs : s ∈ closedBall x0 r) (t : ℝ)
      (ht : t ∈ Icc tmin tmax) :
      HasDerivWithinAt (Y s) (f t (Y s t)) (Icc tmin tmax) t := by
    rw [hY s hs]
    apply ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
      (alpha s hs).continuous_compProj.continuousOn
      (fun _ _ => (alpha s hs).compProj_mem_closedBall hf.mul_max_le) s ht
      |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← halpha s hs]
    rw [ODE.FunSpace.compProj_of_mem ht']
    exact ODE.FunSpace.next_apply hf hs (alpha s hs)
  have hrange (s : ℝ) (hs : s ∈ closedBall x0 r) (t : ℝ) :
      Y s t ∈ closedBall x0 a := by
    rw [hY s hs]
    exact (alpha s hs).compProj_mem_closedBall hf.mul_max_le
  obtain ⟨J, hJ⟩ := ODE.FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
  have hinitLip (t : ℝ) : LipschitzOnWith J (fun s => Y s t) (closedBall x0 r) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs u hu
    rw [hY s hs, hY u hu, ODE.FunSpace.compProj_apply, ODE.FunSpace.compProj_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply,
      ← ODE.FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc tmin tmax) := ⟨t0⟩
    apply ContinuousMap.dist_le_iff_of_nonempty.mp
    exact hJ s u hs hu (alpha s hs) (alpha u hu) (halpha s hs) (halpha u hu)
  have hcont : ContinuousOn (uncurry Y) (closedBall x0 r ×ˢ Icc tmin tmax) := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ J
    · intro s hs
      exact HasDerivWithinAt.continuousOn (hderiv s hs)
    · intro t _
      exact hinitLip t
  have htimeLip (s : ℝ) (hs : s ∈ closedBall x0 r) :
      LipschitzOnWith L (Y s) (Icc tmin tmax) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht u hu
    rw [hY s hs, ODE.FunSpace.compProj_of_mem ht, ODE.FunSpace.compProj_of_mem hu]
    exact (alpha s hs).lipschitzWith.dist_le_mul ⟨t, ht⟩ ⟨u, hu⟩
  exact ⟨Y, fun s hs => ⟨hstart s hs, hderiv s hs⟩, hrange, ⟨J, hinitLip⟩, hcont, htimeLip⟩

end SmoothLocal.Flow

end

end OAI
