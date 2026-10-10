import OAI.Geometry.SurfaceImmersion.Geometry.CompactAnsatzAsymptotics
import OAI.Geometry.SurfaceImmersion.Primitive.LocalPeriodicAnsatzMetric

namespace OAI

/-! The leading jets of the supported local ansatz are the geometric profiles
of the initial periodic primitive. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector
open PeriodicExpansion (directionalMap)

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {O : TopologicalSpace.Opens A}

/-- Retain the actual coefficient values when a supported local family has
already been proved smooth after extension by zero. -/
def globalCoefficients (U : ℕ → Family O E)
    (hU : ∀ i, ContDiff ℝ ∞ (fun y : A × ℝ => (U i).val y.1 (y.2 : Period))) :
    ℕ → PeriodicExpansion.Family A E := fun i => ⟨(U i).val,hU i⟩

lemma globalCoefficients_finiteAnsatz (F : A → E) (U : ℕ → Family O E)
    (hU : ∀ i, ContDiff ℝ ∞ (fun y : A × ℝ => (U i).val y.1 (y.2 : Period)))
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    PeriodicExpansion.finiteAnsatz F (globalCoefficients U hU) ℓ L z =
      finiteAnsatz F U ℓ L z := rfl

lemma global_angle_eq_local (W : PeriodicExpansion.Family A E) (U : Family O E)
    (hW : W.val = U.val) {p : A} (hp : p ∈ O) (t : Period) :
    W.angle.val p t = U.angle.val p t := by
  refine Quotient.inductionOn' t ?_
  intro s
  rw [PeriodicExpansion.Family.angle_apply,Family.angle_apply U hp,hW]

namespace Geometry

variable [FiniteDimensional ℝ A] [CompleteSpace E]
  {dy : A} (g : Geometry (E := E) O dy)

/-- The leading angular correction is the mean-zero velocity primitive. -/
lemma initial_global_angle (W : PeriodicExpansion.Family A E)
    (hW : W.val = g.initial.val) {p : A} (hp : p ∈ O) (t : Period) :
    W.angle.val p t = g.V.val p t-average (g.V.val p) := by
  rw [global_angle_eq_local W g.initial hW hp,g.initial_angle]
  simp only [Family.sub_apply,Family.vectorMean_apply]

/-- Adding the leading angular correction to the old longitudinal derivative
gives precisely the prescribed velocity profile `X`. -/
lemma initial_global_longitudinal {F : A → E} (W : PeriodicExpansion.Family A E)
    (hW : W.val = g.initial.val) (dx : A)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p+average (g.V.val p))
    {p : A} (hp : p ∈ O) (t : Period) :
    directionalMap F dx p+W.angle.val p t = g.longitudinal.val p t := by
  rw [g.initial_global_angle W hW hp]
  change fderiv ℝ F p dx+(g.V.val p t-average (g.V.val p)) = _
  rw [hX p hp]
  simp only [longitudinal,Family.add_apply,Family.constant_apply _ _ hp]
  abel

/-- The second angular derivative of the primitive is the angular derivative
of the actual velocity loop, including its normalization by the mean. -/
lemma initial_global_angle_angle (W : PeriodicExpansion.Family A E)
    (hW : W.val = g.initial.val) {p : A} (hp : p ∈ O) (t : Period) :
    W.angle.angle.val p t = g.V.angle.val p t := by
  refine Quotient.inductionOn' t ?_
  intro s
  have hd := SmoothPeriodicCalculus.derivativeFamily_hasDerivAt
    W.angle.val W.angle.smooth p s
  change HasDerivAt (fun r : ℝ => W.angle.val p (r : Period))
    (W.angle.angle.val p (s : Period)) s at hd
  have he : (fun r : ℝ => W.angle.val p (r : Period)) =
      fun r : ℝ => g.V.val p (r : Period)-average (g.V.val p) :=
    funext (fun r => g.initial_global_angle W hW hp (r : Period))
  rw [he] at hd
  exact hd.unique ((g.V.angle_hasDerivAt hp s).sub_const _)

/-- Slow differentiation of the actual leading profile gives `X_y`, rather
than a separately supplied approximation. -/
lemma initial_global_longitudinal_slow {F : A → E} (hF : ContDiff ℝ ∞ F)
    (W : PeriodicExpansion.Family A E) (hW : W.val = g.initial.val) (dx : A)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p+average (g.V.val p))
    {p : A} (hp : p ∈ O) (s : ℝ) :
    directionalMap (directionalMap F dx) dy p+
      (W.angle.slow dy).val p (s : Period) =
        (g.longitudinal.slow dy).val p (s : Period) := by
  have he : (fun q : A => directionalMap F dx q+W.angle.val q (s : Period)) =ᶠ[𝓝 p]
      fun q : A => g.longitudinal.val q (s : Period) := by
    filter_upwards [O.isOpen.mem_nhds hp] with q hq
    exact g.initial_global_longitudinal W hW dx hX hq _
  have hd := congrArg (fun L : A →L[ℝ] E => L dy) he.fderiv_eq
  have hs : ContDiff ℝ ∞ (fun q : A => W.angle.val q (s : Period)) :=
    W.angle.smooth.comp (contDiff_id.prodMk contDiff_const)
  rw [fderiv_fun_add (f := directionalMap F dx)
    (g := fun q : A => W.angle.val q (s : Period))
    ((PeriodicExpansion.directionalMap_smooth hF dx).differentiable (by simp) p)
    (hs.differentiable (by simp) p)] at hd
  simp only [add_apply] at hd
  rw [PeriodicExpansion.Family.slow_apply,Family.slow_apply _ _ hp,
    ← SmoothPeriodicCalculus.fderiv_slice W.angle.smooth,
    ← LocalPeriodicCalculus.fderiv_slice O.isOpen g.longitudinal.smooth hp]
  exact hd

/-- All five leading-jet estimates for the same globally smooth local ansatz.
The hypotheses are the actual fixed coefficients and their defining primitive
identity; no derivative asymptotic is assumed. -/
theorem compact_initial_ansatz_profiles {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family O E)
    (hU : ∀ i, ContDiff ℝ ∞ (fun y : A × ℝ => (U i).val y.1 (y.2 : Period)))
    (hinit : U 0 = g.initial) {Q : Set A} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (ℓ : A →L[ℝ] ℝ) (dx : A) (hx : ℓ dx = 1) (hy : ℓ dy = 0)
    (hX : ∀ p ∈ O, fderiv ℝ F p dx = g.X₀ p+average (g.V.val p))
    (hY : ∀ p ∈ O, fderiv ℝ F p dy = g.Y p) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 < z → z ≤ 1 → ∀ p ∈ Q,
      let f := finiteAnsatz F U ℓ (n+1) z
      let t : Period := ((ℓ p/z : ℝ) : Period)
      ‖directionalMap f dy p-g.Y p‖ ≤ C*z ∧
      ‖directionalMap (directionalMap f dy) dy p-g.C p‖ ≤ C*z ∧
      ‖directionalMap f dx p-g.longitudinal.val p t‖ ≤ C*z ∧
      ‖directionalMap (directionalMap f dx) dy p-(g.longitudinal.slow dy).val p t‖ ≤ C*z ∧
      ‖z • directionalMap (directionalMap f dx) dx p-g.V.angle.val p t‖ ≤ C*z := by
  let W := globalCoefficients U hU
  have hW : (W 0).val = g.initial.val := by
    change (U 0).val = g.initial.val
    rw [hinit]
  obtain ⟨B,hB,hb⟩ := PeriodicExpansion.compact_finiteAnsatz_transverse_asymptotics
    hF W hQ ℓ (n+1) hy
  obtain ⟨C,hC,hc⟩ := PeriodicExpansion.compact_finiteAnsatz_longitudinal_asymptotics
    hF W hQ ℓ n hx hy
  obtain ⟨D,hD,hd⟩ := PeriodicExpansion.compact_finiteAnsatz_second_longitudinal_asymptotics
    hF W hQ ℓ n hx
  refine ⟨B+C+D,by positivity,?_⟩
  intro z hz hz1 p hp
  dsimp only
  have hpO := hQO hp
  have hb' := hb z hz hz1 p hp
  have hc' := hc z hz hz1 p hp
  have hd' := hd z hz hz1 p hp
  have hf : PeriodicExpansion.finiteAnsatz F W ℓ (n+1) z =
      finiteAnsatz F U ℓ (n+1) z := globalCoefficients_finiteAnsatz F U hU ℓ _ z
  rw [hf] at hb' hc' hd'
  have hY' : directionalMap F dy p = g.Y p := hY p hpO
  have hYY : directionalMap (directionalMap F dy) dy p = g.C p := by
    have he : directionalMap F dy =ᶠ[𝓝 p] g.Y := by
      filter_upwards [O.isOpen.mem_nhds hpO] with q hq
      exact hY q hq
    exact (congrArg (fun L : A →L[ℝ] E => L dy) he.fderiv_eq).trans (g.derivativeY p hpO)
  rw [hY',hYY] at hb'
  have hX' := g.initial_global_longitudinal (W 0) hW dx hX hpO ((ℓ p/z : ℝ) : Period)
  have hXY := g.initial_global_longitudinal_slow hF (W 0) hW dx hX hpO (ℓ p/z)
  have hXX := g.initial_global_angle_angle (W 0) hW hpO ((ℓ p/z : ℝ) : Period)
  simp only [PeriodicExpansion.Family.fastValue,hX',hXY] at hc'
  simp only [PeriodicExpansion.Family.fastValue,hXX] at hd'
  have hB' : B*z ≤ (B+C+D)*z := by nlinarith
  have hC' : C*z ≤ (B+C+D)*z := by nlinarith
  have hD' : D*z ≤ (B+C+D)*z := by nlinarith
  exact ⟨hb'.1.trans hB',hb'.2.trans hB',hc'.1.trans hC',hc'.2.trans hC',hd'.trans hD'⟩

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
