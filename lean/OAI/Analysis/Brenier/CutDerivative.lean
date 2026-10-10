import OAI.Analysis.Brenier.CutVariation
import OAI.Analysis.Brenier.MovingTrace

namespace OAI

noncomputable section

open Filter Topology
open scoped InnerProductSpace

namespace Problem358.AffineHalfspaceSpeed

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The normal velocity of an affine cut, in a fixed transverse coordinate. -/
def speed (n u v : V) (r h : ℝ) (x : V) : ℝ :=
  (r + ⟪v, x⟫_ℝ) / (⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ)

theorem perturbed_affine_eq (n u v x : V) (c r h t : ℝ)
    (hface : ⟪n, x⟫_ℝ + c = 0) :
    ⟪n + h • v, x + t • u⟫_ℝ + (c + h * r) =
      t * (⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ) + h * (r + ⟪v, x⟫_ℝ) := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  nlinarith

/-- A tilted affine inequality is an exact moving scalar threshold. -/
theorem perturbed_nonneg_iff (n u v x : V) (c r h t : ℝ)
    (hface : ⟪n, x⟫_ℝ + c = 0)
    (hden : 0 < ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ) :
    0 ≤ ⟪n + h • v, x + t • u⟫_ℝ + (c + h * r) ↔
      -h * speed n u v r h x ≤ t := by
  rw [perturbed_affine_eq n u v x c r h t hface]
  unfold speed
  rw [← mul_div_assoc, div_le_iff₀ hden]
  constructor <;> intro hi <;> nlinarith

/-- The unperturbed cut is the zero threshold. -/
theorem base_nonneg_iff (n u x : V) (c t : ℝ)
    (hface : ⟪n, x⟫_ℝ + c = 0) (htrans : 0 < ⟪n, u⟫_ℝ) :
    0 ≤ ⟪n, x + t • u⟫_ℝ + c ↔ 0 ≤ t := by
  simpa [speed] using perturbed_nonneg_iff n u 0 x c 0 0 t hface (by simpa using htrans)

/-- The transverse denominator stays uniformly above half its initial value. -/
theorem eventually_denominator_half (n u v : V) (htrans : 0 < ⟪n, u⟫_ℝ) :
    ∀ᶠ h : ℝ in 𝓝 0, ⟪n, u⟫_ℝ / 2 < ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ := by
  have ht : Tendsto (fun h : ℝ => ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ)
      (𝓝 0) (𝓝 ⟪n, u⟫_ℝ) := by
    have hc : ContinuousAt (fun h : ℝ => ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ) 0 := by fun_prop
    simpa using hc.tendsto
  exact ht.eventually_const_lt (by linarith)

theorem continuousAt_speed (n u v : V) (r : ℝ) (x : V)
    (htrans : ⟪n, u⟫_ℝ ≠ 0) : ContinuousAt (fun h => speed n u v r h x) 0 := by
  unfold speed
  apply ContinuousAt.div continuousAt_const
  · fun_prop
  · simpa using htrans

theorem tendsto_speed (n u v : V) (r : ℝ) (x : V)
    (htrans : ⟪n, u⟫_ℝ ≠ 0) :
    Tendsto (fun h => speed n u v r h x) (𝓝 0)
      (𝓝 ((r + ⟪v, x⟫_ℝ) / ⟪n, u⟫_ℝ)) := by
  simpa [speed] using (continuousAt_speed n u v r x htrans).tendsto

/-- A uniform speed bound on a bounded subset of the reference face. -/
theorem abs_speed_le (n u v : V) (r h R : ℝ) (x : V)
    (htrans : 0 < ⟪n, u⟫_ℝ)
    (hden : ⟪n, u⟫_ℝ / 2 ≤ ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ)
    (hx : ‖x‖ ≤ R) :
    |speed n u v r h x| ≤ 2 * (|r| + ‖v‖ * R) / ⟪n, u⟫_ℝ := by
  have hdenpos : 0 < ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ := by linarith
  have hnum : |r + ⟪v, x⟫_ℝ| ≤ |r| + ‖v‖ * R := by
    calc
      |r + ⟪v, x⟫_ℝ| ≤ |r| + |⟪v, x⟫_ℝ| := abs_add_le _ _
      _ ≤ |r| + ‖v‖ * ‖x‖ := add_le_add (le_refl _) (abs_real_inner_le_norm v x)
      _ ≤ |r| + ‖v‖ * R := by gcongr
  have hnumpos : 0 ≤ |r| + ‖v‖ * R := le_trans (abs_nonneg _) hnum
  rw [speed, abs_div, abs_of_pos hdenpos]
  calc
    |r + ⟪v, x⟫_ℝ| / (⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ) ≤
        (|r| + ‖v‖ * R) / (⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ) := by
      exact div_le_div_of_nonneg_right hnum (le_of_lt hdenpos)
    _ ≤ (|r| + ‖v‖ * R) / (⟪n, u⟫_ℝ / 2) :=
      div_le_div_of_nonneg_left hnumpos (by positivity) hden
    _ = 2 * (|r| + ‖v‖ * R) / ⟪n, u⟫_ℝ := by ring

/-- The bound is simultaneous over the whole bounded face region. -/
theorem eventually_abs_speed_le (n u v : V) (r R : ℝ)
    (htrans : 0 < ⟪n, u⟫_ℝ) :
    ∀ᶠ h : ℝ in 𝓝 0, ∀ x : V, ‖x‖ ≤ R →
      |speed n u v r h x| ≤ 2 * (|r| + ‖v‖ * R) / ⟪n, u⟫_ℝ := by
  filter_upwards [eventually_denominator_half n u v htrans] with h hh x hx
  exact abs_speed_le n u v r h R x htrans (le_of_lt hh) hx

/-- Points in the rescaled moving strip converge to their reference-face point. -/
theorem tendsto_scaled_point (n u v x : V) (r a : ℝ)
    (htrans : ⟪n, u⟫_ℝ ≠ 0) :
    Tendsto (fun h : ℝ => x + (-h * speed n u v r h x * a) • u)
      (𝓝 0) (𝓝 x) := by
  have hs := tendsto_speed n u v r x htrans
  have hh : Tendsto (fun h : ℝ => -h * speed n u v r h x * a) (𝓝 0) (𝓝 0) := by
    simpa using (tendsto_id.neg.mul hs).mul_const a
  have hu : Tendsto (fun h : ℝ => (-h * speed n u v r h x * a) • u)
      (𝓝 0) (𝓝 (0 : V)) := by
    simpa using hh.smul_const u
  simpa using (tendsto_const_nhds (x := x)).add hu

variable [MeasurableSpace V] [BorelSpace V]

/-- Joint measurability remains valid even where the totalized denominator vanishes. -/
theorem measurable_speed (n u v : V) (r : ℝ) :
    Measurable (fun p : ℝ × V => speed n u v r p.1 p.2) := by
  unfold speed
  fun_prop

theorem measurable_scaled_point [SecondCountableTopology V] (n u v : V) (r a : ℝ) :
    Measurable (fun p : ℝ × V => p.2 + (-p.1 * speed n u v r p.1 p.2 * a) • u) := by
  exact measurable_snd.add
    (((measurable_fst.neg.mul (measurable_speed n u v r)).mul_const a).smul_const u)

end Problem358.AffineHalfspaceSpeed

end

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace

namespace Problem358

/-- Differentiation of an actual moving affine cut in a fixed transverse chart.
The affine threshold identity, local denominator bounds, velocity limit, and
velocity measurability are all consequences, not extra hypotheses. -/
theorem hasDerivAt_integral_affine_cut_difference
    {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {μ : Measure X} [SFinite μ] {ρ : Measure V}
    (base : X → V) (hbase : Measurable base) (n u v : V) (c r : ℝ)
    (hchart : MeasurePreserving
      (fun p : X × ℝ => base p.1 + p.2 • u) (μ.prod volume) ρ)
    (hface : ∀ x, ⟪n, base x⟫_ℝ + c = 0)
    (htrans : 0 < ⟪n, u⟫_ℝ)
    {f : ℝ → V → ℝ} (hf : ∀ h, Measurable (f h))
    (B trace : X → ℝ)
    (hlim : ∀ᵐ x ∂μ, ∀ a : ℝ,
      Tendsto (fun h : ℝ => f h
        (base x + (-h * AffineHalfspaceSpeed.speed n u v r h (base x) * a) • u))
        (nhds 0) (nhds (trace x)))
    (hbound : ∀ᵐ x ∂μ, ∀ h t : ℝ, ‖f h (base x + t • u)‖ ≤ B x)
    (hdom : Integrable
      (fun x => (2 * (|r| + ‖v‖ * ‖base x‖) / ⟪n, u⟫_ℝ) * B x) μ)
    (hInt : ∀ᶠ h in nhds 0, Integrable (f h) ρ) :
    HasDerivAt (fun h : ℝ => ∫ y,
      f h y *
        ((if 0 ≤ ⟪n + h • v, y⟫_ℝ + (c + h * r) then (1 : ℝ) else 0) -
          (if 0 ≤ ⟪n, y⟫_ℝ + c then (1 : ℝ) else 0)) ∂ρ)
      (∫ x, ((r + ⟪v, base x⟫_ℝ) / ⟪n, u⟫_ℝ) * trace x ∂μ) 0 := by
  let speed : ℝ → X → ℝ := fun h x => AffineHalfspaceSpeed.speed n u v r h (base x)
  let s : Set ℝ := {h | ⟪n, u⟫_ℝ / 2 < ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ}
  have hs : s ∈ nhds 0 := AffineHalfspaceSpeed.eventually_denominator_half n u v htrans
  have hspeed : ∀ h, Measurable (speed h) := by
    intro h
    exact (AffineHalfspaceSpeed.measurable_speed n u v r).comp
      (measurable_const.prodMk hbase)
  have hlevel : ∀ h ∈ s, ∀ p : X × ℝ,
      0 ≤ ⟪n + h • v, base p.1 + p.2 • u⟫_ℝ + (c + h * r) ↔
        -(h * speed h p.1) ≤ p.2 := by
    intro h hh p
    have hpos : 0 < ⟪n, u⟫_ℝ + h * ⟪v, u⟫_ℝ := by
      change ⟪n, u⟫_ℝ / 2 < _ at hh
      linarith
    simpa only [speed, neg_mul] using
      AffineHalfspaceSpeed.perturbed_nonneg_iff n u v (base p.1) c r h p.2
        (hface p.1) hpos
  have hspeedlim : ∀ᵐ x ∂μ,
      Tendsto (fun h => speed h x) (nhds 0)
        (nhds ((r + ⟪v, base x⟫_ℝ) / ⟪n, u⟫_ℝ)) :=
    Eventually.of_forall fun x =>
      AffineHalfspaceSpeed.tendsto_speed n u v r (base x) (ne_of_gt htrans)
  have hspeedbound : ∀ᵐ x ∂μ, ∀ h ∈ s,
      |speed h x| ≤ 2 * (|r| + ‖v‖ * ‖base x‖) / ⟪n, u⟫_ℝ := by
    apply Eventually.of_forall
    intro x h hh
    exact AffineHalfspaceSpeed.abs_speed_le n u v r h ‖base x‖ (base x)
      htrans (le_of_lt hh) le_rfl
  have hlim' : ∀ᵐ x ∂μ, ∀ a : ℝ,
      Tendsto (fun h : ℝ => f h (base x + (-(h * speed h x * a)) • u))
        (nhds 0) (nhds (trace x)) := by
    simpa only [speed, neg_mul] using hlim
  have hd := hasDerivAt_integral_cut_difference_of_chart hchart hs hf
    (ell := fun h y => ⟪n + h • v, y⟫_ℝ + (c + h * r))
    (fun _ => by fun_prop) hspeed hlevel hspeedlim hlim' hspeedbound
    (hbound.mono fun x hx h _ t => hx h t) hdom hInt
  simpa only [zero_smul, add_zero, zero_mul] using hd

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology InnerProductSpace BigOperators

namespace Problem358

/-- A compact source and an almost-everywhere regular reference face suffice to
differentiate a moving cut with all other moving cut indicators attached. In
particular, the trace limit, compact domination, ambient integrability, affine
velocity, and exact threshold identity are all proved internally. -/
theorem hasDerivAt_compact_affine_cut_remainder
    {ι X V : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {μ : Measure X} [SFinite μ] [IsFiniteMeasureOnCompacts μ]
    {ρ : Measure V} [IsFiniteMeasureOnCompacts ρ]
    {K : Set V} (hK : IsCompact K) (w : V → ℝ) (hw : Continuous w)
    (base : X → V) (hbase : Continuous base) (n u v : V) (c r : ℝ)
    (hchart : MeasurePreserving
      (fun p : X × ℝ => base p.1 + p.2 • u) (μ.prod volume) ρ)
    (P : V → X) (hP : Continuous P)
    (hprojection : ∀ (z : X) (t : ℝ), P (base z + t • u) = z)
    (hface : ∀ x, ⟪n, base x⟫_ℝ + c = 0)
    (htrans : 0 < ⟪n, u⟫_ℝ)
    (J : Finset ι) (ell : ℝ → ι → V → ℝ)
    (hell : ∀ i ∈ J, Continuous (fun p : ℝ × V => ell p.1 i p.2))
    (hregular : ∀ᵐ x ∂μ, base x ∉ frontier K ∧
      ∀ i ∈ J, ell 0 i (base x) ≠ 0) :
    HasDerivAt (fun h : ℝ => ∫ y,
      (K.indicator w y * ∏ i ∈ J, MovingCellTrace.cutIndicator (ell h i y)) *
        ((if 0 ≤ ⟪n + h • v, y⟫_ℝ + (c + h * r) then (1 : ℝ) else 0) -
          (if 0 ≤ ⟪n, y⟫_ℝ + c then (1 : ℝ) else 0)) ∂ρ)
      (∫ x, ((r + ⟪v, base x⟫_ℝ) / ⟪n, u⟫_ℝ) *
        (K.indicator w (base x) *
          ∏ i ∈ J, MovingCellTrace.cutIndicator (ell 0 i (base x))) ∂μ) 0 := by
  let f : ℝ → V → ℝ := fun h y =>
    K.indicator w y * ∏ i ∈ J, MovingCellTrace.cutIndicator (ell h i y)
  have hellM (h : ℝ) (i : ι) (hi : i ∈ J) : Measurable (ell h i) :=
    ((hell i hi).comp (continuous_const.prodMk continuous_id)).measurable
  have hf : ∀ h, Measurable (f h) := by
    intro h
    exact MovingCellTrace.measurable_remainder J hK.measurableSet hw.measurable
      (hellM h)
  have hInt : ∀ᶠ h in nhds 0, Integrable (f h) ρ := by
    apply Eventually.of_forall
    intro h
    exact MovingCellTrace.integrable_remainder J hK.measurableSet
      (hw.continuousOn.integrableOn_compact hK) (hellM h)
  have hA : Continuous
      (fun x => 2 * (|r| + ‖v‖ * ‖base x‖) / ⟪n, u⟫_ℝ) := by fun_prop
  obtain ⟨B, _, hdom, hbound⟩ :=
    MovingCellTrace.exists_compact_projection_domination
      (μ := μ) J hK hP (fun p : X × ℝ => base p.1 + p.2 • u)
      hprojection hw.continuousOn (fun h y i => ell h i y) hA
  have hlim : ∀ᵐ x ∂μ, ∀ a : ℝ,
      Tendsto (fun h : ℝ => f h
        (base x + (-h * AffineHalfspaceSpeed.speed n u v r h (base x) * a) • u))
        (nhds 0) (nhds (K.indicator w (base x) *
          ∏ i ∈ J, MovingCellTrace.cutIndicator (ell 0 i (base x)))) := by
    filter_upwards [hregular] with x hx
    intro a
    have hp := AffineHalfspaceSpeed.tendsto_scaled_point n u v (base x) r a
      (ne_of_gt htrans)
    apply MovingCellTrace.tendsto_remainder_trace J hp hx.1 hw.continuousOn _ hx.2
    intro i hi
    exact (hell i hi).continuousAt.tendsto.comp (tendsto_id.prodMk_nhds hp)
  exact hasDerivAt_integral_affine_cut_difference base hbase.measurable n u v c r
    hchart hface htrans hf B _ hlim
    (Eventually.of_forall fun x h t => hbound h x t) hdom hInt

end Problem358

end

end OAI
