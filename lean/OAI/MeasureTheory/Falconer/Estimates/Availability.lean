import OAI.MeasureTheory.Falconer.Estimates.AllDimensions
import OAI.MeasureTheory.Falconer.Angular.AngularBootstrap
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

namespace OAI

/-!
# Available radial exponents in the original product measure

These definitions record `prep:availability`. A bad set is a measurable
set of original pairs, and each remaining radial fiber is measured using
the original opposite marginal. No fiber is renormalized.
The closure and bootstrap express parts of `prep:thin-upgrade`.
-/

namespace Falconer
open Set MeasureTheory Filter
open scoped ENNReal Topology

/-- Radial direction, assigned zero on the diagonal. The application uses
separated supports, so this arbitrary diagonal value has no effect. -/
noncomputable def radialDirection {d : ℕ} (x y : Space d) : Space d :=
  ‖y - x‖⁻¹ • (y - x)

/-- Both directional cap estimates, using the original opposite probability. -/
def RadialCapBound {d : ℕ} (μ ν : ProbabilityMeasure (Space d))
    (G : Set (Space d × Space d)) (N : ℕ) (e q : ℝ) : Prop :=
  (∀ x ∈ (μ : Measure (Space d)).support, ∀ w : Space d, ‖w‖ = 1 →
    ∀ u : ℝ, ((2 : ℝ) ^ N)⁻¹ ≤ u → u ≤ 1 →
    (ν : Measure (Space d)) {y | (x, y) ∈ G ∧ dist (radialDirection x y) w < u} ≤
      ENNReal.ofReal (((2 : ℝ) ^ N) ^ e * u ^ q)) ∧
  (∀ y ∈ (ν : Measure (Space d)).support, ∀ w : Space d, ‖w‖ = 1 →
    ∀ u : ℝ, ((2 : ℝ) ^ N)⁻¹ ≤ u → u ≤ 1 →
    (μ : Measure (Space d)) {x | (x, y) ∈ G ∧ dist (radialDirection y x) w < u} ≤
      ENNReal.ofReal (((2 : ℝ) ^ N) ^ e * u ^ q))

/-- A radial cap exponent available after a power-small deletion of original
pairs. Constants and the starting scale may depend on the desired loss. -/
def CapAvailable {d : ℕ} (μ ν : ProbabilityMeasure (Space d))
    (Γ : ℕ → Set (Space d × Space d)) (q : ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ K : ℕ,
    ∀ N ≥ K, ∃ B : Set (Space d × Space d),
      MeasurableSet B ∧ B ⊆ Γ N ∧
      ((μ : Measure (Space d)).prod (ν : Measure (Space d))) B ≤
        ENNReal.ofReal (C * ((2 : ℝ) ^ N) ^ (-c)) ∧
      RadialCapBound μ ν (Γ N \ B) N e q

private theorem cap_power_change {R u q q' a : ℝ}
    (hR : 1 ≤ R) (hu : R⁻¹ ≤ u) (hu1 : u ≤ 1)
    (ha : 0 ≤ a) (hgap : q' - q ≤ a) : u ^ q ≤ R ^ a * u ^ q' := by
  by_cases hqq : q ≤ q'
  · exact cap_exponent_loss_transfer hR hu hqq hgap
  · have hupos : 0 < u := (inv_pos.mpr (zero_lt_one.trans_le hR)).trans_le hu
    have hp := Real.rpow_le_rpow_of_exponent_ge hupos hu1 (not_le.mp hqq).le
    exact hp.trans (le_mul_of_one_le_left (Real.rpow_nonneg hupos.le _) (Real.one_le_rpow hR ha))

private theorem cap_bound_change {R u q q' e a : ℝ}
    (hR : 1 ≤ R) (hu : R⁻¹ ≤ u) (hu1 : u ≤ 1)
    (ha : 0 ≤ a) (hgap : q' - q ≤ a) :
    R ^ e * u ^ q ≤ R ^ (e + a) * u ^ q' := by
  calc
    R ^ e * u ^ q ≤ R ^ e * (R ^ a * u ^ q') :=
      mul_le_mul_of_nonneg_left (cap_power_change hR hu hu1 ha hgap) (Real.rpow_nonneg (by linarith) _)
    _ = R ^ (e + a) * u ^ q' := by
      rw [Real.rpow_add (zero_lt_one.trans_le hR)]
      ring

theorem RadialCapBound.change_exponent {d N : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {G : Set (Space d × Space d)} {e q q' a : ℝ}
    (h : RadialCapBound μ ν G N e q) (ha : 0 ≤ a) (hgap : q' - q ≤ a) :
    RadialCapBound μ ν G N (e + a) q' := by
  have hR : 1 ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  constructor
  · intro x hx w hw u hu hu1
    exact (h.1 x hx w hw u hu hu1).trans
      (ENNReal.ofReal_le_ofReal (cap_bound_change hR hu hu1 ha hgap))
  · intro y hy w hw u hu hu1
    exact (h.2 y hy w hw u hu hu1).trans
      (ENNReal.ofReal_le_ofReal (cap_bound_change hR hu hu1 ha hgap))

/-- Restricting a pair relation can only decrease each original radial fiber. -/
theorem RadialCapBound.mono {d N : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {G H : Set (Space d × Space d)} {e q : ℝ}
    (h : RadialCapBound μ ν G N e q) (hHG : H ⊆ G) :
    RadialCapBound μ ν H N e q := by
  constructor
  · intro x hx w hw u hu hu1
    have hsets : {y | (x, y) ∈ H ∧ dist (radialDirection x y) w < u} ⊆
        {y | (x, y) ∈ G ∧ dist (radialDirection x y) w < u} := by
      rintro y ⟨hy, hd⟩
      exact ⟨hHG hy, hd⟩
    exact (measure_mono hsets).trans (h.1 x hx w hw u hu hu1)
  · intro y hy w hw u hu hu1
    have hsets : {x | (x, y) ∈ H ∧ dist (radialDirection y x) w < u} ⊆
        {x | (x, y) ∈ G ∧ dist (radialDirection y x) w < u} := by
      rintro x ⟨hx, hd⟩
      exact ⟨hHG hx, hd⟩
    exact (measure_mono hsets).trans (h.2 y hy w hw u hu hu1)

/-- Integer cap bounds continue to hold after the coarse pair filters of
`prep:coarse-filter` are imposed. Only the original bad pairs still lying
inside the new filter need to be deleted. -/
theorem CapAvailable.restrict {d : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {Γ Γ' : ℕ → Set (Space d × Space d)} {q : ℝ}
    (hq : CapAvailable μ ν Γ q) (hΓ' : ∀ N, MeasurableSet (Γ' N))
    (hsub : ∀ N, Γ' N ⊆ Γ N) : CapAvailable μ ν Γ' q := by
  intro e he
  obtain ⟨c, C, hc, hC, K, hK⟩ := hq e he
  refine ⟨c, C, hc, hC, K, ?_⟩
  intro N hN
  obtain ⟨B, hB, _, hmass, hcap⟩ := hK N hN
  refine ⟨B ∩ Γ' N, hB.inter (hΓ' N), inter_subset_right,
    (measure_mono inter_subset_left).trans hmass, hcap.mono ?_⟩
  intro z hz
  exact ⟨hsub N hz.1, fun hb => hz.2 ⟨hb, hz.1⟩⟩

/-- Decreasing the requested cap exponent needs no additional deletion. -/
theorem CapAvailable.mono {d : ℕ} {μ ν : ProbabilityMeasure (Space d)}
    {Γ : ℕ → Set (Space d × Space d)} {q q' : ℝ}
    (hq : CapAvailable μ ν Γ q) (hqq : q' ≤ q) : CapAvailable μ ν Γ q' := by
  intro e he
  obtain ⟨c, C, hc, hC, K, hK⟩ := hq e he
  refine ⟨c, C, hc, hC, K, ?_⟩
  intro N hN
  obtain ⟨B, hB, hsub, hmass, hcap⟩ := hK N hN
  refine ⟨B, hB, hsub, hmass, ?_⟩
  simpa using hcap.change_exponent (le_refl (0 : ℝ)) (sub_nonpos.mpr hqq)

/-- The allowance of every positive scale loss makes availability closed in
the exponent. The same original bad sets and deletion rates work after the
small exponent change. -/
theorem isClosed_capAvailable {d : ℕ} (μ ν : ProbabilityMeasure (Space d))
    (Γ : ℕ → Set (Space d × Space d)) :
    IsClosed {q : ℝ | CapAvailable μ ν Γ q} := by
  apply isClosed_of_closure_subset
  intro q hq e he
  obtain ⟨q₀, hq₀, hdist⟩ := Metric.mem_closure_iff.1 hq (e / 2) (by linarith)
  obtain ⟨c, C, hc, hC, K, hK⟩ := hq₀ (e / 2) (by linarith)
  refine ⟨c, C, hc, hC, K, ?_⟩
  intro N hN
  obtain ⟨B, hB, hsub, hmass, hcap⟩ := hK N hN
  refine ⟨B, hB, hsub, hmass, ?_⟩
  have hgap : q - q₀ ≤ e / 2 := by
    rw [Real.dist_eq] at hdist
    exact le_of_lt ((le_abs_self _).trans_lt hdist)
  convert hcap.change_exponent (by linarith : (0 : ℝ) ≤ e / 2) hgap using 1
  ring

/-- The thin-tube endpoint follows from the integer starting exponent and
the one-scale strict improvement, using closure of cap availability. -/
theorem capAvailable_half_integer {d : ℕ} (k : ℕ)
    (μ ν : ProbabilityMeasure (Space d)) (Γ : ℕ → Set (Space d × Space d))
    (hstart : CapAvailable μ ν Γ ((k : ℝ) - 1))
    (himprove : ∀ q : ℝ, (k : ℝ) - 1 ≤ q → q < (k : ℝ) - 1 / 2 →
      CapAvailable μ ν Γ q →
      ∃ q' : ℝ, q < q' ∧ q' ≤ (k : ℝ) - 1 / 2 ∧ CapAvailable μ ν Γ q') :
    CapAvailable μ ν Γ ((k : ℝ) - 1 / 2) := by
  let A := Set.Icc ((k : ℝ) - 1) ((k : ℝ) - 1 / 2) ∩
    {q : ℝ | CapAvailable μ ν Γ q}
  have hclosed : IsClosed A := isClosed_Icc.inter (isClosed_capAvailable μ ν Γ)
  have hfirst : (k : ℝ) - 1 ∈ A := ⟨⟨le_rfl, by linarith⟩, hstart⟩
  have hstep : ∀ q ∈ A, q < (k : ℝ) - 1 / 2 → ∃ q' ∈ A, q < q' := by
    intro q hq hqlt
    obtain ⟨q', hqq', hq'upper, hq'available⟩ := himprove q hq.1.1 hqlt hq.2
    exact ⟨q', ⟨⟨hq.1.1.trans hqq'.le, hq'upper⟩, hq'available⟩, hqq'⟩
  exact (thin_tube_bootstrap_endpoint k A hclosed hfirst (fun q hq => hq.1.2) hstep).2

end Falconer

end OAI
