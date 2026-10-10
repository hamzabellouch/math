import OAI.Geometry.CylinderCovering.Radial.CapVariantsDefinitions
import OAI.Geometry.CylinderCovering.Radial.CapCosts
import OAI.Geometry.CylinderCovering.Radial.CapCoverage
import OAI.Geometry.CylinderCovering.Radial.PairedSweep

namespace OAI

noncomputable section
open Set Filter
open scoped Topology
namespace CylinderCovering.RadialCapVariants

lemma physicalCost_eq_Q (ε : ℝ) (R : ℝ → ℝ) :
    RadialPairedSweep.physicalCost (Real.sqrt 2) ε R = RadialCaps.Q R ε := by
  unfold RadialPairedSweep.physicalCost RadialCaps.Q RadialCaps.D0
  simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem coverLimit_of_paired (hpaired : RadialPairedSweep.PairedStatement)
    {ε : ℝ} {R : ℝ → ℝ}
    (hR : ContinuousOn R (Icc (-1 : ℝ) 1))
    (hR0 : ∀ r ∈ Icc (-1 : ℝ) 1, 0 ≤ R r) (hcover : SweepsCover ε R) :
    CoverLimit ε R := by
  intro tagU tagL htagU htagL
  obtain ⟨U, L, hUL, hlim⟩ := hpaired (Real.sqrt 2) ε (by positivity) R hR hR0
    tagU tagL htagU htagL
  refine ⟨U, L, ?_, ?_⟩
  · intro N hN
    obtain ⟨haxis, hU, hL⟩ := hUL N hN
    refine ⟨haxis, hU, hL, ?_⟩
    intro z hz
    rcases hcover hz with hzU | hzL
    · exact Or.inl (hU z hzU)
    · exact Or.inr (hL z hzL)
  · simpa only [physicalCost_eq_Q] using hlim

theorem finiteSaving_of_coverLimit {ε : ℝ} {R : ℝ → ℝ}
    (hcover : CoverLimit ε R) (hQ : RadialCaps.Q R ε < 1) : FiniteSaving ε := by
  intro tagU tagL htagU htagL
  obtain ⟨U, L, hUL, hlim⟩ := hcover tagU tagL htagU htagL
  have hlt : 2 * Real.sqrt 2 * RadialCaps.Q R ε < 2 * Real.sqrt 2 := by
    nlinarith [Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)]
  have hcost : ∀ᶠ N in atTop, TriangularCovering.totalArea (U N) +
      TriangularCovering.totalArea (L N) < 2 * Real.sqrt 2 :=
    hlim.eventually (gt_mem_nhds hlt)
  obtain ⟨N, hN, hcostN⟩ := ((Filter.eventually_gt_atTop (0 : ℕ)).and hcost).exists
  obtain ⟨haxis, _, _, hcoverN⟩ := hUL N hN
  exact ⟨N, hN, U N, L N, haxis, hcoverN, hcostN⟩

theorem assemble
    (hpaired : RadialPairedSweep.PairedStatement)
    (hlinear : ∀ β : ℝ, 0 < β → ∀ᶠ ε : ℝ in 𝓝[>] 0,
      SweepsCover ε (RadialCaps.linearCap β ε))
    (hcubic : ∀ c : ℝ, 9 / 2 ≤ c → ∀ ε : ℝ, 0 < ε →
      SweepsCover ε (RadialCaps.cubicCap c ε))
    (hfractional : ∀ c : ℝ, 0 < c → ∀ᶠ ε : ℝ in 𝓝[>] 0,
      SweepsCover ε (RadialCaps.fractionalCap c ε)) : LCFStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ
    have hcov : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        SweepsCover ε (RadialCaps.linearCap β ε) ∧ CoverLimit ε (RadialCaps.linearCap β ε) := by
      filter_upwards [hlinear β hβ] with ε hε
      exact ⟨hε, coverLimit_of_paired hpaired (RadialCaps.continuous_linearCap β ε).continuousOn
        (fun r _ => (RadialCaps.linearCap_pos hβ.le ε r).le) hε⟩
    refine ⟨hcov, RadialCaps.linear_cost_bigO hβ.le, ?_⟩
    intro hβ1
    filter_upwards [hcov, RadialCaps.linear_cost_strict hβ hβ1] with ε hε hQ
    exact ⟨hQ, finiteSaving_of_coverLimit hε.2 hQ⟩
  · intro c hc
    have hc0 : 0 ≤ c := by linarith
    have hcov : ∀ ε : ℝ, 0 < ε →
        SweepsCover ε (RadialCaps.cubicCap c ε) ∧ CoverLimit ε (RadialCaps.cubicCap c ε) := by
      intro ε hε
      have h := hcubic c hc ε hε
      exact ⟨h, coverLimit_of_paired hpaired (RadialCaps.continuous_cubicCap c ε).continuousOn
        (fun r _ => (RadialCaps.cubicCap_pos hc0 hε.le r).le) h⟩
    refine ⟨hcov, RadialCaps.cubic_cost_bigO hc0, ?_⟩
    filter_upwards [RadialCaps.eventually_small_scale c, RadialCaps.cubic_cost_strict hc0] with ε hε hQ
    exact ⟨hQ, finiteSaving_of_coverLimit (hcov ε hε.1).2 hQ⟩
  · intro c hc
    have hcov : ∀ᶠ ε : ℝ in 𝓝[>] 0,
        SweepsCover ε (RadialCaps.fractionalCap c ε) ∧ CoverLimit ε (RadialCaps.fractionalCap c ε) := by
      filter_upwards [hfractional c hc, RadialCaps.eventually_small_scale c] with ε hε hs
      exact ⟨hε, coverLimit_of_paired hpaired (RadialCaps.continuous_fractionalCap c ε).continuousOn
        (fun r _ => (RadialCaps.fractionalCap_pos hc.le hs.1.le r).le) hε⟩
    refine ⟨hcov, RadialCaps.fractional_cost_bigO hc.le, ?_⟩
    filter_upwards [hcov, RadialCaps.fractional_cost_strict hc.le] with ε hε hQ
    exact ⟨hQ, finiteSaving_of_coverLimit hε.2 hQ⟩

lemma eventually_positive_le {a : ℝ} (ha : 0 < a) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ a := by
  have hlt : ∀ᶠ ε : ℝ in 𝓝 0, ε < a :=
    continuousAt_id.eventually_lt continuousAt_const ha
  filter_upwards [eventually_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hlt] with ε hε hεa
  exact ⟨hε, hεa.le⟩

theorem radial_cap_variants : LCFStatement := by
  apply assemble RadialPairedSweep.paired_radial_sweeps
  · intro β hβ
    filter_upwards [eventually_positive_le (show 0 < 2 * β / 9 by positivity)] with ε hε
    exact RadialCapCoverage.linear_covers hβ.le hε.1 hε.2
  · intro c hc ε hε
    exact RadialCapCoverage.cubic_covers hc hε
  · intro c hc
    filter_upwards [eventually_positive_le
      (show 0 < (2 * c / 9) ^ 2 by positivity)] with ε hε
    exact RadialCapCoverage.fractional_covers hc hε.1 hε.2

end CylinderCovering.RadialCapVariants

end

end OAI
