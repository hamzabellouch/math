import Mathlib
import OAI.Geometry.CAT0Fillings.Gradient.ClosedLinear
import OAI.Geometry.CAT0Fillings.Minimizers.SpatialVariation
import OAI.Geometry.CAT0Fillings.Radial.ClosedInequality

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma integrable_radialPair (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    Integrable (fun w => dist o (q.atlasParam w)*
      inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.gradient hg w)) q.atlasMeasure := by
  have h := L2.integrable_inner (𝕜 := ℝ) ((q.memLp_radialB o).toLp _) (q.gradient hg)
  apply h.congr
  filter_upwards [(q.memLp_radialB o).coeFn_toLp] with w hw
  rw [hw,radialB,real_inner_smul_left]

lemma integrable_radialVariation (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    Integrable (fun w => (k+1:ℝ)*g (q.atlasParam w)+dist o (q.atlasParam w)*
      inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.gradient hg w)) q.atlasMeasure := by
  have hgI : Integrable (fun w => g (q.atlasParam w)) q.atlasMeasure :=
    (((Foundations.boundedLip_of_lipschitz hg).memLp (μ := MassMeasure.currentMassMeasure hT) 1).comp_measurePreserving q.atlas_preserving).integrable le_rfl
  exact (hgI.const_mul (k+1:ℝ)).add (q.integrable_radialPair o hg)

lemma radialVariation_eq_integral (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    q.radialVariation o g = ∫ w, (k+1:ℝ)*g (q.atlasParam w)+dist o (q.atlasParam w)*
      inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.gradient hg w) ∂q.atlasMeasure := by
  let f (w : ℕ × Euc (k+1)) := (k+1:ℝ)*g (q.atlasParam w)+dist o (q.atlasParam w)*
      inner ℝ (q.normalizedCovector w.1 (dist o) w.2) (q.normalizedCovector w.1 g w.2)
  have he : (fun w => (k+1:ℝ)*g (q.atlasParam w)+dist o (q.atlasParam w)*
      inner ℝ (q.gradient (LipschitzWith.dist_right o) w) (q.gradient hg w)) =ᵐ[q.atlasMeasure] f := by
    filter_upwards [q.ae_gradient_eq (LipschitzWith.dist_right o),q.ae_gradient_eq hg] with w hr he
    rw [hr,he]
  rw [integral_congr_ae he,q.integral_atlas ((q.integrable_radialVariation o hg).congr he)]
  apply tsum_congr
  intro i
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (q.chart i).borel,q.ae_normalizedCovector_inner i (dist o) g] with z hz hi
  dsimp only [radialVariationChart,f,atlasParam]
  have hsg : g ((q.chart i).paramExtended z) = (q.chart i).scalar g z := (q.chart i).scalar_paramExtended_eqOn g hz
  have hsr : dist o ((q.chart i).paramExtended z) = (q.chart i).scalar (dist o) z := (q.chart i).scalar_paramExtended_eqOn (dist o) hz
  rw [hi,hsg,hsr]
  simp only [Nat.cast_add,Nat.cast_one,covector]

lemma memLp_sweptCoefficient (o : X) :
    MemLp (fun w => dist o (q.atlasParam w)*Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2)) 2 q.atlasMeasure := by
  have hn : (k+1:ℝ) ≠ 0 := by positivity
  have h := (memLp_const (1:ℝ) : MemLp (fun _ : ℕ × Euc (k+1) => (1:ℝ)) 2 q.atlasMeasure).sub
    ((q.memLp_radialA o).const_mul (k+1:ℝ)⁻¹)
  apply (memLp_congr_ae ?_).mp h
  filter_upwards [] with w
  dsimp only [Pi.sub_apply,radialA]
  field_simp
  ring

lemma integrable_sweptField (o : X) (P : q.Sobolev) :
    Integrable (fun w => dist o (q.atlasParam w)*Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2)*
      q.inclusion P (q.atlasParam w)) q.atlasMeasure :=
  (q.memLp_sweptCoefficient o).integrable_mul ((Lp.memLp (q.inclusion P)).comp_measurePreserving q.atlas_preserving)

lemma sweptMass_eq_integral (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    q.sweptMass o g = ∫ w, dist o (q.atlasParam w)*Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2)*
      g (q.atlasParam w) ∂q.atlasMeasure := by
  let f (w : ℕ × Euc (k+1)) := dist o (q.atlasParam w)*
      Real.sqrt (1-‖q.normalizedCovector w.1 (dist o) w.2‖^2)*g (q.atlasParam w)
  have he : (fun w => dist o (q.atlasParam w)*Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2)*g (q.atlasParam w)) =ᵐ[q.atlasMeasure] f := by
    filter_upwards [q.ae_gradient_eq (LipschitzWith.dist_right o)] with w hw
    rw [hw]
  have hgI : MemLp (fun w => g (q.atlasParam w)) 2 q.atlasMeasure :=
    ((Foundations.boundedLip_of_lipschitz hg).memLp 2).comp_measurePreserving q.atlas_preserving
  have hi := (q.memLp_sweptCoefficient o).integrable_mul hgI
  rw [integral_congr_ae he,q.integral_atlas (hi.congr he)]
  apply tsum_congr
  intro i
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (q.chart i).borel,q.ae_normalizedCovector_norm_sq i (dist o)] with z hz hn
  dsimp only [f,atlasParam]
  have hsg : g ((q.chart i).paramExtended z) = (q.chart i).scalar g z := (q.chart i).scalar_paramExtended_eqOn g hz
  have hsr : dist o ((q.chart i).paramExtended z) = (q.chart i).scalar (dist o) z := (q.chart i).scalar_paramExtended_eqOn (dist o) hz
  rw [hn,hsg,hsr]
  dsimp only [IntegerChart.sweptWeight,density,gram,normSq,covector]
  ring
end CAT0Fillings.ChartGeometry
end

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace CAT0Fillings.ChartGeometry
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X] {k : ℕ} {T : Functional X (k+1)}
  {hT : IsMetricCurrent T} (q : ChartGeometry hT)

lemma radialDefect_lip (o : X) {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    q.radialDefect o (q.lipSobolev hg) = q.radialVariation o g-(k+1:ℝ)*q.sweptMass o g := by
  have hI : Integrable (fun w => (k+1:ℝ)*(dist o (q.atlasParam w)*Real.sqrt (1-‖q.gradient (LipschitzWith.dist_right o) w‖^2)*g (q.atlasParam w))) q.atlasMeasure := by
    exact ((q.memLp_sweptCoefficient o).integrable_mul
      (((Foundations.boundedLip_of_lipschitz hg).memLp 2).comp_measurePreserving q.atlas_preserving)).const_mul (k+1:ℝ)
  rw [q.radialDefect_eq_integral,q.radialVariation_eq_integral o hg,q.sweptMass_eq_integral o hg,
    ←integral_const_mul,←integral_sub (q.integrable_radialVariation o hg) hI]
  apply integral_congr_ae
  simp only [q.inclusion_lipSobolev,q.closedGradient_lipSobolev]
  filter_upwards [q.atlas_preserving.quasiMeasurePreserving.ae ((Foundations.boundedLip_of_lipschitz hg).memLp 2).coeFn_toLp] with w hg'
  change value (hT := hT) hg (q.atlasParam w) = g (q.atlasParam w) at hg'
  rw [hg']
  dsimp only [radialA,radialB]
  rw [real_inner_smul_left]
  ring

lemma radialDefect_smul (o : X) (P : q.Sobolev) (c : ℝ) :
    q.radialDefect o (c • P) = c*q.radialDefect o P := by
  have hcomp : Lp.compMeasurePreserving q.atlasParam q.atlas_preserving (c • q.inclusion P) = c • Lp.compMeasurePreserving q.atlasParam q.atlas_preserving (q.inclusion P) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • q.inclusion P) q.atlas_preserving,
      q.atlas_preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul c (q.inclusion P)),
      Lp.coeFn_smul c (Lp.compMeasurePreserving q.atlasParam q.atlas_preserving (q.inclusion P)),
      Lp.coeFn_compMeasurePreserving (q.inclusion P) q.atlas_preserving] with w h1 h2 h3 h4
    simp only [Function.comp_apply] at *
    rw [h1,h2,h3]
    simp only [Pi.smul_apply,h4]
  simp only [radialDefect,map_smul,hcomp,real_inner_smul_right]
  ring

lemma lipSobolev_smul {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (c : ℝ) :
    q.lipSobolev ((lipschitzWith_smul c).comp hg) = c • q.lipSobolev hg := by
  apply Subtype.ext
  exact q.graphPoint_smul hg c

lemma radialDefect_nonpos_lip (o : X)
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
    {g : X → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) (hg0 : ∀ x, 0 ≤ g x) :
    q.radialDefect o (q.lipSobolev hg) ≤ 0 := by
  obtain ⟨C,hC⟩ := (isCompact_range hg.continuous).isBounded.exists_norm_le
  have hpos : 0 < |C|+1 := by positivity
  let c : ℝ := (|C|+1)⁻¹
  have hc : 0 < c := inv_pos.mpr hpos
  have hscaled := hr (fun x => c • g x) _ ((lipschitzWith_smul c).comp hg)
    (fun x => mul_nonneg hc.le (hg0 x)) (fun x => ?_)
  · have hh : q.radialDefect o (q.lipSobolev ((lipschitzWith_smul c).comp hg)) ≤ 0 := by
      rw [q.radialDefect_lip o ((lipschitzWith_smul c).comp hg)]
      exact sub_nonpos.mpr hscaled
    rw [q.lipSobolev_smul hg c,q.radialDefect_smul] at hh
    exact nonpos_of_mul_nonpos_right hh hc
  · change c*g x ≤ 1
    change (|C|+1)⁻¹*g x ≤ 1
    rw [inv_mul_eq_div]
    apply (div_le_one hpos).mpr
    exact (le_abs_self (g x)).trans ((hC _ (mem_range_self x)).trans (by linarith [le_abs_self C]))

lemma radialDefect_nonpos (hz : IsCycle T) (o : X)
    (hr : ∀ (g : X → ℝ) (K : ℝ≥0), LipschitzWith K g →
      (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) → q.radialVariation o g ≤ (k+1:ℝ)*q.sweptMass o g)
    (P : q.Sobolev) (hP : ∀ᵐ x ∂MassMeasure.currentMassMeasure hT, 0 ≤ q.inclusion P x) :
    q.radialDefect o P ≤ 0 :=
  q.nonnegative_mem_closed hz (isClosed_le (q.continuous_radialDefect o) continuous_const)
    (fun _ _ hg hg0 => q.radialDefect_nonpos_lip o hr hg hg0) P hP
end CAT0Fillings.ChartGeometry
end

end OAI
