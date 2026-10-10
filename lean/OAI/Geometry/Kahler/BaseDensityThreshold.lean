import OAI.Geometry.Kahler.BaseProfileBounds

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology
open scoped ContDiff
noncomputable section

open Set Filter Topology
namespace PinchedHartogs.BaseConstruction

lemma density_conditions_eventually {F B D K c C₁ C₂ R : ℝ}
    (hgap : F < 1-2*c) (hder : C₂ < K*c) :
    ∀ᶠ q : ℝ in atTop,
      Real.exp (K*D/Real.sqrt q+2*R/q) ≤ 2 ∧
      Real.exp (K*D/Real.sqrt q+2*R/q)*(F+B*(K/q)) ≤ 1-2*c ∧
      K/q ≤ 1 ∧ C₁/q^2 ≤ 1 ∧ C₂+K/Real.sqrt q ≤ K*c ∧ C₂+K/q ≤ K*c := by
  have hq : Tendsto (fun q : ℝ => K/q) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hqs : Tendsto (fun q : ℝ => K/Real.sqrt q) atTop (𝓝 0) := tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hqd : Tendsto (fun q : ℝ => K*D/Real.sqrt q) atTop (𝓝 0) := tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
  have hqr : Tendsto (fun q : ℝ => 2*R/q) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have hq₂ : Tendsto (fun q : ℝ => C₁/q^2) atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
  have hH : Tendsto (fun q : ℝ => Real.exp (K*D/Real.sqrt q+2*R/q)) atTop (𝓝 1) := by
    have hadd : Tendsto (fun q : ℝ => K*D/Real.sqrt q+2*R/q) atTop (𝓝 0) := by simpa using hqd.add hqr
    simpa only [Function.comp_def, Real.exp_zero] using (Real.continuous_exp.tendsto 0).comp hadd
  have hprod : Tendsto (fun q : ℝ => Real.exp (K*D/Real.sqrt q+2*R/q)*(F+B*(K/q))) atTop (𝓝 F) := by
    simpa using hH.mul (tendsto_const_nhds.add (tendsto_const_nhds.mul hq))
  have hdH : Tendsto (fun q : ℝ => C₂+K/Real.sqrt q) atTop (𝓝 C₂) := by simpa using tendsto_const_nhds.add hqs
  have hdT : Tendsto (fun q : ℝ => C₂+K/q) atTop (𝓝 C₂) := by simpa using tendsto_const_nhds.add hq
  filter_upwards [hH.eventually (gt_mem_nhds (by norm_num : (1:ℝ)<2)),hprod.eventually (gt_mem_nhds hgap),
    hq.eventually (gt_mem_nhds zero_lt_one),hq₂.eventually (gt_mem_nhds zero_lt_one),
    hdH.eventually (gt_mem_nhds hder),hdT.eventually (gt_mem_nhds hder)] with q h1 h2 h3 h4 h5 h6
  exact ⟨h1.le,h2.le,h3.le,h4.le,h5.le,h6.le⟩

lemma exists_density_constants {a : ℝ} (p : RadialProfiles a) {B F₁ B₁ : ℝ}
    (hB : 0 ≤ B) (hF₁ : 0 ≤ F₁) (hB₁ : 0 ≤ B₁) :
    ∃ c K : ℝ, ∃ N : ℕ, 0 < c ∧ 2*c ≤ 1 ∧ 0 < K ∧ 2/c ≤ (2:ℝ)^N ∧
      p.F<1-2*c ∧ 2*(1+2*Real.sqrt (2*p.R))*(4*(p.F+B)+F₁+B₁) < K*c := by
  let c := (1-p.F)/4
  have hc : 0 < c := by dsimp [c]; linarith [p.F_lt]
  let C₂ := 2*(1+2*Real.sqrt (2*p.R))*(4*(p.F+B)+F₁+B₁)
  have hC : 0 ≤ C₂ := by dsimp [C₂]; have hF := p.F_nonneg; positivity
  let K := C₂/c+1
  have hK : 0 < K := by dsimp [K]; positivity
  have hc2 : c ≤ 2 := by dsimp [c]; linarith [p.F_nonneg]
  obtain ⟨N,hN⟩ := exists_nat_pow_near ((one_le_div hc).mpr hc2) (by norm_num : (1:ℝ)<2)
  refine ⟨c,K,N+1,hc,?_,hK,?_,?_,?_⟩
  · dsimp [c]; linarith [p.F_nonneg]
  · exact hN.2.le
  · dsimp [c]; linarith [p.F_lt]
  · dsimp [K]
    have he : (C₂/c+1)*c=C₂+c := by field_simp
    rw [he]
    linarith

end PinchedHartogs.BaseConstruction

end

end OAI
