import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialLocalCompact
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialTail
import Mathlib.Analysis.Normed.Operator.Compact.Basic

namespace OAI

/-! The Dirichlet cusp inclusion is compact for each nonzero Fourier
potential: local compactness is combined with the uniform exponential tail. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CubicFirstMoment

lemma cubicThetaRadial_tail_small {A : ℝ} (hA : 0<A) {δ : ℝ} (hδ : 0<δ) :
    ∃ R : ℝ, 0 ≤ R ∧ (A*Real.exp (2*R))⁻¹<δ := by
  have h₂ : Tendsto (fun R : ℝ => 2*R) atTop atTop :=
    tendsto_id.const_mul_atTop (by norm_num)
  have hlim : Tendsto (fun R : ℝ => (A*Real.exp (2*R))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((Real.tendsto_exp_atTop.comp h₂).const_mul_atTop hA)
  exact ((eventually_ge_atTop 0).and (hlim.eventually (eventually_lt_nhds hδ))).exists

lemma cubicThetaRadial_cutoff_remainder (A : ℝ) {R : ℝ} (hR : 0 ≤ R)
    (f : cubicThetaRadialTests) :
    cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f)-
      cubicThetaL2Cutoff (Icc 0 R) measurableSet_Icc
        (cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f))=
      cubicThetaRadialTail A R (cubicThetaRadialEnergyTest A f) := by
  let F := cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f)
  apply Lp.ext
  filter_upwards [cubicThetaRadialInclusion_test A f,
    cubicThetaL2Cutoff_coe (Icc 0 R) measurableSet_Icc F,
    cubicThetaL2Cutoff_coe (Ioi R) measurableSet_Ioi F,
    Lp.coeFn_sub F (cubicThetaL2Cutoff (Icc 0 R) measurableSet_Icc F)] with t hf hlow hhigh hsub
  change (F-cubicThetaL2Cutoff (Icc 0 R) measurableSet_Icc F) t=
    cubicThetaL2Cutoff (Ioi R) measurableSet_Ioi F t
  simp only [Pi.sub_apply] at hsub
  rw [hsub,hlow,hhigh]
  by_cases ht0 : 0 ≤ t
  · by_cases htR : t ≤ R
    · simp [ht0,htR,not_lt.mpr htR]
    · simp [ht0,htR,lt_of_not_ge htR]
  · have hz : F t=0 := hf.trans (f.property.2.2 t (le_of_not_ge ht0))
    have htR : ¬R<t := not_lt.mpr ((le_of_not_ge ht0).trans hR)
    simp [ht0,htR,hz]

lemma cubicThetaRadial_unit_cutoff_error {A : ℝ} (hA : 0<A) {ε : ℝ} (hε : 0<ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ f : CubicThetaRadialUnitTests A,
      dist (cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f.val))
        (cubicThetaL2Cutoff (Icc 0 R) measurableSet_Icc
          (cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f.val)))<ε := by
  obtain ⟨R,hR,hsmall⟩ := cubicThetaRadial_tail_small hA (sq_pos_of_pos hε)
  refine ⟨R,hR,?_⟩
  intro f
  rw [dist_eq_norm,cubicThetaRadial_cutoff_remainder A hR]
  have hb := cubicThetaRadialTail_test_bound hA R f.val
  have hn : ‖cubicThetaRadialGraph A f.val‖^2 ≤ 1 := by
    simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) f.property 2
  have hc : 0 ≤ (A*Real.exp (2*R))⁻¹ := by positivity
  have hprod : (A*Real.exp (2*R))⁻¹*‖cubicThetaRadialGraph A f.val‖^2 ≤
      (A*Real.exp (2*R))⁻¹ := (mul_le_mul_of_nonneg_left hn hc).trans_eq (mul_one _)
  have hsq := hb.trans hprod
  exact (sq_lt_sq₀ (_root_.norm_nonneg _) hε.le).mp (hsq.trans_lt hsmall)

theorem cubicThetaRadial_unit_precompact {A : ℝ} (hA : 0<A) :
    IsCompact (closure (Set.range (fun f : CubicThetaRadialUnitTests A =>
      cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f.val)))) := by
  suffices ht : TotallyBounded (Set.range (fun f : CubicThetaRadialUnitTests A =>
      cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f.val))) from
    (totallyBounded_closure.mpr ht).isCompact_of_isClosed isClosed_closure
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨R,hR,herror⟩ := cubicThetaRadial_unit_cutoff_error hA (half_pos hε)
  have hlocal := (cubicThetaRadialLocal_precompact A hR).totallyBounded.subset subset_closure
  obtain ⟨T,_,hT,hcover⟩ := Metric.finite_approx_of_totallyBounded hlocal (ε/2) (half_pos hε)
  refine ⟨T,hT,?_⟩
  rintro y ⟨f,rfl⟩
  have hm := hcover (show cubicThetaL2Cutoff (Icc 0 R) measurableSet_Icc
    (cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f.val)) ∈ Set.range
      (fun g : CubicThetaRadialUnitTests A => cubicThetaL2Cutoff (Icc 0 R) measurableSet_Icc
        (cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A g.val))) from ⟨f,rfl⟩)
  obtain ⟨z,hz⟩ := Set.mem_iUnion.mp hm
  obtain ⟨hzT,hzball⟩ := Set.mem_iUnion.mp hz
  refine Set.mem_iUnion.mpr ⟨z,Set.mem_iUnion.mpr ⟨hzT,?_⟩⟩
  have hzdist : dist (cubicThetaL2Cutoff (Icc 0 R) measurableSet_Icc
      (cubicThetaRadialInclusion A (cubicThetaRadialEnergyTest A f.val))) z<ε/2 := hzball
  change dist _ z<ε
  exact (dist_triangle _ _ _).trans_lt (add_lt_add (herror f) hzdist |>.trans_eq (by ring))

end CubicFirstMoment

end

end OAI
