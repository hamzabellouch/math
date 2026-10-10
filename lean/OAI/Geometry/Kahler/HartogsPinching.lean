import OAI.Geometry.Kahler.HartogsCurvatureContinuity

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open scoped ContDiff ENNReal Pointwise
open Set Filter Topology MeasureTheory
open scoped ContDiff
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix

theorem hartogsMetric_uniform_pinching {φ : Base → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ ball) {c C lam : ℝ} (hc : 0 < c) (hC : c ≤ C)
    (hctl : ChartControl φ c C) (hj : ChartJets φ C) (hlam : metricThreshold c C ≤ lam) :
    ∃ a b : ℝ, IsNegativelyPinched (hartogs φ) (hartogsMetric φ lam) a b := by
  have hpsh := chartControl_psh hφ hc.le hctl
  have hlp : 0 < lam := (metricThreshold_pos hc hC).trans_le hlam
  obtain ⟨a,b,ha,hab,hbound⟩ := normalPotentials_uniform_pinching hc hC hlam
  have hnonzero (p : Ambient) (hp : p ∈ hartogs φ) (hp0 : p.2 ≠ 0)
      (u v : Ambient) (hind : LinearIndependent ℝ ![u,v]) :
      -b ≤ sectional (hartogsMetric φ lam) p u v ∧
      sectional (hartogsMetric φ lam) p u v ≤ -a := by
    obtain ⟨r,U,hr,hr1,hz0⟩ := exists_centeredChart hp.1
    let w := Complex.log p.2
    have hw : Complex.exp w = p.2 := Complex.exp_log hp0
    have hpp : (centeredChart r U 0,Complex.exp w) = p := by rw [hz0,hw]
    have hpm : (centeredChart r U 0,Complex.exp w) ∈ hartogs φ := hpp ▸ hp
    let F := fiberGaugeMap (centeredChart r U) (baseGaugePolynomial (φ ∘ centeredChart r U) w)
    have hFc : F (0,w) = (centeredChart r U 0,Complex.exp w) := by simp [F, fiberGaugeMap, baseGaugePolynomial]
    have hn : normalLogWeight (φ ∘ centeredChart r U) w (0,w) < 0 := by
      rw [← gaugeLogParameter_normal]
      apply gaugeLogParameter_neg
      change F (0,w) ∈ hartogs φ
      rwa [hFc]
    have hT := centeredChart_analyticAt (r := r) U (z := 0) (by simp)
    have hi : Function.Injective (fderiv ℂ F (0,w)) :=
      fderiv_fiberGaugeMap_injective (p := (0,w)) hT.differentiableAt
        (fderiv_centeredChart_zero_injective hr hr1 U)
        (firstGaugeJet (fun q : Ambient => (φ ∘ centeredChart r U) q.1) (0,w))
        (secondGaugeJet (fun q : Ambient => (φ ∘ centeredChart r U) q.1) (0,w))
    let L : Ambient ≃ₗ[ℂ] Ambient := LinearEquiv.ofBijective (fderiv ℂ F (0,w)).toLinearMap
      ⟨hi, (LinearMap.injective_iff_surjective (f := (fderiv ℂ F (0,w)).toLinearMap)).mp hi⟩
    have hind' : LinearIndependent ℝ ![L.symm u,L.symm v] := by
      convert hind.map' (L.symm.restrictScalars ℝ).toLinearMap
        (LinearMap.ker_eq_bot_of_injective (L.symm.restrictScalars ℝ).injective) using 1
      all_goals first | rfl | (funext i; fin_cases i <;> rfl)
    have hc' := chartControl_form_bounds hφ hctl hr hr1 U
    have hj' := chartJets_lifted_bounds hφ hj hr hr1 U
    have hb := hbound (φ ∘ centeredChart r U) (chartWeight_contDiffAt hφ hr hr1 U)
      hc'.1 hc'.2 hj'.1 hj'.2 w hn (L.symm u) (L.symm v) hind'
    have he := sectional_normalGauge hφ hpsh hlp hr hr1 U w hpm (L.symm u) (L.symm v)
    change sectional _ _ (L.symm u) (L.symm v) =
      sectional _ _ (L (L.symm u)) (L (L.symm v)) at he
    rw [L.apply_symm_apply,L.apply_symm_apply,hpp] at he
    rwa [he] at hb
  refine ⟨a,b,ha,hab,?_⟩
  intro p hp u v hind
  by_cases hp0 : p.2 = 0
  · let ps : ℕ → Ambient := fun n => (p.1,(1 / (n+1 : ℂ)))
    have ht : Tendsto ps atTop (𝓝 p) := by
      have hh := (tendsto_const_nhds (x := p.1)).prodMk
        (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/(n+1 : ℂ)) atTop (𝓝 0))
      rw [← nhds_prod_eq] at hh
      simpa [ps,← hp0] using hh
    have hev : ∀ᶠ n in atTop, ps n ∈ hartogs φ := ht.eventually ((hartogs_isOpen_smooth hφ).mem_nhds hp)
    have hb : ∀ᶠ n in atTop, -b ≤ sectional (hartogsMetric φ lam) (ps n) u v ∧
        sectional (hartogsMetric φ lam) (ps n) u v ≤ -a := by
      filter_upwards [hev] with n hn
      apply hnonzero (ps n) hn _ u v hind
      change 1/(n+1 : ℂ) ≠ 0
      exact div_ne_zero one_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
    have hlim := (sectional_continuousAt (hartogs_isOpen_smooth hφ)
      (hartogsMetric_isKahler hφ hpsh hlp) hp hind).tendsto.comp ht
    exact ⟨ge_of_tendsto hlim (hb.mono fun _ h => h.1), le_of_tendsto hlim (hb.mono fun _ h => h.2)⟩
  · exact hnonzero p hp hp0 u v hind

end PinchedHartogs

end

end OAI
