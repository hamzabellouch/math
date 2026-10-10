import Mathlib
import OAI.Probability.SKValue.Evolution.HeatTransform
import OAI.Probability.SKValue.Evolution.TerminalAlgebra
import OAI.Probability.SKValue.Gaussian.GaussianFactor

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace SKValue
structure ForwardDensityData where
  variance : ℝ
  variance_pos : 0<variance
  size : ℝ
  size_pos : 0<size
  potential : ℝ → ℝ
  smooth : SmoothTerminal potential
  even : ∀ x,potential (-x)=potential x

namespace ForwardDensityData
variable (D : ForwardDensityData)
noncomputable def weight (x : ℝ) : ℝ :=
  gaussianPDFReal 0 D.variance.toNNReal x*Real.exp (D.size*D.potential x)
noncomputable def jet (n : ℕ) (x : ℝ) : ℝ :=
  (if n=0 then x/D.variance else if n=1 then 1/D.variance else 0)-
    D.size*iteratedDeriv n (deriv D.potential) x
lemma weight_pos (x : ℝ) : 0<D.weight x :=
  mul_pos (gaussianPDFReal_pos _ _ _ (Real.toNNReal_pos.mpr D.variance_pos).ne') (Real.exp_pos _)
lemma weight_measurable : Measurable D.weight :=
  (measurable_gaussianPDFReal _ _).mul ((measurable_const.mul D.smooth.smooth.continuous.measurable).exp)
lemma jet_initial (n : ℕ) (x : ℝ) :
    D.jet n x=forwardJet D.variance D.size D.potential n 0 x := by
  have he : coleHopf D.size 0 D.potential=D.potential := funext (coleHopf_zero _ _)
  have hv : D.variance^2/D.variance=D.variance := by field_simp
  simp [forwardJet,heatDen,heatScale,heatTime,D.variance_pos.ne',hv,scaledHeatJet,he,jet]

lemma jet_space (n : ℕ) (x : ℝ) : HasDerivAt (D.jet n) (D.jet (n+1) x) x := by
  have he (k : ℕ) : D.jet k=forwardJet D.variance D.size D.potential k 0 := funext (D.jet_initial k)
  rw [he n,he (n+1)]
  exact forwardJet_space D.smooth D.size_pos.le n 0 x
lemma jet_continuous (n : ℕ) : Continuous (D.jet n) :=
  continuous_iff_continuousAt.mpr (fun x ↦ (D.jet_space n x).continuousAt)

noncomputable def evolve (t : ℝ) (ht : 0≤t) : ForwardDensityData where
  variance := D.variance+t
  variance_pos := add_pos_of_pos_of_nonneg D.variance_pos ht
  size := D.size
  size_pos := D.size_pos
  potential := fun x ↦ coleHopf D.size (heatTime D.variance t) D.potential (heatScale D.variance t*x)
  smooth := (D.smooth.evolve D.size_pos.le _).comp_mul (by
    rw [abs_of_nonneg (heatScale_mem D.variance_pos t).1]
    exact (heatScale_mem D.variance_pos t).2)
  even := by
    intro x
    rw [mul_neg,coleHopf_even D.even]

lemma evolve_weight (t : ℝ) (ht : 0≤t) (x : ℝ) :
    (D.evolve t ht).weight x=heat t D.weight x := by
  have he (v y : ℝ) : Real.exp (D.size*coleHopf D.size v D.potential y)=
      heat v (fun z ↦ Real.exp (D.size*D.potential z)) y := by
    simp only [coleHopf,ite_eq_right D.size_pos.ne']
    rw [mul_div_cancel₀ _ D.size_pos.ne']
    exact Real.exp_log (lipschitz_exp_integral_pos D.smooth.lipschitz D.size_pos.le y (Real.sqrt v))
  unfold weight
  rw [heat_gaussianFactor D.variance_pos ht
    (D.smooth.smooth.continuous.measurable.const_mul D.size).exp]
  simp only [evolve,he,heatScale,heatTime,heatDen_of_nonneg _ ht]
  congr 2
  field_simp [(add_pos_of_pos_of_nonneg D.variance_pos ht).ne']
  ring

lemma evolve_jet (t : ℝ) (ht : 0≤t) (n : ℕ) (x : ℝ) :
    (D.evolve t ht).jet n x=forwardJet D.variance D.size D.potential n t x := by
  let f := coleHopf D.size (heatTime D.variance t) D.potential
  let lam := heatScale D.variance t
  have hf := D.smooth.evolve D.size_pos.le (heatTime D.variance t)
  have hfd := hf.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have hder : deriv (fun y ↦ f (lam*y))=fun y ↦ lam*deriv f (lam*y) := by
    funext y
    convert! ((hfd (lam*y)).hasDerivAt.comp y ((hasDerivAt_id y).const_mul lam)).deriv using 1
    simp
    ring
  have hjet : iteratedDeriv n (deriv (fun y ↦ f (lam*y))) x=
      lam^(n+1)*iteratedDeriv n (deriv f) (lam*x) := by
    rw [hder,iteratedDeriv_const_mul_field]
    rw [iteratedDeriv_comp_const_mul (hf.jets.smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n))]
    ring
  change (if n=0 then x/(D.variance+t) else if n=1 then 1/(D.variance+t) else 0)-
    D.size*iteratedDeriv n (deriv (fun y ↦ f (lam*y))) x=_
  rw [hjet]
  simp only [forwardJet,heatDen_of_nonneg _ ht,scaledHeatJet]
  dsimp [f,lam]
  ring

lemma evolve_slope_concavity
    (h1 : ∀ x,1/D.variance≤D.jet 1 x)
    (h2 : ∀ x,0≤x → D.jet 2 x≤0) {t : ℝ} (ht : 0≤t) :
    (∀ x,1/(D.variance+t)≤(D.evolve t ht).jet 1 x) ∧
    (∀ x,0≤x → (D.evolve t ht).jet 2 x≤0) := by
  let F := D.smooth.forwardBurgers D.even D.variance_pos D.size_pos t
  have hi1 : ∀ x,1/D.variance≤F.jet 1 0 x := by
    simpa only [F,SmoothTerminal.forwardBurgers,←D.jet_initial] using h1
  have hi2 : ∀ x,0≤x → F.jet 2 0 x≤0 := by
    simpa only [F,SmoothTerminal.forwardBurgers,←D.jet_initial] using h2
  constructor
  · intro x
    rw [D.evolve_jet]
    exact F.preserve_slope D.variance_pos ht hi1 ⟨ht,le_rfl⟩ x
  · intro x hx
    rw [D.evolve_jet]
    exact F.preserve_concavity D.variance_pos ht hi1 hi2 ⟨ht,le_rfl⟩ hx

end ForwardDensityData
end SKValue

end

end OAI
