import OAI.Geometry.Kahler.BaseChartUniform

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
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

lemma iteratedFDeriv_add_mul {f g : Base → ℝ} {z : Base}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) (L : ℝ) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x => f x+L*g x) z =
      iteratedFDeriv ℝ n f z + L • iteratedFDeriv ℝ n g z := by
  have hfn : ContDiffAt ℝ n f z := hf.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  have hgn : ContDiffAt ℝ n g z := hg.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))
  change iteratedFDeriv ℝ n (f + L • g) z = _
  rw [iteratedFDeriv_add_apply hfn (by simpa only [Pi.smul_def,smul_eq_mul] using contDiffAt_const.mul hgn),
    iteratedFDeriv_const_smul_apply hgn]

lemma baseHessian_add_mul {f g : Base → ℝ} {z : Base}
    (hf : ContDiffAt ℝ ∞ f z) (hg : ContDiffAt ℝ ∞ g z) (L : ℝ) (i j : Fin 2) :
    baseHessian (fun x => f x+L*g x) z i j = baseHessian f z i j + (L:ℂ)*baseHessian g z i j := by
  rw [baseHessian_eq_jet (hf.add (contDiffAt_const.mul hg)),iteratedFDeriv_add_mul hf hg,
    map_add,map_smul,← baseHessian_eq_jet hf,← baseHessian_eq_jet hg]
  simp only [Complex.real_smul]

lemma psi_baseHessian_chart_eventually {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (U : Base ≃ₗᵢ[ℂ] Base) :
    baseHessian (psi ∘ centeredChart r U) =ᶠ[𝓝 (0:Base)] baseHessian psi := by
  have he := (psi_chart_hessian_eventually hr hr1 U (0:ℂ)).comp_tendsto
    (continuousAt_id.prodMk continuousAt_const : ContinuousAt (fun z : Base => (z,(0:ℂ))) 0).tendsto
  filter_upwards [he,isOpen_ball.mem_nhds zero_mem_ball] with z hz hzb
  have hψ := psi_contDiffAt hzb
  have hf := (psi_contDiffAt (centeredChart_mapsTo hr hr1 U hzb)).comp z
    ((centeredChart_analyticAt U (centeredChart_den_ne_zero hr hr1 hzb)).contDiffAt.restrict_scalars ℝ)
  ext i j
  have hh := congrArg (fun A => A i.castSucc j.castSucc) hz
  change liftedHessian (psi ∘ centeredChart r U) (z,0) i.castSucc j.castSucc =
    liftedHessian psi (z,0) i.castSucc j.castSucc at hh
  rw [liftedHessian_horizontal (hf.of_le (WithTop.coe_le_coe.mpr le_top)),
    liftedHessian_horizontal (hψ.of_le (WithTop.coe_le_coe.mpr le_top))] at hh
  exact hh

lemma psi_baseHessian_center (i j : Fin 2) : baseHessian psi 0 i j = if i=j then 1 else 0 := by
  rw [← liftedHessian_horizontal (q := (0,(0:ℂ))) ((psi_contDiffAt zero_mem_ball).of_le (WithTop.coe_le_coe.mpr le_top)) i j]
  change complexHessian (fun q : Ambient => psi q.1) (0,0) i.castSucc j.castSucc = _
  rw [psi_hessian_center]
  fin_cases i <;> fin_cases j <;> norm_num [horizontalIdentity]

lemma psi_baseHessian_value (v : Base) :
    (∑ i, ∑ j, baseHessian psi 0 i j*v i*star (v j)).re = ‖v‖^2 := by
  simp only [psi_baseHessian_center]
  simp only [Fin.sum_univ_two,Fin.reduceEq,ite_true,ite_false,one_mul,zero_mul,zero_add,add_zero]
  simp only [Complex.star_def,Complex.mul_conj,Complex.add_re,Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  rw [EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]

lemma baseHessian_chart_normalize {f : Base → ℝ} (hf : ContDiffOn ℝ ∞ f ball)
    (L : ℝ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (U : Base ≃ₗᵢ[ℂ] Base) :
    baseHessian ((fun x => psi x+L*f x) ∘ centeredChart r U) =ᶠ[𝓝 (0:Base)]
      baseHessian (fun z => psi z+L*f (centeredChart r U z)) := by
  filter_upwards [psi_baseHessian_chart_eventually hr hr1 U,isOpen_ball.mem_nhds zero_mem_ball] with z hz hzb
  have hT : ContDiffAt ℝ ∞ (centeredChart r U) z := (centeredChart_analyticAt U (centeredChart_den_ne_zero hr hr1 hzb)).contDiffAt.restrict_scalars ℝ
  have hfc := (hf.contDiffAt (isOpen_ball.mem_nhds (centeredChart_mapsTo hr hr1 U hzb))).comp z hT
  have hψc := (psi_contDiffAt (centeredChart_mapsTo hr hr1 U hzb)).comp z hT
  ext i j
  change baseHessian (fun x => psi (centeredChart r U x)+L*f (centeredChart r U x)) z i j = _
  erw [baseHessian_add_mul hψc hfc L i j,baseHessian_add_mul (psi_contDiffAt hzb) hfc L i j]
  exact congrArg (fun A => A i j + (L:ℂ)*baseHessian (f ∘ centeredChart r U) z i j) hz

lemma baseHessian_congr_derivatives {f g : Base → ℝ} {z : Base}
    (h : baseHessian f =ᶠ[𝓝 z] baseHessian g) (i j k l : Fin 2) :
    dzBase (fun x => baseHessian f x i j) z k = dzBase (fun x => baseHessian g x i j) z k ∧
    dbarBase (fun x => baseHessian f x i j) z l = dbarBase (fun x => baseHessian g x i j) z l ∧
    dzBase (fun x => dbarBase (fun y => baseHessian f y i j) x l) z k =
      dzBase (fun x => dbarBase (fun y => baseHessian g y i j) x l) z k := by
  have he : (fun x => baseHessian f x i j) =ᶠ[𝓝 z] (fun x => baseHessian g x i j) := h.fun_comp (fun A => A i j)
  have hd : (fun x => dbarBase (fun y => baseHessian f y i j) x l) =ᶠ[𝓝 z]
      (fun x => dbarBase (fun y => baseHessian g y i j) x l) := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with x hx
    simp only [dbarBase,hx]
  exact ⟨by simp only [dzBase,he.fderiv_eq],by simp only [dbarBase,he.fderiv_eq],by simp only [dzBase,hd.fderiv_eq]⟩

end PinchedHartogs.BaseConstruction

end

end OAI
