import Mathlib
import OAI.Geometry.PrescribedPotential.ChartTransport
import OAI.Geometry.PrescribedPotential.CoreBounds

namespace OAI

/-! Chart Transport Higher. -/

section

 

noncomputable section
open Set Filter Topology _root_.MeasureTheory _root_.OAI.MeasureTheory LineDeriv TemperedDistribution
open scoped ContDiff SchwartzMap Classical Laplacian

namespace GlobalElliptic
open SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (e : OpenPartialHomeomorph E E) (he : ContDiffOn ℝ ∞ e e.source)

include he in
lemma transportCoefficient_smooth (v : E) (j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (fun x => ((stdOrthonormalBasis ℝ E).repr (fderiv ℝ e x v) j : ℂ)) e.source := by
  apply Complex.ofRealCLM.contDiff.comp_contDiffOn
  apply ((EuclideanSpace.proj j).contDiff.comp (stdOrthonormalBasis ℝ E).repr.contDiff).comp_contDiffOn
  exact (he.fderiv_of_isOpen e.open_source (by simp)).clm_apply contDiffOn_const

def transportCoefficient (κ : ChartCutoff e.source) (v : E) (j : Fin (Module.finrank ℝ E)) :
    ChartCutoff e.source := κ.mulOn e.open_source (transportCoefficient_smooth e he v j)

@[simp] lemma transportCoefficient_apply (κ : ChartCutoff e.source) (v : E)
    (j : Fin (Module.finrank ℝ E)) (x : E) :
    transportCoefficient e he κ v j x =
      κ x * ((stdOrthonormalBasis ℝ E).repr (fderiv ℝ e x v) j : ℂ) := rfl

omit [FiniteDimensional ℝ E] in
lemma chartTransport_tsupport (κ : ChartCutoff e.source) (f : 𝓢(E, ℂ)) :
    tsupport (chartTransport e he κ f : E → ℂ) ⊆ tsupport (κ : E → ℂ) :=
  κ.product_tsupport e.open_source ((f.smooth ⊤).comp_contDiffOn he)

 

lemma chartTransport_deriv (κ : ChartCutoff e.source) (v : E) (f : 𝓢(E, ℂ)) :
    ∂_{v} (chartTransport e he κ f) = chartTransport e he (κ.deriv v) f +
      ∑ j, chartTransport e he (transportCoefficient e he κ v j)
        (∂_{stdOrthonormalBasis ℝ E j} f) := by
  ext x
  by_cases hx : x ∈ e.source
  · have hed := (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
    have hfd := f.differentiableAt.comp x hed
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, chartTransport_apply,
      _root_.add_apply, _root_.sum_apply, transportCoefficient_apply]
    change fderiv ℝ (fun y => κ y * f (e y)) x v =
      fderiv ℝ κ.val x v * f (e x) + _
    have hm := fderiv_fun_mul κ.val.differentiableAt hfd
    have hc := fderiv_comp x f.differentiableAt hed
    dsimp only [Function.comp_def] at hm hc
    rw [hm, hc]
    simp only [_root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul]
    have hb := congrArg (fun z => fderiv ℝ f (e x) z)
      ((stdOrthonormalBasis ℝ E).sum_repr (fderiv ℝ e x v))
    simp only [map_sum, map_smul, Complex.real_smul] at hb
    rw [← hb, Finset.mul_sum]
    ring_nf
  · have hk : x ∉ tsupport (κ : E → ℂ) := fun ht => hx (κ.support_sub ht)
    have ht : x ∉ tsupport (chartTransport e he κ f : E → ℂ) :=
      fun ht => hk (chartTransport_tsupport e he κ f ht)
    have hder : (∂_{v} (chartTransport e he κ f) : 𝓢(E, ℂ)) x = 0 := by
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
        (notMem_tsupport_iff_eventuallyEq.mp ht).fderiv_eq]
      simp
    have hk' : κ.deriv v x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hk (κ.deriv_tsupport v h))
    simp only [_root_.add_apply, _root_.sum_apply, chartTransport_apply,
      transportCoefficient_apply, hder, image_eq_zero_of_notMem_tsupport hk, hk', zero_mul,
      Finset.sum_const_zero, add_zero]

variable [MeasurableSpace E] [BorelSpace E]

lemma word_deriv_comm (ws : List E) (v : E) (f : 𝓢(E, ℂ)) :
    schwartzWord ws (∂_{v} f) = ∂_{v} (schwartzWord ws f) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change ∂_{w} (schwartzWord ws (∂_{v} f)) = ∂_{v} (∂_{w} (schwartzWord ws f))
    rw [ih, schwartz_deriv_comm]

include he in
lemma chartTransport_word_bound (hs : ContDiffOn ℝ ∞ e.symm e.target) (ws : List E)
    (κ : ChartCutoff e.source) {s : ℝ} (hws : (ws.length : ℝ) ≤ s) :
    CoreBound s 0 (fun f => schwartzWord ws (chartTransport e he κ f)) := by
  induction ws generalizing κ s with
  | nil =>
    have hzero : CoreBound 0 0 (chartTransport e he κ) := chartTransport_l2_bound e he hs κ
    exact hzero.comp (CoreBound.id (by simpa using hws))
  | cons w ws ih =>
    have hw : (ws.length : ℝ) + 1 ≤ s := by simpa only [List.length_cons, Nat.cast_add, Nat.cast_one] using hws
    have hfirst := ih (κ.deriv w) (s := s) (by linarith)
    have hrest (j : Fin (Module.finrank ℝ E)) :=
      (ih (transportCoefficient e he κ w j) (s := s - 1) (by linarith)).comp
        (coreBound_deriv (stdOrthonormalBasis ℝ E j) (s := s) (t := s - 1) le_rfl)
    have hh := hfirst.add (CoreBound.sum Finset.univ _ (fun j _ => hrest j))
    convert hh using 1
    funext f
    change ∂_{w} (schwartzWord ws (chartTransport e he κ f)) = _
    rw [← word_deriv_comm, chartTransport_deriv, map_add, map_sum]
    rfl

 

theorem chartTransport_even_bound (hs : ContDiffOn ℝ ∞ e.symm e.target)
    (κ : ChartCutoff e.source) (k : ℕ) :
    CoreBound (2 * (k : ℝ)) (2 * (k : ℝ)) (chartTransport e he κ) := by
  apply coreBound_of_words k
  intro ws hw
  apply chartTransport_word_bound e he hs ws κ
  exact_mod_cast hw

end GlobalElliptic

end
end

end OAI
