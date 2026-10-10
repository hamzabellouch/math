import OAI.Analysis.TriangularHilbert.HeatTime

namespace OAI

universe uι uE

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma heatArray_differentiableAt_centers (A : Three → Matrix ι ι ℂ) {h : ℝ}
    (hh : 0 < h) (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w)
    (p : Three → ℝ) (v : Three) :
    DifferentiableAt ℝ (fun q => heatArray A h u q σ v) p := by
  apply differentiableAt_pi.mpr
  intro i
  apply differentiableAt_pi.mpr
  intro j
  have happ (w : Three) : DifferentiableAt ℝ (fun q : Three → ℝ => q w) p := by
    convert! (ContinuousLinearMap.proj w : (Three → ℝ) →L[ℝ] ℝ).differentiableAt
  have hw (a : Three) (k : ι) : DifferentiableAt ℝ
      (fun q : Three → ℝ => weight h (u k) (q a) (σ a)) p := by
    have hd := (weight_hasDerivAt_center h (u k) (p a) (σ a) (hσ a)).differentiableAt.comp p (happ a)
    exact hd
  have hleft := (hw v i).sqrt (weight_pos hh (hσ v) (u i) (p v)).ne'
  have hright := (hw (v+1) j).sqrt (weight_pos hh (hσ (v+1)) (u j) (p (v+1))).ne'
  exact ((Complex.ofRealCLM.differentiableAt.comp p hleft).mul_const (A v i j)).mul
    (Complex.ofRealCLM.differentiableAt.comp p hright)

lemma continuous_heatRow (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    Continuous (fun p => rowStar (heatArray A h u p σ) v) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  exact (rowStar_differentiableAt (heatArray_differentiableAt_centers A hh u hσ p) v).continuousAt

lemma continuous_heatCarrier (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Continuous (fun p => heatCarrier A h u p σ v w) := by
  unfold heatCarrier
  split_ifs
  · exact continuous_heatRow A hh u hσ v
  · exact (continuous_heatRow A hh u hσ v).star

lemma continuous_heatEnergy (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v : Three) :
    Continuous (fun p => heatEnergy A h u p σ v) := by
  exact continuous_energyGram.comp (continuous_heatRow A hh u hσ v)

omit [Fintype ι] in
lemma continuous_heatMask {E : Type uE} [TopologicalSpace E] {r : E → Three → ι → ℝ}
    (hr : ∀ w j, Continuous (fun x => r x w j)) : Continuous (fun x => heatMask (r x)) := by
  simp only [heatMask_eq_diagonal]
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  by_cases hab : a = b
  · subst b
    simp only [Matrix.diagonal_apply_eq]
    exact Complex.continuous_ofReal.comp (hr a.1 a.2)
  · simp only [Matrix.diagonal_apply_ne _ hab]
    exact continuous_const

omit [Fintype ι] in
lemma continuous_scoreMask (u : ι → ℝ) (σ : Three → ℝ) (w : Three) :
    Continuous (fun p : Three → ℝ => heatMask (fun a j => if a = w then score (u j) (p a) (σ a) else 0)) := by
  apply continuous_heatMask
  intro a j
  split_ifs
  · unfold score; fun_prop
  · exact continuous_const

omit [Fintype ι] in
lemma continuous_secondMask (u : ι → ℝ) (σ : Three → ℝ) (w : Three) :
    Continuous (fun p : Three → ℝ => heatMask (fun a j => if a = w then score (u j) (p a) (σ a)^2-(σ a)⁻¹ else 0)) := by
  apply continuous_heatMask
  intro a j
  split_ifs
  · unfold score; fun_prop
  · exact continuous_const

lemma continuous_energyGradient_insert {E : Type uE} [TopologicalSpace E]
    {R L : E → Matrix ι ι ℂ} (hr : Continuous R) (hl : Continuous L) :
    Continuous (fun x => energyGradient ((R x)ᴴ * R x) ((R x)ᴴ * L x * R x)) := by
  have hs := continuous_sqrt_matrix (hr.star.mul hr) (fun x => Matrix.posSemidef_conjTranspose_mul_self (R x))
  simp only [energyGradient_apply]
  exact continuous_const.mul (traceRealCLM.continuous.comp (hs.mul ((hr.star.mul hl).mul hr)))

lemma continuous_heatFirst (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Continuous (fun p => heatFirst A h u p σ v w) := by
  simp only [heatFirst, localGram_eq_carrier A hh u _ hσ, localFirst_eq_carrier A hh u _ hσ]
  exact continuous_energyGradient_insert (continuous_heatCarrier A hh u hσ v w)
    (continuous_scoreMask u σ w)

lemma continuous_heatSecondGradient (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Continuous (fun p => energyGradient (localGram A h u p σ v w) (localSecond A h u p σ v w)) := by
  simp only [localGram_eq_carrier A hh u _ hσ, localSecond_eq_carrier A hh u _ hσ]
  exact continuous_energyGradient_insert (continuous_heatCarrier A hh u hσ v w)
    (continuous_secondMask u σ w)

lemma continuous_heatVariance (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Continuous (fun p => heatVariance A h u p σ v w) :=
  continuous_const.mul (continuous_heatSecondGradient A hh u hσ v w)

lemma measurable_heatPure (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Measurable (fun p => heatPure A h u p σ v w) := by
  have hc : Continuous (fun q : (Three → ℝ) × ℝ => heatFirst A h u (Function.update q.1 w q.2) σ v w) :=
    (continuous_heatFirst A hh u hσ v w).comp (by fun_prop)
  have hm := (measurable_deriv_with_param
    (f := fun p q => heatFirst A h u (Function.update p w q) σ v w) hc).comp
    (show Measurable (fun p : Three → ℝ => (p, p w)) by fun_prop)
  convert! hm using 1
  funext p
  exact (heatFirst_hasDerivAt_center A hh u p hσ v w).deriv.symm

lemma measurable_heatCost (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    Measurable (fun p => heatCost A h u p σ v w) := by
  have hm := (measurable_heatPure A hh u hσ v w).sub
    (continuous_heatSecondGradient A hh u hσ v w).measurable
  convert! hm using 1
  funext p
  simp [heatPure, heatCost]

lemma measurable_heatMixed (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) {σ : Three → ℝ} (hσ : ∀ a, 0 < σ a)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (hwz : w ≠ z) :
    Measurable (fun p => heatMixed A h u p σ v w z) := by
  have hc : Continuous (fun q : (Three → ℝ) × ℝ => heatFirst A h u (Function.update q.1 z q.2) σ v w) :=
    (continuous_heatFirst A hh u hσ v w).comp (by fun_prop)
  have hm := (measurable_deriv_with_param
    (f := fun p q => heatFirst A h u (Function.update p z q) σ v w) hc).comp
    (show Measurable (fun p : Three → ℝ => (p, p z)) by fun_prop)
  convert! hm using 1
  funext p
  exact (heatFirst_hasDerivAt_other A hh u p hσ hw hz hwz).deriv.symm

end
end TriangularHilbert.Heat
end

end OAI
