import Mathlib
import OAI.Probability.SKValue.Equations.ForwardDensity

namespace OAI

section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace SKValue
lemma SmoothTerminal.const (c : ℝ) : SmoothTerminal (fun _ : ℝ ↦ c) := by
  refine ⟨?_,contDiff_const,?_⟩
  · exact (LipschitzWith.const c).weaken (by norm_num)
  · have he : deriv (fun _ : ℝ ↦ c)=(fun _ ↦ 0) := funext (fun x ↦ deriv_const x c)
    rw [he]
    exact BoundedSmooth.const 0
namespace ForwardDensityData
noncomputable def gaussian (a : ℝ) (ha : 0<a) : ForwardDensityData where
  variance := a
  variance_pos := ha
  size := 1
  size_pos := by norm_num
  potential := fun _ ↦ 0
  smooth := SmoothTerminal.const 0
  even := fun _ ↦ rfl
lemma gaussian_weight (a : ℝ) (ha : 0<a) (x : ℝ) :
    (gaussian a ha).weight x=gaussianPDFReal 0 a.toNNReal x := by
  simp [weight,gaussian]
lemma gaussian_jet (a : ℝ) (ha : 0<a) (n : ℕ) (x : ℝ) :
    (gaussian a ha).jet n x=if n=0 then x/a else if n=1 then 1/a else 0 := by
  simp [jet,gaussian]

variable (D : ForwardDensityData) {φ : ℝ → ℝ}
noncomputable def jump (hφ : SmoothTerminal φ) (heven : ∀ x,φ (-x)=φ x)
    (δ : ℝ) (hδ : 0≤δ) : ForwardDensityData where
  variance := D.variance
  variance_pos := D.variance_pos
  size := D.size+δ
  size_pos := add_pos_of_pos_of_nonneg D.size_pos hδ
  potential := fun x ↦ (D.size/(D.size+δ))*D.potential x+(-δ/(D.size+δ))*φ x
  smooth := D.smooth.linear hφ (by
    have hp : 0<D.size+δ := add_pos_of_pos_of_nonneg D.size_pos hδ
    rw [abs_of_nonneg (div_nonneg D.size_pos.le hp.le),
      abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ) hp.le)]
    field_simp
    linarith)
  even := by intro x; rw [D.even,heven]

lemma jump_weight (hφ : SmoothTerminal φ) (heven : ∀ x,φ (-x)=φ x)
    (δ : ℝ) (hδ : 0≤δ) (x : ℝ) :
    (D.jump hφ heven δ hδ).weight x=D.weight x*Real.exp (-δ*φ x) := by
  have hp : D.size+δ≠0 := (add_pos_of_pos_of_nonneg D.size_pos hδ).ne'
  have he : (D.size+δ)*(D.size/(D.size+δ)*D.potential x+(-δ/(D.size+δ))*φ x)=
      D.size*D.potential x+(-δ*φ x) := by field_simp [hp]
  simp only [weight,jump,he,Real.exp_add,mul_assoc,neg_mul]

lemma jump_jet (hφ : SmoothTerminal φ) (heven : ∀ x,φ (-x)=φ x)
    (δ : ℝ) (hδ : 0≤δ) (n : ℕ) (x : ℝ) :
    (D.jump hφ heven δ hδ).jet n x=D.jet n x+δ*iteratedDeriv n (deriv φ) x := by
  have hp : D.size+δ≠0 := (add_pos_of_pos_of_nonneg D.size_pos hδ).ne'
  have hd := D.smooth.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have hf := hφ.smooth.differentiable (ENat.natCast_lt_of_coe_top_le_withTop le_rfl 0).ne'
  have he : deriv (fun y ↦ D.size/(D.size+δ)*D.potential y+(-δ/(D.size+δ))*φ y)=
      fun y ↦ D.size/(D.size+δ)*deriv D.potential y+(-δ/(D.size+δ))*deriv φ y := by
    funext y
    exact (((hd y).hasDerivAt.const_mul _).add ((hf y).hasDerivAt.const_mul _)).deriv
  simp only [jet,jump,he]
  rw [iteratedDeriv_fun_add
    ((contDiff_const.mul D.smooth.jets.smooth).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt
    ((contDiff_const.mul hφ.jets.smooth).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)).contDiffAt,
    iteratedDeriv_const_mul_field,iteratedDeriv_const_mul_field]
  field_simp
  ring

lemma jump_slope_concavity (hφ : SmoothTerminal φ) (heven : ∀ x,φ (-x)=φ x)
    (δ : ℝ) (hδ : 0≤δ)
    (hslope : ∀ x,1/D.variance≤D.jet 1 x)
    (hconc : ∀ x,0≤x → D.jet 2 x≤0)
    (hφslope : ∀ x,0 ≤ iteratedDeriv 1 (deriv φ) x)
    (hφconc : ∀ x,0≤x → iteratedDeriv 2 (deriv φ) x≤0) :
    (∀ x,1/D.variance≤(D.jump hφ heven δ hδ).jet 1 x) ∧
    (∀ x,0≤x → (D.jump hφ heven δ hδ).jet 2 x≤0) := by
  constructor
  · intro x
    rw [D.jump_jet]
    exact (hslope x).trans (le_add_of_nonneg_right (mul_nonneg hδ (hφslope x)))
  · intro x hx
    rw [D.jump_jet]
    exact add_nonpos (hconc x hx) (mul_nonpos_of_nonneg_of_nonpos hδ (hφconc x hx))
end ForwardDensityData
end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace SKValue
namespace ExpGrowth
lemma const (c:ℝ) : ExpGrowth (fun _ : ℝ ↦ c) :=
  of_bound (abs_nonneg c) (fun _ ↦ le_rfl)
lemma add {f g:ℝ → ℝ} (hf:ExpGrowth f) (hg:ExpGrowth g) : ExpGrowth (fun x ↦ f x+g x) := by
  obtain ⟨a,C,ha,hC,hf⟩ := hf
  obtain ⟨b,D,hb,hD,hg⟩ := hg
  refine ⟨a+b,C+D,add_nonneg ha hb,add_nonneg hC hD,?_⟩
  intro x
  apply (abs_add_le _ _).trans ((add_le_add (hf x) (hg x)).trans _)
  rw [add_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x])) hC)
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg x])) hD)
lemma neg {f:ℝ → ℝ} (hf:ExpGrowth f) : ExpGrowth (fun x ↦ -f x) := by
  simpa only [ExpGrowth,abs_neg] using hf
lemma sub {f g:ℝ → ℝ} (hf:ExpGrowth f) (hg:ExpGrowth g) : ExpGrowth (fun x ↦ f x-g x) :=
  hf.add hg.neg
lemma mul {f g:ℝ → ℝ} (hf:ExpGrowth f) (hg:ExpGrowth g) : ExpGrowth (fun x ↦ f x*g x) := by
  obtain ⟨a,C,ha,hC,hf⟩ := hf
  obtain ⟨b,D,hb,hD,hg⟩ := hg
  refine ⟨a+b,C*D,add_nonneg ha hb,mul_nonneg hC hD,?_⟩
  intro x
  rw [abs_mul,add_mul,Real.exp_add]
  calc
    _ ≤ (C*Real.exp (a*|x|))*(D*Real.exp (b*|x|)) :=
      mul_le_mul (hf x) (hg x) (abs_nonneg _) (mul_nonneg hC (Real.exp_pos _).le)
    _ = _ := by ring
lemma pow {f:ℝ → ℝ} (hf:ExpGrowth f) (n:ℕ) : ExpGrowth (fun x ↦ f x^n) := by
  induction n with
  | zero => simpa using const 1
  | succ n ih => simpa only [pow_succ] using ih.mul hf
lemma abs {f:ℝ → ℝ} (hf:ExpGrowth f) : ExpGrowth (fun x ↦ |f x|) := by
  simpa only [ExpGrowth,abs_abs] using hf
lemma gaussian_integrable {f:ℝ → ℝ} (hf:ExpGrowth f) (hm:Measurable f)
    {a:ℝ} (ha:0≤a) (x:ℝ) : Integrable f (gaussianReal x a.toNNReal) := by
  have hmp := (shiftedGaussian_hasLaw ha x).measurePreserving (by fun_prop)
  exact (hmp.integrable_comp hm.aestronglyMeasurable).mp (hf.shift_integrable hm x (Real.sqrt a))
lemma pdf_integrable {f:ℝ → ℝ} (hf:ExpGrowth f) (hm:Measurable f)
    {a:ℝ} (ha:0<a) (x:ℝ) : Integrable (fun y ↦ gaussianPDFReal x a.toNNReal y*f y) := by
  have hi := hf.gaussian_integrable hm ha.le x
  rw [gaussianReal_of_var_ne_zero _ (Real.toNNReal_pos.mpr ha).ne'] at hi
  have he := (integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
    (ae_of_all _ (fun _ ↦ gaussianPDF_lt_top))).mp hi
  simpa only [toReal_gaussianPDF,smul_eq_mul] using he
end ExpGrowth
end SKValue

end

end OAI
