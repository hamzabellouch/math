import Mathlib
import OAI.Probability.ParisiFinite.ParisiHankelDerivative

namespace OAI

/-! Parisi Cosh Entropy. -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Function Set
open MeasureTheory ProbabilityTheory Set Real Matrix Filter
open scoped Topology NNReal
open MeasureTheory ProbabilityTheory Set Real Filter
open scoped Topology NNReal
namespace ParisiSpectral

def ExpGrowth (M : ℝ) (f : ℝ → ℝ) : Prop := ∃ C : ℝ,0≤C ∧ ∀ x,|f x|≤C*exp (M*|x|)
lemma ExpGrowth.add {M : ℝ} {f g : ℝ → ℝ} (hf : ExpGrowth M f) (hg : ExpGrowth M g) :
    ExpGrowth M (fun x => f x+g x) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hg⟩ := hg
  refine ⟨C+D,add_nonneg hC hD,fun x => ?_⟩
  exact (abs_add_le _ _).trans (by nlinarith [hf x,hg x])
lemma ExpGrowth.const_mul {M : ℝ} {f : ℝ → ℝ} (hf : ExpGrowth M f) (a : ℝ) :
    ExpGrowth M (fun x => a*f x) := by
  obtain ⟨C,hC,hf⟩ := hf
  refine ⟨|a| *C,mul_nonneg (abs_nonneg a) hC,fun x => ?_⟩
  rw [abs_mul,mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf x) (abs_nonneg a)
lemma ExpGrowth.neg {M : ℝ} {f : ℝ → ℝ} (hf : ExpGrowth M f) : ExpGrowth M (fun x => -f x) := by
  simpa only [neg_one_mul] using hf.const_mul (-1)
lemma ExpGrowth.sub {M : ℝ} {f g : ℝ → ℝ} (hf : ExpGrowth M f) (hg : ExpGrowth M g) :
    ExpGrowth M (fun x => f x-g x) := by simpa only [sub_eq_add_neg] using hf.add hg.neg
lemma ExpGrowth.of_bounded {M C : ℝ} (hM : 0≤M) (hC : 0≤C) {f : ℝ → ℝ} (hf : ∀ x,|f x|≤C) :
    ExpGrowth M f := ⟨C,hC,fun x => (hf x).trans (le_mul_of_one_le_right hC (one_le_exp_iff.mpr (by positivity)))⟩
lemma ExpGrowth.mono {M N : ℝ} (hMN : M≤N) {f : ℝ → ℝ} (hf : ExpGrowth M f) : ExpGrowth N f := by
  obtain ⟨C,hC,hf⟩ := hf
  exact ⟨C,hC,fun x => (hf x).trans (mul_le_mul_of_nonneg_left (exp_le_exp.mpr (mul_le_mul_of_nonneg_right hMN (abs_nonneg _))) hC)⟩

lemma cosh_le_exp_abs (x : ℝ) : cosh x≤exp |x| := by
  rw [cosh_eq]
  linarith [exp_le_exp.mpr (le_abs_self x),exp_le_exp.mpr (neg_le_abs x)]
lemma sinh_abs_le_cosh (x : ℝ) : |sinh x|≤cosh x := by
  rw [abs_le]
  constructor <;> (rw [sinh_eq,cosh_eq]; linarith [exp_pos x,exp_pos (-x)])
lemma cosh_ExpGrowth (α : ℝ) : ExpGrowth (|α|+1) (fun x => cosh (α*x)) := by
  refine (show ExpGrowth |α| (fun x => cosh (α*x)) from ⟨1,by norm_num,fun x => ?_⟩).mono (by linarith)
  simpa only [abs_of_pos (cosh_pos _),one_mul,abs_mul] using cosh_le_exp_abs (α*x)
lemma sinh_ExpGrowth (α : ℝ) : ExpGrowth (|α|+1) (fun x => sinh (α*x)) := by
  obtain ⟨C,hC,hb⟩ := cosh_ExpGrowth α
  exact ⟨C,hC,fun x => (sinh_abs_le_cosh _).trans (by simpa only [abs_of_pos (cosh_pos _)] using hb x)⟩
lemma sech_ExpGrowth (α : ℝ) : ExpGrowth (|α|+1) (fun x => (cosh (α*x))⁻¹) := by
  apply ExpGrowth.of_bounded (by positivity) (C := 1) (by norm_num)
  intro x
  rw [abs_inv,abs_of_pos (cosh_pos _)]
  exact inv_le_one_of_one_le₀ (one_le_cosh _)
lemma sechCube_ExpGrowth (α : ℝ) : ExpGrowth (|α|+1) (fun x => (cosh (α*x))⁻¹^3) := by
  apply ExpGrowth.of_bounded (by positivity) (C := 1) (by norm_num)
  intro x
  rw [abs_pow,abs_inv,abs_of_pos (cosh_pos _)]
  exact pow_le_one₀ (inv_pos.mpr (cosh_pos _)).le (inv_le_one_of_one_le₀ (one_le_cosh _))

def coshEntropy (α x : ℝ) := cosh (α*x)*log (cosh (α*x))
def coshEntropyD (α x : ℝ) := α*sinh (α*x)*(log (cosh (α*x))+1)
def coshEntropyU (α x : ℝ) := α^2*(2*cosh (α*x)-(cosh (α*x))⁻¹)
def coshEntropyUD (α x : ℝ) := α^3*(2*sinh (α*x)+sinh (α*x)/(cosh (α*x))^2)

lemma coshEntropy_hasDerivAt (α x : ℝ) : HasDerivAt (coshEntropy α) (coshEntropyD α x) x := by
  have hc := ((hasDerivAt_id x).const_mul α).cosh
  have hl := hc.log (cosh_pos _).ne'
  convert hc.mul hl using 1 <;> first | rfl | (simp only [id_eq,mul_one,coshEntropyD]; field_simp [(cosh_pos (α*x)).ne'])
lemma coshEntropyD_hasDerivAt (α x : ℝ) :
    HasDerivAt (coshEntropyD α) (α^2*coshEntropy α x+coshEntropyU α x) x := by
  have hc := ((hasDerivAt_id x).const_mul α).cosh
  have hs := ((hasDerivAt_id x).const_mul α).sinh
  have hl := hc.log (cosh_pos _).ne'
  convert (hs.const_mul α).mul (hl.add_const 1) using 1 <;> first | rfl | (simp only [id_eq,mul_one,coshEntropy,coshEntropyU]; field_simp [(cosh_pos (α*x)).ne']; linear_combination α^2*(cosh_sq_sub_sinh_sq (α*x)))
lemma coshEntropyU_hasDerivAt (α x : ℝ) : HasDerivAt (coshEntropyU α) (coshEntropyUD α x) x := by
  have hc := ((hasDerivAt_id x).const_mul α).cosh
  convert ((hc.const_mul 2).sub (hc.inv (cosh_pos _).ne')).const_mul (α^2) using 1 <;>
    first | rfl | (simp only [id_eq,mul_one,coshEntropyUD]; field_simp [(cosh_pos (α*x)).ne']; ring)
lemma coshEntropyUD_hasDerivAt (α x : ℝ) :
    HasDerivAt (coshEntropyUD α) (α^2*coshEntropyU α x+2*α^4*((cosh (α*x))⁻¹^3)) x := by
  have hc := ((hasDerivAt_id x).const_mul α).cosh
  have hs := ((hasDerivAt_id x).const_mul α).sinh
  convert ((hs.const_mul 2).add (hs.div (hc.fun_pow 2) (pow_ne_zero 2 (cosh_pos _).ne'))).const_mul (α^3) using 1 <;>
    first | rfl | (simp only [id_eq,mul_one,coshEntropyU,Nat.cast_ofNat,Nat.reduceSub,pow_one]; field_simp [(cosh_pos (α*x)).ne']; linear_combination -2*α^4*(cosh_sq_sub_sinh_sq (α*x)))

lemma coshEntropy_ExpGrowth (α : ℝ) : ExpGrowth (|α|+1) (coshEntropy α) := by
  refine ⟨|α|,abs_nonneg _,fun x => ?_⟩
  rw [coshEntropy,abs_mul,abs_of_pos (cosh_pos _)]
  calc
    cosh (α*x)*|log (cosh (α*x))| ≤ exp (|α| *|x|)*(|α| *|x|) :=
      mul_le_mul (by simpa only [abs_mul] using cosh_le_exp_abs (α*x))
        (by simpa only [abs_mul] using abs_log_cosh_le (α*x)) (abs_nonneg _) (exp_pos _).le
    _ = |α| *(|x| *exp (|α| *|x|)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (ParisiFinite.abs_mul_exp_le |α| x) (abs_nonneg _)

lemma sinh_log_ExpGrowth (α : ℝ) :
    ExpGrowth (|α|+1) (fun x => sinh (α*x)*log (cosh (α*x))) := by
  obtain ⟨C,hC,hf⟩ := coshEntropy_ExpGrowth α
  refine ⟨C,hC,fun x => ?_⟩
  apply le_trans _ (hf x)
  simp only [coshEntropy,abs_mul,abs_of_pos (cosh_pos _)]
  exact mul_le_mul_of_nonneg_right (sinh_abs_le_cosh _) (abs_nonneg _)
lemma coshEntropyD_ExpGrowth (α : ℝ) : ExpGrowth (|α|+1) (coshEntropyD α) := by
  convert ((sinh_log_ExpGrowth α).const_mul α).add ((sinh_ExpGrowth α).const_mul α) using 1
  ext x
  dsimp only [coshEntropyD]
  ring
lemma coshEntropyU_ExpGrowth (α : ℝ) : ExpGrowth (|α|+1) (coshEntropyU α) :=
  (((cosh_ExpGrowth α).const_mul 2).sub (sech_ExpGrowth α)).const_mul (α^2)
lemma coshEntropyUD_ExpGrowth (α : ℝ) : ExpGrowth (|α|+1) (coshEntropyUD α) := by
  have hh : ExpGrowth (|α|+1) (fun x => sinh (α*x)/cosh (α*x)^2) := by
    apply ExpGrowth.of_bounded (by positivity) (C := 1) (by norm_num)
    intro x
    rw [abs_div,abs_pow,abs_of_pos (cosh_pos _),div_le_iff₀ (sq_pos_of_pos (cosh_pos _)),one_mul]
    exact (sinh_abs_le_cosh _).trans (by nlinarith [one_le_cosh (α*x)])
  exact (((sinh_ExpGrowth α).const_mul 2).add hh).const_mul (α^3)

lemma continuous_coshEntropy (α : ℝ) : Continuous (coshEntropy α) :=
  (show Differentiable ℝ (coshEntropy α) from fun x => (coshEntropy_hasDerivAt α x).differentiableAt).continuous
lemma continuous_coshEntropyD (α : ℝ) : Continuous (coshEntropyD α) :=
  (show Differentiable ℝ (coshEntropyD α) from fun x => (coshEntropyD_hasDerivAt α x).differentiableAt).continuous
lemma continuous_coshEntropyU (α : ℝ) : Continuous (coshEntropyU α) :=
  (show Differentiable ℝ (coshEntropyU α) from fun x => (coshEntropyU_hasDerivAt α x).differentiableAt).continuous
lemma continuous_coshEntropyUD (α : ℝ) : Continuous (coshEntropyUD α) :=
  (show Differentiable ℝ (coshEntropyUD α) from fun x => (coshEntropyUD_hasDerivAt α x).differentiableAt).continuous

end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Set Real Filter
open scoped Topology NNReal
namespace ParisiSpectral

lemma heatLaw_eq_map {μ : Measure ℝ} [IsFiniteMeasure μ] {a t : ℝ} (ht : a≤t) :
    heatLaw μ a t=(μ.prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => p.1+sqrt (t-a)*p.2) := by
  have hg : (gaussianReal 0 1).map (fun z : ℝ => sqrt (t-a)*z)=gaussianReal 0 (toNNReal (t-a)) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [sq_sqrt (sub_nonneg.mpr ht),ht]
  rw [heatLaw,Measure.conv,←hg]
  have hm := Measure.map_prod_map μ (gaussianReal 0 1) measurable_id (show Measurable (fun z : ℝ => sqrt (t-a)*z) from by fun_prop)
  rw [Measure.map_id] at hm
  rw [hm,Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma heatObservation_eq_integral {μ : Measure ℝ} [IsFiniteMeasure μ] {a t : ℝ}
    (ht : a≤t) {f : ℝ → ℝ} (hf : Continuous f) :
    heatObservation μ a f t=∫ x,f x ∂heatLaw μ a t := by
  rw [heatLaw_eq_map ht,integral_map (by fun_prop) hf.aestronglyMeasurable]
  rfl

lemma ExpGrowth.integrable_heatLaw {μ : Measure ℝ} [IsFiniteMeasure μ] {a t M : ℝ}
    (ht : a≤t) (hM : 0≤M) {f : ℝ → ℝ} (hf : ExpGrowth M f) (hc : Continuous f)
    (hi : Integrable (fun x => exp (M*|x|)) μ) : Integrable f (heatLaw μ a t) := by
  obtain ⟨C,hC,hf⟩ := hf
  rw [heatLaw_eq_map ht,integrable_map_measure hc.aestronglyMeasurable (by fun_prop)]
  exact integrable_scale_prod hc hM hC hf hi _

lemma ExpGrowth.integrable_heatObservation {μ : Measure ℝ} [IsFiniteMeasure μ] {a t M : ℝ}
    (hM : 0≤M) {f : ℝ → ℝ} (hf : ExpGrowth M f) (hc : Continuous f)
    (hi : Integrable (fun x => exp (M*|x|)) μ) :
    Integrable (fun p : ℝ × ℝ => f (p.1+sqrt (t-a)*p.2)) (μ.prod (gaussianReal 0 1)) := by
  obtain ⟨C,hC,hf⟩ := hf
  exact integrable_scale_prod hc hM hC hf hi _

lemma heatObservation_add {μ : Measure ℝ} [IsFiniteMeasure μ] {a t M : ℝ}
    (hM : 0≤M) {f g : ℝ → ℝ} (hf : ExpGrowth M f) (hg : ExpGrowth M g)
    (hc : Continuous f) (hd : Continuous g) (hi : Integrable (fun x => exp (M*|x|)) μ) :
    heatObservation μ a (fun x => f x+g x) t=heatObservation μ a f t+heatObservation μ a g t :=
  integral_add (hf.integrable_heatObservation hM hc hi) (hg.integrable_heatObservation hM hd hi)
lemma heatObservation_const_mul (μ : Measure ℝ) (a t c : ℝ) (f : ℝ → ℝ) :
    heatObservation μ a (fun x => c*f x) t=c*heatObservation μ a f t := integral_const_mul _ _

lemma hasDerivAt_heatObservation_growth {μ : Measure ℝ} [IsFiniteMeasure μ] {f f' f'' : ℝ → ℝ}
    (hc : Continuous f) (hc' : Continuous f') (hc'' : Continuous f'')
    (hd : ∀ x,HasDerivAt f (f' x) x) (hd' : ∀ x,HasDerivAt f' (f'' x) x)
    {M : ℝ} (hM : 0≤M) (hf : ExpGrowth M f) (hf' : ExpGrowth M f') (hf'' : ExpGrowth M f'')
    (hi : Integrable (fun x => exp (M*|x|)) μ) {a t : ℝ} (ht : a<t) :
    HasDerivAt (heatObservation μ a f) ((heatObservation μ a f'') t/2) t := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,hD,hf'⟩ := hf'
  obtain ⟨E,hE,hf''⟩ := hf''
  exact hasDerivAt_heatObservation hc hc' hc'' hd hd' hM hC hD hE hf hf' hf'' hi ht

lemma continuous_heatObservation_growth {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hc : Continuous f) {M : ℝ} (hM : 0≤M) (hf : ExpGrowth M f)
    (hi : Integrable (fun x => exp (M*|x|)) μ) (a : ℝ) : Continuous (heatObservation μ a f) := by
  obtain ⟨C,hC,hf⟩ := hf
  exact continuous_heatObservation hc hM hC hf hi a

def weightedHeat (μ : Measure ℝ) (a d K α : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  K*exp (α^2/2*(d-t))*heatObservation μ a f t

lemma weightedHeat_hasDerivAt {μ : Measure ℝ} [IsFiniteMeasure μ] {f f' g : ℝ → ℝ}
    (hc : Continuous f) (hc' : Continuous f') (hgc : Continuous g) {α : ℝ}
    (hd : ∀ x,HasDerivAt f (f' x) x) (hd' : ∀ x,HasDerivAt f' (α^2*f x+g x) x)
    {M : ℝ} (hM : 0≤M) (hf : ExpGrowth M f) (hf' : ExpGrowth M f') (hg : ExpGrowth M g)
    (hi : Integrable (fun x => exp (M*|x|)) μ) {a t : ℝ} (ht : a<t) (d K : ℝ) :
    HasDerivAt (weightedHeat μ a d K α f) (weightedHeat μ a d K α g t/2) t := by
  have hh := hasDerivAt_heatObservation_growth hc hc' ((continuous_const.mul hc).add hgc)
    hd hd' hM hf hf' ((hf.const_mul (α^2)).add hg) hi ht
  change HasDerivAt (heatObservation μ a f) (heatObservation μ a (fun x => α^2*f x+g x) t/2) t at hh
  rw [heatObservation_add hM (hf.const_mul (α^2)) hg (continuous_const.mul hc) hgc hi,
    heatObservation_const_mul] at hh
  have he := ((((hasDerivAt_const t d).sub (hasDerivAt_id t)).const_mul (α^2/2)).exp).const_mul K
  convert he.mul hh using 1 <;> first | rfl | (simp only [Pi.sub_apply,id_eq,zero_sub,weightedHeat]; ring)

lemma continuous_weightedHeat {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hc : Continuous f) {M : ℝ} (hM : 0≤M) (hf : ExpGrowth M f)
    (hi : Integrable (fun x => exp (M*|x|)) μ) (a d K α : ℝ) :
    Continuous (weightedHeat μ a d K α f) := by
  exact (show Continuous (fun t => K*exp (α^2/2*(d-t))) from by fun_prop).mul
    (continuous_heatObservation_growth hc hM hf hi a)

lemma weightedHeat_cosh_hasDerivAt {μ : Measure ℝ} [IsFiniteMeasure μ] {α : ℝ}
    (hi : Integrable (fun x => exp ((|α|+1)*|x|)) μ) {a t : ℝ} (ht : a<t) (d K : ℝ) :
    HasDerivAt (weightedHeat μ a d K α (fun x => cosh (α*x))) 0 t := by
  have hd (x : ℝ) : HasDerivAt (fun x => cosh (α*x)) (α*sinh (α*x)) x := by
    simpa only [id_eq,mul_one,mul_comm] using ((hasDerivAt_id x).const_mul α).cosh
  have hd' (x : ℝ) : HasDerivAt (fun x => α*sinh (α*x)) (α^2*cosh (α*x)+0) x := by
    convert (((hasDerivAt_id x).const_mul α).sinh).const_mul α using 1 <;>
      first | rfl | (simp only [id_eq,mul_one]; ring)
  have hh := weightedHeat_hasDerivAt (by fun_prop) (by fun_prop) continuous_const hd hd' (by positivity)
    (cosh_ExpGrowth α) ((sinh_ExpGrowth α).const_mul α)
    (ExpGrowth.of_bounded (M := |α|+1) (by positivity) (C := 0) le_rfl (fun x => by simp)) hi ht d K
  simpa only [weightedHeat,heatObservation,integral_zero,mul_zero,zero_div] using hh

lemma weightedHeat_G_hasDerivAt {μ : Measure ℝ} [IsFiniteMeasure μ] {α : ℝ}
    (hi : Integrable (fun x => exp ((|α|+1)*|x|)) μ) {a t : ℝ} (ht : a<t) (d K : ℝ) :
    HasDerivAt (weightedHeat μ a d K α (coshEntropy α))
      (weightedHeat μ a d K α (coshEntropyU α) t/2) t :=
  weightedHeat_hasDerivAt (continuous_coshEntropy α) (continuous_coshEntropyD α)
    (continuous_coshEntropyU α) (coshEntropy_hasDerivAt α) (coshEntropyD_hasDerivAt α)
    (by positivity) (coshEntropy_ExpGrowth α) (coshEntropyD_ExpGrowth α) (coshEntropyU_ExpGrowth α) hi ht d K

lemma weightedHeat_U_hasDerivAt {μ : Measure ℝ} [IsFiniteMeasure μ] {α : ℝ}
    (hi : Integrable (fun x => exp ((|α|+1)*|x|)) μ) {a t : ℝ} (ht : a<t) (d K : ℝ) :
    HasDerivAt (weightedHeat μ a d K α (coshEntropyU α))
      (α^4*weightedHeat μ a d K α (fun x => (cosh (α*x))⁻¹^3) t) t := by
  have hh := weightedHeat_hasDerivAt (continuous_coshEntropyU α) (continuous_coshEntropyUD α)
    (by exact continuous_const.mul (((continuous_cosh.comp (continuous_const.mul continuous_id)).inv₀ (fun x => (cosh_pos _).ne')).pow 3)) (coshEntropyU_hasDerivAt α) (coshEntropyUD_hasDerivAt α)
    (by positivity) (coshEntropyU_ExpGrowth α) (coshEntropyUD_ExpGrowth α)
    ((sechCube_ExpGrowth α).const_mul (2*α^4)) hi ht d K
  convert hh using 1
  simp only [weightedHeat,heatObservation_const_mul]
  ring

def baseEntropy (μ : Measure ℝ) (a d K α t : ℝ) : ℝ :=
  (log K+α^2/2*(d-t))*weightedHeat μ a d K α (fun x => cosh (α*x)) t+
    weightedHeat μ a d K α (coshEntropy α) t

def baseEntropyD (μ : Measure ℝ) (a d K α t : ℝ) : ℝ :=
  -(α^2/2)*weightedHeat μ a d K α (fun x => cosh (α*x)) t+
    weightedHeat μ a d K α (coshEntropyU α) t/2

def baseCurvature (μ : Measure ℝ) (a d K α t : ℝ) : ℝ :=
  α^4/2*weightedHeat μ a d K α (fun x => (cosh (α*x))⁻¹^3) t

lemma baseEntropy_hasDerivAt {μ : Measure ℝ} [IsFiniteMeasure μ] {α : ℝ}
    (hi : Integrable (fun x => exp ((|α|+1)*|x|)) μ) {a t : ℝ} (ht : a<t) (d K : ℝ) :
    HasDerivAt (baseEntropy μ a d K α) (baseEntropyD μ a d K α t) t := by
  have hL := (((hasDerivAt_const t d).sub (hasDerivAt_id t)).const_mul (α^2/2)).const_add (log K)
  convert (hL.mul (weightedHeat_cosh_hasDerivAt hi ht d K)).add (weightedHeat_G_hasDerivAt hi ht d K) using 1 <;>
    first | rfl | (simp only [mul_zero,zero_sub,add_zero,baseEntropyD]; ring)

lemma baseEntropyD_hasDerivAt {μ : Measure ℝ} [IsFiniteMeasure μ] {α : ℝ}
    (hi : Integrable (fun x => exp ((|α|+1)*|x|)) μ) {a t : ℝ} (ht : a<t) (d K : ℝ) :
    HasDerivAt (baseEntropyD μ a d K α) (baseCurvature μ a d K α t) t := by
  convert ((weightedHeat_cosh_hasDerivAt hi ht d K).const_mul (-(α^2/2))).add
    ((weightedHeat_U_hasDerivAt hi ht d K).div_const 2) using 1 <;>
      first | rfl | (simp only [baseCurvature,mul_zero,zero_add]; ring)

lemma continuous_baseCurvature {μ : Measure ℝ} [IsFiniteMeasure μ] {α : ℝ}
    (hi : Integrable (fun x => exp ((|α|+1)*|x|)) μ) (a d K : ℝ) :
    Continuous (baseCurvature μ a d K α) := by
  exact continuous_const.mul (continuous_weightedHeat (((continuous_cosh.comp (continuous_const.mul continuous_id)).inv₀ (fun x => (cosh_pos _).ne')).pow 3) (by positivity)
    (sechCube_ExpGrowth α) hi a d K α)

lemma baseEntropy_eq_integral {μ : Measure ℝ} [IsFiniteMeasure μ] {α K a t : ℝ}
    (hi : Integrable (fun x => exp ((|α|+1)*|x|)) μ) (ht : a≤t) (hK : 0<K) (d : ℝ) :
    baseEntropy μ a d K α t=∫ x,backwardC d K α t x*log (backwardC d K α t x) ∂heatLaw μ a t := by
  have hc := (cosh_ExpGrowth α).integrable_heatLaw ht (by positivity) (by fun_prop) hi
  have hG := (coshEntropy_ExpGrowth α).integrable_heatLaw ht (by positivity) (continuous_coshEntropy α) hi
  have he (x : ℝ) : backwardC d K α t x*log (backwardC d K α t x)=
      ((log K+α^2/2*(d-t))*(K*exp (α^2/2*(d-t))))*cosh (α*x)+
      (K*exp (α^2/2*(d-t)))*coshEntropy α x := by
    rw [backwardC_log d K α t x hK]
    dsimp only [backwardC,coshEntropy]
    ring
  simp_rw [he]
  rw [integral_add (hc.const_mul _) (hG.const_mul _)]
  simp only [integral_const_mul,baseEntropy,weightedHeat,
    heatObservation_eq_integral ht (show Continuous (fun x => cosh (α*x)) from by fun_prop),
    heatObservation_eq_integral ht (continuous_coshEntropy α)]
  ring

end ParisiSpectral

 

 

open MeasureTheory ProbabilityTheory Filter Function Set Real
open scoped Topology NNReal
namespace ParisiFinite.BoundedCoefficient
open ParisiPath ParisiSpectral
variable {β : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
lemma exp_field_backward (c : BoundedCoefficient β) (hβ : 0<β)
    {a d α : ℝ≥0} (hd1 : d≤1) (ha : 0<α) (hc : ∀ u∈Icc a d,c.val u=α)
    {K : ℝ} {g : ℝ → ℝ} (hg : PositiveDefinite g) (hgc : Continuous g)
    (he : ∀ x,exp ((α:ℝ)*field β c.val d x)=K*cosh ((α:ℝ)*x)-g x)
    {t : ℝ≥0} (ht : t∈Ico a d) (x : ℝ) :
    exp ((α:ℝ)*field β c.val t x)=backwardC d K α t x-backwardG d g t x := by
  rw [field_on_plateau β hβ c.mono c.bound hd1 (fun u hu => hc u ⟨hu.1,hu.2.le⟩) ht x,
    ←NNReal.coe_sub ht.2.le,exp_step_heat (field_lipschitz β hβ c.mono c.bound d) (by exact_mod_cast ha.ne')]
  have hi : Integrable (fun z => g (x+z)) (gaussianReal 0 (d-t)) :=
    Integrable.of_bound (hgc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (g 0) (ae_of_all _ fun z => hg.norm_le _)
  have hδ : toNNReal ((d:ℝ)-t)=d-t := by
    apply NNReal.eq
    simp only [coe_toNNReal _ (sub_nonneg.mpr (show (t:ℝ)≤d from ht.2.le)),NNReal.coe_sub ht.2.le]
  dsimp only [heat]
  simp_rw [he]
  rw [integral_sub ((integrable_cosh_shift (α:ℝ) x (d-t)).const_mul K) hi,integral_const_mul]
  have hh := heat_cosh (α:ℝ) x (d-t)
  dsimp only [heat] at hh
  rw [hh]
  simp only [backwardC,backwardG,hδ,NNReal.coe_sub ht.2.le]
  congr 1
  rw [show ((d:ℝ)-t)*(α:ℝ)^2/2=(α:ℝ)^2/2*((d:ℝ)-t) by ring]
  ring

lemma plateau_backward_representation (c : BoundedCoefficient β) (hβ : 0<β)
    {a d α : ℝ≥0} (had : a<d) (hd1 : d≤1) (ha : 0<α)
    (hc : ∀ u∈Icc a d,c.val u=α) :
    ∃ (K : ℝ) (g : ℝ → ℝ),0<K ∧ PositiveDefinite g ∧ Continuous g ∧ g 0<K ∧
      ∀ t∈Ico a d,∀ x,exp ((α:ℝ)*field β c.val t x)=backwardC d K α t x-backwardG d g t x := by
  obtain ⟨K,g,hK,hg,hgK,he⟩ :=
    (field_coshCone β hβ c.mono c.bound d (by exact_mod_cast ha)
      (by rw [hc d ⟨had.le,le_rfl⟩]; exact le_rfl)).representation
  have hgc : Continuous g := by
    have heq : g=fun x => K*cosh ((α:ℝ)*x)-exp ((α:ℝ)*field β c.val d x) := by
      funext x; calc
        g x = K*cosh ((α:ℝ)*x)-(K*cosh ((α:ℝ)*x)-g x) := by ring
        _ = _ := congrArg (fun v => K*cosh ((α:ℝ)*x)-v) (he x).symm
    rw [heq]
    exact (by fun_prop : Continuous (fun x => K*cosh ((α:ℝ)*x))).sub
      ((continuous_const.mul (field_lipschitz β hβ c.mono c.bound d).continuous).rexp)
  exact ⟨K,g,hK,hg,hgc,hgK,fun t ht x => c.exp_field_backward hβ hd1 ha hc hg hgc he ht x⟩

lemma conjugateMeasure_eq_heatLaw (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) {a d α : ℝ≥0} (ha0 : a≠0) (hd1 : d≤1)
    (ha : 0<α) (hc : ∀ u∈Icc a d,c.val u=α) {t : ℝ≥0} (ht : t∈Ioc a d) :
    c.conjugateMeasure P W hβ ⟨t,t.coe_nonneg,by exact_mod_cast ht.2.trans hd1⟩=
      heatLaw (c.conjugateMeasure P W hβ ⟨a,a.coe_nonneg,by exact_mod_cast ht.1.le.trans ht.2|>.trans hd1⟩) a t := by
  have hh := c.conjugateMeasure_plateau hβ hW ha0 ht.1 (ht.2.trans hd1) ha
    (fun u hu => hc u ⟨hu.1,hu.2.le.trans ht.2⟩) (hc t ⟨ht.1.le,ht.2⟩)
  rw [hh,heatLaw]
  congr 2
end ParisiFinite.BoundedCoefficient

 

 

open MeasureTheory ProbabilityTheory Filter Function Set Real
open scoped Topology NNReal
namespace ParisiSpectral
lemma integrable_gaussian_exp_abs (M : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => exp (M*|x|)) (gaussianReal 0 v) := by
  apply ((integrable_exp_mul_gaussianReal M).add (integrable_exp_mul_gaussianReal (-M))).mono' (by fun_prop)
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_pos (exp_pos _)]
  rcases le_total 0 x with hx|hx
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (exp_pos _).le
  · rw [abs_of_nonpos hx,show M*(-x)=(-M)*x by ring]
    exact le_add_of_nonneg_left (exp_pos _).le
end ParisiSpectral
namespace ParisiPath
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ} {K M : ℝ≥0}
lemma brownian_solution_exp_abs (hW : IsBrownianReal W P) (b : Drift K M) (t : Time) {A : ℝ} (hA : 0≤A) :
    Integrable (fun ω => exp (A*|solution b (brownianPath W ω) t|)) P := by
  have hg := ParisiSpectral.integrable_gaussian_exp_abs A ⟨t,t.property.1⟩
  have hw : Integrable (fun ω => exp (A*|W ⟨t,t.property.1⟩ ω|)) P :=
    by
      rw [←(hW.hasLaw_eval ⟨t,t.property.1⟩).map_eq] at hg
      exact (integrable_map_measure (by fun_prop) (hW.hasLaw_eval _).aemeasurable).mp hg
  have hx := (aemeasurable_solution_eval b (brownianPath W) (brownianPath_aemeasurable_eval hW) t).aestronglyMeasurable
  apply (hw.const_mul (exp (A*((M:ℝ)*(t:ℝ))))).mono'
    ((continuous_exp.comp_aestronglyMeasurable (continuous_abs.comp_aestronglyMeasurable hx |>.const_mul A)))
  filter_upwards [brownianPath_eq_ae hW] with ω hω
  rw [Real.norm_eq_abs,abs_of_pos (exp_pos _),←exp_add]
  apply exp_le_exp.mpr
  have hb := norm_solution_sub_driver b (brownianPath W ω) t
  rw [Real.norm_eq_abs,hω t] at hb
  have hh := abs_add_le (solution b (brownianPath W ω) t-W ⟨t,t.property.1⟩ ω) (W ⟨t,t.property.1⟩ ω)
  rw [sub_add_cancel] at hh
  nlinarith
end ParisiPath
namespace ParisiFinite.BoundedCoefficient
open ParisiPath ParisiSpectral
variable {β : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
lemma conjugateMeasure_exp_abs (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) (t : Time) (ha : 0<c.val ⟨t,t.property.1⟩) {A : ℝ} (hA : 0≤A) :
    Integrable (fun x : ℝ => exp (A*|x|)) (conjugateMeasure P W c hβ t) := by
  have he : Continuous (fun x => exp (-(c.val ⟨t,t.property.1⟩:ℝ)*field β c.val ⟨t,t.property.1⟩ x)) :=
    (continuous_const.mul (field_lipschitz β hβ c.mono c.bound _).continuous).rexp
  have hp := (field_coshCone β hβ c.mono c.bound ⟨t,t.property.1⟩ (by exact_mod_cast ha) le_rfl).neg_exp_positiveDefinite
    (by exact_mod_cast ha) (c.val ⟨t,t.property.1⟩).coe_nonneg
  rw [conjugateMeasure,integrable_withDensity_iff_integrable_smul' he.measurable.ennreal_ofReal
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (exp_pos _).le,smul_eq_mul]
  have hi : Integrable (fun x : ℝ => exp (A*|x|))
      (P.map (fun ω => solution (c.driftData hβ) (brownianPath W ω) t)) :=
    (integrable_map_measure (by fun_prop)
      (aemeasurable_solution_eval _ _ (brownianPath_aemeasurable_eval hW) t)).mpr
      (brownian_solution_exp_abs hW _ t hA)
  exact hi.bdd_mul he.aestronglyMeasurable (ae_of_all _ hp.norm_le)
end ParisiFinite.BoundedCoefficient

 

 

open MeasureTheory ProbabilityTheory Filter Function Set Real
open scoped Topology NNReal
namespace ParisiFinite.BoundedCoefficient
open ParisiPath ParisiSpectral
variable {β : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}
lemma conjugateMeasure_ne_zero (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) (t : Time) : conjugateMeasure P W c hβ t≠0 := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have he : Continuous (fun x => exp (-(c.val ⟨t,t.property.1⟩:ℝ)*field β c.val ⟨t,t.property.1⟩ x)) :=
    (continuous_const.mul (field_lipschitz β hβ c.mono c.bound _).continuous).rexp
  intro hz
  have hh := (withDensity_eq_zero_iff he.measurable.ennreal_ofReal.aemeasurable).mp hz
  have hf : ∀ᵐ x ∂P.map (fun ω => solution (c.driftData hβ) (brownianPath W ω) t),False := hh.mono fun x hx =>
    (ENNReal.ofReal_pos.mpr (exp_pos _)).ne' hx
  exact (Filter.Eventually.exists hf).elim (fun _ h => h)

 

lemma conjugateMeasure_entropy (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) (t : Time) :
    (∫ x,exp ((c.val ⟨t,t.property.1⟩:ℝ)*field β c.val ⟨t,t.property.1⟩ x)*
      log (exp ((c.val ⟨t,t.property.1⟩:ℝ)*field β c.val ⟨t,t.property.1⟩ x))
      ∂conjugateMeasure P W c hβ t)=
      (c.val ⟨t,t.property.1⟩:ℝ)*∫ ω,field β c.val ⟨t,t.property.1⟩
        (solution (c.driftData hβ) (brownianPath W ω) t) ∂P := by
  have fc := (field_lipschitz β hβ c.mono c.bound ⟨t,t.property.1⟩).continuous
  rw [c.integral_conjugateMeasure hβ hW t (by fun_prop),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [log_exp,←mul_assoc,←exp_add]
  simp only [neg_mul,neg_add_cancel,exp_zero,one_mul]

lemma field_along_solution_integrable (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) (t : Time) :
    Integrable (fun ω => field β c.val ⟨t,t.property.1⟩
      (solution (c.driftData hβ) (brownianPath W ω) t)) P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hx := brownian_solution_integrable hW (c.driftData hβ) t
  exact (canonicalSpatialTest β hβ c.mono c.bound ⟨t,t.property.1⟩).integrable_comp hx

lemma conjugateMeasure_entropy_integrable (c : BoundedCoefficient β) (hβ : 0<β)
    (hW : IsBrownianReal W P) (t : Time) :
    Integrable (fun x => exp ((c.val ⟨t,t.property.1⟩:ℝ)*field β c.val ⟨t,t.property.1⟩ x)*
      log (exp ((c.val ⟨t,t.property.1⟩:ℝ)*field β c.val ⟨t,t.property.1⟩ x)))
      (conjugateMeasure P W c hβ t) := by
  have fc := (field_lipschitz β hβ c.mono c.bound ⟨t,t.property.1⟩).continuous
  have he : Continuous (fun x => exp (-(c.val ⟨t,t.property.1⟩:ℝ)*field β c.val ⟨t,t.property.1⟩ x)) :=
    (continuous_const.mul fc).rexp
  rw [conjugateMeasure,integrable_withDensity_iff_integrable_smul' he.measurable.ennreal_ofReal
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (exp_pos _).le,smul_eq_mul,log_exp,←mul_assoc,←exp_add,
    neg_mul,neg_add_cancel,exp_zero,one_mul]
  rw [integrable_map_measure (by fun_prop)
    (aemeasurable_solution_eval _ _ (brownianPath_aemeasurable_eval hW) t)]
  exact (c.field_along_solution_integrable hβ hW t).const_mul _
end ParisiFinite.BoundedCoefficient

 

 

open MeasureTheory ProbabilityTheory Filter Function Set Real
open scoped Topology NNReal
namespace ParisiFinite.BoundedCoefficient
open ParisiPath ParisiSpectral
variable {β : ℝ≥0} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → ℝ}

def fieldEntropy (c : BoundedCoefficient β) (hβ : 0<β) (P : Measure Ω)
    (W : ℝ≥0 → Ω → ℝ) (α t : ℝ) : ℝ :=
  α*(field β c.val 0 0+(∫ u in (0:ℝ)..t,c.real u*expectedProduct P W c c (c.driftData hβ) u)/2)

lemma fieldEntropy_eq (c : BoundedCoefficient β) (hβ : 0<β) (hW : IsBrownianReal W P)
    (t : Time) (ht0 : 0<(t:ℝ)) (ht1 : (t:ℝ)<1) {α : ℝ≥0}
    (ha : c.val ⟨t,t.property.1⟩=α) :
    c.fieldEntropy hβ P W α t =
      ∫ x,exp ((α:ℝ)*field β c.val ⟨t,t.property.1⟩ x)*
        log (exp ((α:ℝ)*field β c.val ⟨t,t.property.1⟩ x)) ∂c.conjugateMeasure P W hβ t := by
  rw [←ha,c.conjugateMeasure_entropy hβ hW,c.field_value_at hW hβ t ht0 ht1]
  rfl

lemma real_eq_on_plateau (c : BoundedCoefficient β) {a d α : ℝ≥0}
    (hc : ∀ u∈Icc a d,c.val u=α) {t : ℝ} (ht : t∈Icc (a:ℝ) d) : c.real t=α := by
  have hp : 0≤t := a.coe_nonneg.trans ht.1
  exact congrArg (fun u : ℝ≥0 => (u:ℝ)) (hc (toNNReal t)
    ⟨by exact_mod_cast (show (a:ℝ)≤(toNNReal t:ℝ) by simpa only [coe_toNNReal _ hp] using ht.1),
      by exact_mod_cast (show (toNNReal t:ℝ)≤d by simpa only [coe_toNNReal _ hp] using ht.2)⟩)

lemma fieldEntropy_hasDerivAt (c : BoundedCoefficient β) (hβ : 0<β) (hW : IsBrownianReal W P)
    {a d α : ℝ≥0} (hc : ∀ u∈Icc a d,c.val u=α) {t : ℝ} (ht : t∈Ioo (a:ℝ) d) :
    HasDerivAt (c.fieldEntropy hβ P W α)
      ((α:ℝ)^2/2*expectedProduct P W c c (c.driftData hβ) t) t := by
  have hp := expectedProduct_continuous hW c c hβ (c.driftData hβ)
  have hm : StronglyMeasurable (fun u => c.real u*expectedProduct P W c c (c.driftData hβ) u) :=
    (c.measurable_real.mul hp.measurable).stronglyMeasurable
  have hi := (c.real_intervalIntegrable 0 t).mul_continuousOn hp.continuousOn
  have he : (fun u => c.real u*expectedProduct P W c c (c.driftData hβ) u)=ᶠ[𝓝 t]
      (fun u => (α:ℝ)*expectedProduct P W c c (c.driftData hβ) u) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    rw [c.real_eq_on_plateau hc ⟨hu.1.le,hu.2.le⟩]
  have hcont := ((continuous_const.mul hp).continuousAt).congr he.symm
  have hh := ((intervalIntegral.integral_hasDerivAt_right hi hm.stronglyMeasurableAtFilter hcont).div_const 2).const_add (field β c.val 0 0)
  have hd := hh.const_mul (α:ℝ)
  rw [c.real_eq_on_plateau hc ⟨ht.1.le,ht.2.le⟩] at hd
  convert hd using 1 <;> first | rfl | ring

lemma fieldEntropyD_hasDerivAt (c : BoundedCoefficient β) (hβ : 0<β) (hW : IsBrownianReal W P)
    (α : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun u => α^2/2*expectedProduct P W c c (c.driftData hβ) u)
      (α^2/2*c.expectedSquareCurvature P W hβ t) t :=
  (hasDerivAt_expectedProduct_self hW hβ c t ht).const_mul _
end ParisiFinite.BoundedCoefficient

 

 

open MeasureTheory ProbabilityTheory Set Real Filter Matrix
open scoped Topology NNReal ContDiff
namespace ParisiSpectral
lemma contDiffOn_two_of_derivatives {f f' f'' : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hd : ∀ x∈s,HasDerivAt f (f' x) x) (hd' : ∀ x∈s,HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f'' s) : ContDiffOn ℝ 2 f s := by
  have he : EqOn (deriv f) f' s := fun x hx => (hd x hx).deriv
  have he' : EqOn (deriv f') f'' s := fun x hx => (hd' x hx).deriv
  have hg : ContDiffOn ℝ 1 f' s := by
    rw [show (1 : ℕ∞ω)=0+1 by rfl,contDiffOn_succ_iff_deriv_of_isOpen hs]
    refine ⟨fun x hx => (hd' x hx).differentiableAt.differentiableWithinAt,by simp,?_⟩
    exact (contDiffOn_zero.mpr hc).congr he'
  rw [show (2 : ℕ∞ω)=1+1 by rfl,contDiffOn_succ_iff_deriv_of_isOpen hs]
  exact ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt,by simp,hg.congr he⟩

lemma iteratedDeriv_two_of_derivatives {f f' f'' : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s)
    (hd : ∀ x∈s,HasDerivAt f (f' x) x) (hd' : ∀ x∈s,HasDerivAt f' (f'' x) x)
    {x : ℝ} (hx : x∈s) : iteratedDeriv 2 f x=f'' x := by
  have he : deriv f =ᶠ[𝓝 x] f' := Filter.mem_of_superset (hs.mem_nhds hx) fun y hy => (hd y hy).deriv
  rw [show 2=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one]
  rw [he.deriv_eq]
  exact (hd' x hx).deriv

lemma HankelPD.congr_on {f g : ℝ → ℝ} {s : Set ℝ} (hf : HankelPD f s)
    (hs : Convex ℝ s) (he : EqOn f g s) : HankelPD g s := by
  have hm (x y : s) : ((x:ℝ)+y)/2∈s := by
    simpa only [midpoint_eq_smul_add,smul_eq_mul,invOf_eq_inv,div_eq_mul_inv,mul_comm]
      using hs.midpoint_mem x.property y.property
  have heq : Matrix.of (fun x y : s => f ((x+y)/2))=Matrix.of (fun x y : s => g ((x+y)/2)) := by
    ext x y
    exact he (hm x y)
  change (Matrix.of (fun x y : s => g ((x+y)/2))).PosSemidef
  rw [←heq]
  exact hf

lemma HankelCPD.congr_on {f g : ℝ → ℝ} {s : Set ℝ} (hf : HankelCPD f s)
    (hs : Convex ℝ s) (he : EqOn f g s) : HankelCPD g s := by
  intro z
  have hm (x y : s) : ((x:ℝ)+y)/2∈s := by
    simpa only [midpoint_eq_smul_add,smul_eq_mul,invOf_eq_inv,div_eq_mul_inv,mul_comm]
      using hs.midpoint_mem x.property y.property
  have heq : Matrix.of (fun x y : s => f ((x+y)/2)-f ((x+z)/2)-f ((z+y)/2)+f z)=
      Matrix.of (fun x y : s => g ((x+y)/2)-g ((x+z)/2)-g ((z+y)/2)+g z) := by
    ext x y
    simp only [Matrix.of_apply,he (hm x y),he (hm x z),he (hm z y),he z.property]
  change (Matrix.of (fun x y : s => g ((x+y)/2)-g ((x+z)/2)-g ((z+y)/2)+g z)).PosSemidef
  rw [←heq]
  exact hf z

lemma HankelCPD.sub_const {f : ℝ → ℝ} {s : Set ℝ} (hf : HankelCPD f s) (C : ℝ) :
    HankelCPD (fun x => f x-C) s := by
  intro z
  have he : Matrix.of (fun x y : s => (f ((x+y)/2)-C)-(f ((x+z)/2)-C)-(f ((z+y)/2)-C)+(f z-C))=
      Matrix.of (fun x y : s => f ((x+y)/2)-f ((x+z)/2)-f ((z+y)/2)+f z) := by
    ext x y
    simp only [Matrix.of_apply]
    ring
  change (Matrix.of (fun x y : s => (f ((x+y)/2)-C)-(f ((x+z)/2)-C)-(f ((z+y)/2)-C)+(f z-C))).PosSemidef
  rw [he]
  exact hf z

lemma HankelCPD.has_second_derivative {f f' f'' : ℝ → ℝ} {s : Set ℝ}
    (hf : HankelCPD f s) (hs : Convex ℝ s) (ho : IsOpen s) (hne : s.Nonempty)
    (hd : ∀ x∈s,HasDerivAt f (f' x) x) (hd' : ∀ x∈s,HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f'' s) : HankelPD f'' s := by
  exact (hf.secondDeriv hs ho hne (contDiffOn_two_of_derivatives ho hd hd' hc)).congr_on hs
    (fun x hx => iteratedDeriv_two_of_derivatives ho hd hd' hx)
end ParisiSpectral

end

end OAI
