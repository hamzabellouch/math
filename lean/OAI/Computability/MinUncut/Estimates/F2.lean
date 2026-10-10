import Mathlib
import OAI.Computability.MinUncut.Model

namespace OAI

namespace MinUncut
open MinUncutGames.BinaryFormula MinUncutGames.BinaryEncoding

end MinUncut

noncomputable section
open scoped BigOperators

namespace MinUncut.BinaryFourier

abbrev F₂ := ZMod 2

def sign (b : F₂) : ℝ := if b = 0 then 1 else -1

@[simp] lemma sign_zero : sign 0 = 1 := by norm_num [sign]
@[simp] lemma sign_one : sign 1 = -1 := by norm_num [sign]
@[simp] lemma sign_sq (b : F₂) : sign b ^ 2 = 1 := by
  unfold sign; split_ifs <;> norm_num
@[simp] lemma sign_abs (b : F₂) : |sign b| = 1 := by
  unfold sign; split_ifs <;> norm_num
lemma sign_add (a b : F₂) : sign (a + b) = sign a * sign b := by
  have h : ∀ a : F₂, a = 0 ∨ a = 1 := by decide
  have h2 : (1 + 1 : F₂) = 0 := by decide
  rcases h a with rfl | rfl <;> rcases h b with rfl | rfl <;> simp [h2]

variable {W : Type*} [AddCommGroup W] [Module F₂ W]

lemma self_add (w : W) : w + w = 0 := by
  have h : (1 + 1 : F₂) = 0 := by decide
  have hh := congrArg (fun t : F₂ => t • w) h
  simpa only [add_smul, one_smul, zero_smul] using hh

lemma neg_eq (w : W) : -w = w := neg_eq_iff_add_eq_zero.mpr (self_add w)

lemma add_eq_zero_iff (v w : W) : v + w = 0 ↔ v = w := by
  rw [add_eq_zero_iff_eq_neg, neg_eq]

def character (α : Module.Dual F₂ W) (w : W) : ℝ := sign (α w)

@[simp] lemma character_zero (w : W) : character (0 : Module.Dual F₂ W) w = 1 := by
  simp [character]
@[simp] lemma character_at_zero (α : Module.Dual F₂ W) : character α 0 = 1 := by
  simp [character]
@[simp] lemma character_sq (α : Module.Dual F₂ W) (w : W) : character α w ^ 2 = 1 := by
  simp [character]
@[simp] lemma character_abs (α : Module.Dual F₂ W) (w : W) : |character α w| = 1 := by
  simp [character]
lemma character_add (α : Module.Dual F₂ W) (v w : W) :
    character α (v + w) = character α v * character α w := by
  simp [character, sign_add]
lemma character_add_dual (α β : Module.Dual F₂ W) (w : W) :
    character (α + β) w = character α w * character β w := by
  simp [character, sign_add]

variable [Fintype W]

omit [Module F₂ W] in
lemma expect_translate (f : W → ℝ) (v : W) : (𝔼 w, f (v + w)) = 𝔼 w, f w := by
  exact Fintype.expect_equiv (Equiv.addLeft v) _ _ (fun _ => rfl)

lemma character_mean (α : Module.Dual F₂ W) :
    (𝔼 w, character α w) = if α = 0 then 1 else 0 := by
  classical
  by_cases hα : α = 0
  · simp [hα]
  rw [ite_eq_right hα]
  have hex : ∃ v, α v ≠ 0 := by
    by_contra! hh
    exact hα (LinearMap.ext hh)
  obtain ⟨v, hv⟩ := hex
  have hs : character α v = -1 := by simp [character, sign, hv]
  have h := expect_translate (character α) v
  simp_rw [character_add, hs, ← Finset.mul_expect] at h
  linarith

lemma character_orthogonality (α β : Module.Dual F₂ W) :
    (𝔼 w, character α w * character β w) = if α = β then 1 else 0 := by
  simp_rw [← character_add_dual]
  simpa only [add_eq_zero_iff] using character_mean (α + β)

local instance f2DecidableEq : DecidableEq W := Classical.decEq W

local instance dualFintype : Fintype (Module.Dual F₂ W) :=
  Fintype.ofInjective (fun α : Module.Dual F₂ W => (α : W → F₂)) DFunLike.coe_injective

local instance f2DualDecidableEq : DecidableEq W := Classical.decEq W

lemma card_dual : Fintype.card (Module.Dual F₂ W) = Fintype.card W := by
  calc
    Fintype.card (Module.Dual F₂ W) =
        Fintype.card F₂ ^ Module.finrank F₂ (Module.Dual F₂ W) :=
      Module.card_eq_pow_finrank (K := F₂)
    _ = Fintype.card F₂ ^ Module.finrank F₂ W := by rw [Subspace.dual_finrank_eq]
    _ = Fintype.card W := (Module.card_eq_pow_finrank (K := F₂)).symm

lemma character_kernel (v w : W) :
    (∑ α : Module.Dual F₂ W, character α v * character α w) =
      if v = w then (Fintype.card W : ℝ) else 0 := by
  classical
  have he : (𝔼 α : Module.Dual F₂ W, character α (v+w)) =
      if v = w then 1 else 0 := by
    have h := character_mean ((Module.Dual.eval F₂ W) (v+w))
    have hz : (Module.Dual.eval F₂ W) (v+w) = 0 ↔ v = w := by
      rw [Module.eval_apply_eq_zero_iff, add_eq_zero_iff]
    simpa only [character, Module.Dual.eval_apply, hz] using h
  simp_rw [character_add] at he
  rw [Fintype.expect_eq_sum_div_card, card_dual] at he
  have hc : (Fintype.card W : ℝ) ≠ 0 := by positivity
  by_cases h : v = w
  · rw [ite_eq_left h] at he ⊢
    simpa using (div_eq_iff hc).mp he
  · rw [ite_eq_right h] at he ⊢
    simpa using (div_eq_iff hc).mp he

def coefficient (f : W → ℝ) (α : Module.Dual F₂ W) : ℝ :=
  𝔼 w, f w * character α w

lemma inversion (f : W → ℝ) (w : W) :
    (∑ α : Module.Dual F₂ W, coefficient f α * character α w) = f w := by
  classical
  unfold coefficient
  simp_rw [Finset.expect_mul]
  rw [← Finset.expect_sum_comm]
  have inner (v : W) :
      (∑ α : Module.Dual F₂ W, (f v * character α v) * character α w) =
      f v * (if v = w then (Fintype.card W : ℝ) else 0) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, character_kernel]
  simp_rw [inner]
  rw [Fintype.expect_eq_sum_div_card]
  simp

lemma parseval_inner (f g : W → ℝ) :
    (∑ α : Module.Dual F₂ W, coefficient f α * coefficient g α) =
      𝔼 w, f w * g w := by
  classical
  unfold coefficient
  simp_rw [Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro w _
  have hi : (∑ α : Module.Dual F₂ W,
      (𝔼 v, f v * character α v) * (g w * character α w)) =
      g w * (∑ α : Module.Dual F₂ W, coefficient f α * character α w) := by
    simp only [Finset.mul_sum, coefficient]
    apply Finset.sum_congr rfl
    intro α _
    ring
  rw [hi, inversion]
  ring

lemma parseval (f : W → ℝ) :
    (∑ α : Module.Dual F₂ W, coefficient f α ^ 2) = 𝔼 w, f w ^ 2 := by
  simpa only [sq] using parseval_inner f f

omit [Fintype W] in
@[simp] lemma add_add_cancel (v w : W) : v + (v + w) = w := by
  rw [← add_assoc, self_add, zero_add]

lemma coefficient_translate (f : W → ℝ) (α : Module.Dual F₂ W) (t : W) :
    coefficient (fun w => f (t+w)) α = character α t * coefficient f α := by
  unfold coefficient
  have ht := expect_translate (fun w => f w * character α (t+w)) t
  simp only [add_add_cancel] at ht
  rw [ht, Finset.mul_expect]
  apply Finset.expect_congr rfl
  intro w _
  rw [character_add]
  ring

def convolution (f g : W → ℝ) (t : W) : ℝ := 𝔼 w, f w * g (w+t)

lemma coefficient_convolution (f g : W → ℝ) (α : Module.Dual F₂ W) :
    coefficient (convolution f g) α = coefficient f α * coefficient g α := by
  unfold coefficient convolution
  simp_rw [Finset.expect_mul]
  rw [Finset.expect_comm]
  calc
    (𝔼 y, 𝔼 x, (f y * g (y+x)) * character α x) =
        𝔼 y, f y * coefficient (fun x => g (y+x)) α := by
      apply Finset.expect_congr rfl
      intro y _
      rw [coefficient, Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    _ = 𝔼 y, f y * (character α y * coefficient g α) := by
      simp_rw [coefficient_translate]
    _ = (𝔼 w, f w * character α w) * (𝔼 w, g w * character α w) := by
      rw [Finset.expect_mul]
      apply Finset.expect_congr rfl
      intro y _
      dsimp [coefficient]
      ring
    _ = 𝔼 w, f w * character α w * (𝔼 y, g y * character α y) := by
      rw [Finset.expect_mul]

lemma convolution_shifts (f g : W → ℝ) (r t : W) :
    (𝔼 s, f (r+s) * g (t+s)) = convolution f g (r+t) := by
  unfold convolution
  have hh : ∀ s : W, (r+s)+(r+t) = t+s := by
    intro s
    calc
      (r+s)+(r+t) = (r+r)+(t+s) := by abel
      _ = t+s := by rw [self_add, zero_add]
  have h := expect_translate (fun s => f s * g (s+(r+t))) r
  simpa only [hh] using h

lemma square_fourier (f₀₀ f₀₁ f₁₀ f₁₁ : W → ℝ) :
    (𝔼 r₀, 𝔼 r₁, 𝔼 s₀, 𝔼 s₁,
      f₀₀ (r₀+s₀) * f₀₁ (r₀+s₁) * f₁₀ (r₁+s₀) * f₁₁ (r₁+s₁)) =
    ∑ α : Module.Dual F₂ W,
      coefficient f₀₀ α * coefficient f₀₁ α * coefficient f₁₀ α * coefficient f₁₁ α := by
  calc
    _ = 𝔼 r₀, 𝔼 r₁,
        (𝔼 s₀, f₀₀ (r₀+s₀) * f₁₀ (r₁+s₀)) *
        (𝔼 s₁, f₀₁ (r₀+s₁) * f₁₁ (r₁+s₁)) := by
      apply Finset.expect_congr rfl
      intro r₀ _
      apply Finset.expect_congr rfl
      intro r₁ _
      rw [Fintype.expect_mul_expect]
      apply Finset.expect_congr rfl
      intro s₀ _
      apply Finset.expect_congr rfl
      intro s₁ _
      ring
    _ = 𝔼 r₀, 𝔼 r₁, convolution f₀₀ f₁₀ (r₀+r₁) * convolution f₀₁ f₁₁ (r₀+r₁) := by
      simp_rw [convolution_shifts]
    _ = 𝔼 t, convolution f₀₀ f₁₀ t * convolution f₀₁ f₁₁ t := by
      trans 𝔼 r₀ : W, (𝔼 t, convolution f₀₀ f₁₀ t * convolution f₀₁ f₁₁ t)
      · apply Finset.expect_congr rfl
        intro r₀ _
        exact expect_translate (fun t => convolution f₀₀ f₁₀ t * convolution f₀₁ f₁₁ t) r₀
      · simp
    _ = ∑ α : Module.Dual F₂ W,
        coefficient (convolution f₀₀ f₁₀) α * coefficient (convolution f₀₁ f₁₁) α :=
      (parseval_inner _ _).symm
    _ = _ := by
      simp_rw [coefficient_convolution]
      apply Finset.sum_congr rfl
      intro α _
      ring

lemma square_bound (f₀₀ f₀₁ f₁₀ f₁₁ : W → ℝ) (ε H : ℝ)
    (hε : 0 ≤ ε)
    (h₀₀ : ∀ α, |coefficient f₀₀ α| ≤ ε)
    (h₀₁ : ∀ α, |coefficient f₀₁ α| ≤ ε)
    (h₁₀ : (𝔼 w, f₁₀ w ^ 2) ≤ H ^ 2)
    (h₁₁ : (𝔼 w, f₁₁ w ^ 2) ≤ H ^ 2) :
    |𝔼 r₀, 𝔼 r₁, 𝔼 s₀, 𝔼 s₁,
      f₀₀ (r₀+s₀) * f₀₁ (r₀+s₁) * f₁₀ (r₁+s₀) * f₁₁ (r₁+s₁)| ≤ ε^2 * H^2 := by
  rw [square_fourier]
  have he₁₀ : (∑ α : Module.Dual F₂ W, |coefficient f₁₀ α| ^ 2) ≤ H^2 := by
    simpa only [sq_abs, parseval] using h₁₀
  have he₁₁ : (∑ α : Module.Dual F₂ W, |coefficient f₁₁ α| ^ 2) ≤ H^2 := by
    simpa only [sq_abs, parseval] using h₁₁
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun α : Module.Dual F₂ W => |coefficient f₁₀ α|)
    (fun α : Module.Dual F₂ W => |coefficient f₁₁ α|)
  have hprod : (∑ α : Module.Dual F₂ W, |coefficient f₁₀ α|^2) *
      (∑ α : Module.Dual F₂ W, |coefficient f₁₁ α|^2) ≤ H^2 * H^2 :=
    mul_le_mul he₁₀ he₁₁ (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
  have hsum : (∑ α : Module.Dual F₂ W,
      |coefficient f₁₀ α| * |coefficient f₁₁ α|) ≤ H^2 := by
    nlinarith [sq_nonneg ((∑ α : Module.Dual F₂ W,
      |coefficient f₁₀ α| * |coefficient f₁₁ α|) - H^2)]
  calc
    _ ≤ ∑ α : Module.Dual F₂ W,
        |coefficient f₀₀ α * coefficient f₀₁ α * coefficient f₁₀ α * coefficient f₁₁ α| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ α : Module.Dual F₂ W,
        ε^2 * (|coefficient f₁₀ α| * |coefficient f₁₁ α|) := by
      apply Finset.sum_le_sum
      intro α _
      rw [show coefficient f₀₀ α * coefficient f₀₁ α * coefficient f₁₀ α * coefficient f₁₁ α =
          (coefficient f₀₀ α * coefficient f₀₁ α) * (coefficient f₁₀ α * coefficient f₁₁ α) by ring,
        abs_mul, abs_mul, abs_mul, sq]
      exact mul_le_mul_of_nonneg_right (mul_le_mul (h₀₀ α) (h₀₁ α) (abs_nonneg _) hε)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = ε^2 * ∑ α : Module.Dual F₂ W, |coefficient f₁₀ α| * |coefficient f₁₁ α| := by
      rw [Finset.mul_sum]
    _ ≤ ε^2 * H^2 := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)

end MinUncut.BinaryFourier

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace MinUncut.GaussianSmoothing

lemma weighted_exp_derivative {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X f : Ω → ℝ}
    (hX : Measurable X) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1)
    (he : ∀ t : ℝ, Integrable (fun x => Real.exp (t * X x)) μ) :
    HasDerivAt (fun t : ℝ => ∫ x, Real.exp (t * X x) * f x ∂μ)
      (∫ x, X x * f x ∂μ) 0 := by
  have hdom : Integrable (fun x => |X x| * Real.exp |X x|) μ := by
    simpa using integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
      (X := X) (v := 0) (t := 2) (x := 1) (by simpa using he 2)
      (by simpa using he (-2)) (by norm_num) (by norm_num) 1
  have hfint : Integrable f μ := (integrable_const (1 : ℝ)).mono'
    hf.aestronglyMeasurable (ae_of_all _ fun x => by simpa using hb x)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := fun t x => Real.exp (t * X x) * f x)
    (F' := fun t x => Real.exp (t * X x) * X x * f x)
    (bound := fun x => |X x| * Real.exp |X x|)
    (s := Set.Ioo (-1 : ℝ) 1) (x₀ := 0)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun t => (by fun_prop : Measurable
      (fun x => Real.exp (t * X x) * f x)).aestronglyMeasurable)
    (by simpa using hfint)
    (by fun_prop)
    (ae_of_all _ fun x t ht => ?_) hdom
    (ae_of_all _ fun x t _ => ?_)
  · simpa using h.2
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have ht' : |t| ≤ 1 := (abs_le.mpr ⟨le_of_lt ht.1, le_of_lt ht.2⟩)
    have hx : t * X x ≤ |X x| := by
      calc t * X x ≤ |t * X x| := le_abs_self _
           _ = |t| * |X x| := abs_mul _ _
           _ ≤ 1 * |X x| := mul_le_mul_of_nonneg_right ht' (abs_nonneg _)
           _ = |X x| := one_mul _
    calc Real.exp (t * X x) * |X x| * |f x|
        ≤ Real.exp (t * X x) * |X x| * 1 := by
          exact mul_le_mul_of_nonneg_left (hb x) (by positivity)
      _ ≤ |X x| * Real.exp |X x| := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hx)
          (abs_nonneg (X x))
  · simpa only [id_eq, one_mul] using
      (((hasDerivAt_id t).mul_const (X x)).exp).mul_const (f x)

lemma gaussianPDF_translate (t x : ℝ) :
    gaussianPDFReal t 1 x =
      gaussianPDFReal 0 1 x * (Real.exp (-(t^2)/2) * Real.exp (t*x)) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma gaussian_translate_integral {f : ℝ → ℝ} (hf : Measurable f) (t : ℝ) :
    (∫ x, f (x+t) ∂gaussianReal 0 1) =
      Real.exp (-(t^2)/2) * ∫ x, Real.exp (t*x) * f x ∂gaussianReal 0 1 := by
  have hm : (gaussianReal 0 1).map (fun x => x+t) = gaussianReal t 1 := by
    simpa using gaussianReal_map_add_const (μ := 0) (v := 1) t
  rw [← integral_map (by fun_prop : AEMeasurable (fun x : ℝ => x+t) (gaussianReal 0 1))
    hf.aestronglyMeasurable, hm]
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [gaussianPDF_translate]
  simp only [smul_eq_mul]
  ring

lemma gaussian_translate_derivative {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ 1) :
    HasDerivAt (fun t => ∫ x, f (x+t) ∂gaussianReal 0 1)
      (∫ x, x * f x ∂gaussianReal 0 1) 0 := by
  have hw := weighted_exp_derivative (μ := gaussianReal 0 1) measurable_id hf hb
    (fun t => integrable_exp_mul_gaussianReal t)
  have hd : HasDerivAt (fun t : ℝ => Real.exp (-(t^2)/2)) 0 0 := by
    convert ((((hasDerivAt_id 0).pow 2).neg).div_const 2).exp using 1 <;> norm_num
  convert! hd.mul hw using 1
  · funext t
    exact gaussian_translate_integral hf t
  · simp

lemma gaussian_convolution_derivative {f : ℝ → ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ 1) {σ : ℝ} (hσ : σ ≠ 0) (c : ℝ) :
    HasDerivAt (fun u => ∫ g, f (u + σ*g) ∂gaussianReal 0 1)
      (σ⁻¹ * ∫ g, g * f (c + σ*g) ∂gaussianReal 0 1) c := by
  have hQ : Measurable (fun g : ℝ => f (c + σ*g)) := hf.comp (by fun_prop)
  have h := gaussian_translate_derivative hQ (fun x => hb _)
  have ha : HasDerivAt (fun u : ℝ => (u-c)/σ) σ⁻¹ c := by
    simpa using ((hasDerivAt_id c).sub_const c).div_const σ
  have hcomp := HasDerivAt.comp c (by simpa only [sub_self, zero_div] using h) ha
  convert! hcomp using 1
  · ext u
    apply integral_congr_ae
    filter_upwards [] with g
    congr 1
    field_simp [hσ]
    ring
  · ring

section FiniteProduct
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev gamma (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

def split (i : ι) : (ι → ℝ) ≃ᵐ ℝ × ({j : ι // j ≠ i} → ℝ) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => ℝ) (· = i)).trans
    ((MeasurableEquiv.piUnique (fun _ : {j : ι // j = i} => ℝ)).prodCongr
      (MeasurableEquiv.refl _))

omit [Fintype ι] in
@[simp] lemma split_apply (i : ι) (g : ι → ℝ) :
    split i g = (g i, fun j => g j.1) := rfl

omit [Fintype ι] in
@[simp] lemma split_symm_apply (i : ι) (u : ℝ × ({j : ι // j ≠ i} → ℝ)) (j : ι) :
    (split i).symm u j = if h : j = i then u.1 else u.2 ⟨j,h⟩ := by
  rfl

lemma split_measurePreserving (i : ι) :
    MeasurePreserving (split i) (gamma ι)
      ((gaussianReal 0 1).prod (gamma {j : ι // j ≠ i})) := by
  let : Fintype {j : ι // j = i} := Subtype.fintype _
  exact ((measurePreserving_piUnique (fun _ : {j : ι // j = i} => gaussianReal 0 1)).prod
    (MeasurePreserving.id _)).comp
      (measurePreserving_piEquivPiSubtypeProd (fun _ : ι => gaussianReal 0 1) (· = i))

lemma integral_split (i : ι) {f : (ι → ℝ) → ℝ} (hf : Integrable f (gamma ι)) :
    (∫ g, f g ∂gamma ι) =
    ∫ t, ∫ h, f ((split i).symm (t,h)) ∂gamma {j : ι // j ≠ i} ∂gaussianReal 0 1 := by
  let hm := (split_measurePreserving i).symm (split i)
  rw [← hm.integral_comp' f, integral_prod]
  exact (hm.integrable_comp hf.aestronglyMeasurable).mpr hf

omit [Fintype ι] in
lemma split_affine_update (i : ι) (c : ι → ℝ) (σ u t : ℝ)
    (h : {j : ι // j ≠ i} → ℝ) :
    Function.update c i u + σ • (split i).symm (t,h) =
      (split i).symm (u+σ*t, fun j => c j.1 + σ*h j) := by
  funext j
  by_cases hj : j = i
  · subst j; simp
  · simp [hj]

lemma product_convolution_derivative {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (hb : ∀ x, |f x| ≤ 1) {σ : ℝ} (hσ : σ ≠ 0) (c : ι → ℝ) (i : ι) :
    HasDerivAt (fun u => ∫ g, f (Function.update c i u + σ • g) ∂gamma ι)
      (σ⁻¹ * ∫ g, g i * f (c + σ • g) ∂gamma ι) (c i) := by
  let Q : ℝ → ℝ := fun z => ∫ h : {j : ι // j ≠ i} → ℝ,
    f ((split i).symm (z, fun j => c j.1 + σ*h j)) ∂gamma {j : ι // j ≠ i}
  have hqm : Measurable Q := by
    apply StronglyMeasurable.measurable
    apply StronglyMeasurable.integral_prod_right
    exact (hf.comp ((split i).symm.measurable.comp (by fun_prop))).stronglyMeasurable
  have hqb (z : ℝ) : |Q z| ≤ 1 := by
    simpa [Q, ← Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const (μ := gamma {j : ι // j ≠ i})
        (ae_of_all _ fun h => (by simpa only [Real.norm_eq_abs] using (hb
          ((split i).symm (z, fun j => c j.1 + σ*h j))))))
  have hint (u : ℝ) : Integrable (fun g => f (Function.update c i u + σ • g)) (gamma ι) :=
    (integrable_const (1 : ℝ)).mono' (hf.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using hb _)
  have heq (u : ℝ) : (∫ g, f (Function.update c i u + σ • g) ∂gamma ι) =
      ∫ t, Q (u+σ*t) ∂gaussianReal 0 1 := by
    rw [integral_split i (hint u)]
    simp only [split_affine_update, Q]
  have hint0 : Integrable (fun g => f (c + σ • g)) (gamma ι) := by
    simpa using hint (c i)
  have hsint : Integrable (fun g => g i * f (c + σ • g)) (gamma ι) := by
    have hi : Integrable (fun g : ι → ℝ => g i) (gamma ι) :=
      integrable_eval ((memLp_id_gaussianReal (μ := 0) (v := 1) 1).integrable (by norm_num))
    exact hi.mul_bdd (hf.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun g => by simpa only [Real.norm_eq_abs] using hb _)
  have hscore : (∫ g, g i * f (c + σ • g) ∂gamma ι) =
      ∫ t, t * Q (c i+σ*t) ∂gaussianReal 0 1 := by
    rw [integral_split i hsint]
    apply integral_congr_ae
    filter_upwards [] with t
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with h
    simp only [split_symm_apply]
    congr 2
    simpa using split_affine_update i c σ (c i) t h
  simpa only [heq, hscore] using gaussian_convolution_derivative hqm hqb hσ (c i)

omit [DecidableEq ι] in
lemma coordinate_memLp_two (i : ι) : MemLp (fun g : ι → ℝ => g i) 2 (gamma ι) :=
  (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i)

lemma coordinate_second_moment (i j : ι) :
    (∫ g : ι → ℝ, g i * g j ∂gamma ι) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [ite_eq_left rfl]
    have hm := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
    have hs : (∫ x : ℝ, x * x ∂gaussianReal 0 1) = 1 := by
      simpa [variance_id_gaussianReal, integral_id_gaussianReal, sq] using hm.symm
    exact (integral_comp_eval (i := i) (μ := fun _ : ι => gaussianReal 0 1) (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ => x*x) (gaussianReal 0 1))).trans hs
  · rw [ite_eq_right hij]
    have hi : (fun g : ι → ℝ => g i) ⟂ᵢ[gamma ι] (fun g : ι → ℝ => g j) :=
      (iIndepFun_pi (X := fun (_ : ι) (x : ℝ) => x) (fun _ => measurable_id.aemeasurable)).indepFun hij
    simpa [gamma, integral_eval, integral_id_gaussianReal] using
      hi.integral_mul_eq_mul_integral (coordinate_memLp_two i).aestronglyMeasurable
        (coordinate_memLp_two j).aestronglyMeasurable

end FiniteProduct

lemma integral_inner_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
  simp [hfω, hgω, mul_comm]

lemma integral_bessel {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    {μ : Measure Ω} {X : ι → Ω → ℝ} (hX : ∀ i, MemLp (X i) 2 μ)
    (hXX : ∀ i j, (∫ ω, X i ω * X j ω ∂μ) = if i = j then 1 else 0)
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    (∑ i, (∫ ω, X i ω * f ω ∂μ)^2) ≤ ∫ ω, (f ω)^2 ∂μ := by
  have hon : Orthonormal ℝ (fun i => (hX i).toLp (X i)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [integral_inner_toLp]
    exact hXX i j
  have h := hon.sum_inner_products_le (s := Finset.univ) (hf.toLp f)
  have hnorm : ‖hf.toLp f‖ ^ 2 = ∫ ω, (f ω)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, integral_inner_toLp]
    simp [sq]
  simpa only [integral_inner_toLp, Real.norm_eq_abs, sq_abs, hnorm, Finset.mem_univ,
    Finset.sum_ite_irrel, ite_true] using h

lemma gaussian_score_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    (∑ i, (∫ g, g i * f g ∂gamma ι)^2) ≤ 1 := by
  have hlp : MemLp f 2 (gamma ι) := MemLp.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hb x)
  refine (integral_bessel (fun i => coordinate_memLp_two i) coordinate_second_moment hlp).trans ?_
  have hs : ∀ x, f x ^ 2 ≤ 1 := fun x => by
    have := hb x
    nlinarith [sq_abs (f x), abs_nonneg (f x)]
  simpa using integral_mono_ae (hlp.integrable_sq) (integrable_const (1 : ℝ))
    (ae_of_all _ hs)

end MinUncut.GaussianSmoothing

namespace MinUncut.Inner
open scoped BigOperators
open MeasureTheory ProbabilityTheory
abbrev F₂ := ZMod 2

variable {m n : ℕ}

abbrev Point (m n : ℕ) := Fin m → Fin n
abbrev Row (m n : ℕ) := Σ i : Fin m, ({j : Fin m // j ≠ i} → Fin n)

def face (x : Point m n) (i : Fin m) : {j : Fin m // j ≠ i} → Fin n := fun j => x j.1

def faceSum (m n : ℕ) : (Row m n → F₂) →ₗ[F₂] (Point m n → F₂) where
  toFun z x := ∑ i : Fin m, z ⟨i, face x i⟩
  map_add' z w := by funext x; simp [Finset.sum_add_distrib]
  map_smul' t z := by funext x; simp [Finset.mul_sum]

abbrev Code (m n : ℕ) := LinearMap.range (faceSum m n)

noncomputable instance codeFintype : Fintype (Code m n) := Fintype.ofFinite _
instance codeDecidableEq : DecidableEq (Code m n) := Classical.decEq _

variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]

abbrev Forms (A : Type*) {V : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] :=
  A →ᵃ[F₂] F₂

noncomputable instance formsFintype [Fintype A] : Fintype (Forms A) := by
  classical
  exact Fintype.ofInjective (fun f : Forms A => (f : A → F₂)) AffineMap.coeFn_injective

abbrev FaceArray (A : Type*) {V : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A]
    (m n : ℕ) := Row m n → Forms A

def labelCode (B : FaceArray A m n) (a : A) : Code m n :=
  ⟨faceSum m n (fun r => B r a), ⟨(fun r => B r a), rfl⟩⟩

@[simp] lemma labelCode_apply (B : FaceArray A m n) (a : A) (x : Point m n) :
    (labelCode B a : Point m n → F₂) x = ∑ i : Fin m, B ⟨i, face x i⟩ a := rfl

structure FoldedProof (A : Type*) where
  answer : (A → Bool) → Bool
  folded : ∀ P, answer (fun a => !(P a)) = !(answer P)

def bitSign (b : Bool) : ℝ := if b then 1 else -1
@[simp] lemma bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by cases b <;> norm_num [bitSign]
@[simp] lemma bitSign_abs (b : Bool) : |bitSign b| = 1 := by cases b <;> norm_num [bitSign]
@[simp] lemma bitSign_not (b : Bool) : bitSign (!b) = -bitSign b := by cases b <;> norm_num [bitSign]

noncomputable def query (u : Point m n → ℝ) (d : Code m n → ℝ) : Code m n → Bool :=
  fun z => decide (0 ≤ (Real.sqrt (n^m : ℕ))⁻¹ *
    (∑ x : Point m n, u x * BinaryFourier.sign (z.val x)) + d z)

noncomputable def pullQuery (B : FaceArray A m n) (u : Point m n → ℝ)
    (d : Code m n → ℝ) : A → Bool := fun a => query u d (labelCode B a)

noncomputable def gauss (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance gauss_probability (ι : Type*) [Fintype ι] : IsProbabilityMeasure (gauss ι) := by
  unfold gauss
  infer_instance

noncomputable def smooth (f : FoldedProof A) (B : FaceArray A m n)
    (σ η : ℝ) (c : Point m n → ℝ) : ℝ :=
  ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
    bitSign (f.answer (pullQuery B (c + σ • g) (η • l)))
      ∂gauss (Code m n) ∂gauss (Point m n)

noncomputable def gradient (f : FoldedProof A) (B : FaceArray A m n)
    (σ η : ℝ) (c : Point m n → ℝ) (x : Point m n) : ℝ :=
  Real.sqrt (n^m : ℕ) *
    deriv (fun t => smooth f B σ η (Function.update c x t)) (c x)

variable [Fintype A]

lemma measurable_query (z : Code m n) :
    Measurable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => query p.1 p.2 z) := by
  apply measurable_to_bool
  have heq : (fun p : (Point m n → ℝ) × (Code m n → ℝ) => query p.1 p.2 z) ⁻¹'
      {true} = {p | 0 ≤ (Real.sqrt (n^m : ℕ))⁻¹ *
        (∑ x : Point m n, p.1 x * BinaryFourier.sign (z.val x)) + p.2 z} := by
    ext p; simp [query]
  rw [heq]
  apply measurableSet_le measurable_const
  fun_prop

omit [Fintype A] in
lemma measurable_pullQuery (B : FaceArray A m n) :
    Measurable (fun p : (Point m n → ℝ) × (Code m n → ℝ) => pullQuery B p.1 p.2) := by
  apply Measurable.of_eval
  intro a
  exact measurable_query (labelCode B a)

lemma measurable_answer (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ) :
    Measurable (fun p : (Point m n → ℝ) × (Code m n → ℝ) =>
      bitSign (f.answer (pullQuery B p.1 (η • p.2)))) := by
  exact (measurable_of_finite bitSign).comp ((measurable_of_finite f.answer).comp
    ((measurable_pullQuery B).comp (by fun_prop : Measurable
      (fun pair : (Point m n → ℝ) × (Code m n → ℝ) => (pair.1, η • pair.2)))))

noncomputable def tableSmooth (f : FoldedProof A) (B : FaceArray A m n)
    (η : ℝ) (u : Point m n → ℝ) : ℝ :=
  ∫ l : Code m n → ℝ, bitSign (f.answer (pullQuery B u (η • l))) ∂gauss (Code m n)

lemma measurable_tableSmooth (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ) :
    Measurable (tableSmooth f B η) := by
  exact ((measurable_answer f B η).stronglyMeasurable.integral_prod_right).measurable

omit [Fintype A] in
lemma tableSmooth_abs_le (f : FoldedProof A) (B : FaceArray A m n) (η : ℝ)
    (u : Point m n → ℝ) : |tableSmooth f B η u| ≤ 1 := by
  simpa [tableSmooth, ← Real.norm_eq_abs] using
    (norm_integral_le_of_norm_le_const (μ := gauss (Code m n))
      (ae_of_all _ fun l => (by simp only [Real.norm_eq_abs, bitSign_abs, le_refl] :
        ‖bitSign (f.answer (pullQuery B u (η • l)))‖ ≤ 1)))

lemma smooth_coordinate_derivative (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    HasDerivAt (fun t => smooth f B σ η (Function.update c x t))
      (σ⁻¹ * ∫ g : Point m n → ℝ, g x * tableSmooth f B η (c + σ • g)
        ∂gauss (Point m n)) (c x) := by
  exact GaussianSmoothing.product_convolution_derivative
    (measurable_tableSmooth f B η) (tableSmooth_abs_le f B η) hσ c x

lemma gradient_convolution (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    gradient f B σ η c x = Real.sqrt (n^m : ℕ) / σ *
      ∫ g : Point m n → ℝ, ∫ l : Code m n → ℝ,
        g x * bitSign (f.answer (pullQuery B (c + σ • g) (η • l)))
          ∂gauss (Code m n) ∂gauss (Point m n) := by
  rw [gradient, (smooth_coordinate_derivative f B hσ η c x).deriv]
  simp only [tableSmooth, integral_const_mul, div_eq_mul_inv, mul_assoc]

noncomputable def spatialEnergy (v : Point m n → ℝ) : ℝ :=
  ((n^m : ℕ) : ℝ)⁻¹ * ∑ x : Point m n, v x ^ 2

lemma gradient_score (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    gradient f B σ η c x = Real.sqrt (n^m : ℕ) / σ *
      ∫ g : Point m n → ℝ, g x * tableSmooth f B η (c + σ • g) ∂gauss (Point m n) := by
  rw [gradient, (smooth_coordinate_derivative f B hσ η c x).deriv]
  ring

lemma gradient_spatialEnergy_le (f : FoldedProof A) (B : FaceArray A m n)
    (hn : 0 < n) {σ : ℝ} (hσ : σ ≠ 0) (η : ℝ) (c : Point m n → ℝ) :
    spatialEnergy (gradient f B σ η c) ≤ σ⁻¹ ^ 2 := by
  have hN : (0 : ℝ) < (n^m : ℕ) := by exact_mod_cast pow_pos hn m
  let S : Point m n → ℝ := fun x => ∫ g : Point m n → ℝ,
    g x * tableSmooth f B η (c + σ • g) ∂gauss (Point m n)
  have hS : (∑ x, S x ^ 2) ≤ 1 :=
    GaussianSmoothing.gaussian_score_energy
      ((measurable_tableSmooth f B η).comp (by fun_prop))
      (fun _ => tableSmooth_abs_le f B η _)
  have hE : spatialEnergy (gradient f B σ η c) = σ⁻¹^2 * ∑ x, S x ^ 2 := by
    simp only [spatialEnergy, gradient_score f B hσ, mul_pow, div_pow,
      Real.sq_sqrt hN.le, ← Finset.mul_sum]
    dsimp [S]
    field_simp
  rw [hE]
  simpa using mul_le_mul_of_nonneg_left hS (sq_nonneg σ⁻¹)

lemma gradient_abs_le (f : FoldedProof A) (B : FaceArray A m n)
    {σ : ℝ} (hσ : 0 < σ) (η : ℝ) (c : Point m n → ℝ) (x : Point m n) :
    |gradient f B σ η c x| ≤ Real.sqrt (n^m : ℕ) / σ := by
  let S : Point m n → ℝ := fun y => ∫ g : Point m n → ℝ,
    g y * tableSmooth f B η (c + σ • g) ∂gauss (Point m n)
  have hS : (∑ y, S y ^ 2) ≤ 1 :=
    GaussianSmoothing.gaussian_score_energy
      ((measurable_tableSmooth f B η).comp (by fun_prop))
      (fun _ => tableSmooth_abs_le f B η _)
  have hsx : S x ^ 2 ≤ 1 := le_trans
    (Finset.single_le_sum (fun y _ => sq_nonneg (S y)) (Finset.mem_univ x)) hS
  have hx : |S x| ≤ 1 := by nlinarith [sq_abs (S x), abs_nonneg (S x)]
  rw [gradient_score f B hσ.ne', abs_mul, abs_of_nonneg
    (div_nonneg (Real.sqrt_nonneg _) hσ.le)]
  simpa using mul_le_mul_of_nonneg_left hx
    (div_nonneg (Real.sqrt_nonneg (n^m : ℕ)) hσ.le)

end MinUncut.Inner

open scoped BigOperators

end

end OAI
