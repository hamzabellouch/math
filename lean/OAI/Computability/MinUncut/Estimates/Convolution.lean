import Mathlib
import OAI.Computability.MinUncut.Estimates.F2
import OAI.Computability.MinUncut.Analysis.Gradient

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma noise_derivative (ρ s : ℝ) (hs : s ≠ 0) {Q : (ι → ℝ) → ℝ}
    (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) (x : ι → ℝ) (i : ι) :
    HasDerivAt (fun t => noise ρ s Q (Function.update x i t)) (gradient ρ s Q i x) (x i) := by
  have hd := GaussianSmoothing.product_convolution_derivative hQ hb hs (ρ • x) i
  have hm : HasDerivAt (fun t : ℝ => ρ*t) ρ (x i) := by
    simpa only [mul_one, id_eq] using (hasDerivAt_id (x i)).const_mul ρ
  have hc := hd.comp (x i) hm
  convert! hc using 1
  · funext t
    unfold noise
    congr 1
    funext g
    congr 2
    ext j
    by_cases hj : j = i
    · subst j; simp; rfl
    · simp [Function.update_of_ne hj]
  · dsimp [gradient, score]
    ring

def convolution (σ : ℝ) (Q : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∫ g, Q (x + σ • g) ∂γpi ι

def convolutionGradient (σ : ℝ) (Q : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) : ℝ :=
  σ⁻¹ * ∫ g, g i * Q (x + σ • g) ∂γpi ι

lemma convolution_derivative {σ : ℝ} (hσ : σ ≠ 0) {Q : (ι → ℝ) → ℝ}
    (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) (x : ι → ℝ) (i : ι) :
    HasDerivAt (fun t => convolution σ Q (Function.update x i t))
      (convolutionGradient σ Q i x) (x i) :=
  GaussianSmoothing.product_convolution_derivative hQ hb hσ x i

omit [DecidableEq ι] in
lemma convolution_as_noise {ρ σ : ℝ} (hρ : ρ ≠ 0) (Q : (ι → ℝ) → ℝ) :
    convolution σ Q = noise ρ (σ*ρ) (fun v => Q (ρ⁻¹ • v)) := by
  funext x
  unfold convolution noise
  congr 1
  funext g
  congr 1
  ext i
  dsimp
  field_simp

omit [DecidableEq ι] in
lemma convolutionGradient_as_noise {ρ σ : ℝ} (hρ : ρ ≠ 0) (hσ : σ ≠ 0)
    (Q : (ι → ℝ) → ℝ) (i : ι) :
    convolutionGradient σ Q i = gradient ρ (σ*ρ) (fun v => Q (ρ⁻¹ • v)) i := by
  funext x
  unfold convolutionGradient gradient score
  have hc : ρ/(σ*ρ) = σ⁻¹ := by field_simp
  rw [hc]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with g
  congr 2
  ext j
  dsimp
  field_simp

lemma convolution_poincare {ρ σ : ℝ} (hρ : ρ ≠ 0) (hσ : σ ≠ 0)
    (h : ρ^2+(σ*ρ)^2=1) {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q)
    (hb : ∀ x, |Q x| ≤ 1) (hmean : (∫ x, convolution σ Q x ∂γpi ι) = 0) :
    (∫ x, (convolution σ Q x)^2 ∂γpi ι) ≤
      ∑ i, ∫ x, (convolutionGradient σ Q i x)^2 ∂γpi ι := by
  simp_rw [convolution_as_noise hρ, convolutionGradient_as_noise hρ hσ] at *
  exact poincare ρ (σ*ρ) h (mul_ne_zero hσ hρ) (hQ.comp (by fun_prop))
    (fun x => hb _) hmean

lemma convolution_gradient_tail {ρ σ ε : ℝ} (hρ : ρ ≠ 0) (hσ : σ ≠ 0)
    (h : ρ^2+(σ*ρ)^2=1) (hε : 0 ≤ ε) (d : ℕ)
    (hd : ∀ k : ℕ, d+2 ≤ k → (k:ℝ)*ρ^(2*k) ≤ ε)
    {Q : (ι → ℝ) → ℝ} (hQ : Measurable Q) (hb : ∀ x, |Q x| ≤ 1) :
    (∑ i, ∫ x, (convolutionGradient σ Q i x -
      project d (convolutionGradient σ Q i) x)^2 ∂γpi ι) ≤ ε := by
  simp_rw [convolutionGradient_as_noise hρ hσ]
  exact gradient_tail_le ρ (σ*ρ) h (mul_ne_zero hσ hρ) (hQ.comp (by fun_prop))
    (fun x => hb _) d hε hd

end MinUncut.GaussianHermite

namespace MinUncut.RowNoise
open BinaryFourier
local instance convolutionDualFintype {U : Type*} [AddCommGroup U] [Module F₂ U] [Fintype U] :
    Fintype (Module.Dual F₂ U) := BinaryFourier.dualFintype
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

lemma expect_prod {A : R → Type*} [∀ r, Fintype (A r)] (f : ∀ r, A r → ℝ) :
    (𝔼 x : ∀ r, A r, ∏ r, f r (x r)) = ∏ r, 𝔼 a, f r a := by
  simp only [Fintype.expect_eq_sum_div_card, Fintype.card_pi]
  rw [← Fintype.prod_sum, Nat.cast_prod, Finset.prod_div_distrib]

def rowDensity (a : ℝ) (b c : W) : ℝ :=
  (1-a)*(if c=b then (Fintype.card W : ℝ) else 0) + a

omit [Module F₂ W] in
lemma rowDensity_mean (a : ℝ) (b : W) : (𝔼 c, rowDensity a b c) = 1 := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [rowDensity, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card W : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring

omit [AddCommGroup W] [Module F₂ W] in
lemma rowDensity_symmetric (a : ℝ) (b c : W) : rowDensity a b c = rowDensity a c b := by
  simp [rowDensity, eq_comm]

omit [Module F₂ W] in
lemma rowDensity_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (b c : W) :
    0 ≤ rowDensity a b c := by
  unfold rowDensity
  split_ifs <;> positivity

def density (a : ℝ) (B C : R → W) : ℝ := ∏ r, rowDensity a (B r) (C r)

omit [Module F₂ W] in
lemma density_mean (a : ℝ) (B : R → W) : (𝔼 C, density a B C) = 1 := by
  simp only [density, expect_prod, rowDensity_mean, Finset.prod_const_one]

omit [DecidableEq R] [AddCommGroup W] [Module F₂ W] in
lemma density_symmetric (a : ℝ) (B C : R → W) : density a B C = density a C B := by
  simp only [density, rowDensity_symmetric a]

omit [DecidableEq R] [Module F₂ W] in
lemma density_nonneg {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (B C : R → W) :
    0 ≤ density a B C := Finset.prod_nonneg (fun _ _ => rowDensity_nonneg ha ha1 _ _)

def frequency (α : Module.Dual F₂ (R → W)) (r : R) : Module.Dual F₂ W :=
  α.comp (LinearMap.single F₂ (fun _ : R => W) r)

omit [Fintype W] [DecidableEq W] in
lemma dual_apply (α : Module.Dual F₂ (R → W)) (B : R → W) :
    α B = ∑ r, frequency α r (B r) := by
  change α B = ∑ r, α (Pi.single r (B r))
  rw [← map_sum]
  congr 1
  ext r
  simp

lemma sign_sum {S : Type*} (s : Finset S) (f : S → F₂) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, sign_add, ih]

omit [Fintype W] [DecidableEq W] in
lemma character_product (α : Module.Dual F₂ (R → W)) (B : R → W) :
    character α B = ∏ r, character (frequency α r) (B r) := by
  simp only [character, dual_apply, sign_sum]

def mask (α : Module.Dual F₂ (R → W)) : Finset R :=
  Finset.univ.filter (fun r => frequency α r ≠ 0)

def degree (α : Module.Dual F₂ (R → W)) : ℕ := (mask α).card

lemma row_character_eigen (a : ℝ) (b : W) (α : Module.Dual F₂ W) :
    (𝔼 c, rowDensity a b c * character α c) =
      (if α=0 then 1 else 1-a)*character α b := by
  unfold rowDensity
  simp only [add_mul, Finset.expect_add_distrib, mul_assoc, ← Finset.mul_expect]
  have hh : (𝔼 c, (if c=b then (Fintype.card W : ℝ) else 0) * character α c) =
      character α b := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  rw [hh, character_mean]
  split_ifs with hα
  · subst α; simp
  · ring

def noise (a : ℝ) (f : (R → W) → ℝ) (B : R → W) : ℝ :=
  𝔼 C, density a B C * f C

lemma noise_character (a : ℝ) (α : Module.Dual F₂ (R → W)) (B : R → W) :
    noise a (character α) B = (1-a)^degree α*character α B := by
  simp only [noise, density, character_product]
  simp_rw [← Finset.prod_mul_distrib]
  rw [expect_prod (fun r c => rowDensity a (B r) c * character (frequency α r) c)]
  simp only [row_character_eigen, Finset.prod_mul_distrib]
  congr 1
  simp only [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  rfl

lemma noise_expansion (a : ℝ) (f : (R → W) → ℝ) (B : R → W) :
    noise a f B = ∑ α, coefficient f α * (1-a)^degree α * character α B := by
  unfold noise
  simp_rw [← inversion f, Finset.mul_sum, Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  have he : (𝔼 C, density a B C * (coefficient f α * character α C)) =
      coefficient f α * noise a (character α) B := by
    unfold noise
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro C _
    ring
  rw [he, noise_character]
  ring

lemma correlation (a : ℝ) (f : (R → W) → ℝ) :
    (𝔼 B, f B * noise a f B) = ∑ α, (1-a)^degree α*(coefficient f α)^2 := by
  simp_rw [noise_expansion, Finset.mul_sum, Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  calc
    _ = ((1-a)^degree α*coefficient f α) * (𝔼 B, f B * character α B) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro B _
      ring
    _ = _ := by rw [← coefficient]; ring

omit [Module F₂ W] in
lemma stationary (a : ℝ) (f : (R → W) → ℝ) : (𝔼 B, noise a f B) = 𝔼 B, f B := by
  unfold noise
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro C _
  simp_rw [density_symmetric a _ C, ← Finset.expect_mul, density_mean, one_mul]

lemma dirichlet (a : ℝ) (f : (R → W) → ℝ) :
    (𝔼 B, 𝔼 C, density a B C * (f B - f C)^2) =
      2 * ∑ α, (1-(1-a)^degree α)*(coefficient f α)^2 := by
  have he (B C : R → W) : density a B C*(f B-f C)^2 =
      (f B)^2*density a B C + density a B C*(f C)^2 - 2*f B*(density a B C*f C) := by ring
  simp_rw [he, Finset.expect_sub_distrib, Finset.expect_add_distrib,
    ← Finset.mul_expect, density_mean, mul_one]
  have ht : (𝔼 B, 2*f B*(𝔼 C, density a B C*f C)) =
      2*(𝔼 B, f B*noise a f B) := by
    simp only [noise, Finset.mul_expect, mul_assoc]
  rw [ht]
  change (𝔼 B, f B^2)+(𝔼 B, noise a (fun C => (f C)^2) B) -
    2*(𝔼 B, f B*noise a f B) = _
  rw [stationary, correlation, ← parseval]
  simp_rw [sub_mul, one_mul, Finset.sum_sub_distrib]
  ring

def project (D : ℕ) (f : (R → W) → ℝ) (B : R → W) : ℝ :=
  ∑ α ∈ Finset.univ.filter (fun α => degree α ≤ D), coefficient f α * character α B

omit [DecidableEq W] in
lemma coefficient_project (D : ℕ) (f : (R → W) → ℝ) (β : Module.Dual F₂ (R → W)) :
    coefficient (project D f) β = if degree β ≤ D then coefficient f β else 0 := by
  unfold coefficient project
  simp_rw [Finset.sum_mul, Finset.expect_sum_comm, mul_assoc, ← Finset.mul_expect,
    character_orthogonality]
  simp [Finset.mem_filter, coefficient]

omit [DecidableEq W] in
lemma coefficient_residual (D : ℕ) (f : (R → W) → ℝ) (β : Module.Dual F₂ (R → W)) :
    coefficient (fun B => f B-project D f B) β =
      if degree β ≤ D then 0 else coefficient f β := by
  have he : coefficient (fun B => f B-project D f B) β =
      coefficient f β - coefficient (project D f) β := by
    simp only [coefficient, sub_mul, Finset.expect_sub_distrib]
  rw [he, coefficient_project]
  split_ifs <;> ring

omit [DecidableEq W] in
lemma residual_energy (D : ℕ) (f : (R → W) → ℝ) :
    (𝔼 B, (f B-project D f B)^2) =
      ∑ α, if D < degree α then (coefficient f α)^2 else 0 := by
  rw [← parseval]
  apply Finset.sum_congr rfl
  intro α _
  rw [coefficient_residual]
  split_ifs <;> simp_all
  omega

lemma geometric_bernoulli {a : ℝ} (_ha : 0 ≤ a) (ha1 : a ≤ 1) (k : ℕ) :
    (1-a)^k*(1+(k:ℝ)*a) ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 0 ≤ (1-a)^k := pow_nonneg (by linarith) _
    have hh : (1-a)*(1+((k:ℝ)+1)*a) ≤ 1+(k:ℝ)*a := by
      nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (k:ℝ)+1) (sq_nonneg a)]
    calc
      _ = (1-a)^k*((1-a)*(1+((k:ℝ)+1)*a)) := by rw [pow_succ]; push_cast; ring
      _ ≤ (1-a)^k*(1+(k:ℝ)*a) := mul_le_mul_of_nonneg_left hh hp
      _ ≤ 1 := ih

lemma spectral_weight_ge_one {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (k : ℕ) (hk : 1 ≤ (k:ℝ)*a) : 1 ≤ 2*(1-(1-a)^k) := by
  have hp := pow_nonneg (by linarith : 0 ≤ 1-a) k
  have hb := geometric_bernoulli ha ha1 k
  nlinarith [mul_nonneg hp (sub_nonneg.mpr hk)]

lemma row_tail_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (D : ℕ)
    (hD : ∀ k : ℕ, D < k → 1 ≤ (k:ℝ)*a) (f : (R → W) → ℝ) :
    (𝔼 B, (f B-project D f B)^2) ≤
      𝔼 B, 𝔼 C, density a B C*(f B-f C)^2 := by
  rw [residual_energy, dirichlet, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α _
  by_cases hd : D < degree α
  · rw [ite_eq_left hd, ← mul_assoc]
    simpa using mul_le_mul_of_nonneg_right
      (spectral_weight_ge_one ha ha1 (degree α) (hD _ hd))
      (sq_nonneg (coefficient f α))
  · rw [ite_eq_right hd]
    have hp : (1-a)^degree α ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    positivity

end MinUncut.RowNoise

end

end OAI
