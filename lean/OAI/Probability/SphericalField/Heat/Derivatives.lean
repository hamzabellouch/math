import Mathlib
import OAI.Probability.SphericalField.Heat.Logarithm

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma inv_bcf_bound {g : ℝ →ᵇ ℝ} {c : ℝ} (hc : 0 < c) (hg : ∀ x, c ≤ g x) (x : ℝ) :
    |(g x)⁻¹| ≤ c⁻¹ := by
  rw [abs_of_pos (inv_pos.mpr (hc.trans_le (hg x)))]
  exact inv_anti₀ hc (hg x)

def invBCF (g : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => (g x)⁻¹, g.continuous.inv₀ (fun x => (hc.trans_le (hg x)).ne')⟩
    (2*c⁻¹) (by
      intro x y; change |(g x)⁻¹ - (g y)⁻¹| ≤ 2*c⁻¹
      exact (abs_sub _ _).trans (by linarith [inv_bcf_bound hc hg x, inv_bcf_bound hc hg y]))

@[simp] lemma invBCF_apply (g : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x) (x : ℝ) :
    invBCF g c hc hg x = (g x)⁻¹ := rfl

lemma invBCF_norm_le (g : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x) :
    ‖invBCF g c hc hg‖ ≤ c⁻¹ := by
  rw [BoundedContinuousFunction.norm_le (inv_nonneg.mpr hc.le)]
  intro x; exact inv_bcf_bound hc hg x

lemma invBCF_hasDerivAt (g g' : ℝ →ᵇ ℝ) (c : ℝ) (hc : 0 < c) (hg : ∀ x, c ≤ g x)
    (hder : ∀ x, HasDerivAt (g : ℝ → ℝ) (g' x) x) (x : ℝ) :
    HasDerivAt (invBCF g c hc hg : ℝ → ℝ) (- g' x * (invBCF g c hc hg x)^2) x := by
  convert! (hder x).inv (hc.trans_le (hg x)).ne' using 1
  simp only [invBCF_apply, div_eq_mul_inv, inv_pow]

def Jet3.heatLogPos (s d : ℝ≥0) (hd : d ≠ 0) (g : Jet3) : Jet3 :=
  let A := (g.exp d).gaussianAverage s
  let c := Real.exp (-d * ‖g.f‖)
  let hc : 0 < c := Real.exp_pos _
  let hA : ∀ x, c ≤ A.f x := fun x => (gaussianAverage_exp_bounds s d d.coe_nonneg g.f x).1
  let J := invBCF A.f c hc hA
  { f := heatLogBCF s d g.f
    d1 := (d : ℝ)⁻¹ • (A.d1 * J)
    d2 := (d : ℝ)⁻¹ • (A.d2 * J - A.d1^2 * J^2)
    d3 := (d : ℝ)⁻¹ • (A.d3 * J - (3 : ℝ) • (A.d1*A.d2*J^2) + (2 : ℝ) • (A.d1^3*J^3))
    has1 x := by
      have hh := ((A.has1 x).log (hc.trans_le (hA x)).ne').const_mul (d : ℝ)⁻¹
      convert! hh using 1
      · ext y
        simp only [heatLogBCF_coe, heatLog, hd, ↓reduceIte]
        rfl
    has2 x := by
      have hi := invBCF_hasDerivAt A.f A.d1 c hc hA A.has1 x
      have hh := ((A.has2 x).mul hi).const_mul (d : ℝ)⁻¹
      convert! hh using 1
      dsimp only [BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_mul,
        BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_pow,
        Pi.smul_apply, smul_eq_mul, Pi.mul_apply, Pi.sub_apply, Pi.pow_apply]
      ring
    has3 x := by
      have hi := invBCF_hasDerivAt A.f A.d1 c hc hA A.has1 x
      have hh := (((A.has3 x).mul hi).sub (((A.has2 x).pow 2).mul (hi.pow 2))).const_mul (d : ℝ)⁻¹
      convert! hh using 1
      dsimp only [BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_mul,
        BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_add,
        BoundedContinuousFunction.coe_pow, Pi.smul_apply, smul_eq_mul, Pi.mul_apply,
        Pi.sub_apply, Pi.add_apply, Pi.pow_apply]
      ring }

def Jet3.heatLog (s d : ℝ≥0) (g : Jet3) : Jet3 :=
  if hd : d = 0 then g.gaussianAverage s else g.heatLogPos s d hd

lemma Jet3.heatLog_f (s d : ℝ≥0) (g : Jet3) : (g.heatLog s d).f = heatLogBCF s d g.f := by
  unfold Jet3.heatLog
  split_ifs with hd
  · subst d; ext x; simp [Jet3.gaussianAverage, SphericalPerceptron.heatLog]
  · rfl

lemma gaussianAverage_jet_error (s : ℝ≥0) (g : Jet3) (x : ℝ) :
    |gaussianAverage s g.f x - g.f x - (s : ℝ)/2 * g.d2 x| ≤
      ‖g.d3‖/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := by
  have hh := gaussian_taylor_mean_bound (P := gaussianReal 0 s) g.f g.contDiff
    ‖g.d1‖ ‖g.d2‖ ‖g.d3‖
    (fun y => by rw [g.deriv_eq]; exact g.d1.norm_coe_le_norm y)
    (fun y => by rw [g.deriv2_eq]; exact g.d2.norm_coe_le_norm y)
    (fun y => by rw [g.deriv3_eq]; exact g.d3.norm_coe_le_norm y)
    (X := fun _ : ℝ => x) aemeasurable_const (Z := id) HasLaw.id (indepFun_const_left _ _)
  simpa only [integral_const, probReal_univ, smul_eq_mul, one_mul, g.deriv2_eq, gaussianAverage, id_eq] using hh

lemma log_linear_error_le {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |Real.log b - Real.log a - (b-a)/a| ≤ (b-a)^2 / c^2 := by
  have ha0 := hc.trans_le ha
  have hb0 := hc.trans_le hb
  have hu := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  have hl := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
  rw [Real.log_div hb0.ne' ha0.ne'] at hu
  rw [Real.log_div ha0.ne' hb0.ne'] at hl
  have heq : b/a-1 = (b-a)/a := by field_simp
  rw [heq] at hu
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  have hlin : -(Real.log b - Real.log a - (b-a)/a) ≤ (b-a)^2/(a*b) := by
    have he : (b-a)/a + (a/b-1) = (b-a)^2/(a*b) := by field_simp; ring
    linarith
  exact hlin.trans (div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hc)
    (by nlinarith [mul_le_mul ha hb hc.le ha0.le]))

lemma gaussianAverage_ge_const (s : ℝ≥0) (f : ℝ →ᵇ ℝ) {c : ℝ}
    (hc : ∀ x, c ≤ f x) (x : ℝ) : c ≤ gaussianAverage s f x := by
  have hh := integral_mono (integrable_const c) (gaussianAverage_integrable s f x) (fun z => hc (x+z))
  simpa only [gaussianAverage, integral_const, probReal_univ, smul_eq_mul, one_mul] using hh

lemma log_gaussian_generator_error (g : Jet3) (c : ℝ) (hc : 0 < c)
    (hg : ∀ x, c ≤ g.f x) (C₂ C₃ : ℝ≥0) (h₂ : ‖g.d2‖ ≤ C₂) (h₃ : ‖g.d3‖ ≤ C₃)
    (s : ℝ≥0) (hs : s ≤ 1) (x : ℝ) :
    |Real.log (gaussianAverage s g.f x) - Real.log (g.f x) -
      (s : ℝ)/2 * g.d2 x / g.f x| ≤
      (((C₂ : ℝ)/2 + (C₃ : ℝ)/6*(∫ z : ℝ, |z|^3 ∂gaussianReal 0 1))^2/c^2 +
        ((C₃ : ℝ)/6*(∫ z : ℝ, |z|^3 ∂gaussianReal 0 1))/c) * (s : ℝ) * Real.sqrt s := by
  let A := gaussianAverage s g.f x
  let a := g.f x
  let K := (C₃ : ℝ)/6 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1
  let D := (C₂ : ℝ)/2 + K
  have ha := hg x
  have hA := gaussianAverage_ge_const s g.f hg x
  have hM : 0 ≤ ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := integral_nonneg (fun z => by positivity)
  have hK : 0 ≤ K := by positivity
  have hD : 0 ≤ D := by positivity
  have hs0 : 0 ≤ (s : ℝ) := s.coe_nonneg
  have hs1 : (s : ℝ) ≤ 1 := hs
  have hr0 := Real.sqrt_nonneg (s : ℝ)
  have hr1 : Real.sqrt (s : ℝ) ≤ 1 := (Real.sqrt_le_one).mpr hs1
  have hrsq := Real.sq_sqrt hs0
  have hsr : (s : ℝ) ≤ Real.sqrt (s : ℝ) := by nlinarith
  have hrcube : (Real.sqrt (s : ℝ))^3 = (s : ℝ) * Real.sqrt (s : ℝ) := by nlinarith
  have herr : |A-a-(s : ℝ)/2*g.d2 x| ≤ K * (s : ℝ) * Real.sqrt s := by
    calc
      _ ≤ ‖g.d3‖/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := gaussianAverage_jet_error s g x
      _ ≤ (C₃ : ℝ)/6 * (Real.sqrt s)^3 * ∫ z : ℝ, |z|^3 ∂gaussianReal 0 1 := by gcongr
      _ = _ := by rw [hrcube]; unfold K; ring
  have hdx : |g.d2 x| ≤ C₂ := (g.d2.norm_coe_le_norm x).trans h₂
  have hdelta : |A-a| ≤ D * (s : ℝ) := by
    have habs := abs_add_le (A-a-(s : ℝ)/2*g.d2 x) ((s : ℝ)/2*g.d2 x)
    rw [sub_add_cancel] at habs
    have hterm : |(s : ℝ)/2*g.d2 x| ≤ (s : ℝ)/2*C₂ := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ s/2)]
      exact mul_le_mul_of_nonneg_left hdx (by positivity)
    have hkr := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hK hs0)
    dsimp [D]; nlinarith
  have hquad : (A-a)^2/c^2 ≤ (D^2/c^2) * (s : ℝ) * Real.sqrt s := by
    have hdsq : (A-a)^2 ≤ (D*(s : ℝ))^2 := by
      have hh := (sq_le_sq₀ (abs_nonneg (A-a)) (mul_nonneg hD hs0)).mpr hdelta
      simpa only [sq_abs] using hh
    calc
      _ ≤ (D*(s : ℝ))^2/c^2 := div_le_div_of_nonneg_right hdsq (sq_nonneg c)
      _ = D^2/c^2 * (s : ℝ)^2 := by ring
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsr hs0)
          (show 0 ≤ D^2/c^2 by positivity)
        nlinarith only [hh]
  have hrem : |A-a-(s : ℝ)/2*g.d2 x|/a ≤ (K/c) * (s : ℝ) * Real.sqrt s := by
    calc
      _ ≤ (K*(s : ℝ)*Real.sqrt s)/c := div_le_div₀ (by positivity) herr hc ha
      _ = _ := by ring
  have hlog := log_linear_error_le hc ha hA
  change |Real.log A - Real.log a - (s : ℝ)/2*g.d2 x/a| ≤ _
  calc
    _ = |(Real.log A-Real.log a-(A-a)/a) + (A-a-(s : ℝ)/2*g.d2 x)/a| := by congr 1; ring
    _ ≤ |Real.log A-Real.log a-(A-a)/a| + |(A-a-(s : ℝ)/2*g.d2 x)/a| := abs_add_le _ _
    _ = |Real.log A-Real.log a-(A-a)/a| + |A-a-(s : ℝ)/2*g.d2 x|/a := by
      rw [abs_div, abs_of_pos (hc.trans_le ha)]
    _ ≤ (D^2/c^2) * (s : ℝ) * Real.sqrt s + (K/c)*(s : ℝ)*Real.sqrt s :=
      add_le_add (hlog.trans hquad) hrem
    _ = _ := by dsimp [D,K]; ring

end SphericalPerceptron
end
end

end OAI
