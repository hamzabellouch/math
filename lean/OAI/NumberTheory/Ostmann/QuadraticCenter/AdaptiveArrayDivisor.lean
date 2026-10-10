import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArrayContinuity
import OAI.NumberTheory.Ostmann.QuadraticCenter.PositiveFrequencyDivisor

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def adaptiveDivisorAmplitude (d : ℕ) (A : ∀ p : ℕ, Finset (ZMod p))
    (mInv : ℤ) (s v : ℕ) : ℕ → ℂ :=
  letI : ∀ p : d.primeFactors, NeZero p.val := fun p => ⟨(divisor_coordinate_prime d p).ne_zero⟩
  letI : NeZero (∏ p : d.primeFactors, p.val) := ⟨divisor_coordinates_product_ne_zero d⟩
  centeredQuadraticAmplitude (fun p : d.primeFactors => p.val) (divisor_coordinates_coprime d)
    (fun p => A p.val) (mInv : ZMod (∏ p : d.primeFactors, p.val)) s v

theorem adaptiveDivisorAmplitude_norm {d : ℕ} (hd : Squarefree d)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℤ) (s v w : ℕ) :
    ‖adaptiveDivisorAmplitude d A mInv s v w‖  ≤  Real.sqrt (d:ℝ) := by
  let : ∀ p : d.primeFactors, NeZero p.val := fun p => ⟨(divisor_coordinate_prime d p).ne_zero⟩
  let : NeZero (∏ p : d.primeFactors, p.val) := ⟨divisor_coordinates_product_ne_zero d⟩
  have hh := norm_centeredProductTransform_le_sqrt
    (fun p : d.primeFactors => p.val) (divisor_coordinates_coprime d)
    (fun p => A p.val)
    (-((s*v*w^2:ℕ):ZMod (∏ p : d.primeFactors,p.val)) * (mInv:ZMod (∏ p : d.primeFactors,p.val)))
  change ‖adaptiveDivisorAmplitude d A mInv s v w‖  ≤ 
    Real.sqrt ((∏ p : d.primeFactors,p.val : ℕ):ℝ) at hh
  simpa only [divisor_coordinates_product hd] using hh

theorem divisorQuadraticSumP_eq_normalized {d : ℕ} (hd : Squarefree d)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℤ) (s v P : ℕ) (R h θ : ℝ) :
    divisorQuadraticSumP d A mInv s v P R h θ =
      normalizedSmoothQuadraticSum P (Real.sqrt (R/((s:ℝ)*v/d)))
        (adaptiveDivisorAmplitude d A mInv s v) ((h+θ)*((s:ℝ)*v/d)) := by
  unfold divisorQuadraticSumP centeredQuadraticSum
  congr 1  <;> rw [divisor_coordinates_product hd]

theorem divisorQuadraticSumP_norm_le {d s v : ℕ} (hd : Squarefree d)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℤ) (hs : 0 < s) (hv : 0 < v)
    (P : ℕ) {R : ℝ} (hR : 0 < R) (h θ : ℝ) :
    ‖divisorQuadraticSumP d A mInv s v P R h θ‖  ≤  Real.sqrt (d:ℝ)*cutoffFourierBound/P := by
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd.ne_zero.bot_lt
  rw [divisorQuadraticSumP_eq_normalized hd]
  apply normalizedSmoothQuadraticSum_bound (by positivity) (Real.sqrt_nonneg _) _ _
  exact fun w _ => adaptiveDivisorAmplitude_norm hd A mInv s v w

theorem adaptive_frequency_bounds {Z d s v : ℕ} (hZ : 1 ≤ Z) (hd : 0 < d)
    (hs : 0 < s) (hv : 0 < v) (hdZ : d ≤ Z) (hvZ : v ≤ Z) (hsZ : s ≤ Z^14) :
    0 < (s:ℝ)*v/d ∧ 1 ≤ (Z:ℝ)*((s:ℝ)*v/d) ∧ (s:ℝ)*v/d ≤ (Z:ℝ)^16 := by
  have hdr : (1:ℝ) ≤ d := by exact_mod_cast hd
  have hsr : (1:ℝ) ≤ s := by exact_mod_cast hs
  have hvr : (1:ℝ) ≤ v := by exact_mod_cast hv
  have hZr : (1:ℝ) ≤ Z := by exact_mod_cast hZ
  have hdZr : (d:ℝ) ≤ Z := by exact_mod_cast hdZ
  have hvZr : (v:ℝ) ≤ Z := by exact_mod_cast hvZ
  have hsZr : (s:ℝ) ≤ (Z:ℝ)^14 := by exact_mod_cast hsZ
  refine ⟨by positivity,?_,?_⟩
  · rw [←mul_div_assoc]
    apply (le_div_iff₀ (by linarith : (0:ℝ) < d)).mpr
    nlinarith [mul_le_mul hsr hvr (by norm_num : (0:ℝ) ≤ 1) (by positivity : (0:ℝ) ≤ s)]
  · calc
      _  ≤  (s:ℝ)*v := div_le_self (by positivity) hdr
      _  ≤  (Z:ℝ)^14*Z := by gcongr
      _ = (Z:ℝ)^15 := by ring
      _  ≤  (Z:ℝ)^16 := pow_le_pow_right₀ hZr (by omega)

theorem divisorQuadraticSumP_grid_error {Z d s v : ℕ} (hZ : 1 ≤ Z)
    (hd : Squarefree d) (hs : 0 < s) (hv : 0 < v)
    (hdZ : d ≤ Z) (hvZ : v ≤ Z) (hsZ : s ≤ Z^14)
    (A : ∀ p : ℕ, Finset (ZMod p)) (mInv : ℤ) (P : ℕ)
    {R R' θ θ' : ℝ} (hR : 1 ≤ R) (hR' : 1 ≤ R')
    (hRB : R ≤ (2*Z^13:ℕ)) (hRB' : R' ≤ (2*Z^13:ℕ)) (h : ℝ)
    (ht : |θ-θ'| ≤ 1/(Z^200:ℕ)) (hr : |R-R'| ≤ 1/(Z^200:ℕ)) :
    ‖divisorQuadraticSumP d A mInv s v P R h θ -
      divisorQuadraticSumP d A mInv s v P R' h θ'‖  ≤ 
      adaptiveArrayConstant*(Z:ℝ)^46/(Z^200:ℕ) := by
  obtain ⟨hq,hqlo,hqhi⟩ := adaptive_frequency_bounds hZ hd.ne_zero.bot_lt hs hv hdZ hvZ hsZ
  let q : ℝ := (s:ℝ)*v/d
  let a := adaptiveDivisorAmplitude d A mInv s v
  let I := (Finset.Ioc 0 (2*Z^7)).filter (fun w => P ∣ w)
  have hW := adaptive_quadratic_support_bound hZ hq hqlo
  have hwR : ⌊Real.sqrt (R/q)⌋₊  ≤  2*Z^7 :=
    (Nat.floor_mono (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hRB hq.le))).trans hW
  have hwR' : ⌊Real.sqrt (R'/q)⌋₊  ≤  2*Z^7 :=
    (Nat.floor_mono (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hRB' hq.le))).trans hW
  have ha : ∀ w, ‖a w‖ ≤ (Z:ℝ) := by
    intro w
    apply (adaptiveDivisorAmplitude_norm hd A mInv s v w).trans
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    have hz : (1:ℝ) ≤ Z := by exact_mod_cast hZ
    have hdz : (d:ℝ) ≤ Z := by exact_mod_cast hdZ
    nlinarith
  rw [divisorQuadraticSumP_eq_normalized hd,divisorQuadraticSumP_eq_normalized hd,
    normalizedSmoothQuadraticSum_eq_grid_sum (by linarith) hq hwR,
    normalizedSmoothQuadraticSum_eq_grid_sum (by linarith) hq hwR',
    ←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  change Real.sqrt q * ‖smoothQuadraticSum I a (fun w => q*(w:ℝ)^2) h θ R -
    smoothQuadraticSum I a (fun w => q*(w:ℝ)^2) h θ' R'‖  ≤  _
  have hc := quadraticGridConstant_nonneg I a (fun w => q*(w:ℝ)^2)
  calc
    _  ≤  Real.sqrt q*(quadraticGridConstant I a (fun w => q*(w:ℝ)^2)*(|θ-θ'|+|R-R'|)) :=
      mul_le_mul_of_nonneg_left (smoothQuadraticSum_parameters I a _ hR hR' h θ θ') (Real.sqrt_nonneg _)
    _  ≤  Real.sqrt q*(quadraticGridConstant I a (fun w => q*(w:ℝ)^2)*
        (1/(Z^200:ℕ)+1/(Z^200:ℕ))) := by gcongr
    _ = (2*Real.sqrt q*quadraticGridConstant I a (fun w => q*(w:ℝ)^2))/(Z^200:ℕ) := by ring
    _  ≤  _ := div_le_div_of_nonneg_right
      (adaptive_quadratic_grid_bound hZ P a hq hqhi ha) (by positivity)

end Ostmann.QuadraticCenter

end

end OAI
