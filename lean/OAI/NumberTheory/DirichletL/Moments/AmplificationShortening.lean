import OAI.NumberTheory.DirichletL.Moments.AmplificationEnergy
import OAI.NumberTheory.DirichletL.Moments.Extraction

namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationShortening
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentGaussEnergy CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentAmplification CenteredMomentAmplificationLocal CenteredMomentAmplificationGlobal
open ProbePhysical
local notation "O" => ActualEisensteinCubic.O

def residualCharacter (p : O) (k : ℕ) (u : O) : ℂ :=
  sexticReciprocityPhase p u ^ k * idealRowHom u (Ideal.span {p}) ^ (2*k)

theorem crossFactor_primary (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1) :
    idealRowHom u (Ideal.span {p^k}) * idealRowHom (p^k) (Ideal.span {u}) =
      residualCharacter p k u := by
  rw [← Ideal.span_singleton_pow,map_pow,idealRowHom_argument_pow p k _ hu,
    idealRowHom_primary_reciprocity u p hup hpp hu hp,
    sexticReciprocityPhase_symm u p,mul_pow]
  unfold residualCharacter
  rw [show 2*k=k+k by omega,pow_add]
  ring

theorem gauss_primary_power_product (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1)
    (hcop : IsCoprime p u) (h : O) :
    sexticGauss (p^k*u) (mul_ne_zero (pow_ne_zero _ (supportedElement_ne_zero p hp))
      (supportedElement_ne_zero u hu)) h =
      residualCharacter p k u * sexticGauss (p^k) (pow_ne_zero _ (supportedElement_ne_zero p hp)) h *
        sexticGauss u (supportedElement_ne_zero u hu) h := by
  rw [sexticGauss_coprime_product (p^k) u (supported_power p hp k) hu hcop.pow_left,
    crossFactor_primary p u k hp hu hpp hup]

theorem residualCharacter_six (p u : O) (hp : Supported (Ideal.span {p})) :
    residualCharacter p 6 u = sexticReciprocityPhase p u ^ 6 *
      coprimalityMask u p := by
  unfold residualCharacter
  norm_num only
  rw [twelfth_power_mask p hp u]

def primeRoot (p : O) (k : ℕ) : ℂ :=
  (Real.sqrt ((Ideal.absNorm (Ideal.span {p}) : ℝ)^k) : ℂ)

theorem primeRoot_sq (p : O) (k : ℕ) :
    primeRoot p k * primeRoot p k = (Ideal.absNorm (Ideal.span {p}) : ℂ)^k := by
  rw [primeRoot,← Complex.ofReal_mul,Real.mul_self_sqrt (by positivity),Complex.ofReal_pow,
    Complex.ofReal_natCast]

theorem modulusRoot_product (p u : O) (k : ℕ) :
    (Real.sqrt (Ideal.absNorm (Ideal.span {p^k*u}) : ℝ) : ℂ) =
      primeRoot p k * (Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) := by
  simp only [← Ideal.span_singleton_mul_span_singleton,← Ideal.span_singleton_pow,
    map_mul,map_pow,Nat.cast_mul,Nat.cast_pow,Real.sqrt_mul (by positivity :
      0 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)^k),Complex.ofReal_mul,primeRoot]

theorem gaussRow_shortening (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1)
    (hcop : IsCoprime p u) (h : O) :
    gaussRow (p^k*u) (supported_mul_elements _ _ (supported_power p hp k) hu) h =
      residualCharacter p k u *
        (sexticGauss (p^k) (pow_ne_zero _ (supportedElement_ne_zero p hp)) h / primeRoot p k) *
          gaussRow u hu h := by
  unfold gaussRow
  rw [gauss_primary_power_product p u k hp hu hpp hup hcop h,modulusRoot_product]
  ring

theorem central_error_shortening (p u : O) (n : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1)
    (hcop : IsCoprime p u) (h : O) :
    (gaussRow (p^(n+1)*u) (supported_mul_elements _ _ (supported_power p hp (n+1)) hu) h -
      gaussRow (p^(n+1)*u) (supported_mul_elements _ _ (supported_power p hp (n+1)) hu) (p^6*h)) /
        primeRoot p (n+1) =
      (centralLocal p (supportedElement_ne_zero p hp) n h -
        centralLocal p (supportedElement_ne_zero p hp) n (p^6*h)) *
          (residualCharacter p (n+1) u * gaussRow u hu h) := by
  rw [gaussRow_shortening p u (n+1) hp hu hpp hup hcop,
    gaussRow_shortening p u (n+1) hp hu hpp hup hcop]
  have hinv : gaussRow u hu (p^6*h) = gaussRow u hu h := by
    unfold gaussRow
    rw [gauss_sixth_frequency u hu p h hcop]
  rw [hinv]
  unfold centralLocal
  rw [← primeRoot_sq p (n+1)]
  ring

theorem supported_phase_sq (p u : O) (hp : Supported (Ideal.span {p}))
    (hu : Supported (Ideal.span {u})) : sexticReciprocityPhase p u ^ 2 = 1 := by
  unfold sexticReciprocityPhase
  exact_mod_cast QuadraticAllOddCRT.quadraticRaySign_sq _ _
    (supported_residue_odd p hp) (supported_residue_odd u hu)

theorem residualCharacter_moving (p u : O) (k : ℕ)
    (hp : Supported (Ideal.span {p})) (hu : Supported (Ideal.span {u}))
    (hpp : goodLambda^2 ∣ p-1) (hup : goodLambda^2 ∣ u-1) :
    residualCharacter p k u = sexticReciprocityPhase p u ^ k *
      idealRowHom (p^(2*k)) (Ideal.span {u}) := by
  rw [residualCharacter,idealRowHom_argument_pow p (2*k) _ hu,
    idealRowHom_primary_reciprocity p u hpp hup hp hu,mul_pow,
    pow_mul,supported_phase_sq p u hp hu,one_pow,one_mul]

def errorScalar (p : O) (hp : p ≠ 0) (n : ℕ) (h : O) : ℂ :=
  centralLocal p hp n h - centralLocal p hp n (p^6*h)

theorem centralLocal_unit_zero (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) (hn : n ≠ 0)
    (h : O) (hph : ¬p ∣ h) : centralLocal p hp.ne_zero n h = 0 := by
  unfold centralLocal
  rw [← mul_one h,sexticGauss_unit_scale _ (supported_power p hs (n+1)) h 1
    ((hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right),
    gauss_prime_power_one p hp hg hc]
  simp only [hn,ite_false,mul_zero,zero_div]

theorem centralLocal_six_zero (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) (hn5 : n ≠ 5) (hn6 : n ≠ 6)
    (h : O) (hph : ¬p ∣ h) : centralLocal p hp.ne_zero n (p^6*h) = 0 := by
  unfold centralLocal
  rw [mul_comm (p^6) h,sexticGauss_unit_scale _ (supported_power p hs (n+1)) h (p^6)
    ((hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right),
    gauss_prime_power_six p hp hg hc]
  simp only [hn5,hn6,ite_false,mul_zero,zero_div]

theorem errorScalar_norms (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖errorScalar p hp.ne_zero 0 h‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ ∧
    ‖errorScalar p hp.ne_zero 5 h‖^2 = (1-(Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹)^2 ∧
    ‖errorScalar p hp.ne_zero 6 h‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ := by
  unfold errorScalar
  rw [centralLocal_six_zero p hp hs hg hc 0 (by decide) (by decide) h hph,
    centralLocal_unit_zero p hp hs hg hc 5 (by decide) h hph,
    centralLocal_unit_zero p hp hs hg hc 6 (by decide) h hph,
    sub_zero,zero_sub,zero_sub,norm_neg,norm_neg,mul_comm (p^6) h]
  exact ⟨centralLocal_one_norm_sq p hp hs hg hc h hph,
    centralLocal_six_norm_sq p hp hs hg hc h hph,
    centralLocal_seven_norm_sq p hp hs hg hc h hph⟩

theorem error_polynomial_shortening {α : Type*} (S : Finset α)
    (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (hpp : goodLambda^2 ∣ p-1) (n : ℕ) (u : α → O)
    (hu : ∀ i, Supported (Ideal.span {u i})) (hup : ∀ i, goodLambda^2 ∣ u i-1)
    (hcop : ∀ i, IsCoprime p (u i)) (c : α → ℂ) (h : O) :
    amplificationError S (fun i => p^(n+1)*u i)
      (fun i => supported_mul_elements _ _ (supported_power p hs (n+1)) (hu i))
      (fun i => c i / primeRoot p (n+1)) (fun i => multiplicity p (p^(n+1)*u i)) p (n+1) h =
      errorScalar p hp.ne_zero n h *
        gaussPolynomial S u hu (fun i => c i * residualCharacter p (n+1) (u i)) h := by
  unfold amplificationError gaussPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hv : multiplicity p (p^(n+1)*u i) = n+1 := by
    rw [multiplicity_mul hp (FiniteMultiplicity.of_prime_left hp
      (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supportedElement_ne_zero _ (hu i)))),
      multiplicity_pow_self_of_prime hp,
      multiplicity_eq_zero_of_not_dvd (hp.irreducible.coprime_iff_not_dvd.mp (hcop i)),add_zero]
  dsimp only
  simp only [ite_eq_left hv]
  have he := central_error_shortening p (u i) n hs (hu i) hpp (hup i) (hcop i) h
  change _ = errorScalar p hp.ne_zero n h *
    (c i * residualCharacter p (n+1) (u i) * gaussRow (u i) (hu i) h)
  calc
    _ = c i * ((gaussRow (p^(n+1)*u i)
        (supported_mul_elements _ _ (supported_power p hs (n+1)) (hu i)) h -
      gaussRow (p^(n+1)*u i)
        (supported_mul_elements _ _ (supported_power p hs (n+1)) (hu i)) (p^6*h)) /
        primeRoot p (n+1)) := by ring
    _ = _ := by rw [he]; unfold errorScalar; ring

end SevenEighths.CenteredMomentAmplificationShortening

end

end OAI
