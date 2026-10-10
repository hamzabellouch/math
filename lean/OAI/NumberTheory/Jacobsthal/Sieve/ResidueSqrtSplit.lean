import OAI.NumberTheory.Jacobsthal.Harmonic.AllCharacterLogPower
import OAI.NumberTheory.Jacobsthal.Primes.IntervalPrimesDefinition
import OAI.NumberTheory.Jacobsthal.Primes.PrimeCountAbel

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology BigOperators

noncomputable def residuePsi {q : ℕ} (a : ZMod q) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊X⌋₊+1), ArithmeticFunction.vonMangoldt.residueClass a n

lemma residuePsi_character_sum {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) (X : ℝ) :
    (residuePsi a X:ℂ) = (q.totient:ℂ)⁻¹ *
      ∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
        sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X := by
  classical
  unfold residuePsi
  rw [Complex.ofReal_sum]
  simp_rw [ArithmeticFunction.vonMangoldt.residueClass_apply ha]
  rw [← Finset.mul_sum,Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro chi _
  unfold sharpSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

lemma residuePsi_error_le {q : ℕ} [NeZero q] (a : ZMod q) (ha : IsUnit a) (X E : ℝ)
    (herror : ∀ chi : DirichletCharacter ℂ q,
      ‖sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0)‖ ≤ E) :
    ‖(residuePsi a X:ℂ)-(X:ℂ)/(q.totient:ℂ)‖ ≤ E := by
  classical
  have hai : IsUnit a⁻¹ := isUnit_of_dvd_one ⟨a,(ZMod.inv_mul_of_unit a ha).symm⟩
  have hmain : (∑ chi : DirichletCharacter ℂ q,
      chi a⁻¹ * (if chi=1 then (X:ℂ) else 0)) = (X:ℂ) := by
    simp [MulChar.one_apply hai]
  have hsum : (∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
      (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0))) =
      (∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
        sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X)-(X:ℂ) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,hmain]
  have he : (residuePsi a X:ℂ)-(X:ℂ)/(q.totient:ℂ) =
      (q.totient:ℂ)⁻¹ * ∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
      (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0)) := by
    rw [residuePsi_character_sum a ha X,hsum]
    ring
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    simpa only [Nat.card_eq_fintype_card] using
      (DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q)
  have hphi : (0:ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hterm (chi : DirichletCharacter ℂ q) :
      ‖chi a⁻¹ * (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0))‖ ≤ E := by
    rw [norm_mul]
    have h := mul_le_mul_of_nonneg_right (chi.norm_le_one a⁻¹)
      (norm_nonneg (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0)))
    simp only [one_mul] at h
    exact h.trans (herror chi)
  have hnorm : ‖∑ chi : DirichletCharacter ℂ q, chi a⁻¹ *
      (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
        (if chi=1 then (X:ℂ) else 0))‖ ≤ (q.totient:ℝ)*E := by
    calc
      _ ≤ ∑ chi : DirichletCharacter ℂ q, ‖chi a⁻¹ *
          (sharpSum (fun n:ℕ => chi n*(ArithmeticFunction.vonMangoldt n:ℂ)) X-
            (if chi=1 then (X:ℂ) else 0))‖ := norm_sum_le _ _
      _ ≤ ∑ _chi : DirichletCharacter ℂ q, E := Finset.sum_le_sum (fun chi _ => hterm chi)
      _ = _ := by simp [hcard]
  rw [he,norm_mul,norm_inv,Complex.norm_natCast]
  calc
    _ ≤ (q.totient:ℝ)⁻¹*((q.totient:ℝ)*E) := mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = E := by rw [← mul_assoc,inv_mul_cancel₀ hphi.ne',one_mul]

theorem residuePsi_log_power (A M : ℝ) (hA : 0 < A) (hM : 0 < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (a : ZMod q),
      IsUnit a → (q:ℝ) ≤ (Real.log X)^A →
      |residuePsi a X-X/(q.totient:ℝ)| ≤ K*X/(Real.log X)^M := by
  obtain ⟨K,hK,hall⟩ := all_character_log_power A M hA hM
  refine ⟨K,hK,?_⟩
  filter_upwards [hall] with X hX
  intro q _ a ha hq
  have h := residuePsi_error_le a ha X (K*X/(Real.log X)^M) (fun chi => hX q chi hq)
  have he : ‖(residuePsi a X:ℂ)-(X:ℂ)/(q.totient:ℂ)‖ =
      |residuePsi a X-X/(q.totient:ℝ)| := by
    rw [show (q.totient:ℂ) = ((q.totient:ℝ):ℂ) by simp,
      ← Complex.ofReal_div,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  rwa [he] at h

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter
open scoped Topology BigOperators

noncomputable def residuePrimeWeight {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  if n.Prime then ArithmeticFunction.vonMangoldt.residueClass a n else 0

noncomputable def residueTheta {q : ℕ} (a : ZMod q) (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊X⌋₊+1), residuePrimeWeight a n

lemma residuePrimeWeight_eq {q : ℕ} (a : ZMod q) (n : ℕ) :
    residuePrimeWeight a n = if n.Prime ∧ (n:ZMod q)=a then Real.log n else 0 := by
  classical
  by_cases hp : n.Prime
  · by_cases ha : (n:ZMod q)=a
    · simp [residuePrimeWeight,ArithmeticFunction.vonMangoldt.residueClass,hp,ha,
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [residuePrimeWeight,ArithmeticFunction.vonMangoldt.residueClass,hp,ha]
  · simp [residuePrimeWeight,hp]

lemma residuePsi_sub_theta_bounds {q : ℕ} (a : ZMod q) (X : ℝ) :
    0 ≤ residuePsi a X-residueTheta a X ∧
    residuePsi a X-residueTheta a X ≤ Chebyshev.psi X-Chebyshev.theta X := by
  classical
  rw [residuePsi,residueTheta,← Finset.sum_sub_distrib]
  constructor
  · apply Finset.sum_nonneg
    intro n _
    unfold residuePrimeWeight
    split_ifs
    · simp only [sub_self,le_refl]
    · simpa only [sub_zero] using ArithmeticFunction.vonMangoldt.residueClass_nonneg a n
  · rw [Chebyshev.psi_eq_sum_Icc,Chebyshev.theta_eq_sum_Icc,Finset.sum_filter,
      ← Finset.sum_sub_distrib,← Nat.range_succ_eq_Icc_zero]
    apply Finset.sum_le_sum
    intro n _
    unfold residuePrimeWeight
    by_cases hp : n.Prime
    · simp [hp,ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simpa only [hp,ite_false,sub_zero] using ArithmeticFunction.vonMangoldt.residueClass_le a n

lemma eventually_sqrt_le_log_power (M : ℝ) :
    ∀ᶠ X : ℝ in atTop, Real.sqrt X ≤ X/(Real.log X)^M := by
  filter_upwards [eventually_log_rpow_le_self (2*M)] with X hX
  have hXp : 0 < X := by linarith [hX.1]
  have hL : 0 < Real.log X := Real.log_pos (by linarith [hX.1])
  have hp : 0 < (Real.log X)^M := Real.rpow_pos_of_pos hL _
  have hsq : ((Real.log X)^M)^2 ≤ X := by
    rw [← Real.rpow_mul_natCast hL.le]
    simpa only [Nat.cast_ofNat,mul_comm] using hX.2
  have hle : (Real.log X)^M ≤ Real.sqrt X := (Real.le_sqrt hp.le hXp.le).mpr hsq
  apply (le_div_iff₀ hp).mpr
  calc
    _ ≤ Real.sqrt X*Real.sqrt X := mul_le_mul_of_nonneg_left hle (Real.sqrt_nonneg _)
    _ = X := Real.mul_self_sqrt hXp.le

theorem residueTheta_log_power (A M : ℝ) (hA : 0 < A) (hM : 0 < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (a : ZMod q),
      IsUnit a → (q:ℝ) ≤ (Real.log X)^A →
      |residueTheta a X-X/(q.totient:ℝ)| ≤ K*X/(Real.log X)^M := by
  obtain ⟨K,hK,hpsi⟩ := residuePsi_log_power A M hA hM
  obtain ⟨D,hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  let C : ℝ := max D 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨K+C,by positivity,?_⟩
  filter_upwards [hpsi,eventually_sqrt_le_log_power M] with X hX hsqrt
  intro q _ a ha hq
  have hgap := residuePsi_sub_theta_bounds a X
  have hb : residuePsi a X-residueTheta a X ≤ C*X/(Real.log X)^M := by
    calc
      _ ≤ D*Real.sqrt X := hgap.2.trans (hD X)
      _ ≤ C*Real.sqrt X := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      _ ≤ C*(X/(Real.log X)^M) := mul_le_mul_of_nonneg_left hsqrt hC.le
      _ = _ := by ring
  calc
    _ ≤ |residuePsi a X-X/(q.totient:ℝ)|+|residuePsi a X-residueTheta a X| := by
      have h := abs_sub_le (residueTheta a X) (residuePsi a X) (X/(q.totient:ℝ))
      rw [abs_sub_comm (residueTheta a X) (residuePsi a X),add_comm] at h
      exact h
    _ ≤ K*X/(Real.log X)^M+C*X/(Real.log X)^M := by
      rw [abs_of_nonneg hgap.1]
      exact add_le_add (hX q a ha hq) hb
    _ = _ := by ring

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Finset _root_.MeasureTheory
open scoped Topology BigOperators

lemma intervalPrimes_zero_eq {X : ℝ} (hX : 0 ≤ X) (q : ℕ) (r : ℤ) :
    intervalPrimes 0 X q r = (range (⌊X⌋₊+1)).filter
      (fun n:ℕ => n.Prime ∧ (n:ZMod q)=(r:ZMod q)) := by
  classical
  ext n
  have hm : (n:ZMod q)=(r:ZMod q) ↔ Int.ModEq (q:ℤ) (n:ℤ) r := by
    simpa using (ZMod.intCast_eq_intCast_iff (n:ℤ) r q)
  rw [mem_intervalPrimes,mem_filter,mem_range,hm]
  constructor
  · rintro ⟨hp,_,hn,hr⟩
    refine ⟨Nat.lt_succ_of_le ((Nat.le_floor_iff hX).mpr ?_),hp,hr⟩
    simpa only [zero_add] using hn
  · rintro ⟨hn,hp,hr⟩
    refine ⟨hp,by exact_mod_cast hp.pos,?_,hr⟩
    simpa only [zero_add] using (Nat.le_floor_iff hX).mp (Nat.le_of_lt_succ hn)

lemma intervalPrimes_card_eq_sum_weight {X : ℝ} (hX : 0 ≤ X) (q : ℕ) (r : ℤ) :
    ((intervalPrimes 0 X q r).card:ℝ) =
      ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * residuePrimeWeight (r:ZMod q) n := by
  classical
  rw [intervalPrimes_zero_eq hX,card_eq_sum_ones,Nat.range_succ_eq_Icc_zero,sum_filter]
  push_cast
  apply sum_congr rfl
  intro n _
  rw [residuePrimeWeight_eq]
  by_cases hp : n.Prime ∧ (n:ZMod q)=(r:ZMod q)
  · have hl : Real.log (n:ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one
      (by exact_mod_cast hp.1.pos) (by exact_mod_cast hp.1.ne_one)
    simp [hp,hl]
  · simp [hp]

lemma residueTheta_kernel_integrable (q : ℕ) (a : ZMod q) (X : ℝ) :
    IntegrableOn (fun t => residueTheta a t/(t*Real.log t^2)) (Set.Icc 2 X) volume := by
  conv => arg 1; ext; rw [residueTheta,Nat.range_succ_eq_Icc_zero,div_eq_mul_one_div,mul_comm]
  refine integrableOn_mul_sum_Icc _ (by norm_num) <| ContinuousOn.integrableOn_Icc ?_
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hl0 : Real.log x ≠ 0 := (Real.log_pos (by linarith [hx.1])).ne'
  have hd : x*Real.log x^2 ≠ 0 := mul_ne_zero hx0 (pow_ne_zero 2 hl0)
  exact ContinuousAt.continuousWithinAt (by fun_prop)

theorem intervalPrimes_card_eq_theta {X : ℝ} (hX : 2 ≤ X) (q : ℕ) (r : ℤ) :
    ((intervalPrimes 0 X q r).card:ℝ) =
      residueTheta (r:ZMod q) X/Real.log X +
        ∫ t in 2..X, residueTheta (r:ZMod q) t/(t*Real.log t^2) := by
  rw [intervalPrimes_card_eq_sum_weight (by linarith) q r]
  rw [sum_mul_eq_sub_integral_mul₁ (residuePrimeWeight (r:ZMod q))
    (f := fun n => (Real.log n)⁻¹) (by simp [residuePrimeWeight])
    (by simp [residuePrimeWeight]),← intervalIntegral.integral_of_le hX]
  · have hi (f : ℝ → ℝ) :
        ∫ u in 2..X, deriv (fun x => (Real.log x)⁻¹) u*f u =
        ∫ u in 2..X, f u * -(u*Real.log u^2)⁻¹ :=
      intervalIntegral.integral_congr fun u _ => by simp [field]
    rw [hi]
    simp only [residueTheta,Nat.range_succ_eq_Icc_zero,div_eq_mul_inv,mul_neg,
      intervalIntegral.integral_neg,sub_neg_eq_add]
    ring
  · intro z hz
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hl0 : Real.log z ≠ 0 := (Real.log_pos (by linarith [hz.1])).ne'
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z hz => ContinuousWithinAt.congr ?_
      (fun _ _ => Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have hz0 : z ≠ 0 := by linarith [hz.1]
    have hl0 : Real.log z^2 ≠ 0 := pow_ne_zero 2 (Real.log_pos (by linarith [hz.1])).ne'
    exact ContinuousAt.continuousWithinAt (by fun_prop)

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.MeasureTheory
open scoped Topology BigOperators
open ErdosPrimeInputs.PrimeCountAbel (logarithmicIntegral mainKernel)

noncomputable def residueErrorKernel {q : ℕ} (a : ZMod q) (t : ℝ) : ℝ :=
  residueTheta a t/(t*Real.log t^2)-mainKernel t/(q.totient:ℝ)

lemma residueErrorKernel_integrable {q : ℕ} (a : ZMod q) {u v : ℝ}
    (hu : 2 ≤ u) (huv : u ≤ v) : IntervalIntegrable (residueErrorKernel a) volume u v := by
  apply IntervalIntegrable.sub
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le huv).mpr
    exact (residueTheta_kernel_integrable q a v).mono_set (Set.Icc_subset_Icc_left hu)
  · exact (ErdosPrimeInputs.PrimeCountAbel.mainKernel_integrable hu huv).div_const _

lemma residueErrorKernel_eq {q : ℕ} (a : ZMod q) {t : ℝ} (ht : 0 < t) :
    residueErrorKernel a t = (residueTheta a t-t/(q.totient:ℝ))/(t*Real.log t^2) := by
  unfold residueErrorKernel mainKernel
  field_simp

theorem intervalPrimes_error_eq {X : ℝ} (hX : 2 ≤ X) (q : ℕ) (r : ℤ) :
    ((intervalPrimes 0 X q r).card:ℝ)-logarithmicIntegral X/(q.totient:ℝ) =
      2/((q.totient:ℝ)*Real.log 2) +
        (residueTheta (r:ZMod q) X-X/(q.totient:ℝ))/Real.log X +
          ∫ t in 2..X, residueErrorKernel (r:ZMod q) t := by
  have hli := _root_.Erdos970.integral_log_inv 2 X (by norm_num) hX
  have hi : (∫ t in 2..X, residueErrorKernel (r:ZMod q) t) =
      (∫ t in 2..X, residueTheta (r:ZMod q) t/(t*Real.log t^2)) -
        (∫ t in 2..X, mainKernel t)/(q.totient:ℝ) := by
    unfold residueErrorKernel
    rw [intervalIntegral.integral_sub,
      intervalIntegral.integral_div]
    · exact (intervalIntegrable_iff_integrableOn_Icc_of_le hX).mpr
        (residueTheta_kernel_integrable q _ X)
    · exact (ErdosPrimeInputs.PrimeCountAbel.mainKernel_integrable (by norm_num) hX).div_const _
  rw [intervalPrimes_card_eq_theta hX,hi]
  unfold logarithmicIntegral mainKernel
  simp only [one_div]
  rw [hli]
  ring

lemma residueTheta_nonneg {q : ℕ} (a : ZMod q) (t : ℝ) : 0 ≤ residueTheta a t := by
  apply Finset.sum_nonneg
  intro n _
  unfold residuePrimeWeight
  split_ifs
  · exact ArithmeticFunction.vonMangoldt.residueClass_nonneg a n
  · exact le_refl 0

lemma residueTheta_le_theta {q : ℕ} (a : ZMod q) (t : ℝ) :
    residueTheta a t ≤ Chebyshev.theta t := by
  classical
  rw [residueTheta,Chebyshev.theta_eq_sum_Icc,Finset.sum_filter,Nat.range_succ_eq_Icc_zero]
  apply Finset.sum_le_sum
  intro n _
  unfold residuePrimeWeight
  by_cases hp : n.Prime
  · simpa only [hp,ite_true,ArithmeticFunction.vonMangoldt_apply_prime hp] using
      ArithmeticFunction.vonMangoldt.residueClass_le a n
  · simp [hp]

lemma residueErrorKernel_coarse {q : ℕ} [NeZero q] (a : ZMod q) {t : ℝ} (ht : 2 ≤ t) :
    |residueErrorKernel a t| ≤ (Real.log 4+1)/(Real.log 2)^2 := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have hphi : (1:ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hdiv : t/(q.totient:ℝ) ≤ t := div_le_self ht0.le hphi
  have hnum : |residueTheta a t-t/(q.totient:ℝ)| ≤ (Real.log 4+1)*t := by
    calc
      _ ≤ |residueTheta a t|+|t/(q.totient:ℝ)| := abs_sub _ _
      _ = residueTheta a t+t/(q.totient:ℝ) := by rw [abs_of_nonneg (residueTheta_nonneg a t),abs_of_nonneg (by positivity)]
      _ ≤ Real.log 4*t+t := add_le_add ((residueTheta_le_theta a t).trans
        (Chebyshev.theta_le_log4_mul_x ht0.le)) hdiv
      _ = _ := by ring
  rw [residueErrorKernel_eq a ht0,abs_div,abs_of_pos (by positivity : 0 < t*Real.log t^2)]
  calc
    _ ≤ ((Real.log 4+1)*t)/(t*Real.log t^2) := div_le_div_of_nonneg_right hnum (by positivity)
    _ = (Real.log 4+1)/Real.log t^2 := by field_simp
    _ ≤ _ := by
      have hlog : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (sq_le_sq₀ (Real.log_pos (by norm_num : (1:ℝ)<2)).le hl.le |>.mpr hlog)

lemma residueErrorKernel_low_integral {q : ℕ} [NeZero q] (a : ZMod q) {Y : ℝ} (hY : 2 ≤ Y) :
    |∫ t in 2..Y, residueErrorKernel a t| ≤ (Real.log 4+1)/(Real.log 2)^2*Y := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=2) (b:=Y)
    (f:=residueErrorKernel a) (C:=(Real.log 4+1)/(Real.log 2)^2) (fun t ht => by
      rw [Set.uIoc_of_le hY] at ht
      simpa only [Real.norm_eq_abs] using residueErrorKernel_coarse a ht.1.le)
  rw [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ Y-2)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end Erdos970Dependency.SiegelWalfisz

end

section

namespace Erdos970Dependency.SiegelWalfisz
open _root_.Filter _root_.MeasureTheory
open scoped Topology

lemma modulus_admissible_above_sqrt {A X t : ℝ} (hA : 0 < A) (hX : 3 ≤ Real.sqrt X)
    (hlog : 2*(2:ℝ)^A ≤ Real.log X) (ht : Real.sqrt X ≤ t) {q : ℕ}
    (hq : (q:ℝ) ≤ (Real.log X)^A) :
    (q:ℝ) ≤ (Real.log t)^(A+1) := by
  have hs : 0 < Real.sqrt X := by linarith
  have hx0 : 0 ≤ X := (Real.sqrt_pos.mp hs).le
  have ht3 : 3 ≤ t := hX.trans ht
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have hcompare : Real.log X ≤ 2*Real.log t := by
    have h : Real.log (Real.sqrt X) ≤ Real.log t := Real.log_le_log hs ht
    rw [Real.log_sqrt hx0] at h
    linarith
  have hpow : (2:ℝ)^A ≤ Real.log t := by linarith
  have hL : 0 ≤ Real.log X := le_trans (by positivity) hlog
  calc
    _ ≤ (Real.log X)^A := hq
    _ ≤ (2*Real.log t)^A := Real.rpow_le_rpow hL hcompare hA.le
    _ = (2:ℝ)^A*(Real.log t)^A := Real.mul_rpow (by norm_num) hl.le
    _ ≤ Real.log t*(Real.log t)^A := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (Real.log t)^(A+1) := by rw [Real.rpow_add hl,Real.rpow_one]; ring

lemma residueErrorKernel_upper_bound {q : ℕ} (a : ZMod q) {K M X t : ℝ}
    (hK : 0 ≤ K) (hM : 0 < M) (hX : 3 ≤ Real.sqrt X) (ht : Real.sqrt X ≤ t)
    (herror : |residueTheta a t-t/(q.totient:ℝ)| ≤ K*t/(Real.log t)^M) :
    |residueErrorKernel a t| ≤ K*(2:ℝ)^M/(Real.log X)^M := by
  have hs : 0 < Real.sqrt X := by linarith
  have hx0 : 0 < X := Real.sqrt_pos.mp hs
  have hx3 : 3 ≤ X := by nlinarith [Real.sq_sqrt hx0.le]
  have ht3 : 3 ≤ t := hX.trans ht
  have ht0 : 0 < t := by linarith
  have hl1 : 1 ≤ Real.log t :=
    ((Real.lt_log_iff_exp_lt ht0).mpr (Real.exp_one_lt_three.trans_le ht3)).le
  have hl : 0 < Real.log t := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hcompare : Real.log X ≤ 2*Real.log t := by
    have h : Real.log (Real.sqrt X) ≤ Real.log t := Real.log_le_log hs ht
    rw [Real.log_sqrt hx0.le] at h
    linarith
  have hp : (Real.log X)^M ≤ (2:ℝ)^M*(Real.log t)^M := by
    rw [← Real.mul_rpow (by norm_num : (0:ℝ)≤2) hl.le]
    exact Real.rpow_le_rpow hL.le hcompare hM.le
  rw [residueErrorKernel_eq a ht0,abs_div,abs_of_pos (by positivity : 0 < t*Real.log t^2)]
  calc
    _ ≤ (K*t/(Real.log t)^M)/(t*Real.log t^2) :=
      div_le_div_of_nonneg_right herror (by positivity)
    _ = (K/(Real.log t)^M)/(Real.log t)^2 := by field_simp
    _ ≤ K/(Real.log t)^M := div_le_self (by positivity) (by nlinarith)
    _ ≤ _ := by
      apply (div_le_div_iff₀ (by positivity : 0 < (Real.log t)^M)
        (by positivity : 0 < (Real.log X)^M)).mpr
      calc
        _ ≤ K*((2:ℝ)^M*(Real.log t)^M) := mul_le_mul_of_nonneg_left hp hK
        _ = _ := by ring

lemma residueErrorKernel_high_integral {q : ℕ} (a : ZMod q) {K M X : ℝ}
    (hK : 0 ≤ K) (hM : 0 < M) (hX : 3 ≤ Real.sqrt X)
    (herror : ∀ t, Real.sqrt X ≤ t →
      |residueTheta a t-t/(q.totient:ℝ)| ≤ K*t/(Real.log t)^M) :
    |∫ t in Real.sqrt X..X, residueErrorKernel a t| ≤
      (K*(2:ℝ)^M)*X/(Real.log X)^M := by
  have hs : 0 < Real.sqrt X := by linarith
  have hx0 : 0 < X := Real.sqrt_pos.mp hs
  have hsX : Real.sqrt X ≤ X := by nlinarith [Real.sq_sqrt hx0.le]
  have hL : 0 < Real.log X := Real.log_pos (by nlinarith [Real.sq_sqrt hx0.le])
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a:=Real.sqrt X) (b:=X)
    (f:=residueErrorKernel a) (C:=K*(2:ℝ)^M/(Real.log X)^M) (fun t ht => by
      rw [Set.uIoc_of_le hsX] at ht
      simpa only [Real.norm_eq_abs] using
        residueErrorKernel_upper_bound a hK hM hX ht.1.le (herror t ht.1.le))
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hsX)] at h
  calc
    _ ≤ K*(2:ℝ)^M/(Real.log X)^M*(X-Real.sqrt X) := h
    _ ≤ K*(2:ℝ)^M/(Real.log X)^M*X :=
      mul_le_mul_of_nonneg_left (sub_le_self _ (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by ring

end Erdos970Dependency.SiegelWalfisz

end

end Erdos970

end OAI
