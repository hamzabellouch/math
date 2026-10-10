import OAI.NumberTheory.PrimeGaps.OrthantIntegrals

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

theorem theta_le_vonMangoldt (n : ℕ) : theta n ≤ ArithmeticFunction.vonMangoldt n := by
  by_cases hn : Nat.Prime n
  · simp [theta, hn, ArithmeticFunction.vonMangoldt_apply_prime hn]
  · simp [theta, hn]

theorem sum_vonMangoldt_sub_theta (Y : ℕ) :
    (∑ n ∈ Finset.Ioc 0 Y, (ArithmeticFunction.vonMangoldt n - theta n)) =
      Chebyshev.psi Y - Chebyshev.theta Y := by
  simp only [Finset.sum_sub_distrib, Chebyshev.psi, Chebyshev.theta, Nat.floor_natCast,
    theta, Finset.sum_filter]

theorem residueSlice_nonneg (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) (L U q c : ℕ) :
    0 ≤ residueSlice f L U q c := Finset.sum_nonneg fun n _ => hf n

theorem residueSlice_primepower_error {U : ℕ} (hU : 1 ≤ U) (L q c : ℕ) :
    |residueSlice ArithmeticFunction.vonMangoldt L U q c - residueSlice theta L U q c| ≤
      2 * Real.sqrt U * Real.log U := by
  have hdiff : 0 ≤ residueSlice ArithmeticFunction.vonMangoldt L U q c -
      residueSlice theta L U q c := by
    rw [residueSlice, residueSlice, ← Finset.sum_sub_distrib]
    exact Finset.sum_nonneg fun n _ => sub_nonneg.mpr (theta_le_vonMangoldt n)
  rw [abs_of_nonneg hdiff, residueSlice, residueSlice, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 U, (ArithmeticFunction.vonMangoldt n - theta n) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        obtain ⟨hn,_⟩ := Finset.mem_filter.mp hn
        obtain ⟨hnL,hnU⟩ := Finset.mem_Ioc.mp hn
        exact Finset.mem_Ioc.mpr ⟨by omega, hnU⟩
      · intro n _ _
        exact sub_nonneg.mpr (theta_le_vonMangoldt n)
    _ = Chebyshev.psi U - Chebyshev.theta U := sum_vonMangoldt_sub_theta U
    _ ≤ _ := Chebyshev.psi_sub_theta_le (by exact_mod_cast hU)

theorem residueSlice_theta_le {L U bound : ℕ} (hU : U ≤ bound) (hb : 1 ≤ bound)
    (q c : ℕ) : residueSlice theta L U q c ≤ (U-L:ℕ) * Real.log bound := by
  have hlog : 0 ≤ Real.log (bound:ℝ) := Real.log_nonneg (by exact_mod_cast hb)
  calc
    _ ≤ ∑ n ∈ (Finset.Ioc L U).filter (fun n => n % q = c), Real.log bound := by
      apply Finset.sum_le_sum
      intro n hn
      have hnU := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2
      by_cases hp : Nat.Prime n
      · rw [theta, ite_eq_left hp]
        exact Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast hnU.trans hU)
      · simpa [theta, hp]
    _ = (((Finset.Ioc L U).filter (fun n => n % q = c)).card:ℝ) * Real.log bound := by simp
    _ ≤ (U-L:ℕ) * Real.log bound := by
      apply mul_le_mul_of_nonneg_right _ hlog
      exact_mod_cast (Finset.card_filter_le (Finset.Ioc L U) (fun n => n % q = c)).trans_eq
        (Nat.card_Ioc L U)

theorem residueSlice_theta_shift_error {X H a : ℕ} (hX : 1 ≤ X) (ha : a ≤ H) (q c : ℕ) :
    |residueSlice theta (X+a) (2*X+a) q c - residueSlice theta X (2*X) q c| ≤
      2*(H:ℝ) * Real.log (2*X+H) := by
  have hid : residueSlice theta (X+a) (2*X+a) q c - residueSlice theta X (2*X) q c =
      residueSlice theta (2*X) (2*X+a) q c - residueSlice theta X (X+a) q c := by
    rw [← residuePrefix_sub theta (by omega), ← residuePrefix_sub theta (by omega),
      ← residuePrefix_sub theta (by omega), ← residuePrefix_sub theta (by omega)]
    ring
  rw [hid]
  have hA := residueSlice_theta_le (L := 2*X) (U := 2*X+a) (bound := 2*X+H)
    (by omega) (by omega) q c
  have hB := residueSlice_theta_le (L := X) (U := X+a) (bound := 2*X+H)
    (by omega) (by omega) q c
  simp only [Nat.add_sub_cancel_left, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hA hB
  have hA0 := residueSlice_nonneg theta theta_nonneg (2*X) (2*X+a) q c
  have hB0 := residueSlice_nonneg theta theta_nonneg X (X+a) q c
  have haR : (a:ℝ) ≤ H := by exact_mod_cast ha
  have hlog : 0 ≤ Real.log (2*(X:ℝ)+H) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2*X+H by omega))
  have hah := mul_le_mul_of_nonneg_right haR hlog
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

noncomputable def endpointError (x : ℝ) (q : ℕ) : NNReal :=
  (Finset.range q).sup fun c => if Nat.Coprime c q then
    NNReal.mk (|residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c - x/q.totient|)
      (abs_nonneg _) else 0

theorem endpointClassError_le (X : ℕ) {q c : ℕ} (hc : c < q) (hcop : Nat.Coprime c q) :
    |residuePrefix ArithmeticFunction.vonMangoldt X q c - (X:ℝ)/q.totient| ≤
      (endpointError X q : ℝ) := by
  have h := Finset.le_sup (f := fun c => if Nat.Coprime c q then
    NNReal.mk (|residuePrefix ArithmeticFunction.vonMangoldt ⌊(X:ℝ)⌋₊ q c -
      (X:ℝ)/q.totient|) (abs_nonneg _) else 0) (Finset.mem_range.mpr hc)
  have hr := NNReal.coe_le_coe.mpr h
  simpa only [ite_eq_left hcop, NNReal.coe_mk, Nat.floor_natCast, endpointError] using hr

def BombieriVinogradov : Prop :=
  ∀ A : ℝ, 0 < A → ∃ b : ℝ, 0 < b ∧ ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      (∑ q ∈ Finset.Icc 1 ⌊x^(1/2:ℝ) * (Real.log x)^(-b)⌋₊,
        (endpointError x q : ℝ)) ≤ M*x*(Real.log x)^(-A)

theorem residueSlice_vonMangoldt_endpoint_error (X : ℕ) {q c : ℕ}
    (hc : c < q) (hcop : Nat.Coprime c q) :
    |residueSlice ArithmeticFunction.vonMangoldt X (2*X) q c - (X:ℝ)/q.totient| ≤
      (endpointError (2*X:ℕ) q : ℝ) + (endpointError X q : ℝ) := by
  rw [← residuePrefix_sub _ (by omega)]
  have hid : residuePrefix ArithmeticFunction.vonMangoldt (2*X) q c -
      residuePrefix ArithmeticFunction.vonMangoldt X q c - (X:ℝ)/q.totient =
      (residuePrefix ArithmeticFunction.vonMangoldt (2*X) q c - ((2*X:ℕ):ℝ)/q.totient) -
      (residuePrefix ArithmeticFunction.vonMangoldt X q c - (X:ℝ)/q.totient) := by
    push_cast
    ring
  rw [hid]
  exact (abs_sub _ _).trans (add_le_add (endpointClassError_le (2*X) hc hcop)
    (endpointClassError_le X hc hcop))

theorem markedClassError_le_endpointErrors {X H q a c : ℕ} (hX : 1 ≤ X)
    (ha : a ≤ H) (hc : c < q) (hcop : Nat.Coprime (c+a) q) :
    |(∑ m ∈ residueStarts X q c, theta (m+a)) - (X:ℝ)/q.totient| ≤
      (endpointError (2*X:ℕ) q : ℝ) + (endpointError X q : ℝ) +
        2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
        2*(H:ℝ) * Real.log (2*X+H) := by
  let r := (c+a)%q
  have hq : 0 < q := by omega
  have hr : r < q := Nat.mod_lt _ hq
  have hrcop : Nat.Coprime r q := by
    change Nat.gcd ((c+a)%q) q = 1
    rw [← Nat.gcd_rec q (c+a), Nat.gcd_comm]
    exact hcop
  rw [shifted_sum_eq_residueSlice theta X q a hc]
  have hs := residueSlice_theta_shift_error hX ha q r
  have hp := residueSlice_primepower_error (U := 2*X) (by omega) X q r
  have he := residueSlice_vonMangoldt_endpoint_error X hr hrcop
  have htri := abs_sub_le (residueSlice theta (X+a) (2*X+a) q r)
    (residueSlice theta X (2*X) q r) ((X:ℝ)/q.totient)
  have htri' := abs_sub_le (residueSlice theta X (2*X) q r)
    (residueSlice ArithmeticFunction.vonMangoldt X (2*X) q r) ((X:ℝ)/q.totient)
  rw [abs_sub_comm (residueSlice ArithmeticFunction.vonMangoldt _ _ _ _)] at hp
  norm_cast at hp
  simpa only [r] using (show |residueSlice theta (X+a) (2*X+a) q r - (X:ℝ)/q.totient| ≤
      (endpointError (2*X:ℕ) q : ℝ) + (endpointError X q : ℝ) +
        2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
        2*(H:ℝ) * Real.log (2*X+H) by
    push_cast at hp
    linarith)

theorem markedError_le_endpointErrors {X H q : ℕ} (hX : 1 ≤ X) :
    (markedError X H q : ℝ) ≤
      (endpointError (2*X:ℕ) q : ℝ) + (endpointError X q : ℝ) +
        2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
        2*(H:ℝ) * Real.log (2*X+H) := by
  have hlog : 0 ≤ Real.log (2*(X:ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2*X by omega))
  have hlog' : 0 ≤ Real.log (2*(X:ℝ)+H) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2*X+H by omega))
  have hnonneg : 0 ≤ (endpointError (2*X:ℕ) q : ℝ) + (endpointError X q : ℝ) +
      2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
      2*(H:ℝ) * Real.log (2*X+H) := by positivity
  change markedError X H q ≤ NNReal.mk _ hnonneg
  apply Finset.sup_le
  rintro ⟨a,c⟩ hac
  have ha : a ≤ H := by simpa using (Finset.mem_product.mp hac).1
  have hc : c < q := Finset.mem_range.mp (Finset.mem_product.mp hac).2
  dsimp only
  split_ifs with hcop
  · exact markedClassError_le_endpointErrors hX ha hc hcop
  · exact zero_le

theorem sum_markedError_le_endpointErrors {X : ℕ} (hX : 1 ≤ X) (H Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, (markedError X H q : ℝ)) ≤
      (∑ q ∈ Finset.Icc 1 Q, (endpointError (2*X:ℕ) q : ℝ)) +
      (∑ q ∈ Finset.Icc 1 Q, (endpointError X q : ℝ)) +
      (Q:ℝ) * (2 * Real.sqrt (2*(X:ℝ)) * Real.log (2*(X:ℝ)) +
        2*(H:ℝ) * Real.log (2*X+H)) := by
  apply (Finset.sum_le_sum (fun q _ => markedError_le_endpointErrors (H:=H) (q:=q) hX)).trans_eq
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
    nsmul_eq_mul]
  ring

noncomputable def powerModulus (rho : ℝ) (X : ℕ) : ℕ := ⌊(X:ℝ)^rho⌋₊

theorem eventually_rpow_le_BV_range {rho : ℝ} (hrho : rho < 1/2) (b : ℝ) :
    ∀ᶠ x : ℝ in atTop, x^rho ≤ x^(1/2:ℝ) * (Real.log x)^(-b) := by
  have h := (isLittleO_log_rpow_rpow_atTop b (show (0:ℝ) < 1/2-rho by linarith)).bound
    (show (0:ℝ) < 1 by norm_num)
  filter_upwards [h, eventually_gt_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx1
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL.le _),
    abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at hx
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hL b)).mpr
  calc
    _ ≤ x^rho * x^(1/2-rho) := mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hx0.le _)
    _ = _ := by rw [← Real.rpow_add hx0]; congr 1; ring

theorem endpoint_error_sum_nonneg (x : ℝ) (Q : ℕ) :
    0 ≤ ∑ q ∈ Finset.Icc 1 Q, (endpointError x q : ℝ) := by positivity

theorem endpoint_sum_log_decay (hBV : BombieriVinogradov) {rho : ℝ}
    (hrho : 0 ≤ rho) (hrhohalf : rho < 1/2) {k : ℕ} (hk : 1 ≤ k) (A : ℕ) :
    Tendsto (fun X : ℕ =>
      ((∑ q ∈ Finset.Icc 1 (powerModulus rho X), (endpointError (k*X:ℕ) q : ℝ)) / X) *
        (Real.log (X:ℝ))^A) atTop (nhds 0) := by
  obtain ⟨b,hb,M,hM,x₀,hx₀,hest⟩ := hBV (A+1) (by positivity)
  have hkR : (0:ℝ) < k := by exact_mod_cast (show 0<k by omega)
  have hXlim : Tendsto (fun X : ℕ => (X:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hkXlim : Tendsto (fun X : ℕ => ((k*X:ℕ):ℝ)) atTop atTop := by
    simpa only [Nat.cast_mul] using hXlim.const_mul_atTop hkR
  have hLlim : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hXlim
  have hlim : Tendsto (fun X : ℕ => (M*(k:ℝ)) / Real.log (X:ℝ)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hLlim).const_mul (M*(k:ℝ))
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact mul_nonneg (div_nonneg (endpoint_error_sum_nonneg _ _) (Nat.cast_nonneg _))
      (pow_nonneg (log_pos_of_two_le hX).le _)
  · filter_upwards [eventually_ge_atTop 2, hkXlim.eventually (eventually_ge_atTop x₀),
        hkXlim.eventually (eventually_rpow_le_BV_range hrhohalf b)] with X hX hx hcut
    have hX0 : (0:ℝ) < X := by exact_mod_cast (show 0<X by omega)
    have hLX : 0 < Real.log (X:ℝ) := log_pos_of_two_le hX
    have hkX0 : (0:ℝ) < ((k*X:ℕ):ℝ) := by positivity
    have hXkX : (X:ℝ) ≤ ((k*X:ℕ):ℝ) := by exact_mod_cast (Nat.le_mul_of_pos_left X hk)
    have hLle : Real.log (X:ℝ) ≤ Real.log ((k*X:ℕ):ℝ) := Real.log_le_log hX0 hXkX
    have hQ : powerModulus rho X ≤
        ⌊(((k*X:ℕ):ℝ))^(1/2:ℝ) * (Real.log ((k*X:ℕ):ℝ))^(-b)⌋₊ :=
      Nat.floor_le_floor ((Real.rpow_le_rpow hX0.le hXkX hrho).trans hcut)
    have hsum : (∑ q ∈ Finset.Icc 1 (powerModulus rho X),
        (endpointError (k*X:ℕ) q : ℝ)) ≤
        M * ((k*X:ℕ):ℝ) * (Real.log ((k*X:ℕ):ℝ))^(-(A+1:ℝ)) := by
      apply le_trans _ (hest _ hx)
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hQ)
      intro q _ _
      exact NNReal.coe_nonneg _
    have hlogpow : (Real.log ((k*X:ℕ):ℝ))^(-(A+1:ℝ)) ≤
        (Real.log (X:ℝ))^(-(A+1:ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hLX hLle (by have := Nat.cast_nonneg (α:=ℝ) A; linarith)
    calc
      _ ≤ (M * ((k*X:ℕ):ℝ) * (Real.log ((k*X:ℕ):ℝ))^(-(A+1:ℝ)) / X) *
          (Real.log (X:ℝ))^A :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsum hX0.le) (by positivity)
      _ ≤ (M * ((k*X:ℕ):ℝ) * (Real.log (X:ℝ))^(-(A+1:ℝ)) / X) *
          (Real.log (X:ℝ))^A := by gcongr
      _ = (M*(k:ℝ)) / Real.log (X:ℝ) := by
        rw [Real.rpow_neg hLX.le]
        have hnat : (A:ℝ)+1 = ((A+1:ℕ):ℝ) := by push_cast; rfl
        rw [hnat, Real.rpow_natCast, pow_succ, Nat.cast_mul]
        field_simp

theorem polylog_shift_eventually_le (H : ℕ → ℕ) {D B : ℝ}
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ) ≤ D*(Real.log (X:ℝ))^B) :
    ∀ᶠ X : ℕ in atTop, H X ≤ X := by
  have hlim : Tendsto (fun X : ℕ => D * ((Real.log (X:ℝ))^B / (X:ℝ)))
      atTop (nhds 0) := by
    have hh := ((isLittleO_log_rpow_rpow_atTop B (show (0:ℝ)<1 by norm_num)).tendsto_div_nhds_zero
      ).comp tendsto_natCast_atTop_atTop
    simpa only [Real.rpow_one, Function.comp_def, mul_zero] using hh.const_mul D
  filter_upwards [hH, hlim.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),
    eventually_ge_atTop 1] with X hHX hsmall hX
  have hX0 : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hh : D*(Real.log (X:ℝ))^B ≤ (X:ℝ) := by
    rw [← mul_div_assoc] at hsmall
    exact (div_lt_one hX0).mp hsmall |>.le
  exact_mod_cast hHX.trans hh

theorem log_shift_bound {X H : ℕ} (hX : 3 ≤ X) (hH : H ≤ X) :
    Real.log (2*(X:ℝ)+H) ≤ 2 * Real.log (X:ℝ) := by
  have hX3 : (3:ℝ) ≤ X := by exact_mod_cast hX
  have hHle : (H:ℝ) ≤ X := by exact_mod_cast hH
  have hX0 : (0:ℝ)<X := by linarith
  calc
    _ ≤ Real.log ((X:ℝ)^2) := Real.log_le_log (by positivity) (by nlinarith)
    _ = _ := by rw [Real.log_pow]; norm_num

theorem power_log_identity {x L : ℝ} (hx : 0<x) (rho b : ℝ) :
    x^rho * x^b * L / x = L / x^(1-rho-b) := by
  rw [div_eq_mul_inv L, ← Real.rpow_neg hx.le]
  have he : -(1-rho-b) = rho+b-1 := by ring
  rw [he, Real.rpow_sub hx, Real.rpow_add hx, Real.rpow_one]
  ring

theorem primepower_shift_tail_log_decay (H : ℕ → ℕ) {rho D B : ℝ}
    (hrhohalf : rho < 1/2) (hD : 0 < D)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ) ≤ D*(Real.log (X:ℝ))^B) (A : ℕ) :
    Tendsto (fun X : ℕ =>
      ((powerModulus rho X:ℝ) *
        (2*Real.sqrt (2*(X:ℝ))*Real.log (2*(X:ℝ)) +
          2*(H X:ℝ)*Real.log (2*(X:ℝ)+H X)) / X) *
        (Real.log (X:ℝ))^A) atTop (nhds 0) := by
  have hlim1 : Tendsto (fun X : ℕ =>
      (Real.log (X:ℝ))^((A:ℝ)+1) / (X:ℝ)^(1/2-rho)) atTop (nhds 0) := by
    exact ((isLittleO_log_rpow_rpow_atTop ((A:ℝ)+1) (by linarith)).tendsto_div_nhds_zero
      ).comp tendsto_natCast_atTop_atTop
  have hlim2 : Tendsto (fun X : ℕ =>
      (Real.log (X:ℝ))^(B+(A:ℝ)+1) / (X:ℝ)^(1-rho)) atTop (nhds 0) := by
    exact ((isLittleO_log_rpow_rpow_atTop (B+(A:ℝ)+1) (by linarith)).tendsto_div_nhds_zero
      ).comp tendsto_natCast_atTop_atTop
  have hlim := (hlim1.const_mul 8).add (hlim2.const_mul (4*D))
  simp only [mul_zero, add_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 3] with X hX
    have hlog1 : 0 ≤ Real.log (2*(X:ℝ)) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X by omega))
    have hlog2 : 0 ≤ Real.log (2*(X:ℝ)+H X) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X+H X by omega))
    have hlog : 0 ≤ Real.log (X:ℝ) := (log_pos_of_two_le (by omega)).le
    positivity
  · filter_upwards [hH, polylog_shift_eventually_le H hH,
      eventually_ge_atTop 3] with X hHX hHX' hX
    have hX0 : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
    have hL : 0<Real.log (X:ℝ) := log_pos_of_two_le (by omega)
    have hlog1 : Real.log (2*(X:ℝ)) ≤ 2*Real.log (X:ℝ) := by
      simpa only [Nat.cast_zero, add_zero] using log_shift_bound (H:=0) hX (Nat.zero_le X)
    have hlog2 := log_shift_bound hX hHX'
    have hlog1' : 0 ≤ Real.log (2*(X:ℝ)) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X by omega))
    have hlog2' : 0 ≤ Real.log (2*(X:ℝ)+H X) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X+H X by omega))
    have hroot : Real.sqrt (2*(X:ℝ)) ≤ 2*(X:ℝ)^(1/2:ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply (Real.sqrt_le_left (by positivity)).mpr
      nlinarith [Real.sq_sqrt hX0.le]
    have hQ : (powerModulus rho X:ℝ) ≤ (X:ℝ)^rho :=
      Nat.floor_le (Real.rpow_nonneg hX0.le _)
    calc
      _ ≤ ((X:ℝ)^rho *
          (2*(2*(X:ℝ)^(1/2:ℝ))*(2*Real.log (X:ℝ)) +
            2*(D*(Real.log (X:ℝ))^B)*(2*Real.log (X:ℝ))) / X) *
          (Real.log (X:ℝ))^A := by gcongr
      _ = 8*((Real.log (X:ℝ))^((A:ℝ)+1)/(X:ℝ)^(1/2-rho)) +
          (4*D)*((Real.log (X:ℝ))^(B+(A:ℝ)+1)/(X:ℝ)^(1-rho)) := by
        have hLA : (Real.log (X:ℝ))^((A:ℝ)+1) = (Real.log (X:ℝ))^A * Real.log (X:ℝ) := by
          rw [Real.rpow_add hL, Real.rpow_natCast, Real.rpow_one]
        have hLBA : (Real.log (X:ℝ))^(B+(A:ℝ)+1) =
            (Real.log (X:ℝ))^B * (Real.log (X:ℝ))^A * Real.log (X:ℝ) := by
          rw [Real.rpow_add hL, Real.rpow_add hL, Real.rpow_natCast, Real.rpow_one]
        rw [hLA, hLBA]
        have h1 := power_log_identity (L:=Real.log (X:ℝ)) hX0 rho (1/2)
        have h2 := power_log_identity (L:=Real.log (X:ℝ)) hX0 rho 0
        simp only [Real.rpow_zero, mul_one, sub_zero] at h2
        have hex : (1:ℝ)-rho-1/2 = 1/2-rho := by ring
        rw [hex] at h1
        calc
          _ = 8 * (Real.log (X:ℝ))^A *
                ((X:ℝ)^rho*(X:ℝ)^(1/2:ℝ)*Real.log (X:ℝ)/(X:ℝ)) +
              (4*D)*(Real.log (X:ℝ))^B*(Real.log (X:ℝ))^A *
                ((X:ℝ)^rho*Real.log (X:ℝ)/(X:ℝ)) := by ring
          _ = _ := by rw [h1,h2]; ring

theorem marked_error_sum_log_decay (hBV : BombieriVinogradov) (H : ℕ → ℕ)
    {rho D B : ℝ} (hrho : 0 ≤ rho) (hrhohalf : rho < 1/2) (hD : 0 < D)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ) ≤ D*(Real.log (X:ℝ))^B) (A : ℕ) :
    Tendsto (fun X : ℕ =>
      ((∑ q ∈ Finset.Icc 1 (powerModulus rho X), (markedError X (H X) q : ℝ)) / X) *
        (Real.log (X:ℝ))^A) atTop (nhds 0) := by
  have h1 := endpoint_sum_log_decay hBV hrho hrhohalf (k:=1) (by norm_num) A
  have h2 := endpoint_sum_log_decay hBV hrho hrhohalf (k:=2) (by norm_num) A
  have htail := primepower_shift_tail_log_decay H hrhohalf hD hH A
  have hlim := (h2.add h1).add htail
  simp only [add_zero, one_mul] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hL := (log_pos_of_two_le hX).le
    positivity
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hh := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (sum_markedError_le_endpointErrors (X:=X) (by omega)
        (H X) (powerModulus rho X)) (show (0:ℝ)≤X by positivity))
      (pow_nonneg (log_pos_of_two_le hX).le A)
    convert hh using 1
    ring

theorem harmonic_nonneg_real (Q : ℕ) : 0 ≤ (harmonic Q : ℝ) := by
  simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  positivity

theorem harmonic_le_twice_log {Q X : ℕ} (hQX : Q ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    (harmonic Q : ℝ) ≤ 2 * Real.log (X:ℝ) := by
  have hmono : (harmonic Q : ℝ) ≤ (harmonic X : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hQX) (by intros; positivity)
  have hh := harmonic_le_one_add_log X
  linarith

theorem powerModulus_le {rho : ℝ} (hrho : rho ≤ 1) {X : ℕ} (hX : 1 ≤ X) :
    powerModulus rho X ≤ X := by
  have hX1 : (1:ℝ) ≤ X := by exact_mod_cast hX
  have hh := Real.rpow_le_rpow_of_exponent_le hX1 hrho
  rw [Real.rpow_one] at hh
  have hfloor := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg X) rho)
  exact_mod_cast hfloor.trans hh

theorem marked_error_weight_budget (K : ℕ) {X H Q : ℕ}
    (hX : 3 ≤ X) (hH : H ≤ X) (hQ : Q ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    3*Real.log (2*(X:ℝ)+H)*(harmonic Q:ℝ)^(K^2) +
      (harmonic Q:ℝ)^(2*K^2) ≤
    (6*(2:ℝ)^(K^2)+(2:ℝ)^(2*K^2)) * (Real.log (X:ℝ))^(2*K^2+1) := by
  have hL0 : 0 ≤ Real.log (X:ℝ) := by linarith
  have hhar := harmonic_le_twice_log hQ hL
  have hlog := log_shift_bound hX hH
  have hpow1 : (Real.log (X:ℝ))^(K^2+1) ≤ (Real.log (X:ℝ))^(2*K^2+1) :=
    pow_le_pow_right₀ hL (by omega)
  have hpow2 : (Real.log (X:ℝ))^(2*K^2) ≤ (Real.log (X:ℝ))^(2*K^2+1) :=
    pow_le_pow_right₀ hL (by omega)
  calc
    _ ≤ (3*(2*Real.log (X:ℝ)))*(2*Real.log (X:ℝ))^(K^2) +
        (2*Real.log (X:ℝ))^(2*K^2) := by
      apply add_le_add
      · apply mul_le_mul
        · linarith
        · exact pow_le_pow_left₀ (harmonic_nonneg_real Q) hhar _
        · exact pow_nonneg (harmonic_nonneg_real Q) _
        · positivity
      · exact pow_le_pow_left₀ (harmonic_nonneg_real Q) hhar _
    _ = 6*(2:ℝ)^(K^2)*(Real.log (X:ℝ))^(K^2+1) +
        (2:ℝ)^(2*K^2)*(Real.log (X:ℝ))^(2*K^2) := by rw [mul_pow, mul_pow, pow_succ]; ring
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hpow1 (show (0:ℝ)≤6*2^(K^2) by positivity),
      mul_le_mul_of_nonneg_left hpow2 (show (0:ℝ)≤2^(2*K^2) by positivity)]

noncomputable def weightedErrorSum (K X H Q : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 Q, if Squarefree q then (K:ℝ)^q.primeFactors.card *
    (markedError X H q : ℝ) else 0

theorem weightedErrorSum_nonneg (K X H Q : ℕ) : 0 ≤ weightedErrorSum K X H Q := by
  classical
  apply Finset.sum_nonneg
  intro q _
  split_ifs <;> positivity

theorem weightedErrorSum_sq_bound (K : ℕ) {X H Q : ℕ}
    (hX : 3 ≤ X) (hH : H ≤ X) (hQ : Q ≤ X) (hL : 1 ≤ Real.log (X:ℝ)) :
    (weightedErrorSum K X H Q)^2 ≤
      (∑ q ∈ Finset.Icc 1 Q, (markedError X H q : ℝ)) * X *
      ((6*(2:ℝ)^(K^2)+(2:ℝ)^(2*K^2)) * (Real.log (X:ℝ))^(2*K^2+1)) := by
  have hlog : 0 ≤ 3 * Real.log (2*(X:ℝ)+H) := by
    have hh : 0 ≤ Real.log (2*(X:ℝ)+H) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2*X+H by omega))
    positivity
  apply (weighted_error_square_bound K Q (fun q => (markedError X H q : ℝ))
    (fun q => NNReal.coe_nonneg _) (Nat.cast_nonneg X) hlog ?_).trans
  · apply mul_le_mul_of_nonneg_left (marked_error_weight_budget K hX hH hQ hL)
    positivity
  · intro q hq hsq
    obtain ⟨hq1,hqQ⟩ := Finset.mem_Icc.mp hq
    exact markedError_trivial (by omega) hq1 (hqQ.trans hQ) hsq

theorem weightedErrorSum_log_decay (hBV : BombieriVinogradov) (K : ℕ) (H : ℕ → ℕ)
    {rho D B : ℝ} (hrho : 0 ≤ rho) (hrhohalf : rho < 1/2) (hD : 0 < D)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ) ≤ D*(Real.log (X:ℝ))^B) (A : ℕ) :
    Tendsto (fun X : ℕ => (weightedErrorSum K X (H X) (powerModulus rho X) / X) *
      (Real.log (X:ℝ))^A) atTop (nhds 0) := by
  let c : ℝ := 6*(2:ℝ)^(K^2)+(2:ℝ)^(2*K^2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hlim := (marked_error_sum_log_decay hBV H hrho hrhohalf hD hH
    (2*K^2+1+2*A)).const_mul c
  simp only [mul_zero] at hlim
  have hsqrt := hlim.sqrt
  simp only [Real.sqrt_zero] at hsqrt
  have hLlim : Tendsto (fun X : ℕ => Real.log (X:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' _ _ hsqrt
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact mul_nonneg (div_nonneg (weightedErrorSum_nonneg _ _ _ _) (Nat.cast_nonneg _))
      (pow_nonneg (log_pos_of_two_le hX).le _)
  · filter_upwards [eventually_ge_atTop 3, polylog_shift_eventually_le H hH,
      hLlim.eventually (eventually_ge_atTop 1)] with X hX hHX hLX
    have hX0 : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
    have hs := weightedErrorSum_sq_bound K hX hHX
      (powerModulus_le (by linarith : rho ≤ 1) (by omega)) hLX
    have hh : ((weightedErrorSum K X (H X) (powerModulus rho X) / X) *
        (Real.log (X:ℝ))^A)^2 ≤
        c * (((∑ q ∈ Finset.Icc 1 (powerModulus rho X), (markedError X (H X) q : ℝ)) / X) *
          (Real.log (X:ℝ))^(2*K^2+1+2*A)) := by
      have hm := mul_le_mul_of_nonneg_right hs
        (show 0 ≤ (Real.log (X:ℝ))^(2*A)/(X:ℝ)^2 by positivity)
      dsimp only [c]
      convert hm using 1
      · rw [mul_pow, div_pow, ← pow_mul, Nat.mul_comm A 2]
        ring
      · rw [pow_add]
        field_simp
    have hnonneg : 0 ≤ (weightedErrorSum K X (H X) (powerModulus rho X) / X) *
        (Real.log (X:ℝ))^A := by
      apply mul_nonneg (div_nonneg (weightedErrorSum_nonneg _ _ _ _) hX0.le)
      exact pow_nonneg (by linarith) _
    have hh' := Real.sqrt_le_sqrt hh
    simpa only [Real.sqrt_sq hnonneg] using hh'

theorem marked_arithmetic_error_log_decay (hBV : BombieriVinogradov)
    {n : ℕ} {F : (Fin n → ℝ) → ℝ} {rho M D B : ℝ}
    (hrho : 0 ≤ rho) (hrhohalf : rho < 1/2) (hbudget : HasBudget F rho)
    (hM : 0 ≤ M) (hbound : ∀ v, (∀ i, 0 ≤ v i) → |F v| ≤ M)
    (H a : ℕ → ℕ) (b : ℕ → Fin n → ℕ) (hD : 0 < D)
    (hH : ∀ᶠ X : ℕ in atTop, (H X:ℝ) ≤ D*(Real.log (X:ℝ))^B)
    (ha : ∀ X, a X ≤ H X) (A : ℕ) :
    Tendsto (fun X : ℕ =>
      |average X (fun m => divisorSum X F m (b X) * theta (m + a X)) -
        markedDensitySum X F rho (b X) (a X)| * (Real.log (X:ℝ))^A)
      atTop (nhds 0) := by
  have hlim := (weightedErrorSum_log_decay hBV (2^n) H hrho hrhohalf hD hH A).const_mul M
  simp only [mul_zero] at hlim
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop 2] with X hX
    exact mul_nonneg (abs_nonneg _) (pow_nonneg (log_pos_of_two_le hX).le _)
  · filter_upwards [eventually_ge_atTop 2] with X hX
    have hX0 : (0:ℝ) < X := by exact_mod_cast (show 0<X by omega)
    have hY : ⌊Real.exp (rho * Real.log (X:ℝ))⌋₊ = powerModulus rho X := by
      unfold powerModulus
      rw [Real.rpow_def_of_pos hX0, mul_comm rho]
    have he := marked_arithmetic_error hX (ha X) (by linarith : rho ≤ 1)
      hbudget hM hbound (b X)
    rw [hY] at he
    have he' : |average X (fun m => divisorSum X F m (b X) * theta (m+a X)) -
        markedDensitySum X F rho (b X) (a X)| ≤
        M / (X:ℝ) * weightedErrorSum (2^n) X (H X) (powerModulus rho X) := by
      simpa only [weightedErrorSum, Nat.cast_pow] using he
    have hh := mul_le_mul_of_nonneg_right he' (pow_nonneg (log_pos_of_two_le hX).le A)
    convert hh using 1
    ring

end LargePrimeGaps

end OAI
