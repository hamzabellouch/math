import OAI.NumberTheory.CubicMoment.Estimates.ExceptionalRows
import OAI.NumberTheory.CubicMoment.Estimates.GramLargeValues

namespace OAI

/-! Repeated short factors in the final Gram estimate. -/
noncomputable section
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def shortRepeatedSupport (m : ℕ) (X : ℝ) : Finset Eisenstein :=
  orderedConvolutionSupport (fun _ : Fin m => primaryElementBall X)

def shortRepeatedCoefficient (m : ℕ) (X : ℝ) (A : EisensteinArithmeticFunction)
    (u : Eisenstein → ℂ) : Eisenstein → ℂ :=
  orderedConvolution (fun _ : Fin m => primaryElementBall X)
    (fun _ n => ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*u n)

lemma shortRepeatedSupport_mem {m : ℕ} {X : ℝ} {b : Eisenstein}
    (hb : b ∈ shortRepeatedSupport m X) : primary b ∧ norm b ≤ X^m := by
  refine ⟨orderedPrimarySupport_primary _ (fun _ _ hn =>
    (mem_primaryElementBall.mp hn).1) hb,?_⟩
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp hb
  rw [norm_finset_prod]
  calc
    _ ≤ ∏ _i : Fin m, X := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      (fun i _ => (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp hf i)).2)
    _ = _ := by simp

lemma shortRepeated_polynomial (m : ℕ) (X : ℝ) (A : EisensteinArithmeticFunction)
    (u : Eisenstein → ℂ) {a : Eisenstein} (ha : primary a) :
    (∑ b ∈ shortRepeatedSupport m X,
      shortRepeatedCoefficient m X A u b*cubicSymbol a b) =
      (primaryIdealPolynomial X A (fun n => u n*cubicSymbol a n))^m := by
  rw [shortRepeatedSupport,shortRepeatedCoefficient,← primeCubicProductPolynomial_eq _ _ ha]
  simp only [primeCubicProductPolynomial,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    primaryIdealPolynomial_eq_elements,mul_assoc]

/-- The actual coefficient energy has only an arbitrarily small power loss;
all logarithmic weights and repeated factorizations are included. -/
theorem shortRepeated_energy (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F X : ℝ) (A : EisensteinArithmeticFunction)
      (u : Eisenstein → ℂ), ShortArithmeticFactor F A → 1 ≤ X →
      (∀ n ∈ primaryElementBall X, ‖u n‖ ≤ 1) →
      (∑ b ∈ shortRepeatedSupport m X, ‖shortRepeatedCoefficient m X A u b‖^2) ≤
        C*(X^m)^(1+ε) := by
  obtain ⟨C,hC,henergy⟩ := primary_orderedConvolution_energy (ι := Fin m)
    (show 0 < ε/2 by positivity)
  obtain ⟨B,hB,hlog⟩ := one_add_log_small_power (show 0 < ε/4 by positivity)
  refine ⟨C*(18*B^2)^m,by positivity,?_⟩
  intro F X A u hA hX hu
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hL : 1 ≤ X^m := one_le_pow₀ hX
  have htuple (f : Fin m → Eisenstein)
      (hf : f ∈ Fintype.piFinset (fun _ : Fin m => primaryElementBall X)) :
      norm (∏ i, f i) ≤ X^m := by
    rw [norm_finset_prod]
    calc
      _ ≤ ∏ _i : Fin m, X := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => (mem_primaryElementBall.mp (Fintype.mem_piFinset.mp hf i)).2)
      _ = _ := by simp
  have he := henergy (fun _ : Fin m => primaryElementBall X)
    (fun _ n => ((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*u n)
    (fun _ _ hn => (mem_primaryElementBall.mp hn).1) (X^m) hL htuple
  have hfactor := shortArithmeticFactor_energy hA hX u hu
  have hlog2 : (1+Real.log X)^2 ≤ B^2*X^(ε/2) := by
    have h := pow_le_pow_left₀ (by linarith [Real.log_nonneg hX]) (hlog X hX) 2
    rw [mul_pow,← Real.rpow_mul_natCast hXp.le] at h
    convert h using 1
    ring_nf
  have hfactor' : (∑ n ∈ primaryElementBall X,
      ‖((MvPowerSeries.coeff (idealExponentOf n) A:ℝ):ℂ)*u n‖^2) ≤
      (18*B^2)*X^(1+ε/2) := by
    apply hfactor.trans
    calc
      _ ≤ 18*X*(B^2*X^(ε/2)) := mul_le_mul_of_nonneg_left hlog2 (by positivity)
      _ = _ := by rw [Real.rpow_add hXp,Real.rpow_one]; ring
  apply he.trans
  simp only [primeConvolutionEnergy,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  calc
    _ ≤ C*(X^m)^(ε/2)*((18*B^2)*X^(1+ε/2))^m :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hfactor' m) (by positivity)
    _ = (C*(18*B^2)^m)*(X^m)^(1+ε) := by
      have hp : (X^(1+ε/2))^m = (X^m)^(1+ε/2) := by
        rw [← Real.rpow_mul_natCast hXp.le,← Real.rpow_natCast_mul hXp.le]
        congr 1
        ring
      have heps : (X^m)^(ε/2)*(X^m)^(1+ε/2) = (X^m)^(1+ε) := by
        rw [← Real.rpow_add (pow_pos hXp m)]
        congr 1
        ring
      rw [mul_pow,hp]
      calc
        _ = (C*(18*B^2)^m)*((X^m)^(ε/2)*(X^m)^(1+ε/2)) := by ring
        _ = _ := by rw [heps]

/-- Applying the proved Gram theorem to the literal copied factor gives
an exact finite large-value inequality with its true coefficient energy. -/
theorem shortRepeated_gram_large_values (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C D E : ℝ, 0 < C ∧ 0 < D ∧ 0 < E ∧
      ∀ (F X P V : ℝ) (A : EisensteinArithmeticFunction) (u : Eisenstein → ℂ)
        (Q : Finset Eisenstein), ShortArithmeticFactor F A → 1 ≤ X → 1 ≤ P → 0 < V →
        (∀ n ∈ primaryElementBall X, ‖u n‖ ≤ 1) →
        (∀ p ∈ Q, gramDyad P p) →
        (∀ p ∈ Q, V ≤ ‖primaryIdealPolynomial X A
          (fun n => u n*cubicSymbol p n)‖^m) →
        (Q.card:ℝ)*V^4 ≤ 2*(E*(X^m)^(1+ε))*(D*(X^m))*V^2+
          (E*(X^m)^(1+ε))^2*
            (C*(P*(X^m))^ε*(X^m)*(P+(P^3/(X^m))^(2/3:ℝ))) := by
  obtain ⟨C,D,hC,hD,hgram⟩ := cubic_gram_large_value_count hε
  obtain ⟨E,hE,henergy⟩ := shortRepeated_energy m hε
  refine ⟨C,D,E,hC,hD,hE,?_⟩
  intro F X P V A u Q hA hX hP hV hu hQ hlarge
  apply hgram Q (shortRepeatedSupport m X) P (X^m) V (E*(X^m)^(1+ε))
    (shortRepeatedCoefficient m X A u) hP (one_le_pow₀ hX) hV (by positivity) hQ
    (fun _ hb => shortRepeatedSupport_mem hb) (henergy F X A u hA hX hu)
  intro p hp
  rw [shortRepeated_polynomial m X A u (hQ p hp).1,norm_pow]
  exact hlarge p hp


lemma HasPowerExponent.const_mul {Y f : ℕ → ℝ} {a C : ℝ}
    (hf : HasPowerExponent Y f a) (hY : Tendsto Y atTop atTop) (hC : 0 < C)
    (hfp : ∀ᶠ j in atTop, 0 < f j) :
    HasPowerExponent Y (fun j => C*f j) a := by
  simpa only [zero_add] using (HasPowerExponent.const hY C).mul hf
    (Eventually.of_forall (fun _ => hC)) hfp

lemma HasPowerExponent.div {Y f g : ℕ → ℝ} {a b : ℝ}
    (hf : HasPowerExponent Y f a) (hg : HasPowerExponent Y g b)
    (hfp : ∀ᶠ j in atTop, 0 < f j) (hgp : ∀ᶠ j in atTop, 0 < g j) :
    HasPowerExponent Y (fun j => f j/g j) (a-b) := by
  apply (hf.sub hg).congr'
  filter_upwards [hfp,hgp] with j hfj hgj
  rw [Real.log_div hfj.ne' hgj.ne',sub_div]

private lemma remove_gram_loss {a b c : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ b+ε*c) : a ≤ b := by
  by_contra hab
  have hgap : 0 < a-b := sub_pos.mpr (lt_of_not_ge hab)
  let ε : ℝ := (a-b)/(2*(|c|+1))
  have hε : 0 < ε := div_pos hgap (by positivity)
  have he : ε*(2*(|c|+1)) = a-b := div_mul_cancel₀ _ (by positivity)
  have hc := mul_le_mul_of_nonneg_left (le_abs_self c) hε.le
  have hb := h ε hε
  nlinarith [mul_nonneg hε.le (abs_nonneg c)]

/-- The root-free Gram inequality has a strict limiting exponent gap.
This takes limits of the actual finite inequality, including the energy loss. -/
theorem gram_large_values_exponent {Y R V N L : ℕ → ℝ} {r v z : ℝ}
    (hY : Tendsto Y atTop atTop) (hz : 0 ≤ z)
    (hRp : ∀ᶠ j in atTop, 0 < R j) (hVp : ∀ᶠ j in atTop, 0 < V j)
    (hNp : ∀ᶠ j in atTop, 0 < N j) (hLp : ∀ᶠ j in atTop, 0 < L j)
    (hR : HasPowerExponent Y R r) (hV : HasPowerExponent Y V v)
    (hN : HasPowerExponent Y N 1) (hL : HasPowerExponent Y L z)
    (hgram : ∀ ε : ℝ, 0 < ε → ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ᶠ j in atTop, R j*(V j)^4 ≤
        A*(L j)^(2+ε)*(V j)^2+
        B*(L j)^(3+2*ε)*(N j*L j)^ε*
          (N j+((N j)^3/L j)^(2/3:ℝ))) :
    r+4*v ≤ max (2*z+2*v) (3*z+max 1 (2-2*z/3)) := by
  apply remove_gram_loss (c := 1+3*z)
  intro ε hε
  obtain ⟨A,B,hA,hB,hbound⟩ := hgram ε hε
  have hLpow (t : ℝ) : ∀ᶠ j in atTop, 0 < (L j)^t := by
    filter_upwards [hLp] with j hj using Real.rpow_pos_of_pos hj _
  have hV2p : ∀ᶠ j in atTop, 0 < (V j)^2 := by
    filter_upwards [hVp] with j hj using sq_pos_of_pos hj
  have hV4p : ∀ᶠ j in atTop, 0 < (V j)^4 := by
    filter_upwards [hVp] with j hj using pow_pos hj _
  have hNLp : ∀ᶠ j in atTop, 0 < N j*L j := by
    filter_upwards [hNp,hLp] with j hn hl using mul_pos hn hl
  have hdualP : ∀ᶠ j in atTop, 0 < ((N j)^3/L j)^(2/3:ℝ) := by
    filter_upwards [hNp,hLp] with j hn hl
    exact Real.rpow_pos_of_pos (div_pos (pow_pos hn _) hl) _
  have hinnerP : ∀ᶠ j in atTop, 0 < N j+((N j)^3/L j)^(2/3:ℝ) := by
    filter_upwards [hNp,hdualP] with j hn hd using add_pos hn hd
  have hinner := hN.add (((hN.natPow 3).div hL
    (by filter_upwards [hNp] with j hn using pow_pos hn _) hLp).rpow
      (by filter_upwards [hNp,hLp] with j hn hl using div_pos (pow_pos hn _) hl) (2/3:ℝ))
        hY hNp hdualP
  have hfirst := ((hL.rpow hLp (2+ε)).mul (hV.natPow 2)
    (hLpow _) hV2p).const_mul hY hA
      (by filter_upwards [hLpow (2+ε),hV2p] with j hl hv using mul_pos hl hv)
  have hprod := ((hL.rpow hLp (3+2*ε)).mul ((hN.mul hL hNp hLp).rpow hNLp ε)
    (hLpow _) (by filter_upwards [hNLp] with j hn using Real.rpow_pos_of_pos hn _))
  have hprodP : ∀ᶠ j in atTop, 0 < (L j)^(3+2*ε)*(N j*L j)^ε := by
    filter_upwards [hLp,hNLp] with j hl hn
    exact mul_pos (Real.rpow_pos_of_pos hl _) (Real.rpow_pos_of_pos hn _)
  have hsecond := (hprod.mul hinner hprodP hinnerP).const_mul hY hB
    (by filter_upwards [hprodP,hinnerP] with j hp hi using mul_pos hp hi)
  have hright := hfirst.add hsecond hY
    (by filter_upwards [hLp,hVp] with j hl hv using
      mul_pos hA (mul_pos (Real.rpow_pos_of_pos hl _) (sq_pos_of_pos hv)))
    (by filter_upwards [hprodP,hinnerP] with j hp hi using mul_pos hB (mul_pos hp hi))
  have h := (hR.mul (hV.natPow 4) hRp hV4p).mono hright hY
    (by filter_upwards [hRp,hV4p] with j hr hv using mul_pos hr hv)
      (by filter_upwards [hbound] with j hj; simpa only [mul_assoc] using hj)
  have hn : (2/3:ℝ)*((3:ℝ)*1-z) = 2-2*z/3 := by norm_num; ring
  simp only [Nat.cast_ofNat,hn] at h
  have h₁ : (2+ε)*z+2*v ≤ max (2*z+2*v) (3*z+max 1 (2-2*z/3))+ε*(1+3*z) := by
    nlinarith [le_max_left (2*z+2*v) (3*z+max 1 (2-2*z/3)),mul_nonneg hε.le hz]
  have h₂ : (3+2*ε)*z+ε*(1+z)+max 1 (2-2*z/3) ≤
      max (2*z+2*v) (3*z+max 1 (2-2*z/3))+ε*(1+3*z) := by
    nlinarith [le_max_right (2*z+2*v) (3*z+max 1 (2-2*z/3))]
  exact h.trans (max_le h₁ h₂)


private lemma gram_energy_group {L : ℝ} (hL : 0 < L) (ε E C D P V T : ℝ) :
    2*(E*L^(1+ε))*(D*L)*V^2+(E*L^(1+ε))^2*(C*(P*L)^ε*L*T) =
      (2*E*D)*L^(2+ε)*V^2+(E^2*C)*L^(3+2*ε)*(P*L)^ε*T := by
  have h₁ : L^(1+ε)*L = L^(2+ε) := by
    nth_rw 2 [← Real.rpow_one L]
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have h₂ : (L^(1+ε))^2*L = L^(3+2*ε) := by
    rw [← Real.rpow_mul_natCast hL.le]
    nth_rw 2 [← Real.rpow_one L]
    rw [← Real.rpow_add hL]
    congr 1
    ring
  calc
    _ = (2*E*D)*(L^(1+ε)*L)*V^2+(E^2*C)*((L^(1+ε))^2*L)*(P*L)^ε*T := by ring
    _ = _ := by rw [h₁,h₂]

/-- A fixed number of copies of an actual short factor satisfies the
limiting Gram inequality; no coefficient-energy exponent is assumed. -/
theorem ShortFactorFamily.copied_rows_gram_exponent {ι : Type*}
    (F : ShortFactorFamily ι) (i : ι) (m : ℕ)
    {Y N : ℕ → ℝ} (P : ℕ → Finset Eisenstein) (B : ℕ → ℝ)
    {r a v : ℝ} (hY : Tendsto Y atTop atTop) (hN : ∀ j, 1 ≤ N j)
    (hP : ∀ j, ∀ p ∈ P j, gramDyad (N j) p)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j, 0 < B j)
    (hrow : ∀ j, ∀ p ∈ P j, B j ≤ ‖F.cubicValue j i p‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hNexp : HasPowerExponent Y N 1)
    (hXexp : HasPowerExponent Y (fun j => F.length j i) a)
    (hBexp : HasPowerExponent Y B v) :
    r+4*((m:ℝ)*v) ≤ max (2*((m:ℝ)*a)+2*((m:ℝ)*v))
      (3*((m:ℝ)*a)+max 1 (2-2*((m:ℝ)*a)/3)) := by
  have hap : 0 ≤ a := (HasPowerExponent.const hY 1).mono hXexp hY
    (Eventually.of_forall (fun _ => zero_lt_one))
    (Eventually.of_forall (fun j => F.length_ge_one j i))
  apply gram_large_values_exponent hY (mul_nonneg (Nat.cast_nonneg _) hap)
    (Eventually.of_forall (fun j => Nat.cast_pos.mpr (Finset.card_pos.mpr (hPne j))))
    (Eventually.of_forall (fun j => pow_pos (hB j) m))
    (Eventually.of_forall (fun j => zero_lt_one.trans_le (hN j)))
    (Eventually.of_forall (fun j => pow_pos (zero_lt_one.trans_le (F.length_ge_one j i)) m))
    hRexp (hBexp.natPow m) hNexp (hXexp.natPow m)
  intro ε hε
  obtain ⟨C,D,E,hC,hD,hE,hgram⟩ := shortRepeated_gram_large_values m hε
  refine ⟨2*E*D,E^2*C,by positivity,by positivity,Eventually.of_forall (fun j => ?_)⟩
  have h := hgram (F.cutoff j) (F.length j i) (N j) ((B j)^m)
    (F.coefficient j i) (F.twist j i) (P j) (F.factor_spec j i)
    (F.length_ge_one j i) (hN j) (pow_pos (hB j) m) (F.twist_bound j i) (hP j)
    (fun p hp => pow_le_pow_left₀ (hB j).le (hrow j p hp) m)
  rwa [gram_energy_group (pow_pos (zero_lt_one.trans_le (F.length_ge_one j i)) m)] at h

/-- The saturated first configuration cannot contain a positive short
factor with a fixed number of copies in the interior Gram range. -/
theorem ShortFactorFamily.copied_rows_gram_contradiction {ι : Type*}
    (F : ShortFactorFamily ι) (i : ι) (m : ℕ)
    {Y N : ℕ → ℝ} (P : ℕ → Finset Eisenstein) (B : ℕ → ℝ)
    {a : ℝ} (hY : Tendsto Y atTop atTop) (hN : ∀ j, 1 ≤ N j)
    (hP : ∀ j, ∀ p ∈ P j, gramDyad (N j) p)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j, 0 < B j)
    (hrow : ∀ j, ∀ p ∈ P j, B j ≤ ‖F.cubicValue j i p‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) (2/3))
    (hNexp : HasPowerExponent Y N 1)
    (hXexp : HasPowerExponent Y (fun j => F.length j i) a)
    (hBexp : HasPowerExponent Y B (5*a/6))
    (hz₀ : 4/3 < (m:ℝ)*a) (hz₁ : (m:ℝ)*a < 2) : False := by
  have h := F.copied_rows_gram_exponent i m P B hY hN hP hPne hB hrow
    hRexp hNexp hXexp hBexp
  let z : ℝ := (m:ℝ)*a
  have hv : (m:ℝ)*(5*a/6) = 5*z/6 := by dsimp [z]; ring
  change 2/3+4*((m:ℝ)*(5*a/6)) ≤ max (2*z+2*((m:ℝ)*(5*a/6)))
    (3*z+max 1 (2-2*z/3)) at h
  rw [hv] at h
  have hgap : max (2*z+2*(5*z/6)) (3*z+max 1 (2-2*z/3)) < 2/3+4*(5*z/6) := by
    apply max_lt
    · change z < 2 at hz₁
      linarith
    · rcases le_total (1:ℝ) (2-2*z/3) with hcase | hcase
      · rw [max_eq_right hcase]
        change 4/3 < z at hz₀
        linarith
      · rw [max_eq_left hcase]
        change 4/3 < z at hz₀
        linarith
  exact not_lt_of_ge h hgap

private lemma exists_positive_short_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i < 1) (hsum : ∑ i, a i = 1) :
    ∃ i, 0 < a i ∧ a i ≤ 1/2 := by
  have hex : ∃ j, 0 < a j := by
    by_contra! h
    have hn := Finset.sum_nonpos (s := Finset.univ) (fun i _ => h i)
    linarith
  obtain ⟨j,hj⟩ := hex
  by_cases hjhalf : a j ≤ 1/2
  · exact ⟨j,hj,hjhalf⟩
  have hrest := Finset.sum_erase_add Finset.univ a (Finset.mem_univ j)
  rw [hsum] at hrest
  have hrestpos : 0 < ∑ i ∈ Finset.univ.erase j, a i := by linarith [(ha j).2]
  obtain ⟨i,hi,hipos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun i _ => (ha i).1)).mp hrestpos
  have hile := Finset.single_le_sum (fun i _ => (ha i).1) hi
  exact ⟨i,hipos,by linarith⟩

/-- The complete short-factor contradiction in the first exceptional
configuration. Both the rigidity and the final Gram bound apply to the
literal polynomials defined by the given arithmetic family. -/
theorem ShortFactorFamily.first_rows_contradiction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : ShortFactorFamily ι) {Y N : ℕ → ℝ}
    (P : ℕ → Finset Eisenstein) (B : ℕ → ι → ℝ) {a v : ι → ℝ} {r : ℝ}
    (hY : Tendsto Y atTop atTop) (hN : ∀ j, 1 ≤ N j)
    (hP : ∀ j, ∀ p ∈ P j, gramDyad (N j) p)
    (hPne : ∀ j, (P j).Nonempty) (hB : ∀ j i, 0 < B j i)
    (hrow : ∀ j, ∀ p ∈ P j, ∀ i, B j i ≤ ‖F.cubicValue j i p‖)
    (hRexp : HasPowerExponent Y (fun j => ((P j).card:ℝ)) r)
    (hNexp : HasPowerExponent Y N 1)
    (hXexp : ∀ i, HasPowerExponent Y (fun j => F.length j i) (a i))
    (hBexp : ∀ i, HasPowerExponent Y (fun j => B j i) (v i))
    (ha : ∀ i, a i < 1) (hsum : ∑ i, a i = 1)
    (hlarge : 7/3-2*(∑ i, v i) ≤ r) : False := by
  have hNpos : ∀ᶠ j in atTop, 0 < N j :=
    Eventually.of_forall (fun j => zero_lt_one.trans_le (hN j))
  have hN2exp := hNexp.const_mul hY (by norm_num : (0:ℝ) < 2) hNpos
  obtain ⟨hv,hr⟩ := F.cubic_rows_rigidity (N := fun j => 2*N j) P B hY
    (fun j => by linarith [hN j])
    (fun j p hp => ⟨(hP j p hp).1,(hP j p hp).2.1,(hP j p hp).2.2.2.le⟩)
    hPne hB hrow hRexp hN2exp hXexp hBexp ha hsum hlarge
  obtain ⟨i,hi,hihalf⟩ := exists_positive_short_factor a
    (fun i => ⟨F.length_exponent_nonneg hY hXexp i,ha i⟩) hsum
  obtain ⟨m,hm₀,hm₁⟩ := exists_copies_in_gram_range hi hihalf
  apply F.copied_rows_gram_contradiction i m P (fun j => B j i) hY hN hP hPne
    (fun j => hB j i) (fun j p hp => hrow j p hp i)
    (by simpa only [hr] using hRexp) hNexp (hXexp i)
    (by simpa only [hv i] using hBexp i) hm₀ hm₁

end CubicFirstMoment

end

end OAI
