import OAI.NumberTheory.PrimeGaps.DivisorSums

namespace OAI

namespace LargePrimeGaps

open Filter

theorem divisorSum_eq_product_bounded {n X : ℕ} (hX : 2 ≤ X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : HasBudget F rho)
    (m : ℕ) (hm : 0 < m) (b : Fin n → ℕ) :
    divisorSum X F m b =
      ∑ d ∈ positiveProductTuples n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
        if ∀ i, d i ∣ m + b i then divisorCoefficient X F d else 0 := by
  classical
  rw [divisorSum_eq_bounded hX hbudget m hm b, ← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro d hd
    simp only [Finset.mem_filter] at hd ⊢
    exact ⟨(Finset.mem_filter.mp hd.1).1, hd.2⟩
  · intro d hd hdnot
    by_contra hne
    simp only [Finset.mem_filter] at hd
    obtain ⟨hbox, hdiv⟩ := hd
    have hdpos : ∀ i, 0 < d i := fun i =>
      (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hbox i)).1
    have hF := (divisorCoefficient_ne_zero_iff.mp hne).2
    have hp : ∏ i, d i ≤ ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ :=
      (Nat.le_floor_iff (Real.exp_pos _).le).mpr (divisor_product_bound hX hbudget hdpos hF)
    exact hdnot (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hbox, hp⟩, hdiv⟩)

noncomputable def unmarkedDensitySum {n : ℕ} (X : ℕ) (F : (Fin n → ℝ) → ℝ)
    (rho : ℝ) (b : Fin n → ℕ) : ℝ :=
  ∑ d ∈ positiveProductTuples n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
    divisorCoefficient X F d * tupleDensity d b

theorem unmarked_arithmetic_error {n X : ℕ} (hX : 2 ≤ X)
    {F : (Fin (n + 1) → ℝ) → ℝ} {rho M : ℝ} (hbudget : HasBudget F rho)
    (hM : 0 ≤ M) (hbound : ∀ v, (∀ i, 0 ≤ v i) → |F v| ≤ M)
    (b : Fin (n + 1) → ℕ) :
    |average X (fun m => divisorSum X F m b) - unmarkedDensitySum X F rho b| ≤
      2 * M / (X : ℝ) * ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ *
       (1 + Real.log (⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ : ℝ)) ^ n := by
  classical
  let Y : ℕ := ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊
  let s := positiveProductTuples (n + 1) Y
  have hs : ∀ d ∈ s, ∀ i, 0 < d i := by
    intro d hd i
    exact (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hd).1 i)).1
  have heq : average X (fun m => divisorSum X F m b) =
      average X (fun m => ∑ d ∈ s, if ∀ i, d i ∣ m + b i then divisorCoefficient X F d else 0) := by
    unfold average
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    exact divisorSum_eq_product_bounded hX hbudget m
      (lt_trans (by omega : 0 < X) (Finset.mem_Ioc.mp hm).1) b
  rw [heq]
  have he := finite_density_sum_error (by omega : 0 < X) s (divisorCoefficient X F) b hs
  have he' : |average X (fun m => ∑ d ∈ s, if ∀ i, d i ∣ m + b i then divisorCoefficient X F d else 0) -
      unmarkedDensitySum X F rho b| ≤ 2 / (X : ℝ) * ∑ d ∈ s, |divisorCoefficient X F d| := by
    convert he using 1
    congr 2
    unfold average
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> rfl
  apply he'.trans
  have habs : ∑ d ∈ s, |divisorCoefficient X F d| ≤ (s.card : ℝ) * M := by
    calc
      _ ≤ ∑ _d ∈ s, M := Finset.sum_le_sum fun d hd =>
        (abs_divisorCoefficient_le X F d).trans (hbound _ (logCoordinates_nonneg hX (hs d hd)))
      _ = _ := by simp
  have hcard := positiveProductTuples_card_log_bound n Y
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  calc
    2 / (X : ℝ) * ∑ d ∈ s, |divisorCoefficient X F d| ≤
        2 / (X : ℝ) * ((s.card : ℝ) * M) :=
      mul_le_mul_of_nonneg_left habs (by positivity)
    _ ≤ 2 / (X : ℝ) * (((Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ n) * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hM) (by positivity)
    _ = _ := by ring

theorem unmarked_arithmetic_error_exponential {n X : ℕ} (hX : 2 ≤ X)
    (hlog : 1 ≤ Real.log (X : ℝ)) {F : (Fin (n + 1) → ℝ) → ℝ} {rho M : ℝ}
    (hrho : 0 ≤ rho) (hbudget : HasBudget F rho) (hM : 0 ≤ M)
    (hbound : ∀ v, (∀ i, 0 ≤ v i) → |F v| ≤ M) (b : Fin (n + 1) → ℕ) :
    |average X (fun m => divisorSum X F m b) - unmarkedDensitySum X F rho b| ≤
      (2 * M * (1 + rho) ^ n) * (Real.log (X : ℝ)) ^ n *
        Real.exp (-(1 - rho) * Real.log (X : ℝ)) := by
  let L := Real.log (X : ℝ)
  let Y : ℕ := ⌊Real.exp (rho * L)⌋₊
  have hL : 0 ≤ L := le_trans (by norm_num) hlog
  have hY : 1 ≤ Y := (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    (by simpa using Real.one_le_exp_iff.mpr (mul_nonneg hrho hL))
  have hYR : (0 : ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hfloor : (Y : ℝ) ≤ Real.exp (rho * L) := Nat.floor_le (Real.exp_pos _).le
  have hlogY : Real.log (Y : ℝ) ≤ rho * L := by
    simpa only [Real.log_exp] using Real.log_le_log hYR hfloor
  have hlogY0 : 0 ≤ Real.log (Y : ℝ) := Real.log_nonneg (by exact_mod_cast hY)
  have hlogbound : 1 + Real.log (Y : ℝ) ≤ (1 + rho) * L := by nlinarith
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  apply (unmarked_arithmetic_error hX hbudget hM hbound b).trans
  calc
    2 * M / (X : ℝ) * (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ n ≤
        2 * M / (X : ℝ) * Real.exp (rho * L) * ((1 + rho) * L) ^ n := by
      gcongr
    _ = (2 * M * (1 + rho) ^ n) * L ^ n * Real.exp (-(1 - rho) * L) := by
      rw [show -(1 - rho) * L = rho * L - L by ring, Real.exp_sub, Real.exp_log hXR]
      rw [mul_pow]
      ring

theorem unmarked_arithmetic_error_log_decay {n : ℕ} {F : (Fin (n + 1) → ℝ) → ℝ}
    {rho M : ℝ} (hrho : 0 ≤ rho) (hrho1 : rho < 1) (hbudget : HasBudget F rho)
    (hM : 0 ≤ M) (hbound : ∀ v, (∀ i, 0 ≤ v i) → |F v| ≤ M)
    (b : ℕ → Fin (n + 1) → ℕ) (A : ℕ) :
    Filter.Tendsto (fun X : ℕ =>
      |average X (fun m => divisorSum X F m (b X)) - unmarkedDensitySum X F rho (b X)| *
         (Real.log (X : ℝ)) ^ A) Filter.atTop (nhds 0) := by
  have hloglim : Filter.Tendsto (fun X : ℕ => Real.log (X : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbase : Filter.Tendsto (fun x : ℝ => x ^ (n + A) * Real.exp (-(1 - rho) * x))
      Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n + A : ℕ) (1 - rho) (by linarith)
  have hlimit := (hbase.comp hloglim).const_mul (2 * M * (1 + rho) ^ n)
  simp only [mul_zero] at hlimit
  apply squeeze_zero' _ _ hlimit
  · filter_upwards [hloglim.eventually (Filter.eventually_ge_atTop 1)] with X hLX
    exact mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith) _)
  · filter_upwards [Filter.eventually_ge_atTop 2,
      hloglim.eventually (Filter.eventually_ge_atTop 1)] with X hX hLX
    have he := mul_le_mul_of_nonneg_right
      (unmarked_arithmetic_error_exponential hX hLX hrho hbudget hM hbound (b X))
      (pow_nonneg (by linarith : 0 ≤ Real.log (X : ℝ)) A)
    dsimp only [Function.comp_def]
    convert he using 1
    rw [pow_add]
    ring

def squarefreeModulusFiber (n Y q : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 Y)).filter
    fun d => (∀ i, Squarefree (d i)) ∧ tupleModulus d = q

theorem card_divisors_of_squarefree {q : ℕ} (hq : Squarefree q) :
    q.divisors.card = 2 ^ q.primeFactors.card := by
  rw [Nat.card_divisors hq.ne_zero]
  calc
    _ = ∏ _p ∈ q.primeFactors, (2 : ℕ) := by
      apply Finset.prod_congr rfl
      intro p hp
      have h := Nat.mem_primeFactors.mp hp
      rw [Nat.factorization_eq_one_of_squarefree hq h.1 h.2.1]
    _ = _ := by simp

theorem squarefreeModulusFiber_card_le (n Y q : ℕ) (hq : 0 < q) :
    (squarefreeModulusFiber n Y q).card ≤ (q.divisors.card) ^ n := by
  classical
  calc
    _ ≤ (Fintype.piFinset (fun _ : Fin n => q.divisors)).card := by
      apply Finset.card_le_card
      intro d hd
      have hd' := (Finset.mem_filter.mp hd).2
      apply Fintype.mem_piFinset.mpr
      intro i
      apply Nat.mem_divisors.mpr
      exact ⟨hd'.2 ▸ Finset.dvd_lcm (Finset.mem_univ i), hq.ne'⟩
    _ = _ := by simp

theorem squarefreeModulusFiber_card_le_pow (n Y q : ℕ) (hq : Squarefree q) :
    (squarefreeModulusFiber n Y q).card ≤ (2 ^ n) ^ q.primeFactors.card := by
  have h := squarefreeModulusFiber_card_le n Y q (Nat.pos_of_ne_zero hq.ne_zero)
  rw [card_divisors_of_squarefree hq, ← pow_mul, Nat.mul_comm, pow_mul] at h
  exact h

def markedTupleCompatible {ι : Type*} [Fintype ι] (d b : ι → ℕ) (a : ℕ) : Prop :=
  ∃ c < tupleModulus d, (∀ i, d i ∣ c + b i) ∧ Nat.Coprime (c + a) (tupleModulus d)

noncomputable def markedTupleDensity {ι : Type*} [Fintype ι] (d b : ι → ℕ) (a : ℕ) : ℝ := by
  classical
  exact if markedTupleCompatible d b a then ((tupleModulus d).totient : ℝ)⁻¹ else 0

noncomputable def markedError (X H q : ℕ) : NNReal :=
  ((Finset.range (H + 1)) ×ˢ (Finset.range q)).sup fun ac =>
    if Nat.Coprime (ac.2 + ac.1) q then
      NNReal.mk (|(∑ m ∈ residueStarts X q ac.2, theta (m + ac.1)) - (X : ℝ) / q.totient|)
        (abs_nonneg _) else 0

theorem markedClassError_le {X H q a c : ℕ} (ha : a ≤ H) (hc : c < q)
    (hcop : Nat.Coprime (c + a) q) :
    |(∑ m ∈ residueStarts X q c, theta (m + a)) - (X : ℝ) / q.totient| ≤
      (markedError X H q : ℝ) := by
  have hm : (a, c) ∈ (Finset.range (H + 1)) ×ˢ (Finset.range q) := by simp; omega
  have h := Finset.le_sup (f := fun ac : ℕ × ℕ =>
    if Nat.Coprime (ac.2 + ac.1) q then
      NNReal.mk (|(∑ m ∈ residueStarts X q ac.2, theta (m + ac.1)) -
        (X : ℝ) / q.totient|) (abs_nonneg _) else 0) hm
  have hr := NNReal.coe_le_coe.mpr h
  simpa only [Prod.fst, Prod.snd, ite_eq_left hcop, NNReal.coe_mk, markedError] using hr

theorem markedTupleCompatible_iff_coprime {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} {a c : ℕ} (hc : c < tupleModulus d)
    (hsol : ∀ i, d i ∣ c + b i) :
    markedTupleCompatible d b a ↔ Nat.Coprime (c + a) (tupleModulus d) := by
  constructor
  · rintro ⟨c', hc', hsol', hcop'⟩
    have hmod := (tuple_divisibility_iff_modEq d b hsol c').mp hsol'
    change c' % tupleModulus d = c % tupleModulus d at hmod
    rw [Nat.mod_eq_of_lt hc', Nat.mod_eq_of_lt hc] at hmod
    simpa [hmod] using hcop'
  · intro hcop
    exact ⟨c, hc, hsol, hcop⟩

theorem markedTupleCompatible_imp {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} {a : ℕ} (h : markedTupleCompatible d b a) : tupleCompatible d b := by
  obtain ⟨c, hc, hs, _⟩ := h
  exact ⟨c, hc, hs⟩

theorem markedTuple_density_error {ι : Type*} [Fintype ι]
    {X H a : ℕ} {d b : ι → ℕ} (hd : ∀ i, 0 < d i)
    (hmod : tupleModulus d ≤ X) (ha : a ≤ H) :
    |(∑ m ∈ tupleStarts X d b, theta (m + a)) - (X : ℝ) * markedTupleDensity d b a| ≤
      (markedError X H (tupleModulus d) : ℝ) := by
  classical
  by_cases h : tupleCompatible d b
  · obtain ⟨c, hc, hsol⟩ := h
    by_cases hcop : Nat.Coprime (c + a) (tupleModulus d)
    · rw [tupleStarts_eq_residueStarts X d b hc hsol, markedTupleDensity,
        ite_eq_left ((markedTupleCompatible_iff_coprime hc hsol).mpr hcop)]
      simpa only [div_eq_mul_inv] using markedClassError_le (X := X) ha hc hcop
    · have hr : ¬ markedTupleCompatible d b a :=
        fun hr => hcop ((markedTupleCompatible_iff_coprime hc hsol).mp hr)
      have hz : ∑ m ∈ tupleStarts X d b, theta (m + a) = 0 := by
        apply Finset.sum_eq_zero
        intro m hm
        obtain ⟨hmX, hmdiv⟩ := Finset.mem_filter.mp hm
        have hmX' := (Finset.mem_Ioc.mp hmX).1
        have hn := not_prime_on_nonreduced_class (tupleModulus_pos hd)
          ((tuple_divisibility_iff_modEq d b hsol m).mp hmdiv) hcop (by omega)
        simp [theta, hn]
      simp only [hz, markedTupleDensity, ite_eq_right hr, mul_zero, sub_zero, abs_zero]
      exact NNReal.coe_nonneg _
  · rw [tupleStarts_eq_empty_of_incompatible X hd h]
    have hr : ¬ markedTupleCompatible d b a := fun hr => h (markedTupleCompatible_imp hr)
    simp only [Finset.sum_empty, markedTupleDensity, ite_eq_right hr, mul_zero, sub_zero, abs_zero]
    exact NNReal.coe_nonneg _

def markedLocalCompatible {ι : Type*} [Fintype ι] (d b : ι → ℕ) (a : ℕ) : Prop :=
  localCompatible d b ∧ ∀ p, Nat.Prime p → p ∣ tupleModulus d →
    ∀ i, p ∣ d i → ¬ Nat.ModEq p (b i) a

theorem markedTupleCompatible_iff_local {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} {a : ℕ} (hd : ∀ i, Squarefree (d i)) :
    markedTupleCompatible d b a ↔ markedLocalCompatible d b a := by
  constructor
  · intro h
    refine ⟨localCompatible_of_tupleCompatible (markedTupleCompatible_imp h), ?_⟩
    obtain ⟨c, _, hsol, hcop⟩ := h
    intro p hp hpq i hpi hba
    have hcb : Nat.ModEq p (c + b i) 0 := Nat.modEq_zero_iff_dvd.mpr (hpi.trans (hsol i))
    have hca : p ∣ c + a := Nat.modEq_zero_iff_dvd.mp ((hba.add_left c).symm.trans hcb)
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hca hpq) hcop
  · rintro ⟨hlocal, hexcl⟩
    obtain ⟨c, hc, hsol⟩ := tupleCompatible_of_localCompatible hd hlocal
    refine ⟨c, hc, hsol, ?_⟩
    by_contra hcop
    obtain ⟨p, hp, hpca, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
    obtain ⟨i, _, hpi⟩ := (hp.prime.dvd_finsetProd_iff d).mp
      (hpq.trans (tupleModulus_dvd_prod d))
    apply hexcl p hp hpq i hpi
    have hcb : Nat.ModEq p (c + b i) 0 := Nat.modEq_zero_iff_dvd.mpr (hpi.trans (hsol i))
    have hca : Nat.ModEq p (c + a) 0 := Nat.modEq_zero_iff_dvd.mpr hpca
    exact Nat.ModEq.add_left_cancel (Nat.ModEq.refl c) (hcb.trans hca.symm)

theorem totient_eq_primeFactors_prod_of_squarefree {q : ℕ} (hq : Squarefree q) :
    q.totient = ∏ p ∈ q.primeFactors, (p - 1) := by
  rw [Nat.totient_eq_div_primeFactors_mul, Nat.prod_primeFactors_of_squarefree hq,
    Nat.div_self (Nat.pos_of_ne_zero hq.ne_zero), one_mul]

theorem sum_marked_divisibility_eq {ι : Type*} [Fintype ι]
    (X a : ℕ) (s : Finset (ι → ℕ)) (A : (ι → ℕ) → ℝ) (b : ι → ℕ) :
    (∑ m ∈ Finset.Ioc X (2 * X),
      (∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) * theta (m + a)) =
      ∑ d ∈ s, A d * ∑ m ∈ tupleStarts X d b, theta (m + a) := by
  classical
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter, ← Finset.mul_sum]
  rfl

theorem finite_marked_density_sum_error {ι : Type*} [Fintype ι]
    {X H a : ℕ} (hX : 0 < X) (ha : a ≤ H)
    (s : Finset (ι → ℕ)) (A : (ι → ℕ) → ℝ) (b : ι → ℕ)
    (hs : ∀ d ∈ s, (∀ i, 0 < d i) ∧ tupleModulus d ≤ X) :
    |average X (fun m =>
        (∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) * theta (m + a)) -
      ∑ d ∈ s, A d * markedTupleDensity d b a| ≤
      (X : ℝ)⁻¹ * ∑ d ∈ s, |A d| * (markedError X H (tupleModulus d) : ℝ) := by
  classical
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hexp : average X (fun m =>
      (∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) * theta (m + a)) -
        ∑ d ∈ s, A d * markedTupleDensity d b a =
      (X : ℝ)⁻¹ * ∑ d ∈ s, A d * ((∑ m ∈ tupleStarts X d b, theta (m + a)) -
        (X : ℝ) * markedTupleDensity d b a) := by
    unfold average
    rw [sum_marked_divisibility_eq]
    let T : (ι → ℕ) → ℝ := fun d => ∑ m ∈ tupleStarts X d b, theta (m + a)
    change (∑ d ∈ s, A d * T d) / X - (∑ d ∈ s, A d * markedTupleDensity d b a) =
      (X : ℝ)⁻¹ * ∑ d ∈ s, A d * (T d - (X : ℝ) * markedTupleDensity d b a)
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    field_simp [hXR.ne']
  rw [hexp, abs_mul, abs_of_pos (inv_pos.mpr hXR)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hXR.le)
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro d hd
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (markedTuple_density_error (hs d hd).1 (hs d hd).2 ha)
    (abs_nonneg _)

theorem squarefree_tuple_modulus_sum_bound (n Y : ℕ) (s : Finset (Fin n → ℕ))
    (E : ℕ → ℝ) (hE : ∀ q, 0 ≤ E q)
    (hbox : ∀ d ∈ s, ∀ i, d i ∈ Finset.Icc 1 Y)
    (hsq : ∀ d ∈ s, ∀ i, Squarefree (d i))
    (hmod : ∀ d ∈ s, tupleModulus d ≤ Y) :
    (∑ d ∈ s, E (tupleModulus d)) ≤
      ∑ q ∈ Finset.Icc 1 Y, if Squarefree q then
        (((2 ^ n) ^ q.primeFactors.card : ℕ) : ℝ) * E q else 0 := by
  classical
  have hmap : ∀ d ∈ s, tupleModulus d ∈ Finset.Icc 1 Y := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨tupleModulus_pos
      (fun i => (Finset.mem_Icc.mp (hbox d hd i)).1), hmod d hd⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_le_sum
  intro q _hqY
  let T := s.filter fun d => tupleModulus d = q
  have hT : T ⊆ squarefreeModulusFiber n Y q := by
    intro d hd
    obtain ⟨hds, hdq⟩ := Finset.mem_filter.mp hd
    simp only [squarefreeModulusFiber, Finset.mem_filter, Fintype.mem_piFinset]
    exact ⟨hbox d hds, hsq d hds, hdq⟩
  have heq : (∑ d ∈ T, E (tupleModulus d)) = (T.card : ℝ) * E q := by
    calc
      _ = ∑ _d ∈ T, E q := Finset.sum_congr rfl fun d hd => by
        rw [(Finset.mem_filter.mp hd).2]
      _ = _ := by simp
  change (∑ d ∈ T, E (tupleModulus d)) ≤ _
  rw [heq]
  by_cases hq : Squarefree q
  · rw [ite_eq_left hq]
    have hcard := (Finset.card_le_card hT).trans (squarefreeModulusFiber_card_le_pow n Y q hq)
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hE q)
  · rw [ite_eq_right hq]
    have hT0 : T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro d hd
      obtain ⟨hds, hdq⟩ := Finset.mem_filter.mp hd
      exact hq (hdq ▸ tupleModulus_squarefree (hsq d hds))
    simp [hT0]

def squarefreeProductTuples (n Y : ℕ) : Finset (Fin n → ℕ) :=
  (positiveProductTuples n Y).filter fun d => ∀ i, Squarefree (d i)

theorem divisorSum_eq_squarefree_product_bounded {n X : ℕ} (hX : 2 ≤ X)
    {F : (Fin n → ℝ) → ℝ} {rho : ℝ} (hbudget : HasBudget F rho)
    (m : ℕ) (hm : 0 < m) (b : Fin n → ℕ) :
    divisorSum X F m b =
      ∑ d ∈ squarefreeProductTuples n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
        if ∀ i, d i ∣ m + b i then divisorCoefficient X F d else 0 := by
  classical
  rw [divisorSum_eq_product_bounded hX hbudget m hm b]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hd hnot
  have hz : divisorCoefficient X F d = 0 := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hd, (divisorCoefficient_ne_zero_iff.mp hne).1⟩)
  simp only [hz, ite_self]

noncomputable def markedDensitySum {n : ℕ} (X : ℕ)
    (F : (Fin n → ℝ) → ℝ) (rho : ℝ) (b : Fin n → ℕ) (a : ℕ) : ℝ :=
  ∑ d ∈ squarefreeProductTuples n ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
    divisorCoefficient X F d * markedTupleDensity d b a

theorem floor_support_le_X {X : ℕ} (hX : 2 ≤ X) {rho : ℝ} (hrho1 : rho ≤ 1) :
    ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ ≤ X := by
  have hXR : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  apply Nat.floor_le_of_le
  calc
    Real.exp (rho * Real.log (X : ℝ)) ≤ Real.exp (Real.log (X : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [log_pos_of_two_le hX]
    _ = _ := Real.exp_log hXR

theorem marked_arithmetic_error {n X H a : ℕ} (hX : 2 ≤ X) (ha : a ≤ H)
    {F : (Fin n → ℝ) → ℝ} {rho M : ℝ} (hrho1 : rho ≤ 1)
    (hbudget : HasBudget F rho) (hM : 0 ≤ M)
    (hbound : ∀ v, (∀ i, 0 ≤ v i) → |F v| ≤ M) (b : Fin n → ℕ) :
    |average X (fun m => divisorSum X F m b * theta (m + a)) -
      markedDensitySum X F rho b a| ≤
      M / (X : ℝ) * ∑ q ∈ Finset.Icc 1 ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊,
        if Squarefree q then (((2 ^ n) ^ q.primeFactors.card : ℕ) : ℝ) *
          (markedError X H q : ℝ) else 0 := by
  classical
  let Y : ℕ := ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊
  let s := squarefreeProductTuples n Y
  have hbox : ∀ d ∈ s, ∀ i, d i ∈ Finset.Icc 1 Y := by
    intro d hd i
    exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).1 i
  have hpos : ∀ d ∈ s, ∀ i, 0 < d i := fun d hd i => (Finset.mem_Icc.mp (hbox d hd i)).1
  have hsq : ∀ d ∈ s, ∀ i, Squarefree (d i) := fun d hd => (Finset.mem_filter.mp hd).2
  have hmod : ∀ d ∈ s, tupleModulus d ≤ Y := by
    intro d hd
    exact (tupleModulus_le_prod (hpos d hd)).trans (Finset.mem_filter.mp (Finset.mem_filter.mp hd).1).2
  have hs : ∀ d ∈ s, (∀ i, 0 < d i) ∧ tupleModulus d ≤ X :=
    fun d hd => ⟨hpos d hd, (hmod d hd).trans (floor_support_le_X hX hrho1)⟩
  have he := finite_marked_density_sum_error (by omega : 0 < X) ha s (divisorCoefficient X F) b hs
  have hexp : average X (fun m => divisorSum X F m b * theta (m + a)) =
      average X (fun m => (∑ d ∈ s, if ∀ i, d i ∣ m + b i then
        divisorCoefficient X F d else 0) * theta (m + a)) := by
    unfold average
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    dsimp only
    rw [divisorSum_eq_squarefree_product_bounded hX hbudget m (by
      have := (Finset.mem_Ioc.mp hm).1
      omega) b]
  rw [hexp]
  have he' : |average X (fun m => (∑ d ∈ s, if ∀ i, d i ∣ m + b i then
        divisorCoefficient X F d else 0) * theta (m + a)) - markedDensitySum X F rho b a| ≤
      (X : ℝ)⁻¹ * ∑ d ∈ s, |divisorCoefficient X F d| *
        (markedError X H (tupleModulus d) : ℝ) := by
    convert he using 1
    congr 2
    unfold average
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    dsimp only
    congr 1
    apply Finset.sum_congr rfl
    intro d _
    split_ifs <;> rfl
  apply he'.trans
  have hcoeff : ∑ d ∈ s, |divisorCoefficient X F d| *
      (markedError X H (tupleModulus d) : ℝ) ≤
      M * ∑ d ∈ s, (markedError X H (tupleModulus d) : ℝ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    exact mul_le_mul_of_nonneg_right
      ((abs_divisorCoefficient_le X F d).trans (hbound _ (logCoordinates_nonneg hX (hpos d hd))))
      (NNReal.coe_nonneg _)
  have hgroup := squarefree_tuple_modulus_sum_bound n Y s
    (fun q => (markedError X H q : ℝ)) (fun q => NNReal.coe_nonneg _) hbox hsq hmod
  calc
    (X : ℝ)⁻¹ * ∑ d ∈ s, |divisorCoefficient X F d| *
        (markedError X H (tupleModulus d) : ℝ) ≤
      (X : ℝ)⁻¹ * (M * ∑ d ∈ s, (markedError X H (tupleModulus d) : ℝ)) :=
        mul_le_mul_of_nonneg_left hcoeff (by positivity)
    _ ≤ (X : ℝ)⁻¹ * (M * ∑ q ∈ Finset.Icc 1 Y, if Squarefree q then
        (((2 ^ n) ^ q.primeFactors.card : ℕ) : ℝ) * (markedError X H q : ℝ) else 0) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgroup hM) (by positivity)
    _ = _ := by ring

end LargePrimeGaps

end OAI
