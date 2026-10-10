import Mathlib

namespace OAI

namespace LargePrimeGaps

noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

noncomputable def largeGapIndices (C : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n =>
    C * Real.log (prime n : ℝ) < (prime (n + 1) : ℝ) - (prime n : ℝ)

def primeIndex (p : ℕ) : ℕ := Nat.primeCounting' p + 1

noncomputable def successor (p : ℕ) : ℕ := prime (primeIndex p + 1)

theorem prime_isPrime (n : ℕ) : Nat.Prime (prime n) :=
  Nat.prime_nth_prime _

theorem prime_primeIndex {p : ℕ} (hp : Nat.Prime p) : prime (primeIndex p) = p := by
  simpa [prime, primeIndex, Nat.primeCounting'] using Nat.nth_count hp

theorem primeIndex_pos (p : ℕ) : 0 < primeIndex p := by
  simp [primeIndex]

theorem primeIndex_prime {n : ℕ} (hn : 0 < n) : primeIndex (prime n) = n := by
  simp [primeIndex, prime, Nat.primeCounting'_nth_eq, Nat.sub_add_cancel hn]

theorem prime_lt_prime {m n : ℕ} (hm : 0 < m) (hmn : m < n) :
    prime m < prime n := by
  apply Nat.nth_strictMono Nat.infinite_setOfPred_prime
  omega

theorem prime_le_prime {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    prime m ≤ prime n := by
  apply (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
  omega

theorem lt_successor {p : ℕ} (hp : Nat.Prime p) : p < successor p := by
  calc
    p = prime (primeIndex p) := (prime_primeIndex hp).symm
    _ < successor p := prime_lt_prime (primeIndex_pos _) (Nat.lt_succ_self _)

theorem successor_isPrime (p : ℕ) : Nat.Prime (successor p) := prime_isPrime _

theorem successor_le_of_prime_lt {p q : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p < q) : successor p ≤ q := by
  by_contra! h
  have hqle := Nat.le_nth_of_lt_nth_succ (p := Nat.Prime)
    (k := Nat.primeCounting' p) (a := q) (by simpa [successor, prime, primeIndex] using h) hq
  have hp' := prime_primeIndex hp
  simp only [prime, primeIndex, Nat.add_sub_cancel] at hp'
  omega

noncomputable def goodStarts (X h : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc X (2 * X)).filter fun m =>
    (∃ p, Nat.Prime p ∧ m < p ∧ p ≤ m + h) ∧
      ∀ q, m + h < q → q ≤ m + 2 * h → ¬ Nat.Prime q

noncomputable def gapPrimes (X h : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc X (2 * X + h)).filter fun p =>
    Nat.Prime p ∧ p + h < successor p

theorem exists_gapPrime_of_goodStart {X h m : ℕ} (hm : m ∈ goodStarts X h) :
    ∃ p ∈ gapPrimes X h, m ∈ Finset.Ico (p - h) p := by
  classical
  obtain ⟨hmrange, ⟨hex, hempty⟩⟩ := Finset.mem_filter.mp hm
  obtain ⟨hp, hpprime, hmp, hpend⟩ := hex
  let S := (Finset.Ioc m (m + h)).filter Nat.Prime
  have hSne : S.Nonempty := ⟨hp, by simp [S, hpprime, hmp, hpend]⟩
  let p := S.max' hSne
  have hpS : p ∈ S := Finset.max'_mem S hSne
  obtain ⟨hprange, hpprime⟩ := Finset.mem_filter.mp hpS
  obtain ⟨hmp, hpend⟩ := Finset.mem_Ioc.mp hprange
  have hn : m + 2 * h < successor p := by
    by_contra! hend
    have hnext := successor_isPrime p
    have hlt := lt_successor hpprime
    by_cases hsmall : successor p ≤ m + h
    · have hnS : successor p ∈ S := by
        simp only [S, Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨lt_trans hmp hlt, hsmall⟩, hnext⟩
      have := Finset.le_max' S (successor p) hnS
      exact (not_le_of_gt hlt) this
    · exact hempty (successor p) (by omega) hend hnext
  refine ⟨p, ?_, ?_⟩
  · simp only [gapPrimes, Finset.mem_filter, Finset.mem_Ioc]
    obtain ⟨hmlo, hmhi⟩ := Finset.mem_Ioc.mp hmrange
    exact ⟨⟨by omega, by omega⟩, hpprime, by omega⟩
  · simp only [Finset.mem_Ico]
    omega

theorem goodStarts_card_le (X h : ℕ) :
    (goodStarts X h).card ≤ (gapPrimes X h).card * h := by
  classical
  calc
    (goodStarts X h).card ≤
        ((gapPrimes X h).biUnion fun p => Finset.Ico (p - h) p).card := by
      apply Finset.card_le_card
      intro m hm
      obtain ⟨p, hp, hmp⟩ := exists_gapPrime_of_goodStart hm
      exact Finset.mem_biUnion.mpr ⟨p, hp, hmp⟩
    _ ≤ ∑ p ∈ gapPrimes X h, (Finset.Ico (p - h) p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ gapPrimes X h, h := by
      apply Finset.sum_le_sum
      intro p _
      rw [Nat.card_Ico]
      omega
    _ = (gapPrimes X h).card * h := by simp

theorem primeIndex_injOn : Set.InjOn primeIndex {p | Nat.Prime p} := by
  intro p hp q hq h
  simpa [prime_primeIndex hp, prime_primeIndex hq] using congrArg prime h

theorem gapPrimes_card_le_largeGapIndices (C : ℝ) (X h N : ℕ) (hN : 0 < N)
    (hrange : 2 * X + h ≤ prime N)
    (hthreshold : ∀ p ∈ gapPrimes X h, C * Real.log (p : ℝ) ≤ (h : ℝ)) :
    (gapPrimes X h).card ≤ (largeGapIndices C N).card := by
  classical
  apply Finset.card_le_card_of_injOn primeIndex
  · intro p hp
    obtain ⟨hprange, hpprime, hgap⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hpupper⟩ := Finset.mem_Ioc.mp hprange
    have hipos := primeIndex_pos p
    have hiN : primeIndex p ≤ N := by
      by_contra! hi
      have := prime_lt_prime hN hi
      rw [prime_primeIndex hpprime] at this
      omega
    have hgapR : (p : ℝ) + (h : ℝ) < (successor p : ℝ) := by exact_mod_cast hgap
    change primeIndex p ∈ largeGapIndices C N
    simp only [largeGapIndices, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hipos, hiN⟩, ?_⟩
    rw [prime_primeIndex hpprime]
    have hth := hthreshold p hp
    change C * Real.log (p : ℝ) < (successor p : ℝ) - (p : ℝ)
    linarith
  · intro p hp q hq h
    exact primeIndex_injOn (Finset.mem_filter.mp hp).2.1 (Finset.mem_filter.mp hq).2.1 h

theorem detector_cauchy {ι : Type*} (s : Finset ι) (w u : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, 0 ≤ u i) :
    (∑ i ∈ s, w i * u i) ^ 2 ≤
      (∑ i ∈ s with 0 < u i, w i) * (∑ i ∈ s, w i * u i ^ 2) := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    split_ifs
    · exact hw i hi
    · exact le_rfl
  · intro i hi
    exact mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    by_cases hui : 0 < u i
    · simp only [ite_eq_left hui]
      nlinarith [sq_nonneg (w i * u i)]
    · have huzero : u i = 0 := le_antisymm (le_of_not_gt hui) (hu i hi)
      simp [huzero]

theorem mass_after_suppression {ι : Type*} (s : Finset ι) (w u v : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hv : ∀ i ∈ s, 0 ≤ v i)
    (hvone : ∀ i ∈ s, 0 < v i → 1 ≤ v i) :
    (∑ i ∈ s with 0 < u i, w i) ≤
      (∑ i ∈ s with 0 < u i ∧ v i = 0, w i) + ∑ i ∈ s, w i * v i := by
  classical
  simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hui : 0 < u i
  · by_cases hvi : v i = 0
    · simp [hui, hvi]
    · simp only [hui, hvi, and_false, ite_false, ite_true, zero_add]
      exact le_mul_of_one_le_right (hw i hi) (hvone i hi (lt_of_le_of_ne (hv i hi) (Ne.symm hvi)))
  · simp only [hui, false_and, ite_false, zero_add]
    exact mul_nonneg (hw i hi) (hv i hi)

theorem mass_cauchy {ι : Type*} [DecidableEq ι] (s t : Finset ι) (w : ι → ℝ)
    (ht : t ⊆ s) :
    (∑ i ∈ t, w i) ^ 2 ≤ (t.card : ℝ) * ∑ i ∈ s, w i ^ 2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq t (fun _ => (1 : ℝ)) w
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  refine hc.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg ht (fun _ _ _ => sq_nonneg _)

theorem finite_moment_bound {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (w u v : ι → ℝ) (X a K b M : ℝ)
    (hX : 0 < X) (ha : 0 < a) (hK : 0 < K) (hM : 0 < M)
    (hb : b < a ^ 2 / K)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hu : ∀ i ∈ s, 0 ≤ u i)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hvone : ∀ i ∈ s, 0 < v i → 1 ≤ v i)
    (hfirst : a * X ≤ ∑ i ∈ s, w i * u i)
    (hdetect : (∑ i ∈ s, w i * u i ^ 2) ≤ K * X)
    (hsuppress : (∑ i ∈ s, w i * v i) ≤ b * X)
    (hsecond : (∑ i ∈ s, w i ^ 2) ≤ M * X) :
    (a ^ 2 / K - b) ^ 2 / M * X ≤
      ((s.filter fun i => 0 < u i ∧ v i = 0).card : ℝ) := by
  classical
  let A := s.filter fun i => 0 < u i
  let T := s.filter fun i => 0 < u i ∧ v i = 0
  have hAnonneg : 0 ≤ ∑ i ∈ A, w i :=
    Finset.sum_nonneg fun i hi => hw i (Finset.mem_filter.mp hi).1
  have hAsq := detector_cauchy s w u hw hu
  have hfirstsq := mul_self_le_mul_self (le_of_lt (mul_pos ha hX)) hfirst
  have hAsq' : (a ^ 2 * X) * X ≤ ((∑ i ∈ A, w i) * K) * X := by
    calc
      _ = (a * X) * (a * X) := by ring
      _ ≤ (∑ i ∈ s, w i * u i) * (∑ i ∈ s, w i * u i) := hfirstsq
      _ = (∑ i ∈ s, w i * u i) ^ 2 := by ring
      _ ≤ (∑ i ∈ A, w i) * (∑ i ∈ s, w i * u i ^ 2) := hAsq
      _ ≤ (∑ i ∈ A, w i) * (K * X) := mul_le_mul_of_nonneg_left hdetect hAnonneg
      _ = _ := by ring
  have hAlower : a ^ 2 / K * X ≤ ∑ i ∈ A, w i := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hK]
    exact (mul_le_mul_iff_left₀ hX).mp (by nlinarith only [hAsq'])
  have hremoved := mass_after_suppression s w u v hw hv hvone
  have hTlower : (a ^ 2 / K - b) * X ≤ ∑ i ∈ T, w i := by
    dsimp [A] at hAlower
    dsimp [T]
    linarith
  have hTnonneg : 0 ≤ (a ^ 2 / K - b) * X := mul_nonneg (sub_nonneg.mpr hb.le) hX.le
  have hTfirstsq := mul_self_le_mul_self hTnonneg hTlower
  have hTsq := mass_cauchy s T w (Finset.filter_subset _ s)
  have hTcardnonneg : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have hTbound : (a ^ 2 / K - b) ^ 2 * X * X ≤ (T.card : ℝ) * M * X := by
    calc
      _ = ((a ^ 2 / K - b) * X) * ((a ^ 2 / K - b) * X) := by ring
      _ ≤ (∑ i ∈ T, w i) * (∑ i ∈ T, w i) := hTfirstsq
      _ = (∑ i ∈ T, w i) ^ 2 := by ring
      _ ≤ (T.card : ℝ) * (∑ i ∈ s, w i ^ 2) := hTsq
      _ ≤ (T.card : ℝ) * (M * X) := mul_le_mul_of_nonneg_left hsecond hTcardnonneg
      _ = _ := by ring
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  exact (mul_le_mul_iff_left₀ hX).mp hTbound

noncomputable def theta (n : ℕ) : ℝ := if Nat.Prime n then Real.log n else 0

noncomputable def average (X : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ m ∈ Finset.Ioc X (2 * X), f m) / (X : ℝ)

noncomputable def detector (X : ℕ) (B : Finset ℕ) (m : ℕ) : ℝ :=
  (∑ b ∈ B, theta (m + b)) / Real.log (X : ℝ)

noncomputable def blockLength (lam : ℝ) (X : ℕ) : ℕ :=
  ⌊lam * Real.log (X : ℝ)⌋₊

theorem log_pos_of_two_le {X : ℕ} (hX : 2 ≤ X) : 0 < Real.log (X : ℝ) :=
  Real.log_pos (by exact_mod_cast (show 1 < X by omega))

theorem theta_nonneg (n : ℕ) : 0 ≤ theta n := by
  by_cases hn : Nat.Prime n
  · simp only [theta, ite_eq_left hn]
    exact (log_pos_of_two_le hn.two_le).le
  · simp [theta, hn]

theorem theta_pos_iff (n : ℕ) : 0 < theta n ↔ Nat.Prime n := by
  by_cases hn : Nat.Prime n
  · simp only [theta, hn, iff_true]
    exact log_pos_of_two_le hn.two_le
  · simp [theta, hn]

theorem detector_nonneg {X : ℕ} (hX : 2 ≤ X) (B : Finset ℕ) (m : ℕ) :
    0 ≤ detector X B m :=
  div_nonneg (Finset.sum_nonneg fun _ _ => theta_nonneg _) (log_pos_of_two_le hX).le

theorem detector_pos_iff {X : ℕ} (hX : 2 ≤ X) (B : Finset ℕ) (m : ℕ) :
    0 < detector X B m ↔ ∃ b ∈ B, Nat.Prime (m + b) := by
  rw [detector, div_pos_iff_of_pos_right (log_pos_of_two_le hX),
    Finset.sum_pos_iff_of_nonneg (fun _ _ => theta_nonneg _)]
  simp only [theta_pos_iff]

theorem one_le_detector {X m : ℕ} (hX : 2 ≤ X) (hm : X < m)
    (B : Finset ℕ) (hv : 0 < detector X B m) : 1 ≤ detector X B m := by
  obtain ⟨b, hb, hp⟩ := (detector_pos_iff hX B m).mp hv
  have hlog : Real.log (X : ℝ) ≤ theta (m + b) := by
    rw [theta, ite_eq_left hp]
    apply Real.log_le_log (by exact_mod_cast (show 0 < X by omega))
    exact_mod_cast (show X ≤ m + b by omega)
  have hsum := Finset.single_le_sum (fun q (_ : q ∈ B) => theta_nonneg (m + q)) hb
  rw [detector, le_div_iff₀ (log_pos_of_two_le hX), one_mul]
  exact hlog.trans hsum

theorem first_detector_pos_iff {X : ℕ} (hX : 2 ≤ X) (h m : ℕ) :
    0 < detector X (Finset.Ioc 0 h) m ↔
      ∃ p, Nat.Prime p ∧ m < p ∧ p ≤ m + h := by
  rw [detector_pos_iff hX]
  constructor
  · rintro ⟨b, hb, hp⟩
    obtain ⟨hb0, hbh⟩ := Finset.mem_Ioc.mp hb
    exact ⟨m + b, hp, by omega, by omega⟩
  · rintro ⟨p, hp, hmp, hph⟩
    refine ⟨p - m, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · simpa [Nat.add_sub_of_le hmp.le] using hp

theorem second_detector_zero_iff {X : ℕ} (hX : 2 ≤ X) (h m : ℕ) :
    detector X (Finset.Ioc h (2 * h)) m = 0 ↔
      ∀ q, m + h < q → q ≤ m + 2 * h → ¬ Nat.Prime q := by
  have hnonneg := detector_nonneg hX (Finset.Ioc h (2 * h)) m
  have heq : detector X (Finset.Ioc h (2 * h)) m = 0 ↔
      ¬ 0 < detector X (Finset.Ioc h (2 * h)) m := by
    constructor <;> intro nh <;> linarith
  rw [heq, detector_pos_iff hX]
  constructor
  · intro hnone q hqlo hqhi hp
    apply hnone
    refine ⟨q - m, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      omega
    · simpa [Nat.add_sub_of_le (show m ≤ q by omega)] using hp
  · intro hnone
    rintro ⟨b, hb, hp⟩
    obtain ⟨hblo, hbhi⟩ := Finset.mem_Ioc.mp hb
    exact hnone (m + b) (by omega) (by omega) hp

theorem goodStarts_eq_detector_filter {X : ℕ} (hX : 2 ≤ X) (h : ℕ) :
    goodStarts X h = (Finset.Ioc X (2 * X)).filter fun m =>
      0 < detector X (Finset.Ioc 0 h) m ∧ detector X (Finset.Ioc h (2 * h)) m = 0 := by
  classical
  ext m
  simp only [goodStarts, Finset.mem_filter, first_detector_pos_iff hX,
    second_detector_zero_iff hX]

theorem goodStarts_bound_of_moments {X h : ℕ} (hX : 2 ≤ X) (w : ℕ → ℝ)
    (a K b M : ℝ) (ha : 0 < a) (hK : 0 < K) (hM : 0 < M) (hb : b < a ^ 2 / K)
    (hw : ∀ m ∈ Finset.Ioc X (2 * X), 0 ≤ w m)
    (hfirst : a ≤ average X (fun m => w m * detector X (Finset.Ioc 0 h) m))
    (hdetect : average X (fun m => w m * detector X (Finset.Ioc 0 h) m ^ 2) ≤ K)
    (hsuppress : average X (fun m => w m * detector X (Finset.Ioc h (2 * h)) m) ≤ b)
    (hsecond : average X (fun m => w m ^ 2) ≤ M) :
    (a ^ 2 / K - b) ^ 2 / M * (X : ℝ) ≤ ((goodStarts X h).card : ℝ) := by
  classical
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  rw [goodStarts_eq_detector_filter hX]
  apply finite_moment_bound _ w _ _ (X : ℝ) a K b M hXpos ha hK hM hb hw
  · intro m _
    exact detector_nonneg hX _ m
  · intro m _
    exact detector_nonneg hX _ m
  · intro m hm hv
    exact one_le_detector hX (Finset.mem_Ioc.mp hm).1 _ hv
  · exact (le_div_iff₀ hXpos).mp hfirst
  · exact (div_le_iff₀ hXpos).mp hdetect
  · exact (div_le_iff₀ hXpos).mp hsuppress
  · exact (div_le_iff₀ hXpos).mp hsecond

open Filter

theorem le_prime (n : ℕ) : n ≤ prime n := by
  have := Nat.add_two_le_nth_prime (n - 1)
  change n ≤ Nat.nth Nat.Prime (n - 1)
  omega

theorem tendsto_prime : Tendsto prime atTop atTop :=
  tendsto_atTop_mono le_prime tendsto_id

theorem primeCounting_prime {n : ℕ} (hn : 0 < n) : Nat.primeCounting (prime n) = n := by
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  change Nat.count Nat.Prime (prime n + 1) = n
  rw [Nat.count_succ, ite_eq_left (prime_isPrime n)]
  have := primeIndex_prime hn
  exact this

theorem eventually_index_log_prime_le :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * Real.log (prime n : ℝ) ≤ (Real.log 4 + 1) * (prime n : ℝ) := by
  have hcheb := (tendsto_natCast_atTop_atTop.comp tendsto_prime).eventually
    (Chebyshev.eventually_primeCounting_le (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hcheb, eventually_ge_atTop 1] with n hn hnpos
  simp only [Function.comp_apply, Nat.floor_natCast, primeCounting_prime (by omega : 0 < n)] at hn
  exact (le_div_iff₀ (log_pos_of_two_le (prime_isPrime n).two_le)).mp hn

noncomputable def indexScale (N : ℕ) : ℕ := prime N / 3

theorem tendsto_indexScale : Tendsto indexScale atTop atTop :=
  (Nat.tendsto_div_const_atTop (by norm_num : (3 : ℕ) ≠ 0)).comp tendsto_prime

theorem eventually_scale_comparison :
    ∀ᶠ N : ℕ in atTop, 2 ≤ indexScale N ∧
      (N : ℝ) * Real.log (indexScale N : ℝ) ≤
        (6 * (Real.log 4 + 1)) * (indexScale N : ℝ) := by
  filter_upwards [eventually_index_log_prime_le,
    tendsto_indexScale.eventually (eventually_ge_atTop 2)] with N hcheb hX
  refine ⟨hX, ?_⟩
  have hprime : indexScale N ≤ prime N := Nat.div_le_self _ _
  have hlog : Real.log (indexScale N : ℝ) ≤ Real.log (prime N : ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0 < indexScale N by omega))
      (by exact_mod_cast hprime)
  have hsizeN : prime N ≤ 6 * indexScale N := by
    have hmod := Nat.mod_lt (prime N) (by norm_num : 0 < 3)
    have hdiv := Nat.div_add_mod (prime N) 3
    change 2 ≤ prime N / 3 at hX
    change prime N ≤ 6 * (prime N / 3)
    omega
  have hsize : (prime N : ℝ) ≤ 6 * (indexScale N : ℝ) := by exact_mod_cast hsizeN
  have hA : 0 ≤ Real.log 4 + 1 := by positivity
  calc
    (N : ℝ) * Real.log (indexScale N : ℝ) ≤
        (N : ℝ) * Real.log (prime N : ℝ) := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
    _ ≤ (Real.log 4 + 1) * (prime N : ℝ) := hcheb
    _ ≤ (6 * (Real.log 4 + 1)) * (indexScale N : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hsize hA]

theorem blockLength_le_mul_log {lam : ℝ} (hlam : 0 ≤ lam) {X : ℕ} (hX : 2 ≤ X) :
    (blockLength lam X : ℝ) ≤ lam * Real.log (X : ℝ) :=
  Nat.floor_le (mul_nonneg hlam (log_pos_of_two_le hX).le)

theorem eventually_blockLength_le (lam : ℝ) (hlam : 0 < lam) :
    ∀ᶠ X : ℕ in atTop, blockLength lam X ≤ X := by
  have he := tendsto_natCast_atTop_atTop.eventually (Real.isLittleO_log_id_atTop.bound
    (by positivity : 0 < 1 / lam))
  filter_upwards [he, eventually_ge_atTop 2] with X hbound hX
  have hlog := log_pos_of_two_le hX
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg hlog.le,
    abs_of_nonneg (show (0 : ℝ) ≤ (X : ℝ) from Nat.cast_nonneg X)] at hbound
  have hmul : lam * Real.log (X : ℝ) ≤ (X : ℝ) := by
    calc
      lam * Real.log (X : ℝ) ≤ lam * ((1 / lam) * (X : ℝ)) :=
        mul_le_mul_of_nonneg_left hbound hlam.le
      _ = (X : ℝ) := by field_simp
  exact_mod_cast (blockLength_le_mul_log hlam.le hX).trans hmul

theorem eventually_blockLength_threshold (C : ℝ) (hC : 0 < C) :
    ∀ᶠ X : ℕ in atTop, ∀ p : ℕ, 0 < p → p ≤ 3 * X →
      C * Real.log (p : ℝ) ≤ (blockLength (C + 1) X : ℝ) := by
  have hlim : Tendsto (fun X : ℕ => Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_ge_atTop (C * Real.log 3 + 1)),
    eventually_ge_atTop 2] with X hlog hX
  intro p hp hpX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hupper : Real.log (p : ℝ) ≤ Real.log (3 * (X : ℝ)) :=
    Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hpX)
  rw [Real.log_mul (by norm_num) hXpos.ne'] at hupper
  have hfloor := Nat.lt_floor_add_one ((C + 1) * Real.log (X : ℝ))
  change (C + 1) * Real.log (X : ℝ) < (blockLength (C + 1) X : ℝ) + 1 at hfloor
  nlinarith [mul_le_mul_of_nonneg_left hupper hC.le]

theorem index_bound_of_goodStarts {C delta lam A : ℝ} {X N : ℕ}
    (hdelta : 0 < delta) (hlam : 0 < lam) (hA : 0 < A)
    (hX : 2 ≤ X) (hN : 0 < N)
    (hrange : 2 * X + blockLength lam X ≤ prime N)
    (hthreshold : ∀ p ∈ gapPrimes X (blockLength lam X),
      C * Real.log (p : ℝ) ≤ (blockLength lam X : ℝ))
    (hcompare : (N : ℝ) * Real.log (X : ℝ) ≤ A * (X : ℝ))
    (hstarts : delta * (X : ℝ) ≤ ((goodStarts X (blockLength lam X)).card : ℝ)) :
    delta / (A * lam) * (N : ℝ) ≤ ((largeGapIndices C N).card : ℝ) := by
  have hcount := goodStarts_card_le X (blockLength lam X)
  have hindices := gapPrimes_card_le_largeGapIndices C X (blockLength lam X) N hN
    hrange hthreshold
  have hmul : delta * (X : ℝ) ≤
      ((largeGapIndices C N).card : ℝ) * (lam * Real.log (X : ℝ)) := by
    calc
      delta * (X : ℝ) ≤ ((goodStarts X (blockLength lam X)).card : ℝ) := hstarts
      _ ≤ ((gapPrimes X (blockLength lam X)).card : ℝ) * (blockLength lam X : ℝ) :=
        by exact_mod_cast hcount
      _ ≤ ((largeGapIndices C N).card : ℝ) * (blockLength lam X : ℝ) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hindices) (Nat.cast_nonneg _)
      _ ≤ ((largeGapIndices C N).card : ℝ) * (lam * Real.log (X : ℝ)) :=
        mul_le_mul_of_nonneg_left (blockLength_le_mul_log hlam.le hX) (Nat.cast_nonneg _)
  have hcomp := mul_le_mul_of_nonneg_left hcompare hdelta.le
  have hmulA := mul_le_mul_of_nonneg_left hmul hA.le
  have hpos := log_pos_of_two_le hX
  apply (mul_le_mul_iff_left₀ hpos).mp
  apply (mul_le_mul_iff_right₀ (mul_pos hA hlam)).mp
  calc
    (A * lam) * (delta / (A * lam) * (N : ℝ) * Real.log (X : ℝ)) =
        delta * ((N : ℝ) * Real.log (X : ℝ)) := by field_simp [hA.ne', hlam.ne']
    _ ≤ A * (delta * (X : ℝ)) := by nlinarith
    _ ≤ (A * lam) * (((largeGapIndices C N).card : ℝ) * Real.log (X : ℝ)) := by
      nlinarith

end LargePrimeGaps

end OAI
