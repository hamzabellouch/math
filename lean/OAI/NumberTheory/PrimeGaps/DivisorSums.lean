import OAI.NumberTheory.PrimeGaps.Indices

namespace OAI

namespace LargePrimeGaps

open Filter

noncomputable def logCoordinates {ι : Type*} (X : ℕ) (d : ι → ℕ) : ι → ℝ :=
  fun i => Real.log (d i : ℝ) / Real.log (X : ℝ)

noncomputable def divisorCoefficient {ι : Type*} [Fintype ι]
    (X : ℕ) (F : (ι → ℝ) → ℝ) (d : ι → ℕ) : ℝ :=
  (∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) * F (logCoordinates X d)

noncomputable def divisorSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ℕ) (F : (ι → ℝ) → ℝ) (m : ℕ) (b : ι → ℕ) : ℝ :=
  ∑ d ∈ Fintype.piFinset (fun i => (m + b i).divisors), divisorCoefficient X F d

def HasBudget {ι : Type*} [Fintype ι] (F : (ι → ℝ) → ℝ) (rho : ℝ) : Prop :=
  ∀ v : ι → ℝ, (∀ i, 0 ≤ v i) → rho < ∑ i, v i → F v = 0

theorem divisorCoefficient_ne_zero_iff {ι : Type*} [Fintype ι]
    {X : ℕ} {F : (ι → ℝ) → ℝ} {d : ι → ℕ} :
    divisorCoefficient X F d ≠ 0 ↔
      (∀ i, Squarefree (d i)) ∧ F (logCoordinates X d) ≠ 0 := by
  simp only [divisorCoefficient, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Finset.mem_univ, forall_true_left, Int.cast_ne_zero,
    ArithmeticFunction.moebius_ne_zero_iff_squarefree]

theorem logCoordinates_nonneg {ι : Type*} {X : ℕ} (hX : 2 ≤ X)
    {d : ι → ℕ} (hd : ∀ i, 0 < d i) (i : ι) : 0 ≤ logCoordinates X d i := by
  exact div_nonneg (Real.log_nonneg (by exact_mod_cast hd i)) (log_pos_of_two_le hX).le

theorem divisor_product_bound {ι : Type*} [Fintype ι]
    {X : ℕ} (hX : 2 ≤ X) {F : (ι → ℝ) → ℝ} {rho : ℝ}
    (hbudget : HasBudget F rho) {d : ι → ℕ} (hd : ∀ i, 0 < d i)
    (hF : F (logCoordinates X d) ≠ 0) :
    ((∏ i, d i : ℕ) : ℝ) ≤ Real.exp (rho * Real.log (X : ℝ)) := by
  have hsum : ∑ i, logCoordinates X d i ≤ rho := by
    by_contra! hgt
    exact hF (hbudget _ (logCoordinates_nonneg hX hd) hgt)
  have hlog : ∑ i, Real.log (d i : ℝ) ≤ rho * Real.log (X : ℝ) := by
    apply (div_le_iff₀ (log_pos_of_two_le hX)).mp
    simpa only [logCoordinates, Finset.sum_div] using hsum
  calc
    ((∏ i, d i : ℕ) : ℝ) = Real.exp (∑ i, Real.log (d i : ℝ)) := by
      rw [Real.exp_sum, Nat.cast_prod]
      apply Finset.prod_congr rfl
      intro i _
      exact (Real.exp_log (by exact_mod_cast hd i)).symm
    _ ≤ Real.exp (rho * Real.log (X : ℝ)) := Real.exp_le_exp.mpr hlog

theorem divisor_coordinate_bound {ι : Type*} [Fintype ι]
    {X : ℕ} (hX : 2 ≤ X) {F : (ι → ℝ) → ℝ} {rho : ℝ}
    (hbudget : HasBudget F rho) {d : ι → ℕ} (hd : ∀ i, 0 < d i)
    (hF : F (logCoordinates X d) ≠ 0) (i : ι) :
    d i ≤ ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊ := by
  have hprod : 0 < ∏ i, d i := Finset.prod_pos fun i _ => hd i
  have hle : d i ≤ ∏ i, d i := Nat.le_of_dvd hprod (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  exact (Nat.le_floor_iff (Real.exp_pos _).le).mpr
    ((by exact_mod_cast hle : (d i : ℝ) ≤ ((∏ i, d i : ℕ) : ℝ)).trans
      (divisor_product_bound hX hbudget hd hF))

theorem abs_divisorCoefficient_le {ι : Type*} [Fintype ι]
    (X : ℕ) (F : (ι → ℝ) → ℝ) (d : ι → ℕ) :
    |divisorCoefficient X F d| ≤ |F (logCoordinates X d)| := by
  rw [divisorCoefficient, abs_mul, Finset.abs_prod]
  have hp : (∏ i, |(ArithmeticFunction.moebius (d i) : ℝ)|) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro i _
      exact abs_nonneg _
    · intro i _
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d i))
  simpa using mul_le_mul_of_nonneg_right hp (abs_nonneg (F (logCoordinates X d)))

theorem divisorSum_eq_bounded {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ℕ} (hX : 2 ≤ X) {F : (ι → ℝ) → ℝ} {rho : ℝ}
    (hbudget : HasBudget F rho) (m : ℕ) (hm : 0 < m) (b : ι → ℕ) :
    divisorSum X F m b =
      ∑ d ∈ (Fintype.piFinset (fun _ : ι =>
        Finset.Icc 1 ⌊Real.exp (rho * Real.log (X : ℝ))⌋₊)).filter
          (fun d => ∀ i, d i ∣ m + b i), divisorCoefficient X F d := by
  classical
  unfold divisorSum
  symm
  apply Finset.sum_subset
  · intro d hd
    have hdbox := Fintype.mem_piFinset.mp (Finset.mem_filter.mp hd).1
    have hddiv := (Finset.mem_filter.mp hd).2
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Nat.mem_divisors.mpr ⟨hddiv i, by omega⟩
  · intro d hd hdnot
    by_contra hne
    have hdpos : ∀ i, 0 < d i := by
      intro i
      have hdmem := Fintype.mem_piFinset.mp hd i
      exact Nat.pos_of_mem_divisors hdmem
    have hF := (divisorCoefficient_ne_zero_iff.mp hne).2
    apply hdnot
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr (fun i => ?_), fun i => ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hdpos i, divisor_coordinate_bound hX hbudget hdpos hF i⟩
    · exact (Nat.mem_divisors.mp (Fintype.mem_piFinset.mp hd i)).1

def residueStarts (X q c : ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun m => m % q = c

theorem residueStarts_card_error (X : ℕ) {q c : ℕ} (hq : 0 < q) (hc : c < q) :
    |((residueStarts X q c).card : ℝ) - (X : ℝ) / (q : ℝ)| ≤ 2 := by
  have hupper : (residueStarts X q c).card ≤
      (Finset.Icc (X / q) ((2 * X) / q)).card := by
    apply Finset.card_le_card_of_injOn (fun m => m / q)
    · intro m hm
      obtain ⟨hmrange, hmc⟩ := Finset.mem_filter.mp hm
      obtain ⟨hmlo, hmhi⟩ := Finset.mem_Ioc.mp hmrange
      exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right hmlo.le, Nat.div_le_div_right hmhi⟩
    · intro m hm n hn heq
      have hmc := (Finset.mem_filter.mp hm).2
      have hnc := (Finset.mem_filter.mp hn).2
      have hmdiv := Nat.div_add_mod m q
      have hndiv := Nat.div_add_mod n q
      change m / q = n / q at heq
      rw [heq, hmc] at hmdiv
      rw [hnc] at hndiv
      omega
  have hlower : (Finset.Ioo (X / q) ((2 * X) / q)).card ≤
      (residueStarts X q c).card := by
    apply Finset.card_le_card_of_injOn (fun k => q * k + c)
    · intro k hk
      obtain ⟨hklo, hkhi⟩ := Finset.mem_Ioo.mp hk
      have hrX := Nat.mod_lt X hq
      have hr2X := Nat.mod_lt (2 * X) hq
      have hXdiv := Nat.div_add_mod X q
      have h2Xdiv := Nat.div_add_mod (2 * X) q
      change q * k + c ∈ residueStarts X q c
      simp only [residueStarts, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have hh := Nat.mul_le_mul_left q (show X / q + 1 ≤ k by omega)
        simp only [Nat.mul_add, Nat.mul_one] at hh
        omega
      · have hh := Nat.mul_le_mul_left q (show k + 1 ≤ (2 * X) / q by omega)
        simp only [Nat.mul_add, Nat.mul_one] at hh
        omega
      · simp [Nat.add_mod, Nat.mod_eq_of_lt hc]
    · intro k _ l _ heq
      exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel heq)
  rw [Nat.card_Icc] at hupper
  rw [Nat.card_Ioo] at hlower
  have hord : X / q ≤ (2 * X) / q := Nat.div_le_div_right (by omega)
  have hu : (residueStarts X q c).card + X / q ≤ (2 * X) / q + 1 := by omega
  have hl : (2 * X) / q ≤ (residueStarts X q c).card + X / q + 1 := by omega
  have hrX := Nat.mod_lt X hq
  have hr2X := Nat.mod_lt (2 * X) hq
  have hXdiv := Nat.div_add_mod X q
  have h2Xdiv := Nat.div_add_mod (2 * X) q
  have hupperN : (residueStarts X q c).card * q ≤ X + 2 * q := by
    have hh := Nat.mul_le_mul_left q hu
    rw [Nat.mul_comm]
    simp only [Nat.mul_add, Nat.mul_one] at hh
    omega
  have hlowerN : X ≤ (residueStarts X q c).card * q + 2 * q := by
    have hh := Nat.mul_le_mul_left q hl
    rw [Nat.mul_comm]
    simp only [Nat.mul_add, Nat.mul_one] at hh
    omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hupperR : ((residueStarts X q c).card : ℝ) * q ≤ (X : ℝ) + 2 * q := by
    exact_mod_cast hupperN
  have hlowerR : (X : ℝ) ≤ ((residueStarts X q c).card : ℝ) * q + 2 * q := by
    exact_mod_cast hlowerN
  have hu' : ((residueStarts X q c).card : ℝ) ≤ (X : ℝ) / q + 2 := by
    have hh := (le_div_iff₀ hqR).mpr hupperR
    simpa [add_div, hqR.ne'] using hh
  have hl' : (X : ℝ) / q ≤ ((residueStarts X q c).card : ℝ) + 2 := by
    apply (div_le_iff₀ hqR).mpr
    nlinarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

def tupleModulus {ι : Type*} [Fintype ι] (d : ι → ℕ) : ℕ := Finset.univ.lcm d

theorem tupleModulus_pos {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, 0 < d i) : 0 < tupleModulus d := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr fun i _ => (hd i).ne'

theorem tupleModulus_dvd_prod {ι : Type*} [Fintype ι] (d : ι → ℕ) :
    tupleModulus d ∣ ∏ i, d i :=
  Finset.lcm_dvd fun _ hi => Finset.dvd_prod_of_mem d hi

theorem tupleModulus_le_prod {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, 0 < d i) : tupleModulus d ≤ ∏ i, d i :=
  Nat.le_of_dvd (Finset.prod_pos fun i _ => hd i) (tupleModulus_dvd_prod d)

theorem modEq_lcm_iff {ι : Type*} (s : Finset ι) (d : ι → ℕ) (m c : ℕ) :
    Nat.ModEq (s.lcm d) m c ↔ ∀ i ∈ s, Nat.ModEq (d i) m c := by
  classical
  constructor
  · intro h i hi
    exact h.of_dvd (Finset.dvd_lcm hi)
  · induction s using Finset.induction_on with
    | empty => intro _; exact Nat.modEq_one
    | @insert a s ha ih =>
      intro h
      rw [Finset.lcm_insert]
      exact Nat.mod_lcm (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem tuple_divisibility_iff_modEq {ι : Type*} [Fintype ι]
    (d b : ι → ℕ) {c : ℕ} (hc : ∀ i, d i ∣ c + b i) (m : ℕ) :
    (∀ i, d i ∣ m + b i) ↔ Nat.ModEq (tupleModulus d) m c := by
  rw [tupleModulus, modEq_lcm_iff]
  simp only [Finset.mem_univ, forall_true_left]
  constructor
  · intro hm i
    apply Nat.ModEq.add_right_cancel (Nat.ModEq.refl (b i))
    exact (Nat.modEq_zero_iff_dvd.mpr (hm i)).trans (Nat.modEq_zero_iff_dvd.mpr (hc i)).symm
  · intro hm i
    exact ((hm i |>.add_right (b i)).dvd_iff (dvd_refl (d i))).mpr (hc i)

def tupleCompatible {ι : Type*} [Fintype ι] (d b : ι → ℕ) : Prop :=
  ∃ c < tupleModulus d, ∀ i, d i ∣ c + b i

theorem compatible_of_solution {ι : Type*} [Fintype ι] {d b : ι → ℕ}
    (hd : ∀ i, 0 < d i) {m : ℕ} (hm : ∀ i, d i ∣ m + b i) : tupleCompatible d b := by
  refine ⟨m % tupleModulus d, Nat.mod_lt _ (tupleModulus_pos hd), ?_⟩
  apply (tuple_divisibility_iff_modEq d b hm _).mpr
  simp [Nat.ModEq]

def localCompatible {ι : Type*} [Fintype ι] (d b : ι → ℕ) : Prop :=
  ∀ p, Nat.Prime p → p ∣ tupleModulus d →
    ∀ i j, p ∣ d i → p ∣ d j → Nat.ModEq p (b i) (b j)

theorem localCompatible_of_tupleCompatible {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} (h : tupleCompatible d b) : localCompatible d b := by
  obtain ⟨c, _, hc⟩ := h
  intro p _ _ i j hpi hpj
  apply Nat.ModEq.add_left_cancel (Nat.ModEq.refl c)
  exact (Nat.modEq_zero_iff_dvd.mpr (hpi.trans (hc i))).trans
    (Nat.modEq_zero_iff_dvd.mpr (hpj.trans (hc j))).symm

theorem squarefree_dvd_of_prime_dvd {n k : ℕ} (hn : Squarefree n)
    (h : ∀ p, Nat.Prime p → p ∣ n → p ∣ k) : n ∣ k := by
  by_cases hk : k = 0
  · simp [hk]
  rw [← Nat.prod_primeFactors_of_squarefree hn, Nat.prod_primeFactors_dvd_iff hk]
  intro p hp
  obtain ⟨hpp, hpn, _⟩ := Nat.mem_primeFactors.mp hp
  exact Nat.mem_primeFactors.mpr ⟨hpp, h p hpp hpn, hk⟩

theorem tupleCompatible_of_localCompatible {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} (hd : ∀ i, Squarefree (d i)) (h : localCompatible d b) :
    tupleCompatible d b := by
  classical
  have hdpos : ∀ i, 0 < d i := fun i => Nat.pos_of_ne_zero (hd i).ne_zero
  let P := {p : ℕ // p ∈ (tupleModulus d).primeFactors}
  have hp : ∀ p : P, Nat.Prime p.val := fun p => Nat.prime_of_mem_primeFactors p.property
  have hit : ∀ p : P, ∃ i, p.val ∣ d i := by
    intro p
    have hpq := (Nat.mem_primeFactors.mp p.property).2.1
    obtain ⟨i, _, hi⟩ := ((hp p).prime.dvd_finsetProd_iff d).mp
      (hpq.trans (tupleModulus_dvd_prod d))
    exact ⟨i, hi⟩
  choose idx hidx using hit
  let a : P → ℕ := fun p => (p.val - b (idx p) % p.val) % p.val
  obtain ⟨c, hc⟩ := Nat.chineseRemainderOfFinset a (fun p : P => p.val) Finset.univ
    (fun p _ => (hp p).ne_zero) (by
      intro p _ q _ hpq
      exact (Nat.coprime_primes (hp p) (hp q)).mpr fun heq => hpq (Subtype.ext heq))
  apply compatible_of_solution hdpos (m := c)
  intro i
  apply squarefree_dvd_of_prime_dvd (hd i)
  intro p hpp hpi
  have hpq : p ∣ tupleModulus d := hpi.trans (Finset.dvd_lcm (Finset.mem_univ i))
  let p' : P := ⟨p, Nat.mem_primeFactors.mpr ⟨hpp, hpq, (tupleModulus_pos hdpos).ne'⟩⟩
  have hshift : Nat.ModEq p (b (idx p')) (b i) := h p hpp hpq (idx p') i (hidx p') hpi
  have hres : Nat.ModEq p c (a p') := hc p' (Finset.mem_univ _)
  have hb : b (idx p') % p < p := Nat.mod_lt _ hpp.pos
  have hzero : Nat.ModEq p (a p' + b (idx p')) 0 := by
    change (((p - b (idx p') % p) % p + b (idx p')) % p) = 0 % p
    rw [Nat.zero_mod, Nat.add_mod, Nat.mod_mod]
    calc
      ((p - b (idx p') % p) % p + b (idx p') % p) % p =
          ((p - b (idx p') % p) + b (idx p') % p) % p := by
            rw [Nat.add_mod (p - b (idx p') % p) (b (idx p') % p) p,
              Nat.mod_eq_of_lt hb]
      _ = 0 := by rw [Nat.sub_add_cancel hb.le, Nat.mod_self]
  exact Nat.modEq_zero_iff_dvd.mp ((hres.add hshift.symm).trans hzero)

theorem tupleCompatible_iff_localCompatible {ι : Type*} [Fintype ι]
    {d b : ι → ℕ} (hd : ∀ i, Squarefree (d i)) :
    tupleCompatible d b ↔ localCompatible d b :=
  ⟨localCompatible_of_tupleCompatible, tupleCompatible_of_localCompatible hd⟩

noncomputable def tupleStarts {ι : Type*} [Fintype ι] (X : ℕ) (d b : ι → ℕ) : Finset ℕ :=
  (Finset.Ioc X (2 * X)).filter fun m => ∀ i, d i ∣ m + b i

theorem tupleStarts_eq_residueStarts {ι : Type*} [Fintype ι] (X : ℕ)
    (d b : ι → ℕ) {c : ℕ} (hc : c < tupleModulus d) (hsol : ∀ i, d i ∣ c + b i) :
    tupleStarts X d b = residueStarts X (tupleModulus d) c := by
  classical
  ext m
  simp only [tupleStarts, residueStarts, Finset.mem_filter]
  rw [tuple_divisibility_iff_modEq d b hsol, Nat.ModEq, Nat.mod_eq_of_lt hc]

theorem tupleStarts_eq_empty_of_incompatible {ι : Type*} [Fintype ι] (X : ℕ)
    {d b : ι → ℕ} (hd : ∀ i, 0 < d i) (h : ¬ tupleCompatible d b) :
    tupleStarts X d b = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m hm
  exact h (compatible_of_solution hd (Finset.mem_filter.mp hm).2)

theorem tupleStarts_card_error {ι : Type*} [Fintype ι] (X : ℕ)
    {d b : ι → ℕ} (hd : ∀ i, 0 < d i) (h : tupleCompatible d b) :
    |((tupleStarts X d b).card : ℝ) - (X : ℝ) / (tupleModulus d : ℝ)| ≤ 2 := by
  obtain ⟨c, hc, hsol⟩ := h
  rw [tupleStarts_eq_residueStarts X d b hc hsol]
  exact residueStarts_card_error X (tupleModulus_pos hd) hc

theorem tupleModulus_squarefree {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ i, Squarefree (d i)) : Squarefree (tupleModulus d) := by
  have hq : 0 < tupleModulus d := tupleModulus_pos fun i => Nat.pos_of_ne_zero (hd i).ne_zero
  apply Squarefree.squarefree_of_dvd (y := primorial (tupleModulus d))
  · apply Finset.lcm_dvd
    intro i _
    apply squarefree_dvd_of_prime_dvd (hd i)
    intro p hp hpi
    apply hp.dvd_primorial_iff.mpr
    exact Nat.le_of_dvd hq (hpi.trans (Finset.dvd_lcm (Finset.mem_univ i)))
  · exact squarefree_primorial _

theorem not_prime_on_nonreduced_class {m c a q : ℕ} (hq : 0 < q)
    (hmc : Nat.ModEq q m c) (hcop : ¬ Nat.Coprime (c + a) q) (hlt : q < m + a) :
    ¬ Nat.Prime (m + a) := by
  intro hp
  have hnq : Nat.Coprime (m + a) q := hp.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt hq hlt)
  apply hcop
  rw [Nat.coprime_iff_gcd_eq_one, ← (hmc.add_right a).gcd_eq]
  exact hnq.gcd_eq_one

noncomputable def tupleDensity {ι : Type*} [Fintype ι] (d b : ι → ℕ) : ℝ := by
  classical
  exact if tupleCompatible d b then (tupleModulus d : ℝ)⁻¹ else 0

theorem tupleStarts_density_error {ι : Type*} [Fintype ι] (X : ℕ)
    {d b : ι → ℕ} (hd : ∀ i, 0 < d i) :
    |((tupleStarts X d b).card : ℝ) - (X : ℝ) * tupleDensity d b| ≤ 2 := by
  classical
  by_cases h : tupleCompatible d b
  · simpa [tupleDensity, h, div_eq_mul_inv] using tupleStarts_card_error X hd h
  · simp [tupleDensity, h, tupleStarts_eq_empty_of_incompatible X hd h]

theorem sum_divisibility_eq_counts {ι : Type*} [Fintype ι]
    (X : ℕ) (s : Finset (ι → ℕ)) (A : (ι → ℕ) → ℝ) (b : ι → ℕ) :
    (∑ m ∈ Finset.Ioc X (2 * X), ∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) =
      ∑ d ∈ s, A d * ((tupleStarts X d b).card : ℝ) := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [← Finset.sum_filter]
  simp only [tupleStarts, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem finite_density_sum_error {ι : Type*} [Fintype ι]
    {X : ℕ} (hX : 0 < X) (s : Finset (ι → ℕ)) (A : (ι → ℕ) → ℝ)
    (b : ι → ℕ) (hs : ∀ d ∈ s, ∀ i, 0 < d i) :
    |average X (fun m => ∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) -
        ∑ d ∈ s, A d * tupleDensity d b| ≤
      2 / (X : ℝ) * ∑ d ∈ s, |A d| := by
  classical
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  have hexp : average X (fun m => ∑ d ∈ s, if ∀ i, d i ∣ m + b i then A d else 0) -
      ∑ d ∈ s, A d * tupleDensity d b =
      (X : ℝ)⁻¹ * ∑ d ∈ s, A d * (((tupleStarts X d b).card : ℝ) -
        (X : ℝ) * tupleDensity d b) := by
    unfold average
    rw [sum_divisibility_eq_counts]
    simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d _
    field_simp [hXR.ne']
  rw [hexp, abs_mul, abs_of_pos (inv_pos.mpr hXR)]
  have he : |∑ d ∈ s, A d * (((tupleStarts X d b).card : ℝ) -
        (X : ℝ) * tupleDensity d b)| ≤ 2 * ∑ d ∈ s, |A d| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [abs_mul, mul_comm (2 : ℝ)]
    exact mul_le_mul_of_nonneg_left (tupleStarts_density_error X (hs d hd)) (abs_nonneg _)
  calc
    _ ≤ (X : ℝ)⁻¹ * (2 * ∑ d ∈ s, |A d|) := mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hXR.le)
    _ = _ := by ring

def positiveProductTuples (n Y : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 Y)).filter fun d => ∏ i, d i ≤ Y

theorem positiveProductTuples_card_bound (n Y : ℕ) :
    ((positiveProductTuples (n + 1) Y).card : ℝ) ≤
      (Y : ℝ) * (harmonic Y : ℝ) ^ n := by
  classical
  let B := Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 Y)
  let A : (Fin n → ℕ) → Finset (Fin (n + 1) → ℕ) :=
    fun e => (Finset.Icc 1 (Y / ∏ i, e i)).image fun v => Fin.cons v e
  have hsubset : positiveProductTuples (n + 1) Y ⊆ B.biUnion A := by
    intro d hd
    obtain ⟨hbox, hprod⟩ := Finset.mem_filter.mp hd
    have hemem : Fin.tail d ∈ B := Fintype.mem_piFinset.mpr
      fun i => (Fintype.mem_piFinset.mp hbox) i.succ
    have hdpos : ∀ i, 0 < d i := fun i => (Finset.mem_Icc.mp
      (Fintype.mem_piFinset.mp hbox i)).1
    have hepos : 0 < ∏ i : Fin n, Fin.tail d i := Finset.prod_pos fun i _ => hdpos i.succ
    refine Finset.mem_biUnion.mpr ⟨Fin.tail d, hemem, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨d 0, Finset.mem_Icc.mpr ⟨hdpos 0, ?_⟩, Fin.cons_self_tail d⟩
    apply (Nat.le_div_iff_mul_le hepos).mpr
    simpa only [Fin.prod_univ_succ, Fin.tail] using hprod
  have hcard : (positiveProductTuples (n + 1) Y).card ≤
      ∑ e ∈ B, Y / ∏ i, e i := by
    calc
      _ ≤ (B.biUnion A).card := Finset.card_le_card hsubset
      _ ≤ ∑ e ∈ B, (A e).card := Finset.card_biUnion_le
      _ ≤ ∑ e ∈ B, (Finset.Icc 1 (Y / ∏ i, e i)).card :=
        Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ = _ := by simp only [Nat.card_Icc, Nat.add_sub_cancel]
  calc
    ((positiveProductTuples (n + 1) Y).card : ℝ) ≤
        ∑ e ∈ B, ((Y / ∏ i, e i : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ ∑ e ∈ B, (Y : ℝ) / ((∏ i, e i : ℕ) : ℝ) :=
      Finset.sum_le_sum fun _ _ => Nat.cast_div_le
    _ = (Y : ℝ) * ∑ e ∈ B, ∏ i, (e i : ℝ)⁻¹ := by
      simp only [div_eq_mul_inv, Nat.cast_prod, Finset.prod_inv_distrib, Finset.mul_sum]
    _ = (Y : ℝ) * (harmonic Y : ℝ) ^ n := by
      congr 1
      dsimp only [B]
      rw [Finset.sum_prod_piFinset _ (fun (_ : Fin n) (a : ℕ) => (a : ℝ)⁻¹)]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      congr 1
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem positiveProductTuples_card_log_bound (n Y : ℕ) :
    ((positiveProductTuples (n + 1) Y).card : ℝ) ≤
      (Y : ℝ) * (1 + Real.log (Y : ℝ)) ^ n := by
  apply (positiveProductTuples_card_bound n Y).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg Y)
  apply pow_le_pow_left₀ (by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    exact Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
  exact harmonic_le_one_add_log Y

end LargePrimeGaps

end OAI
