import OAI.NumberTheory.EgyptianFractions.PrimeProductBound

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter Real

namespace Problem337

/-- Number of primes used by a logarithmic supply construction. -/
def supplyPrimeCount (a : ℝ) (m : ℕ) : ℕ := ⌈a * Real.log (m : ℝ)⌉₊

/-- A common supply denominator, before the rational-representation argument. -/
def supplyInteger (a : ℝ) (m : ℕ) : ℕ :=
  primePrefixProduct (supplyPrimeCount a m) ^ 2 *
    (⌊Real.log (Real.log (m : ℝ))⌋₊).factorial

lemma supplyInteger_pos (a : ℝ) (m : ℕ) : 0 < supplyInteger a m := by
  exact Nat.mul_pos (pow_pos (primePrefixProduct_pos _) _) (Nat.factorial_pos _)

lemma tendsto_supplyPrimeCount {a : ℝ} (ha : 0 < a) :
    Tendsto (supplyPrimeCount a) atTop atTop := by
  exact tendsto_nat_ceil_atTop.comp
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop ha)

lemma log_factorial_le_square (n : ℕ) : Real.log (n.factorial : ℝ) ≤ (n : ℝ)^2 := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  calc
    Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ)^n) := by
      apply Real.log_le_log
      · exact_mod_cast Nat.factorial_pos n
      · exact_mod_cast Nat.factorial_le_pow n
    _ = (n : ℝ) * Real.log (n : ℝ) := by rw [Real.log_pow]
    _ ≤ (n : ℝ) * (n : ℝ) := by
      gcongr
      exact (Real.log_le_sub_one_of_pos hnpos).trans (by linarith)
    _ = _ := by ring

lemma eventually_log_supplyInteger_le_aux {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (supplyInteger a m : ℝ) ≤
        (2 * (1 + δ)^2 * (a + δ) + δ) *
          Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)) := by
  have hx : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL := Real.tendsto_log_atTop.comp hx
  have hprime := (tendsto_supplyPrimeCount ha).eventually
    (eventually_log_primePrefixProduct_le hδ)
  have hsmall := hx.eventually ((Real.isLittleO_log_id_atTop).bound hδ)
  filter_upwards [hprime, hx.eventually_ge_atTop 1,
    hx.eventually_ge_atTop (1 / δ), hL.eventually_ge_atTop 0,
    hL.eventually_ge_atTop (Real.log (a + δ) / δ), hsmall] with m hm hx1 hxδ hL0 hLδ hs
  let x := Real.log (m : ℝ)
  let L := Real.log x
  let l := supplyPrimeCount a m
  have hxpos : 0 < x := by dsimp [x]; linarith
  have hLnonneg : 0 ≤ L := hL0
  have hapos : 0 < a + δ := by linarith
  have hlpos : 0 < (l : ℝ) := by
    have hu : a * x ≤ (l : ℝ) := Nat.le_ceil _
    exact lt_of_lt_of_le (mul_pos ha hxpos) hu
  have hlbound : (l : ℝ) ≤ (a + δ) * x := by
    have hc : (l : ℝ) < a * x + 1 := Nat.ceil_lt_add_one (by positivity)
    have hh : 1 ≤ δ * x := by
      simpa [x, mul_comm] using (div_le_iff₀ hδ).mp hxδ
    nlinarith
  have hlogl : Real.log (l : ℝ) ≤ (1 + δ) * L := by
    have hh : Real.log (a + δ) ≤ δ * L := by
      simpa [L, x, Function.comp_apply, mul_comm] using (div_le_iff₀ hδ).mp hLδ
    calc
      Real.log (l : ℝ) ≤ Real.log ((a + δ) * x) :=
        Real.log_le_log hlpos hlbound
      _ = Real.log (a + δ) + L := by rw [Real.log_mul hapos.ne' hxpos.ne']
      _ ≤ _ := by nlinarith
  have hprimebound : Real.log (primePrefixProduct l : ℝ) ≤
      (1 + δ)^2 * (a + δ) * x * L := by
    calc
      Real.log (primePrefixProduct l : ℝ) ≤
          (1 + δ) * (l : ℝ) * Real.log (l : ℝ) := hm
      _ ≤ (1 + δ) * ((a + δ) * x) * ((1 + δ) * L) := by
        gcongr
      _ = _ := by ring
  have hLsmall : L ≤ δ * x := by
    change ‖L‖ ≤ δ * ‖x‖ at hs
    simpa only [Real.norm_eq_abs, abs_of_nonneg hLnonneg, abs_of_pos hxpos] using hs
  have hfact : Real.log ((⌊L⌋₊).factorial : ℝ) ≤ δ * x * L := by
    calc
      Real.log ((⌊L⌋₊).factorial : ℝ) ≤ (⌊L⌋₊ : ℝ)^2 := log_factorial_le_square _
      _ ≤ L^2 := by gcongr; exact Nat.floor_le hLnonneg
      _ ≤ δ * x * L := by nlinarith
  have hp0 : (primePrefixProduct l : ℝ) ≠ 0 := by
    exact_mod_cast (primePrefixProduct_pos l).ne'
  have hf0 : ((⌊L⌋₊).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (⌊L⌋₊)).ne'
  change Real.log (((primePrefixProduct l)^2 * (⌊L⌋₊).factorial : ℕ) : ℝ) ≤ _
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (pow_ne_zero _ hp0) hf0, Real.log_pow]
  change 2 * Real.log (primePrefixProduct l : ℝ) + Real.log ((⌊L⌋₊).factorial : ℝ) ≤
    (2 * (1 + δ)^2 * (a + δ) + δ) * x * L
  nlinarith

/-- The logarithmic supply has the sharp leading size coefficient `2*a`.
Only elementary Chebyshev bounds are used; no prime number theorem is assumed. -/
lemma eventually_log_supplyInteger_le {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (supplyInteger a m : ℝ) ≤
        (2 * a + ε) * Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)) := by
  have hcont : ContinuousAt (fun δ : ℝ => 2 * (1 + δ)^2 * (a + δ) + δ) 0 := by
    fun_prop
  have hevent : ∀ᶠ δ : ℝ in 𝓝 0,
      2 * (1 + δ)^2 * (a + δ) + δ < 2 * a + ε := by
    have hh : ∀ᶠ y : ℝ in 𝓝 (2 * (1 + (0 : ℝ))^2 * (a + 0) + 0),
        y < 2 * a + ε := eventually_lt_nhds (by norm_num; linarith)
    exact hcont.tendsto.eventually hh
  obtain ⟨r, hr, hrr⟩ := Metric.eventually_nhds_iff.mp hevent
  have hδ : 0 < r / 2 := by positivity
  have hcoeff : 2 * (1 + r/2)^2 * (a + r/2) + r/2 ≤ 2*a+ε := by
    apply le_of_lt (hrr ?_)
    simp only [dist_zero_right, Real.norm_eq_abs, abs_of_pos hδ]
    linarith
  have hx : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hL := Real.tendsto_log_atTop.comp hx
  filter_upwards [eventually_log_supplyInteger_le_aux ha hδ,
    hx.eventually_ge_atTop 0, hL.eventually_ge_atTop 0] with m hm hx0 hL0
  exact hm.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoeff hx0) hL0)

lemma eventual_marked_supply_size {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop,
      Real.log (supplyInteger (16 / Real.log 2) m : ℝ) ≤
        (32 / Real.log 2 + ε) * Real.log (m : ℝ) *
          Real.log (Real.log (m : ℝ)) := by
  simpa only [show (2 : ℝ) * (16 / Real.log 2) = 32 / Real.log 2 by ring] using
    eventually_log_supplyInteger_le
      (a := 16 / Real.log 2) (ε := ε) (by positivity) hε

lemma log_supplyInteger_lower (a : ℝ) (m : ℕ) :
    2 * a * Real.log 2 * Real.log (m : ℝ) ≤
      Real.log (supplyInteger a m : ℝ) := by
  let l := supplyPrimeCount a m
  let f := (⌊Real.log (Real.log (m : ℝ))⌋₊).factorial
  have hp0 : (primePrefixProduct l : ℝ) ≠ 0 := by
    exact_mod_cast (primePrefixProduct_pos l).ne'
  have hf0 : (f : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos _).ne'
  have hpp : (l : ℝ) * Real.log 2 ≤ Real.log (primePrefixProduct l : ℝ) := by
    calc
      (l : ℝ) * Real.log 2 = Real.log ((2 : ℝ)^l) := (Real.log_pow _ _).symm
      _ ≤ Real.log (primePrefixProduct l : ℝ) := by
        apply Real.log_le_log (by positivity)
        exact_mod_cast two_pow_le_primePrefixProduct l
  have hl : a * Real.log (m : ℝ) ≤ (l : ℝ) := Nat.le_ceil _
  have hlog2 : 0 < Real.log 2 := by positivity
  have hff : 0 ≤ Real.log (f : ℝ) := Real.log_natCast_nonneg f
  change _ ≤ Real.log (((primePrefixProduct l)^2 * f : ℕ) : ℝ)
  rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul (pow_ne_zero _ hp0) hf0, Real.log_pow]
  have hmul := mul_le_mul_of_nonneg_right hl hlog2.le
  norm_num only [Nat.cast_ofNat]
  nlinarith

lemma marked_supplyInteger_gt {m : ℕ} (hm : 2 ≤ m) :
    m < supplyInteger (16 / Real.log 2) m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm)
  have hlog2 : Real.log 2 ≠ 0 := by positivity
  have hlower := log_supplyInteger_lower (16 / Real.log 2) m
  have heq : 2 * (16 / Real.log 2) * Real.log 2 = (32 : ℝ) := by
    field_simp
    ring
  rw [heq] at hlower
  by_contra h
  have hle : supplyInteger (16 / Real.log 2) m ≤ m := by omega
  have hlogle : Real.log (supplyInteger (16 / Real.log 2) m : ℝ) ≤ Real.log (m : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast supplyInteger_pos (16 / Real.log 2) m
    · exact_mod_cast hle
  linarith

lemma marked_supply_size {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, 2 ≤ M ∧ ∀ m : ℕ, M ≤ m →
      m < supplyInteger (16 / Real.log 2) m ∧
      Real.log (supplyInteger (16 / Real.log 2) m : ℝ) ≤
        (32 / Real.log 2 + ε) * Real.log (m : ℝ) *
          Real.log (Real.log (m : ℝ)) := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (eventual_marked_supply_size hε)
  refine ⟨max M 2, le_max_right _ _, ?_⟩
  intro m hm
  exact ⟨marked_supplyInteger_gt (le_trans (le_max_right _ _) hm),
    hM m (le_trans (le_max_left _ _) hm)⟩

lemma supplyPrimeCount_marked_eq (m : ℕ) :
    supplyPrimeCount (16 / Real.log 2) m =
      ⌈4 * Real.log ((m ^ 4 : ℕ) : ℝ) / Real.log 2⌉₊ := by
  unfold supplyPrimeCount
  rw [Nat.cast_pow, Real.log_pow]
  congr 1
  ring

lemma eventually_small_dvd_supplyInteger (a : ℝ) (S : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ s : ℕ, 1 ≤ s → s ≤ S → s ∣ supplyInteger a m := by
  have hL : Tendsto (fun m : ℕ => Real.log (Real.log (m : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hL.eventually_ge_atTop (S : ℝ)] with m hm s hs hS
  have hfloor : S ≤ ⌊Real.log (Real.log (m : ℝ))⌋₊ := Nat.le_floor hm
  have hdvd := Nat.dvd_factorial (show 0 < s by omega) (hS.trans hfloor)
  exact hdvd.trans (dvd_mul_left _ _)

/-- The prime product indexed by the argument used in the rational supply. -/
def rationalSupplyBase (u : ℕ) : ℕ :=
  primePrefixProduct ⌈4 * Real.log (u : ℝ) / Real.log 2⌉₊

lemma rationalSupplyBase_dvd_mono {u v : ℕ} (hu : 0 < u) (huv : u ≤ v) :
    rationalSupplyBase u ∣ rationalSupplyBase v := by
  apply primePrefixProduct_dvd_mono
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ Real.log 2)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 4)
  apply Real.log_le_log
  · exact_mod_cast hu
  · exact_mod_cast huv

lemma rationalSupplyBase_fourth_power (m : ℕ) :
    rationalSupplyBase (m ^ 4) = primePrefixProduct (supplyPrimeCount (16 / Real.log 2) m) := by
  unfold rationalSupplyBase
  rw [supplyPrimeCount_marked_eq]

lemma rationalSupplyBase_sq_dvd_supplyInteger {u m : ℕ} (hu : 0 < u) (hum : u ≤ m ^ 4) :
    rationalSupplyBase u ^ 2 ∣ supplyInteger (16 / Real.log 2) m := by
  have hd := rationalSupplyBase_dvd_mono hu hum
  rw [rationalSupplyBase_fourth_power] at hd
  exact (pow_dvd_pow_of_dvd hd 2).trans (dvd_mul_right _ _)

lemma fourth_power_le_divisors_card_rationalSupplyBase (u : ℕ) :
    u ^ 4 ≤ (rationalSupplyBase u).divisors.card := by
  unfold rationalSupplyBase
  rw [card_divisors_primePrefixProduct]
  by_cases hu : u = 0
  · simp [hu]
  have huR : (0 : ℝ) < u := by exact_mod_cast Nat.pos_of_ne_zero hu
  let l := ⌈4 * Real.log (u : ℝ) / Real.log 2⌉₊
  have hlog2 : 0 < Real.log 2 := by positivity
  have hc : 4 * Real.log (u : ℝ) ≤ (l : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).mp (Nat.le_ceil _)
  have hlogs : Real.log ((u : ℝ)^4) ≤ Real.log ((2 : ℝ)^l) := by
    rw [Real.log_pow, Real.log_pow]
    norm_num
    exact hc
  have hreal : (u : ℝ)^4 ≤ (2 : ℝ)^l :=
    (Real.log_le_log_iff (by positivity) (by positivity)).mp hlogs
  exact_mod_cast hreal

lemma rationalSupplyBase_le_supplyInteger (u : ℕ) :
    rationalSupplyBase u ≤ supplyInteger (4 / Real.log 2) u := by
  have heq : rationalSupplyBase u =
      primePrefixProduct (supplyPrimeCount (4 / Real.log 2) u) := by
    unfold rationalSupplyBase supplyPrimeCount
    congr 2
    ring
  rw [heq]
  let P := primePrefixProduct (supplyPrimeCount (4 / Real.log 2) u)
  let f := (⌊Real.log (Real.log (u : ℝ))⌋₊).factorial
  have hP : 1 ≤ P := primePrefixProduct_pos _
  have hf : 1 ≤ f := Nat.factorial_pos _
  change P ≤ P^2 * f
  have hmul := Nat.mul_le_mul_left (P^2) hf
  nlinarith

lemma eventually_log_rationalSupplyBase_le :
    ∀ᶠ u : ℕ in atTop,
      Real.log (rationalSupplyBase u : ℝ) ≤
        (8 / Real.log 2 + 1) * Real.log (u : ℝ) * Real.log (Real.log (u : ℝ)) := by
  have h := eventually_log_supplyInteger_le (a := 4 / Real.log 2)
    (ε := 1) (by positivity) (by norm_num)
  filter_upwards [h] with u hu
  calc
    Real.log (rationalSupplyBase u : ℝ) ≤ Real.log (supplyInteger (4 / Real.log 2) u : ℝ) := by
      apply Real.log_le_log
      · exact_mod_cast primePrefixProduct_pos _
      · exact_mod_cast rationalSupplyBase_le_supplyInteger u
    _ ≤ _ := by
      simpa only [show (2 : ℝ) * (4 / Real.log 2) = 8 / Real.log 2 by ring] using hu

end Problem337

end

end OAI
