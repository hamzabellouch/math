import Mathlib

namespace OAI

noncomputable section

namespace HeightThree.PTypical

variable {A B : Type*} [CommRing A] [CommRing B]

def series (p : ℕ) (c : ℕ → B) : PowerSeries B :=
  PowerSeries.mk (Function.extend (fun n : ℕ => p^n) c (fun _ => 0))

@[simp] theorem coeff_series_power (p : ℕ) (hp : 2 ≤ p) (c : ℕ → B) (n : ℕ) :
    (series p c).coeff (p^n) = c n := by
  simp only [series, PowerSeries.coeff_mk, (Nat.pow_right_injective hp).extend_apply]

@[simp] theorem coeff_series_outside (p j : ℕ) (c : ℕ → B)
    (hj : ¬ ∃ n : ℕ, p^n = j) : (series p c).coeff j = 0 := by
  simp only [series, PowerSeries.coeff_mk, Function.extend_apply' c (fun _ => 0) j hj]

@[simp] theorem series_constant (p : ℕ) (hp : 2 ≤ p) (c : ℕ → B) :
    (series p c).constantCoeff = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  exact coeff_series_outside p 0 c (by
    rintro ⟨n, hn⟩
    exact pow_ne_zero n (by omega : p ≠ 0) hn)

@[simp] theorem series_linear (p : ℕ) (hp : 2 ≤ p) (c : ℕ → B) :
    (series p c).coeff 1 = c 0 := by
  simpa only [pow_zero] using coeff_series_power p hp c 0

def HasIntegralNumerators [Algebra ℚ B] (ι : A →+* B) (p : ℕ)
    (f : PowerSeries B) : Prop :=
  ∀ j, (f.coeff j = 0) ∨
    ∃ n : ℕ, j = p^n ∧ ∃ a : A, f.coeff j = ((p : ℚ)⁻¹)^n • ι a

theorem series_integralNumerators [Algebra ℚ B] (ι : A →+* B)
    (p : ℕ) (hp : 2 ≤ p) (a : ℕ → A) :
    HasIntegralNumerators ι p (series p (fun n => ((p : ℚ)⁻¹)^n • ι (a n))) := by
  intro j
  by_cases hj : ∃ n : ℕ, p^n = j
  · obtain ⟨n, rfl⟩ := hj
    right
    exact ⟨n, rfl, a n, coeff_series_power p hp _ n⟩
  · exact Or.inl (coeff_series_outside p j _ hj)

def IntegralSeries (ι : A →+* B) {σ : Type*} (f : MvPowerSeries σ B) : Prop :=
  ∀ d, ∃ a : A, ι a = MvPowerSeries.coeff d f

def integralLift (ι : A →+* B) {σ : Type*} (f : MvPowerSeries σ B)
    (hf : IntegralSeries ι f) : MvPowerSeries σ A :=
  fun d => (hf d).choose

theorem map_integralLift (ι : A →+* B) {σ : Type*} (f : MvPowerSeries σ B)
    (hf : IntegralSeries ι f) : MvPowerSeries.map ι (integralLift ι f hf) = f := by
  ext d
  exact (hf d).choose_spec

theorem integral_iff_range (ι : A →+* B) {σ : Type*} (f : MvPowerSeries σ B) :
    IntegralSeries ι f ↔ f ∈ (MvPowerSeries.map ι : MvPowerSeries σ A →+*
      MvPowerSeries σ B).range := by
  constructor
  · intro hf
    exact ⟨integralLift ι f hf, map_integralLift ι f hf⟩
  · rintro ⟨a, rfl⟩ d
    exact ⟨MvPowerSeries.coeff d a, by simp⟩

theorem power_difference (p n : ℕ) {σ : Type*}
    {a b : MvPowerSeries σ A} (h : (p : MvPowerSeries σ A) ∣ a - b) :
    ∃ v : MvPowerSeries σ A,
      a^(p^n) - b^(p^n) = (p : MvPowerSeries σ A)^(n+1) * v :=
  dvd_sub_pow_of_dvd_sub h n

theorem rational_cancel (p : ℕ) (hp : p ≠ 0) (n : ℕ) [Algebra ℚ B] (x : B) :
    (((p : ℚ)⁻¹)^n) • ((p : B)^(n+1) * x) = (p : B) * x := by
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hc : (((p : ℚ)⁻¹)^n) • ((p : B)^n) = 1 := by
    rw [Algebra.smul_def]
    calc
      _ = algebraMap ℚ B ((((p : ℚ)⁻¹)^n) * (p : ℚ)^n) := by simp
      _ = 1 := by simp [hpQ]
  rw [pow_succ, mul_assoc, ← smul_mul_assoc, hc, one_mul]

theorem logarithm_difference [Algebra ℚ B] (ι : A →+* B) (p : ℕ)
    (hp : p ≠ 0) (f : PowerSeries B) (hf : HasIntegralNumerators ι p f)
    {σ : Type*} (a b : MvPowerSeries σ A)
    (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0)
    (hab : (p : MvPowerSeries σ A) ∣ a - b) :
    ∃ v : MvPowerSeries σ A,
      f.subst (a.map ι) - f.subst (b.map ι) =
        (p : MvPowerSeries σ B) * v.map ι := by
  classical
  let θ : A →+ B := (AddMonoidHom.mulLeft (p : B)).comp ι.toAddMonoidHom
  have ha' : PowerSeries.HasSubst (a.map ι) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp [ha])
  have hb' : PowerSeries.HasSubst (b.map ι) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp [hb])
  have hc (d : σ →₀ ℕ) :
      MvPowerSeries.coeff d (f.subst (a.map ι) - f.subst (b.map ι)) ∈ θ.range := by
    rw [map_sub, PowerSeries.coeff_subst ha', PowerSeries.coeff_subst hb',
      ← finsum_sub_distrib (PowerSeries.coeff_subst_finite ha' f d)
        (PowerSeries.coeff_subst_finite hb' f d)]
    refine finsum_induction (fun z => z ∈ θ.range) θ.range.zero_mem
      (fun _ _ => θ.range.add_mem) ?_
    intro j
    rcases hf j with hzero | ⟨n, rfl, u, hu⟩
    · simp [hzero]
    obtain ⟨w, hw⟩ := power_difference p n hab
    have hwc : ι (MvPowerSeries.coeff d (a^(p^n))) -
        ι (MvPowerSeries.coeff d (b^(p^n))) =
          (p : B)^(n+1) * ι (MvPowerSeries.coeff d w) := by
      have hh := congrArg (fun z => ι (MvPowerSeries.coeff d z)) hw
      rw [map_sub, map_sub] at hh
      rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := A)), ← map_pow,
        MvPowerSeries.coeff_C_mul] at hh
      simpa using hh
    refine ⟨u * MvPowerSeries.coeff d w, ?_⟩
    change (p : B) * ι (u * MvPowerSeries.coeff d w) = _
    simp only [hu, ← map_pow, MvPowerSeries.coeff_map, smul_eq_mul,
      ← mul_sub, hwc]
    rw [smul_mul_assoc]
    calc
      (p : B) * ι (u * MvPowerSeries.coeff d w) =
          ((p : ℚ)⁻¹)^n • ((p : B)^(n+1) * (ι u * ι (MvPowerSeries.coeff d w))) := by
            rw [rational_cancel p hp, map_mul]
      _ = ((p : ℚ)⁻¹)^n • (ι u * ((p : B)^(n+1) * ι (MvPowerSeries.coeff d w))) := by
            congr 1
            ring
  choose v hv using hc
  refine ⟨fun d => v d, ?_⟩
  ext d
  have hh := hv d
  change (p : B) * ι (v d) = _ at hh
  rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := B)), MvPowerSeries.coeff_C_mul]
  change _ = (p : B) * ι (v d)
  exact hh.symm

lemma constant_dvd_iff {σ : Type*} (r : A) (a : MvPowerSeries σ A) :
    MvPowerSeries.C r ∣ a ↔ ∀ d, r ∣ MvPowerSeries.coeff d a := by
  constructor
  · rintro ⟨b, rfl⟩ d
    exact ⟨MvPowerSeries.coeff d b, MvPowerSeries.coeff_C_mul d b r⟩
  · intro h
    choose b hb using h
    let c : MvPowerSeries σ A := fun d => b d
    refine ⟨c, ?_⟩
    ext d
    exact (hb d).trans (MvPowerSeries.coeff_C_mul d c r).symm

theorem frobenius_lift_series (p : ℕ) [hp : Fact p.Prime]
    (ψ : A →+* A) (hψ : ∀ a : A, (p : A) ∣ ψ a - a^p)
    {σ : Type*} (a : MvPowerSeries σ A) :
    (p : MvPowerSeries σ A) ∣
      (a.map ψ).expand p hp.out.ne_zero - a^p := by
  by_cases hu : IsUnit (p : A)
  · have hu' : IsUnit (p : MvPowerSeries σ A) := by
      simpa using hu.map (MvPowerSeries.C (σ := σ) (R := A))
    exact hu'.dvd
  let I : Ideal A := Ideal.span {(p : A)}
  let π : A →+* A ⧸ I := Ideal.Quotient.mk I
  let : CharP (A ⧸ I) p := CharP.quotient A p hu
  have hπ : π.comp ψ = (frobenius (A ⧸ I) p).comp π := by
    ext x
    change π (ψ x) = (π x)^p
    rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact hψ x
  have heq : (((a.map ψ).expand p hp.out.ne_zero) - a^p).map π = 0 := by
    rw [map_sub, MvPowerSeries.map_expand, MvPowerSeries.map_map, hπ,
      ← MvPowerSeries.map_map, ← MvPowerSeries.map_expand,
      MvPowerSeries.map_frobenius_expand, map_pow, sub_self]
  rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := A)), constant_dvd_iff]
  intro d
  have hd := congrArg (MvPowerSeries.coeff d) heq
  rw [MvPowerSeries.coeff_map, map_zero] at hd
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hd)

def twist {σ : Type*} (p : ℕ) (hp : p ≠ 0) (ψ : A →+* A) :
    MvPowerSeries σ A →+* MvPowerSeries σ A :=
  (MvPowerSeries.expand p hp).toRingHom.comp (MvPowerSeries.map ψ)

@[simp] lemma twist_coe {σ : Type*} (p : ℕ) (hp : p ≠ 0) (ψ : A →+* A)
    (a : MvPowerSeries σ A) : twist p hp ψ a = (a.map ψ).expand p hp := rfl

theorem twist_iterate_congr (p : ℕ) [hp : Fact p.Prime]
    (ψ : A →+* A) (hψ : ∀ a : A, (p : A) ∣ ψ a - a^p)
    {σ : Type*} (a : MvPowerSeries σ A) (n : ℕ) :
    (p : MvPowerSeries σ A) ∣
      (twist p hp.out.ne_zero ψ ^ n) a - a^(p^n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ, pow_mul]
    change (p : MvPowerSeries σ A) ∣
      twist p hp.out.ne_zero ψ ((twist p hp.out.ne_zero ψ ^ n) a) - (a^(p^n))^p
    have h₁ := frobenius_lift_series p ψ hψ ((twist p hp.out.ne_zero ψ ^ n) a)
    have h₂ := ih.trans (sub_dvd_pow_sub_pow _ _ p)
    simpa only [twist_coe, sub_add_sub_cancel] using dvd_add h₁ h₂

theorem twist_iterate {σ : Type*} (p : ℕ) (hp : p ≠ 0) (ψ : A →+* A)
    (a : MvPowerSeries σ A) (n : ℕ) :
    (twist p hp ψ ^ n) a = (a.map (ψ^n)).expand (p^n) (pow_ne_zero n hp) := by
  induction n with
  | zero =>
    change a = (a.map (RingHom.id A)).expand 1 _
    simp [MvPowerSeries.map_id]
  | succ n ih =>
    rw [pow_succ']
    change twist p hp ψ ((twist p hp ψ ^ n) a) = _
    rw [ih, twist_coe, MvPowerSeries.map_expand, MvPowerSeries.map_map,
      ← MvPowerSeries.expand_mul]
    simp only [pow_succ', RingHom.mul_def]

@[simp] theorem twist_iterate_constant {σ : Type*} (p : ℕ) (hp : p ≠ 0) (ψ : A →+* A)
    (a : MvPowerSeries σ A) (n : ℕ) :
    ((twist p hp ψ ^ n) a).constantCoeff = (ψ^n) a.constantCoeff := by
  simp [twist_iterate]

theorem map_twist_iterate {σ : Type*} (p : ℕ) (hp : p ≠ 0)
    (ι : A →+* B) (ψ : A →+* A) (χ : B →+* B) (hc : χ.comp ι = ι.comp ψ)
    (a : MvPowerSeries σ A) (n : ℕ) :
    (MvPowerSeries.map ι) ((twist p hp ψ ^ n) a) =
      (twist p hp χ ^ n) (a.map ι) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ' (twist p hp ψ), pow_succ' (twist p hp χ)]
    change (twist p hp ψ ((twist p hp ψ ^ n) a)).map ι =
      twist p hp χ ((twist p hp χ ^ n) (a.map ι))
    rw [twist_coe, twist_coe, MvPowerSeries.map_expand, ← ih,
      MvPowerSeries.map_map, MvPowerSeries.map_map, hc]

theorem twist_iterate_subst {σ : Type*} (p : ℕ) (hp : p ≠ 0) (ψ : A →+* A)
    (f : PowerSeries A) (a : MvPowerSeries σ A) (ha : PowerSeries.HasSubst a) (n : ℕ) :
    (twist p hp ψ ^ n) (f.subst a) =
      (f.map (ψ^n)).subst ((twist p hp ψ ^ n) a) := by
  rw [twist_iterate, twist_iterate, PowerSeries.map_subst ha,
    PowerSeries.expand_subst _ _ (show PowerSeries.HasSubst (a.map (ψ^n)) from by
      simpa only [PowerSeries.HasSubst, MvPowerSeries.constantCoeff_map] using ha.map (ψ^n))]

theorem integralNumerators_map [Algebra ℚ B] (ι : A →+* B)
    (ψ : A →+* A) (χ : B →ₐ[ℚ] B) (hc : χ.toRingHom.comp ι = ι.comp ψ)
    (p : ℕ) (f : PowerSeries B) (hf : HasIntegralNumerators ι p f) :
    HasIntegralNumerators ι p (f.map χ.toRingHom) := by
  intro j
  rw [PowerSeries.coeff_map]
  rcases hf j with h | ⟨n, hn, a, ha⟩
  · left; simp [h]
  · right
    refine ⟨n, hn, ψ a, ?_⟩
    rw [ha]
    change χ (((p : ℚ)⁻¹)^n • ι a) = _
    rw [χ.map_smul_of_tower]
    congr 1
    exact DFunLike.congr_fun hc a

theorem integralNumerators_map_iterate [Algebra ℚ B] (ι : A →+* B)
    (ψ : A →+* A) (χ : B →ₐ[ℚ] B) (hc : χ.toRingHom.comp ι = ι.comp ψ)
    (p : ℕ) (f : PowerSeries B) (hf : HasIntegralNumerators ι p f) (n : ℕ) :
    HasIntegralNumerators ι p (f.map (χ.toRingHom^n)) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    rw [pow_succ']
    exact integralNumerators_map ι ψ χ hc p _ ih

theorem order_difference_powers {σ : Type*} (a b : MvPowerSeries σ A)
    (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0) (n : ℕ)
    (hab : (n : ℕ∞) ≤ (a - b).order) (k : ℕ) :
    ((n+k : ℕ) : ℕ∞) ≤ (a^(k+1) - b^(k+1)).order := by
  induction k with
  | zero => simpa using hab
  | succ k ih =>
    have heq : a^(k+1+1) - b^(k+1+1) =
        a * (a^(k+1) - b^(k+1)) + (a-b) * b^(k+1) := by ring
    rw [heq]
    apply le_trans _ MvPowerSeries.min_order_le_add
    apply le_min
    · apply le_trans _ MvPowerSeries.le_order_mul
      calc
        ((n+(k+1) : ℕ) : ℕ∞) = 1 + ((n+k : ℕ) : ℕ∞) := by push_cast; ac_rfl
        _ ≤ a.order + (a^(k+1) - b^(k+1)).order := add_le_add
          (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr ha) ih
    · apply le_trans _ MvPowerSeries.le_order_mul
      calc
        ((n+(k+1) : ℕ) : ℕ∞) = (n : ℕ∞) + ((k+1 : ℕ) : ℕ∞) := by simp
        _ ≤ (a-b).order + (b^(k+1)).order := add_le_add hab
          (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero (k+1) hb)

theorem coeff_log_difference {σ : Type*} (f : PowerSeries A) (hf : f.coeff 1 = 1)
    (a b : MvPowerSeries σ A) (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0)
    (n : ℕ) (hab : (n : ℕ∞) ≤ (a-b).order) (d : σ →₀ ℕ) (hd : d.degree ≤ n) :
    MvPowerSeries.coeff d (f.subst a - f.subst b) = MvPowerSeries.coeff d (a-b) := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  have hb' := PowerSeries.HasSubst.of_constantCoeff_zero hb
  rw [map_sub, PowerSeries.coeff_subst ha', PowerSeries.coeff_subst hb',
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite ha' f d)
      (PowerSeries.coeff_subst_finite hb' f d), finsum_eq_single _ 1]
  · simp [hf]
  · intro j hj
    rw [← smul_sub, ← map_sub]
    by_cases hj0 : j = 0
    · simp [hj0]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have hk : 0 < k := by omega
      have hlt : (d.degree : ℕ∞) < ((n+k : ℕ) : ℕ∞) := by exact_mod_cast (by omega : d.degree < n+k)
      rw [MvPowerSeries.coeff_of_lt_order (hlt.trans_le
        (order_difference_powers a b ha hb n hab k)), smul_zero]

theorem order_log_difference {σ : Type*} (f : PowerSeries A) (hf : f.coeff 1 = 1)
    (a b : MvPowerSeries σ A) (ha : a.constantCoeff = 0) (hb : b.constantCoeff = 0)
    (n : ℕ) (hab : (n : ℕ∞) ≤ (a-b).order) :
    (n : ℕ∞) ≤ (f.subst a - f.subst b).order := by
  apply MvPowerSeries.nat_le_order
  intro d hd
  rw [coeff_log_difference f hf a b ha hb n hab d hd.le]
  exact MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd) hab)

theorem coeff_twist_iterate_zero {σ : Type*} (p : ℕ) (hp : 2 ≤ p)
    (ψ : A →+* A) (a : MvPowerSeries σ A) (k : ℕ) (hk : 0 < k)
    (n : ℕ) (hn : 0 < n) (ha : (n : ℕ∞) ≤ a.order)
    (d : σ →₀ ℕ) (hd : d.degree ≤ n) :
    MvPowerSeries.coeff d ((twist p (by omega) ψ ^ k) a) = 0 := by
  rw [twist_iterate]
  apply MvPowerSeries.coeff_of_lt_order
  rw [MvPowerSeries.order_expand, nsmul_eq_mul]
  have hpk : 1 < p^k := one_lt_pow₀ (by omega) (by omega)
  have hlt : d.degree < p^k * n := lt_of_le_of_lt hd (by nlinarith)
  calc
    (d.degree : ℕ∞) < ((p^k * n : ℕ) : ℕ∞) := by exact_mod_cast hlt
    _ = (p^k : ℕ) * (n : ℕ∞) := by simp
    _ ≤ (p^k : ℕ) * (a.map (ψ^k)).order := by
      gcongr
      exact ha.trans (MvPowerSeries.le_order_map _)

theorem subst_twist_iterate {σ : Type*} (p : ℕ) (hp : p ≠ 0) (ψ : A →+* A)
    (f : PowerSeries A) (a : MvPowerSeries σ A) (ha : PowerSeries.HasSubst a) (n : ℕ) :
    PowerSeries.subst a ((twist p hp ψ ^ n) f) = (f.map (ψ^n)).subst (a^(p^n)) := by
  rw [twist_iterate]
  change ((f.map (ψ^n)).expand (p^n) (pow_ne_zero n hp)).subst a = _
  rw [PowerSeries.expand_apply, PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.X_pow (pow_ne_zero n hp)) ha,
    PowerSeries.subst_pow ha, PowerSeries.subst_X ha]

lemma divide_p_mul [Algebra ℚ B] (p : ℕ) (hp : p ≠ 0) (x : B) :
    (p : ℚ)⁻¹ • ((p : B) * x) = x := by
  have h : (p : B) * x = (p : ℚ) • x := by simp [Algebra.smul_def]
  rw [h, inv_smul_smul₀ (by exact_mod_cast hp : (p : ℚ) ≠ 0)]

def defect [Algebra ℚ B] {σ : Type*} (p : ℕ) (hp : p ≠ 0)
    (χ : B →+* B) (v : Fin 3 → B) (f : MvPowerSeries σ B) : MvPowerSeries σ B :=
  f - ∑ i : Fin 3, (p : ℚ)⁻¹ • (v i • ((twist p hp χ ^ (i.val+1)) f))

lemma defect_add [Algebra ℚ B] {σ : Type*} (p : ℕ) (hp : p ≠ 0)
    (χ : B →+* B) (v : Fin 3 → B) (f g : MvPowerSeries σ B) :
    defect p hp χ v (f+g) = defect p hp χ v f + defect p hp χ v g := by
  simp only [defect, map_add, smul_add, Finset.sum_add_distrib]
  abel

lemma defect_sub [Algebra ℚ B] {σ : Type*} (p : ℕ) (hp : p ≠ 0)
    (χ : B →+* B) (v : Fin 3 → B) (f g : MvPowerSeries σ B) :
    defect p hp χ v (f-g) = defect p hp χ v f - defect p hp χ v g := by
  simp only [defect, map_sub, smul_sub, Finset.sum_sub_distrib]
  abel

theorem coeff_defect_le [Algebra ℚ B] {σ : Type*} (p : ℕ) (hp : 2 ≤ p)
    (χ : B →+* B) (v : Fin 3 → B) (f : MvPowerSeries σ B)
    (n : ℕ) (hn : 0 < n) (hf : (n : ℕ∞) ≤ f.order)
    (d : σ →₀ ℕ) (hd : d.degree ≤ n) :
    MvPowerSeries.coeff d (defect p (by omega) χ v f) = MvPowerSeries.coeff d f := by
  simp only [defect, map_sub, map_sum]
  have hz (i : Fin 3) : MvPowerSeries.coeff d
      ((p : ℚ)⁻¹ • (v i • ((twist p (by omega) χ ^ (i.val+1)) f))) = 0 := by
    rw [(MvPowerSeries.coeff d).map_smul_of_tower, MvPowerSeries.coeff_smul,
      coeff_twist_iterate_zero p hp χ f (i.val+1) (by omega) n hn hf d hd,
      mul_zero, smul_zero]
  simp only [hz, Finset.sum_const_zero, sub_zero]

theorem defect_subst_eq [Algebra ℚ B] {σ : Type*} (p : ℕ) (hp : p ≠ 0)
    (χ : B →+* B) (v : Fin 3 → B) (f : PowerSeries B)
    (hf : defect p hp χ v f = PowerSeries.X)
    (a : MvPowerSeries σ B) (ha : PowerSeries.HasSubst a) :
    defect p hp χ v (f.subst a) = a + ∑ i : Fin 3,
      (p : ℚ)⁻¹ • (v i • ((f.map (χ^(i.val+1))).subst (a^(p^(i.val+1))) -
        (f.map (χ^(i.val+1))).subst ((twist p hp χ ^ (i.val+1)) a))) := by
  have hsum : PowerSeries.subst a (∑ i : Fin 3,
        (p : ℚ)⁻¹ • (v i • ((twist p hp χ ^ (i.val+1)) f))) =
      ∑ i : Fin 3, (p : ℚ)⁻¹ • (v i •
        (f.map (χ^(i.val+1))).subst (a^(p^(i.val+1)))) := by
    rw [← PowerSeries.coe_substAlgHom ha, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [AlgHom.map_smul_of_tower, AlgHom.map_smul_of_tower,
      PowerSeries.coe_substAlgHom, subst_twist_iterate p hp χ f a ha]
  have he := congrArg (PowerSeries.subst a) hf
  rw [defect, PowerSeries.subst_sub ha, hsum, PowerSeries.subst_X ha] at he
  have he' := sub_eq_iff_eq_add.mp he
  simp only [defect, twist_iterate_subst p hp χ f a ha]
  rw [he']
  simp only [smul_sub, Finset.sum_sub_distrib]
  abel

lemma IntegralSeries.add (ι : A →+* B) {σ : Type*} {f g : MvPowerSeries σ B}
    (hf : IntegralSeries ι f) (hg : IntegralSeries ι g) : IntegralSeries ι (f+g) := by
  rw [integral_iff_range] at hf hg ⊢
  exact Subring.add_mem _ hf hg

lemma IntegralSeries.sub (ι : A →+* B) {σ : Type*} {f g : MvPowerSeries σ B}
    (hf : IntegralSeries ι f) (hg : IntegralSeries ι g) : IntegralSeries ι (f-g) := by
  rw [integral_iff_range] at hf hg ⊢
  exact Subring.sub_mem _ hf hg

lemma integral_map (ι : A →+* B) {σ : Type*} (a : MvPowerSeries σ A) :
    IntegralSeries ι (a.map ι) := by
  rw [integral_iff_range]
  exact ⟨a, rfl⟩

lemma IntegralSeries.sum (ι : A →+* B) {σ τ : Type*} (s : Finset τ)
    (f : τ → MvPowerSeries σ B) (hf : ∀ i ∈ s, IntegralSeries ι (f i)) :
    IntegralSeries ι (∑ i ∈ s, f i) := by
  apply (integral_iff_range ι _).mpr
  exact Subring.sum_mem _ fun i hi => (integral_iff_range ι _).mp (hf i hi)

theorem defect_log_integral [Algebra ℚ B] (ι : A →+* B) (p : ℕ) [hp : Fact p.Prime]
    (ψ : A →+* A) (χ : B →ₐ[ℚ] B) (hc : χ.toRingHom.comp ι = ι.comp ψ)
    (hψ : ∀ a : A, (p : A) ∣ ψ a - a^p)
    (v : Fin 3 → A) (f : PowerSeries B) (hf : HasIntegralNumerators ι p f)
    (he : defect p hp.out.ne_zero χ.toRingHom (ι ∘ v) f = PowerSeries.X)
    {σ : Type*} (a : MvPowerSeries σ A) (ha : a.constantCoeff = 0) :
    IntegralSeries ι (defect p hp.out.ne_zero χ.toRingHom (ι ∘ v) (f.subst (a.map ι))) := by
  have ha' : PowerSeries.HasSubst (a.map ι) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp [ha])
  rw [defect_subst_eq p hp.out.ne_zero χ.toRingHom (ι ∘ v) f he _ ha']
  apply (integral_map ι a).add
  apply IntegralSeries.sum
  intro i _
  have hi0 : p^(i.val+1) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have haPow : (a^(p^(i.val+1))).constantCoeff = 0 := by
    rw [map_pow, ha, zero_pow hi0]
  have haTw : ((twist p hp.out.ne_zero ψ ^ (i.val+1)) a).constantCoeff = 0 := by
    rw [twist_iterate_constant, ha, map_zero]
  obtain ⟨w, hw⟩ := logarithm_difference ι p hp.out.ne_zero
    (f.map (χ.toRingHom^(i.val+1)))
    (integralNumerators_map_iterate ι ψ χ hc p f hf (i.val+1))
    (a^(p^(i.val+1))) ((twist p hp.out.ne_zero ψ ^ (i.val+1)) a)
    haPow haTw ((dvd_sub_comm).mp (twist_iterate_congr p ψ hψ a (i.val+1)))
  rw [map_pow, map_twist_iterate p hp.out.ne_zero ι ψ χ.toRingHom hc] at hw
  rw [hw, smul_comm, divide_p_mul p hp.out.ne_zero]
  have hm : (ι (v i)) • w.map ι = (v i • w).map ι := by
    simp only [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.map_C]
  change IntegralSeries ι (ι (v i) • w.map ι)
  rw [hm]
  exact integral_map ι _

theorem integral_of_defect_log [Algebra ℚ B] (ι : A →+* B) (p : ℕ) [hp : Fact p.Prime]
    (ψ : A →+* A) (χ : B →ₐ[ℚ] B) (hc : χ.toRingHom.comp ι = ι.comp ψ)
    (hψ : ∀ a : A, (p : A) ∣ ψ a - a^p)
    (v : Fin 3 → A) (f : PowerSeries B) (hf : HasIntegralNumerators ι p f)
    (he : defect p hp.out.ne_zero χ.toRingHom (ι ∘ v) f = PowerSeries.X)
    (hf1 : f.coeff 1 = 1)
    {σ : Type*} (g : MvPowerSeries σ B) (hg : g.constantCoeff = 0)
    (hint : IntegralSeries ι (defect p hp.out.ne_zero χ.toRingHom (ι ∘ v) (f.subst g))) :
    IntegralSeries ι g := by
  classical
  have main : ∀ n : ℕ, ∀ d : σ →₀ ℕ, d.degree = n → ∃ u : A, ι u = MvPowerSeries.coeff d g := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro d hd
      by_cases hn : n = 0
      · have hd0 : d = 0 := Finsupp.degree_eq_zero_iff d |>.mp (hd.trans hn)
        subst d
        exact ⟨0, by simpa using hg.symm⟩
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let a : MvPowerSeries σ A := fun e =>
        if e = 0 then 0 else if he : e.degree < n then (ih e.degree he e rfl).choose else 0
      have haC (e : σ →₀ ℕ) : MvPowerSeries.coeff e a =
          if e = 0 then 0 else if he : e.degree < n then (ih e.degree he e rfl).choose else 0 := rfl
      have ha0 : a.constantCoeff = 0 := by
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, haC, ite_eq_left rfl]
      have hao : (n : ℕ∞) ≤ (g - a.map ι).order := by
        apply MvPowerSeries.nat_le_order
        intro e he
        rw [map_sub, MvPowerSeries.coeff_map, haC]
        by_cases he0 : e = 0
        · subst e
          simpa using hg
        · rw [ite_eq_right he0, dite_eq_left he, (ih e.degree he e rfl).choose_spec, sub_self]
      have ham0 : (a.map ι).constantCoeff = 0 := by simp [ha0]
      have hia := defect_log_integral ι p ψ χ hc hψ v f hf he a ha0
      have hid := hint.sub ι hia
      obtain ⟨u, hu⟩ := hid d
      have heq : MvPowerSeries.coeff d
          (defect p hp.out.ne_zero χ.toRingHom (ι ∘ v) (f.subst g) -
            defect p hp.out.ne_zero χ.toRingHom (ι ∘ v) (f.subst (a.map ι))) =
              MvPowerSeries.coeff d (g - a.map ι) := by
        rw [← defect_sub, coeff_defect_le p hp.out.two_le χ.toRingHom (ι ∘ v) _ n hnpos
          (order_log_difference f hf1 g (a.map ι) hg ham0 n hao) d hd.le,
          coeff_log_difference f hf1 g (a.map ι) hg ham0 n hao d hd.le]
      change ι u = MvPowerSeries.coeff d
          (defect p hp.out.ne_zero χ.toRingHom (ι ∘ v) (f.subst g) -
            defect p hp.out.ne_zero χ.toRingHom (ι ∘ v) (f.subst (a.map ι))) at hu
      rw [heq, map_sub, MvPowerSeries.coeff_map] at hu
      refine ⟨u + MvPowerSeries.coeff d a, ?_⟩
      rw [map_add, hu, sub_add_cancel]
  intro d
  exact main d.degree d rfl

end HeightThree.PTypical

end

end OAI
