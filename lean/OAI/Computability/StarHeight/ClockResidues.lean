import OAI.Computability.StarHeight.PeriodicLanguages

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uC uC2 uC3 uC4 uC5 uI

namespace SlotResidues

def modulus (N : ℤ) : ℤ := 20 * (N + 1) ^ 3

def representative (N i : ℤ) : ℤ := 4 * N ^ 2 * i + i ^ 2

lemma representative_strict {N i j : ℤ} (_hN : 0 < N) (hi : 0 ≤ i) (hij : i < j) :
    representative N i < representative N j := by
  have hp : 0 < (j - i) * (4 * N ^ 2 + i + j) := mul_pos (by omega) (by nlinarith)
  dsimp [representative]
  nlinarith

lemma positive_quotient {N i j : ℤ} (hN : 0 < N)
    (hj : 1 ≤ j) (hji : j < i) (hi : i ≤ N) :
    (representative N i - representative N j) / (4 * N ^ 2) = i - j := by
  rw [Int.ediv_eq_iff_of_pos (by positivity : 0 < 4 * N ^ 2)]
  have hsq : j ^ 2 < i ^ 2 := by nlinarith
  have hisq : i ^ 2 ≤ N ^ 2 := by nlinarith
  dsimp [representative]
  constructor <;> nlinarith [sq_nonneg j]

lemma positive_unique {N i j k l : ℤ} (hN : 0 < N)
    (hj : 1 ≤ j) (hji : j < i) (hi : i ≤ N)
    (hl : 1 ≤ l) (hlk : l < k) (hk : k ≤ N)
    (he : representative N i - representative N j =
      representative N k - representative N l) : i = k ∧ j = l := by
  have hd : i - j = k - l := by
    rw [← positive_quotient hN hj hji hi, he, positive_quotient hN hl hlk hk]
  have hp : (i - j) * (i + j) = (i - j) * (k + l) := by
    calc
      _ = i ^ 2 - j ^ 2 := by ring
      _ = k ^ 2 - l ^ 2 := by dsimp [representative] at he; nlinarith [hd]
      _ = (k - l) * (k + l) := by ring
      _ = _ := by rw [hd]
  have hs : i + j = k + l := mul_left_cancel₀ (by omega) hp
  omega

lemma signed_unique {N i j k l : ℤ} (hN : 0 < N)
    (hi : 1 ≤ i) (hiN : i ≤ N) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hk : 1 ≤ k) (hkN : k ≤ N) (hl : 1 ≤ l) (hlN : l ≤ N)
    (hij : i ≠ j) (hkl : k ≠ l)
    (he : representative N i - representative N j =
      representative N k - representative N l) : i = k ∧ j = l := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hlt := representative_strict hN (by omega) hij
    have hkl' : k < l := by
      by_contra hn
      have hgt := representative_strict hN (by omega) (by omega : l < k)
      omega
    have hh := positive_unique hN hi hij hjN hk hkl' hlN (by omega)
    exact ⟨hh.2, hh.1⟩
  · have hlt := representative_strict hN (by omega) hji
    have hlk : l < k := by
      by_contra hn
      have hgt := representative_strict hN (by omega) (by omega : k < l)
      omega
    exact positive_unique hN hj hji hiN hl hlk hkN he

lemma representative_bounds {N i : ℤ} (hN : 0 < N) (hi : 1 ≤ i) (hiN : i ≤ N) :
    0 < representative N i ∧ representative N i < modulus N / 2 := by
  have hsq : i ^ 2 ≤ N ^ 2 := by nlinarith
  have hmul : 4 * N ^ 2 * i ≤ 4 * N ^ 2 * N :=
    mul_le_mul_of_nonneg_left hiN (by positivity)
  have hm : modulus N / 2 = 10 * (N + 1) ^ 3 := by
    dsimp [modulus]
    omega
  rw [hm]
  dsimp [representative]
  constructor
  · positivity
  · nlinarith [sq_nonneg N, mul_nonneg (by omega : 0 ≤ N) (sq_nonneg N)]

lemma mod_difference_eq {N i j k l : ℤ} (hN : 0 < N)
    (hi : 1 ≤ i) (hiN : i ≤ N) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hk : 1 ≤ k) (hkN : k ≤ N) (hl : 1 ≤ l) (hlN : l ≤ N)
    (he : (representative N i - representative N j) % modulus N =
      (representative N k - representative N l) % modulus N) :
    representative N i - representative N j = representative N k - representative N l := by
  have hb₁ := representative_bounds hN hi hiN
  have hb₂ := representative_bounds hN hj hjN
  have hb₃ := representative_bounds hN hk hkN
  have hb₄ := representative_bounds hN hl hlN
  have hB : 0 < modulus N := by dsimp [modulus]; positivity
  have hh : |(representative N i - representative N j) -
      (representative N k - representative N l)| < modulus N := by
    apply abs_lt.mpr
    constructor <;> omega
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd (by
    simpa only [neg_sub] using dvd_neg.mpr (Int.modEq_iff_dvd.mp he)) hh)

lemma distinct_differences {N i j k l : ℤ} (hN : 0 < N)
    (hi : 1 ≤ i) (hiN : i ≤ N) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hk : 1 ≤ k) (hkN : k ≤ N) (hl : 1 ≤ l) (hlN : l ≤ N)
    (hij : i ≠ j) (hkl : k ≠ l)
    (he : (representative N i - representative N j) % modulus N =
      (representative N k - representative N l) % modulus N) : i = k ∧ j = l :=
  signed_unique hN hi hiN hj hjN hk hkN hl hlN hij hkl
    (mod_difference_eq hN hi hiN hj hjN hk hkN hl hlN he)

lemma nonzero_difference {N i j : ℤ} (hN : 0 < N)
    (hi : 1 ≤ i) (hiN : i ≤ N) (hj : 1 ≤ j) (hjN : j ≤ N) (hij : i ≠ j) :
    (representative N i - representative N j) % modulus N ≠ 0 := by
  intro he
  have he' : (representative N i - representative N j) % modulus N =
      (representative N i - representative N i) % modulus N := by simpa using he
  have hh := mod_difference_eq hN hi hiN hj hjN hi hiN hi hiN he'
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hlt := representative_strict hN (by omega) hij
    omega
  · have hlt := representative_strict hN (by omega) hji
    omega

end SlotResidues

namespace PeriodicClock

open RobustClock
open scoped BigOperators

variable {C : Type uC} [Fintype C]

lemma large_primes (N : ℕ) : ∃ p : C → ℕ,
    Function.Injective p ∧ ∀ c, Nat.Prime (p c) ∧ N < p c := by
  classical
  let s : Set ℕ := {p | Nat.Prime p ∧ N < p}
  have hs : s.Infinite := Set.infinite_of_forall_exists_gt (fun a => by
    obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes (max a N + 1)
    exact ⟨p, ⟨hprime, by omega⟩, by omega⟩)
  have : Infinite s := hs.to_subtype
  let e : C ↪ s := (Fintype.equivFin C).toEmbedding.trans
    ((Fin.valEmbedding).trans (Infinite.natEmbedding s))
  exact ⟨fun c => (e c).val, Subtype.val_injective.comp e.injective,
    fun c => (e c).property⟩

def speedMap (v : C → ℝ) : ℤ →+ (C → RobustClock.Circle) where
  toFun z c := (((z : ℝ) * v c : ℝ) : RobustClock.Circle)
  map_zero' := by ext c; simp
  map_add' x y := by ext c; simp [add_mul]

omit [Fintype C] in
@[simp] lemma speedMap_apply (v : C → ℝ) (z : ℤ) (c : C) :
    speedMap v z c = (((z : ℝ) * v c : ℝ) : RobustClock.Circle) := rfl

lemma period (n a : C → ℕ) (hn : ∀ c, 0 < n c) :
    speedMap (fun c => (a c : ℝ) / n c) ((∏ c, n c : ℕ) : ℤ) = 0 := by
  classical
  ext c
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ c)
  change (((((∏ c, n c : ℕ) : ℝ) * ((a c : ℝ) / n c)) : ℝ) : RobustClock.Circle) = 0
  rw [hk]
  push_cast
  have hnr : (n c : ℝ) ≠ 0 := by exact_mod_cast (hn c).ne'
  have he : (n c : ℝ) * k * ((a c : ℝ) / n c) = ((k * a c : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [he]
  exact coe_integer (k * a c)

lemma crt_grid (n : C → ℕ) (hn : ∀ c, 0 < n c)
    (hp : Pairwise (Function.onFun Nat.Coprime n)) (B : ℕ)
    (hB : ∀ c, Nat.Coprime B (n c)) (j : ∀ c, Fin (n c)) :
    ∃ a : ℕ, a < ∏ c, n c ∧ ∀ c,
      ((a * B : ℕ) : ZMod (n c)) = (j c : ℕ) := by
  classical
  have hnprod : 0 < ∏ c, n c := Finset.prod_pos (fun c _ => hn c)
  have : NeZero (∏ c, n c) := ⟨hnprod.ne'⟩
  let b : ∀ c, ZMod (n c) := fun c => ↑((ZMod.unitOfCoprime B (hB c))⁻¹) * (j c : ℕ)
  let r := (ZMod.prodEquivPi n hp).symm b
  refine ⟨r.val, ZMod.val_lt r, fun c => ?_⟩
  have hc := congrFun ((ZMod.prodEquivPi n hp).apply_symm_apply b) c
  rw [ZMod.prodEquivPi_apply] at hc
  have hv : (r.val : ZMod (n c)) = b c := by
    rw [← hc, ← ZMod.natCast_zmod_val r]
    simp [r]
  push_cast
  rw [hv]
  dsimp [b]
  rw [mul_right_comm, ← ZMod.coe_unitOfCoprime B (hB c), Units.inv_mul, one_mul]

lemma net (n : C → ℕ) (hn : ∀ c, 0 < n c)
    (hp : Pairwise (Function.onFun Nat.Coprime n)) (B : ℕ)
    (hB : ∀ c, Nat.Coprime B (n c)) {ε : ℝ}
    (hε : 0 < ε) (hmesh : ∀ c, 1 / (2 * (n c : ℝ)) < ε)
    (v : C → RobustClock.Circle) :
    ∃ a : ℕ, a < ∏ c, n c ∧
      dist (speedMap (fun c => 1 / (n c : ℝ)) (a * B)) v < ε := by
  classical
  choose j hj using fun c => grid_near (n c) (hn c) (-v c)
  obtain ⟨a, ha, hac⟩ := crt_grid n hn hp B hB j
  refine ⟨a, ha, (dist_pi_lt_iff hε).mpr (fun c => ?_)⟩
  have : NeZero (n c) := ⟨(hn c).ne'⟩
  have he : (a * B : ℕ) % n c = (j c : ℕ) := by
    have hv := congrArg ZMod.val (hac c)
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (j c).isLt] using hv
  have heZ : ((a * B : ℕ) : ℤ) % (n c : ℤ) = j c := by exact_mod_cast he
  push_cast at heZ
  have hh : speedMap (fun c => 1 / (n c : ℝ)) (a * B) c =
      ((((j c : ℕ) : ℝ) / n c : ℝ) : RobustClock.Circle) := by
    rw [speedMap_apply, mul_one_div, ← coe_mod_fraction (n c) (hn c), heZ]
    simp only [Int.cast_natCast]
  rw [hh, dist_eq_norm]
  have hnorm := hj c
  rw [neg_add_eq_sub] at hnorm
  exact hnorm.trans_lt (hmesh c)

end PeriodicClock

namespace ScheduleCopies

lemma exists_log_linear (A C : ℝ) (hA : 0 < A) :
    ∃ μ : ℕ, 0 < μ ∧ A * Real.log μ + C < μ := by
  have hb := Real.isLittleO_log_id_atTop.bound (div_pos (by norm_num : (0 : ℝ) < 1)
    (mul_pos (by norm_num) hA) : 0 < 1 / (2 * A))
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp hb
  obtain ⟨μ, hμ⟩ := exists_nat_gt (max b (max 1 (2 * C)))
  have hm1 : (1 : ℝ) < μ :=
    (le_trans (le_max_left _ _) (le_max_right b _)).trans_lt hμ
  have hm0 : (0 : ℝ) < μ := lt_trans zero_lt_one hm1
  have hbm : b ≤ (μ : ℝ) := le_of_lt ((le_max_left _ _).trans_lt hμ)
  have hbig : 2 * C < (μ : ℝ) := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hμ)
  have hh := hb (μ : ℝ) hbm
  simp only [id_eq, Real.norm_eq_abs, abs_of_pos hm0] at hh
  have hmain : A * Real.log μ ≤ (μ : ℝ) / 2 := calc
    A * Real.log μ ≤ A * |Real.log μ| := mul_le_mul_of_nonneg_left (le_abs_self _) hA.le
    _ ≤ A * ((1 / (2 * A)) * μ) := mul_le_mul_of_nonneg_left hh hA.le
    _ = (μ : ℝ) / 2 := by field_simp
  exact ⟨μ, by exact_mod_cast hm0, by linarith⟩

lemma exists_log_polynomial (κ D A C : ℝ) (hκ : 0 ≤ κ) (hD : 0 < D) (hA : 0 < A) :
    ∃ μ : ℕ, 0 < μ ∧ A * Real.log (D * (κ * μ + 1) ^ 3) + C < μ := by
  let D' := D * (κ + 1) ^ 3
  have hD' : 0 < D' := by dsimp [D']; positivity
  obtain ⟨μ, hm, hbound⟩ := exists_log_linear (3 * A) (A * Real.log D' + C) (by positivity)
  have hmR : (1 : ℝ) ≤ μ := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < μ := lt_of_lt_of_le zero_lt_one hmR
  have hbase : κ * (μ : ℝ) + 1 ≤ (κ + 1) * μ := by nlinarith
  have hpoly : D * (κ * (μ : ℝ) + 1) ^ 3 ≤ D' * (μ : ℝ) ^ 3 := by
    dsimp [D']
    rw [mul_assoc D, ← mul_pow]
    gcongr
  have hlog : Real.log (D * (κ * (μ : ℝ) + 1) ^ 3) ≤ Real.log D' + 3 * Real.log μ := by
    have hh := Real.log_le_log (by positivity : 0 < D * (κ * (μ : ℝ) + 1) ^ 3) hpoly
    rw [Real.log_mul hD'.ne' (pow_pos hmpos 3).ne', Real.log_pow] at hh
    norm_num at hh ⊢
    exact hh
  exact ⟨μ, hm, by nlinarith [mul_le_mul_of_nonneg_left hlog hA.le]⟩

end ScheduleCopies

namespace PeriodicClock

open RobustClock
open scoped BigOperators

lemma floor_approx {s ε : ℝ} (hs : 0 < s) (hs1 : s < 1) (hε : 0 < ε)
    {n : ℕ} (hn : max (1 / s) (1 / ε) < (n : ℝ)) :
    1 ≤ ⌊(n : ℝ) * s⌋₊ ∧ ⌊(n : ℝ) * s⌋₊ < n ∧
      |(⌊(n : ℝ) * s⌋₊ : ℝ) / n - s| < ε := by
  have hns : 1 / s < (n : ℝ) := (le_max_left _ _).trans_lt hn
  have hne : 1 / ε < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hnpos : (0 : ℝ) < n := (div_pos zero_lt_one hs).trans hns
  have hns' : 1 < (n : ℝ) * s := (div_lt_iff₀ hs).mp hns
  have hns0 : 0 ≤ (n : ℝ) * s := le_of_lt (mul_pos hnpos hs)
  refine ⟨(Nat.one_le_floor_iff _).mpr hns'.le,
    (Nat.floor_lt hns0).mpr (mul_lt_of_lt_one_right hnpos hs1), ?_⟩
  have hf := Nat.floor_le hns0
  have hl := Nat.lt_floor_add_one ((n : ℝ) * s)
  have hle : (⌊(n : ℝ) * s⌋₊ : ℝ) / n ≤ s := (div_le_iff₀ hnpos).mpr (by nlinarith [hf])
  have hmesh : 1 / (n : ℝ) < ε := (div_lt_iff₀ hnpos).mpr (by
    have hh := (div_lt_iff₀ hε).mp hne
    nlinarith)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  have ha := div_mul_cancel₀ (⌊(n : ℝ) * s⌋₊ : ℝ) hnpos.ne'
  have hb := div_mul_cancel₀ (1 : ℝ) hnpos.ne'
  have hh : -((⌊(n : ℝ) * s⌋₊ : ℝ) / n - s) < 1 / (n : ℝ) := by nlinarith
  exact hh.trans hmesh

lemma approximate_speeds {C : Type uC2} [Fintype C] (v : C → ℝ)
    (hv : ∀ c, 0 < v c ∧ v c < 1) (L : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n a : C → ℕ, Function.Injective n ∧
      (∀ c, Nat.Prime (n c) ∧ L < n c ∧ 1 ≤ a c ∧ a c < n c) ∧
      ∀ c, |(a c : ℝ) / n c - v c| < ε := by
  classical
  choose N hN using fun c => exists_nat_gt (max (1 / v c) (1 / ε))
  obtain ⟨n, hinj, hn⟩ := large_primes (C := C) (max L (Finset.univ.sup N))
  let a := fun c => ⌊(n c : ℝ) * v c⌋₊
  have hclose c := floor_approx (hv c).1 (hv c).2 hε (n := n c) (lt_trans (hN c) (by
    exact_mod_cast lt_of_le_of_lt (Finset.le_sup (Finset.mem_univ c))
      (lt_of_le_of_lt (le_max_right _ _) (hn c).2)))
  exact ⟨n, a, hinj, fun c => ⟨(hn c).1,
    lt_of_le_of_lt (le_max_left _ _) (hn c).2, (hclose c).1, (hclose c).2.1⟩,
    fun c => (hclose c).2.2⟩

lemma dist_coordinate_le {C : Type uC3} (v w : C → ℝ) (z : ℤ) (c : C) :
    dist (speedMap v z c) (speedMap w z c) ≤ |(z : ℝ)| * |v c - w c| := by
  rw [speedMap_apply, speedMap_apply, dist_eq_norm, ← AddCircle.coe_sub]
  exact (norm_coe_le_abs _).trans_eq (by rw [← mul_sub, abs_mul])

lemma approximate_finite {C : Type uC4} [Fintype C] (v : C → ℝ)
    (hv : ∀ c, 0 < v c ∧ v c < 1) (L : ℕ) (F : Finset ℤ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n a : C → ℕ, Function.Injective n ∧
      (∀ c, Nat.Prime (n c) ∧ L < n c ∧ 1 ≤ a c ∧ a c < n c) ∧
      ∀ z ∈ F, dist (speedMap (fun c => (a c : ℝ) / n c) z) (speedMap v z) < ε := by
  classical
  let D : ℝ := (∑ z ∈ F, |(z : ℝ)|) + 1
  have hD : 0 < D := by
    dsimp [D]
    positivity
  obtain ⟨n, a, hn, hna, he⟩ := approximate_speeds v hv L (div_pos hε hD)
  refine ⟨n, a, hn, hna, fun z hz => (dist_pi_lt_iff hε).mpr (fun c => ?_)⟩
  have hzD : |(z : ℝ)| ≤ D := by
    have hzsum := Finset.single_le_sum (fun i (_ : i ∈ F) => abs_nonneg (i : ℝ)) hz
    dsimp [D]
    linarith
  apply (dist_coordinate_le _ _ z c).trans_lt
  calc
    |(z : ℝ)| * |(a c : ℝ) / n c - v c| ≤ D * |(a c : ℝ) / n c - v c| :=
      mul_le_mul_of_nonneg_right hzD (abs_nonneg _)
    _ < D * (ε / D) := mul_lt_mul_of_pos_left (he c) hD
    _ = ε := by field_simp

lemma coprime_product_of_small {C : Type uC5} [Fintype C] (n : C → ℕ)
    (hn : ∀ c, Nat.Prime (n c)) {k : ℕ} (hk : 0 < k) (hkn : ∀ c, k < n c) :
    Nat.Coprime k (∏ c, n c) := by
  apply Nat.Coprime.prod_right
  intro c _
  apply Nat.Coprime.symm
  apply (hn c).coprime_iff_not_dvd.mpr
  intro hd
  exact (not_le_of_gt (hkn c)) (Nat.le_of_dvd hk hd)

end PeriodicClock

namespace SpacedStencil

open scoped BigOperators

lemma exists_points (N : ℕ) (K : ℤ) (U : Fin N → ℤ → Prop)
    (hU : ∀ i L, ∃ z, L < z ∧ U i z) :
    ∃ p : Fin N → ℤ, (∀ i, U i (p i) ∧ K < p i) ∧
      ∀ i j, i < j → 2 * p i + K < p j := by
  classical
  induction N with
  | zero => exact ⟨Fin.elim0, (fun i => Fin.elim0 i), fun i => Fin.elim0 i⟩
  | succ N ih =>
    obtain ⟨p, hp, hg⟩ := ih (fun i => U i.castSucc) (fun i => hU i.castSucc)
    let B : ℤ := (Finset.univ.sup (fun i => (p i).natAbs) : ℕ)
    have hB i : p i ≤ B := by
      have hb : (p i).natAbs ≤ Finset.univ.sup (fun i => (p i).natAbs) :=
        Finset.le_sup (f := fun i => (p i).natAbs) (Finset.mem_univ i)
      have hab : p i ≤ ((p i).natAbs : ℤ) := Int.le_natAbs
      dsimp [B]
      omega
    obtain ⟨q, hq, hqU⟩ := hU (Fin.last N) (max K (2 * B + K))
    refine ⟨Fin.lastCases q p, ?_, ?_⟩
    · intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using And.intro hqU (lt_of_le_of_lt (le_max_left _ _) hq)
      · simpa using hp i
    · intro i j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro h
        exact False.elim (not_lt_of_ge (Fin.le_last j) h)
      · refine Fin.lastCases ?_ (fun j => ?_) j
        · intro _
          simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
          have hb := hB i
          have hh := lt_of_le_of_lt (le_max_right _ _) hq
          omega
        · simpa only [Fin.lastCases_castSucc, Fin.castSucc_lt_castSucc_iff] using hg i j

variable {I : Type uI} [LinearOrder I] {p : I → ℤ} {K : ℤ}

lemma positive_gap (hK : 0 ≤ K) (hp : ∀ i, K < p i)
    (hg : ∀ i j, i < j → 2 * p i + K < p j) {i j : I} (hij : i < j) :
    K < p j - p i := by
  have h := hg i j hij
  have hi := hp i
  omega

lemma positive_differences (hK : 0 ≤ K) (hp : ∀ i, K < p i)
    (hg : ∀ i j, i < j → 2 * p i + K < p j)
    {i j k l : I} (hji : j < i) (hlk : l < k) (hne : (i, j) ≠ (k, l)) :
    K < |(p i - p j) - (p k - p l)| := by
  rcases lt_trichotomy i k with hik | hik | hki
  · have h1 := hg i k hik
    have h2 := hg l k hlk
    have h3 := hp j
    have hh : (p i - p j) - (p k - p l) < -K := by omega
    exact (lt_abs).mpr (Or.inr (by omega))
  · subst k
    have hjl : j ≠ l := by intro h; exact hne (by simp [h])
    rcases lt_or_gt_of_ne hjl with hjl | hlj
    · have hh := positive_gap hK hp hg hjl
      exact (lt_abs).mpr (Or.inl (by omega))
    · have hh := positive_gap hK hp hg hlj
      exact (lt_abs).mpr (Or.inr (by omega))
  · have h1 := hg k i hki
    have h2 := hg j i hji
    have h3 := hp l
    exact (lt_abs).mpr (Or.inl (by omega))

lemma ordered_differences (hK : 0 ≤ K) (hp : ∀ i, K < p i)
    (hg : ∀ i j, i < j → 2 * p i + K < p j)
    {i j k l : I} (hij : i ≠ j) (hkl : k ≠ l) (hne : (i, j) ≠ (k, l)) :
    K < |(p i - p j) - (p k - p l)| := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · rcases lt_or_gt_of_ne hkl with hkl | hlk
    · have hh := positive_differences hK hp hg hij hkl (by
        intro h
        have hh := Prod.mk.inj h
        exact hne (Prod.ext hh.2 hh.1))
      simpa only [show (p j - p i) - (p l - p k) = -((p i - p j) - (p k - p l)) by ring,
        abs_neg] using hh
    · have h1 := positive_gap hK hp hg hij
      have h2 := positive_gap hK hp hg hlk
      exact (lt_abs).mpr (Or.inr (by omega))
  · rcases lt_or_gt_of_ne hkl with hkl | hlk
    · have h1 := positive_gap hK hp hg hji
      have h2 := positive_gap hK hp hg hkl
      exact (lt_abs).mpr (Or.inl (by omega))
    · exact positive_differences hK hp hg hji hlk hne

lemma nonzero_differences (hK : 0 ≤ K) (hp : ∀ i, K < p i)
    (hg : ∀ i j, i < j → 2 * p i + K < p j) {i j : I} (hij : i ≠ j) :
    K < |p i - p j| := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hh := positive_gap hK hp hg hij
    exact (lt_abs).mpr (Or.inr (by omega))
  · exact (lt_abs).mpr (Or.inl (positive_gap hK hp hg hji))

end SpacedStencil

end GeneralizedStarHeight

end OAI
