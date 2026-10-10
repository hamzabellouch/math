import Mathlib

namespace OAI

universe u_α

noncomputable section

namespace Problem310.GridSeparation

/-- The periodic key of a real point in a grid of mesh `1 / q`. -/
def periodicKey (q x : ℝ) : ℤ := ⌊q * Int.fract x⌋

lemma periodicKey_add_one (q x : ℝ) :
    periodicKey q (x + 1) = periodicKey q x := by
  simp [periodicKey]

/-- Points separated by at least one grid mesh in both circular directions
cannot have the same periodic key. This includes points on cell boundaries. -/
lemma periodicKey_ne_of_separated {q x y : ℝ} (hq : 0 < q)
    (hlo : 1 ≤ q * (y - x)) (hhi : q * (y - x) ≤ q - 1) :
    periodicKey q x ≠ periodicKey q y := by
  intro heq
  have hxlo := Int.floor_le (q * Int.fract x)
  have hxhi := Int.lt_floor_add_one (q * Int.fract x)
  have hylo := Int.floor_le (q * Int.fract y)
  have hyhi := Int.lt_floor_add_one (q * Int.fract y)
  change ⌊q * Int.fract x⌋ = ⌊q * Int.fract y⌋ at heq
  have hcast : (⌊q * Int.fract x⌋ : ℝ) = (⌊q * Int.fract y⌋ : ℝ) :=
    congrArg (fun n : ℤ => (n : ℝ)) heq
  have hdifflo : -1 < q * (Int.fract y - Int.fract x) := by nlinarith
  have hdiffhi : q * (Int.fract y - Int.fract x) < 1 := by nlinarith
  have hx := Int.floor_add_fract x
  have hy := Int.floor_add_fract y
  let k : ℤ := ⌊y⌋ - ⌊x⌋
  have hk : (k : ℝ) = y - x - (Int.fract y - Int.fract x) := by
    simp only [k, Int.cast_sub]
    linarith
  have hkpos : 0 < (k : ℝ) := by nlinarith
  have hklt : (k : ℝ) < 1 := by nlinarith
  have hkpos' : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hklt' : k < (1 : ℤ) := by exact_mod_cast hklt
  omega

lemma periodicKey_ne_of_small_shift {q x d : ℝ} (hq : 4 ≤ q)
    (hlo : 1 ≤ q * d) (hhi : d ≤ 1 / 4) :
    periodicKey q x ≠ periodicKey q (x + d) := by
  apply periodicKey_ne_of_separated (by linarith)
  · simpa using hlo
  · have hmul := mul_le_mul_of_nonneg_left hhi (show 0 ≤ q by linarith)
    have : q * d ≤ q - 1 := by nlinarith
    simpa using this

lemma mesh_mul_dyadic (b : ℕ) :
    (2 : ℝ) ^ (b + 2) * (2 : ℝ)⁻¹ ^ b = 4 := by
  rw [pow_add, inv_pow]
  have hb : (2 : ℝ) ^ b ≠ 0 := by positivity
  field_simp
  ring

lemma mesh_ge_four (b : ℕ) : 4 ≤ (2 : ℝ) ^ (b + 2) := by
  have hb : (1 : ℝ) ≤ 2 ^ b := one_le_pow₀ (by norm_num)
  rw [pow_add]
  norm_num
  nlinarith

lemma dyadic_shift_le_quarter {n : ℕ} {t : ℝ} (hn : 3 ≤ n)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) : t * (2 : ℝ)⁻¹ ^ n ≤ 1 / 4 := by
  have hp : (2 : ℝ)⁻¹ ^ n ≤ (2 : ℝ)⁻¹ ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  norm_num at hp
  have hnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  nlinarith

lemma mesh_mul_shift_ge_four {b n : ℕ} {t : ℝ}
    (hn : n ≤ b) (ht : 1 ≤ t) :
    4 ≤ (2 : ℝ) ^ (b + 2) * (t * (2 : ℝ)⁻¹ ^ n) := by
  have hp : (2 : ℝ)⁻¹ ^ b ≤ (2 : ℝ)⁻¹ ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have hpos : 0 < (2 : ℝ) ^ (b + 2) := by positivity
  have hpnonneg : 0 ≤ (2 : ℝ)⁻¹ ^ n := by positivity
  have hshift : (2 : ℝ)⁻¹ ^ b ≤ t * (2 : ℝ)⁻¹ ^ n := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hshift hpos.le
  rw [mesh_mul_dyadic] at hmul
  exact hmul

/-- Every tested dyadic translate uses a key different from the center's key. -/
lemma periodicKey_dyadic_ne_center {b n : ℕ} {x t : ℝ}
    (hnlo : 3 ≤ n) (hnhi : n ≤ b) (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    periodicKey ((2 : ℝ) ^ (b + 2)) x ≠
      periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ n) := by
  apply periodicKey_ne_of_small_shift (mesh_ge_four b)
  · have := mesh_mul_shift_ge_four hnhi htlo
    linarith
  · exact dyadic_shift_le_quarter hnlo htlo hthi

lemma dyadic_gap_ge_smaller {n m : ℕ} (hnm : n < m) :
    (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ n - (2 : ℝ)⁻¹ ^ m := by
  have hp : (2 : ℝ)⁻¹ ^ m ≤ (2 : ℝ)⁻¹ ^ (n + 1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  rw [pow_succ] at hp
  norm_num at hp
  linarith

/-- Different indices in one window use different periodic keys, uniformly in
all normalized scales. No exclusion of grid-boundary centers is needed. -/
lemma periodicKey_dyadic_ne_of_lt {b n m : ℕ} {x t : ℝ}
    (hnlo : 3 ≤ n) (hnm : n < m) (hmhi : m ≤ b)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ n) ≠
      periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ m) := by
  have hgap := dyadic_gap_ge_smaller hnm
  have hmon : (2 : ℝ)⁻¹ ^ b ≤ (2 : ℝ)⁻¹ ^ m :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hmhi
  have hmpos : 0 < (2 : ℝ)⁻¹ ^ m := by positivity
  have hqpos : 0 < (2 : ℝ) ^ (b + 2) := by positivity
  have hdiff : (2 : ℝ)⁻¹ ^ b ≤
      t * (2 : ℝ)⁻¹ ^ n - t * (2 : ℝ)⁻¹ ^ m := by
    have hprod := mul_nonneg (sub_nonneg.mpr htlo)
      (show 0 ≤ (2 : ℝ)⁻¹ ^ n - (2 : ℝ)⁻¹ ^ m by linarith)
    nlinarith
  have hlow := mul_le_mul_of_nonneg_left hdiff hqpos.le
  rw [mesh_mul_dyadic] at hlow
  have hsmall : t * (2 : ℝ)⁻¹ ^ n - t * (2 : ℝ)⁻¹ ^ m ≤ 1 / 4 := by
    have := dyadic_shift_le_quarter hnlo htlo hthi
    have hprod : 0 ≤ t * (2 : ℝ)⁻¹ ^ m := mul_nonneg (by linarith) hmpos.le
    linarith
  have hne := periodicKey_ne_of_small_shift
    (x := x + t * (2 : ℝ)⁻¹ ^ m) (mesh_ge_four b)
    (show 1 ≤ (2 : ℝ) ^ (b + 2) *
      (t * (2 : ℝ)⁻¹ ^ n - t * (2 : ℝ)⁻¹ ^ m) by linarith) hsmall
  have heq : x + t * (2 : ℝ)⁻¹ ^ m +
      (t * (2 : ℝ)⁻¹ ^ n - t * (2 : ℝ)⁻¹ ^ m) =
      x + t * (2 : ℝ)⁻¹ ^ n := by ring
  rw [heq] at hne
  exact hne.symm

lemma periodicKey_dyadic_injOn {a b : ℕ} {x t : ℝ} (ha : 3 ≤ a)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    Set.InjOn (fun n : ℕ =>
      periodicKey ((2 : ℝ) ^ (b + 2)) (x + t * (2 : ℝ)⁻¹ ^ n))
      (Set.Icc a b) := by
  intro n hn m hm heq
  rcases lt_trichotomy n m with hlt | heq' | hgt
  · exact False.elim ((periodicKey_dyadic_ne_of_lt
      (le_trans ha hn.1) hlt hm.2 htlo hthi) heq)
  · exact heq'
  · exact False.elim ((periodicKey_dyadic_ne_of_lt
      (le_trans ha hm.1) hgt hn.2 htlo hthi) heq.symm)

/-- The nesting identity for the periodic dyadic grids. -/
lemma periodicKey_dyadic_refine {b B : ℕ} (hb : b ≤ B) (x : ℝ) :
    periodicKey ((2 : ℝ) ^ (b + 2)) x =
      periodicKey ((2 : ℝ) ^ (B + 2)) x / (2 : ℤ) ^ (B - b) := by
  have heq : (2 : ℝ) ^ (B + 2) * Int.fract x =
      ((2 : ℝ) ^ (b + 2) * Int.fract x) * ((2 ^ (B - b) : ℕ) : ℝ) := by
    push_cast
    rw [mul_right_comm, ← pow_add]
    congr 1
    congr 1
    omega
  unfold periodicKey
  rw [heq]
  simpa using (Int.mul_natCast_floor_div_cancel
    (n := 2 ^ (B - b)) (by positivity)
    ((2 : ℝ) ^ (b + 2) * Int.fract x)).symm

lemma periodicKey_dyadic_eq_of_refine {b B : ℕ} {x y : ℝ} (hb : b ≤ B)
    (heq : periodicKey ((2 : ℝ) ^ (B + 2)) x =
      periodicKey ((2 : ℝ) ^ (B + 2)) y) :
    periodicKey ((2 : ℝ) ^ (b + 2)) x =
      periodicKey ((2 : ℝ) ^ (b + 2)) y := by
  rw [periodicKey_dyadic_refine hb x, periodicKey_dyadic_refine hb y, heq]

lemma periodicKey_dyadic_ne_refine {b B : ℕ} {x y : ℝ} (hb : b ≤ B)
    (hne : periodicKey ((2 : ℝ) ^ (b + 2)) x ≠
      periodicKey ((2 : ℝ) ^ (b + 2)) y) :
    periodicKey ((2 : ℝ) ^ (B + 2)) x ≠
      periodicKey ((2 : ℝ) ^ (B + 2)) y := by
  exact fun heq => hne (periodicKey_dyadic_eq_of_refine hb heq)

lemma periodicKey_nonneg {q : ℝ} (hq : 0 ≤ q) (x : ℝ) :
    0 ≤ periodicKey q x := by
  exact Int.floor_nonneg.mpr (mul_nonneg hq (Int.fract_nonneg x))

lemma periodicKey_lt (q : ℕ) (hq : 0 < q) (x : ℝ) :
    periodicKey (q : ℝ) x < (q : ℤ) := by
  apply Int.floor_lt.mpr
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have := mul_lt_mul_of_pos_left (Int.fract_lt_one x) hq'
  simpa using this

/-- A finite-table address for the periodic dyadic grid. -/
def dyadicKey (b : ℕ) (x : ℝ) : Fin (2 ^ (b + 2)) :=
  ⟨(periodicKey ((2 ^ (b + 2) : ℕ) : ℝ) x).toNat,
    (Int.toNat_lt (periodicKey_nonneg (by positivity) x)).mpr
      (periodicKey_lt _ (by positivity) x)⟩

lemma dyadicKey_eq_iff (b : ℕ) (x y : ℝ) :
    dyadicKey b x = dyadicKey b y ↔
      periodicKey ((2 : ℝ) ^ (b + 2)) x =
        periodicKey ((2 : ℝ) ^ (b + 2)) y := by
  constructor
  · intro h
    have hv := congrArg (fun k : Fin (2 ^ (b + 2)) => (k.val : ℤ)) h
    dsimp [dyadicKey] at hv
    rw [Int.toNat_of_nonneg (periodicKey_nonneg (by positivity) x),
      Int.toNat_of_nonneg (periodicKey_nonneg (by positivity) y)] at hv
    simpa using hv
  · intro h
    apply Fin.ext
    dsimp [dyadicKey]
    have h' : periodicKey ((2 ^ (b + 2) : ℕ) : ℝ) x =
        periodicKey ((2 ^ (b + 2) : ℕ) : ℝ) y := by simpa using h
    rw [h']

lemma dyadicKey_ne_center {b n : ℕ} {x t : ℝ}
    (hnlo : 3 ≤ n) (hnhi : n ≤ b) (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    dyadicKey b x ≠ dyadicKey b (x + t * (2 : ℝ)⁻¹ ^ n) := by
  rw [ne_eq, dyadicKey_eq_iff]
  exact periodicKey_dyadic_ne_center hnlo hnhi htlo hthi

lemma dyadicKey_injOn {a b : ℕ} {x t : ℝ} (ha : 3 ≤ a)
    (htlo : 1 ≤ t) (hthi : t ≤ 2) :
    Set.InjOn (fun n : ℕ => dyadicKey b (x + t * (2 : ℝ)⁻¹ ^ n))
      (Set.Icc a b) := by
  intro n hn m hm heq
  apply periodicKey_dyadic_injOn ha htlo hthi hn hm
  exact (dyadicKey_eq_iff b _ _).mp heq

lemma dyadicKey_eq_of_refine {b B : ℕ} {x y : ℝ} (hb : b ≤ B)
    (heq : dyadicKey B x = dyadicKey B y) : dyadicKey b x = dyadicKey b y := by
  apply (dyadicKey_eq_iff b x y).mpr
  exact periodicKey_dyadic_eq_of_refine hb ((dyadicKey_eq_iff B x y).mp heq)

lemma dyadicKey_ne_refine {b B : ℕ} {x y : ℝ} (hb : b ≤ B)
    (hne : dyadicKey b x ≠ dyadicKey b y) : dyadicKey B x ≠ dyadicKey B y :=
  fun heq => hne (dyadicKey_eq_of_refine hb heq)

lemma dyadicKey_add_one (b : ℕ) (x : ℝ) : dyadicKey b (x + 1) = dyadicKey b x := by
  rw [dyadicKey_eq_iff]
  exact periodicKey_add_one _ _

lemma measurable_periodicKey (q : ℝ) : Measurable (periodicKey q) := by
  have hfract : Measurable (Int.fract : ℝ → ℝ) :=
    measurable_id.sub ((measurable_of_countable (fun k : ℤ => (k : ℝ))).comp
      Int.measurable_floor)
  exact Int.measurable_floor.comp (measurable_const.mul hfract)

lemma measurable_dyadicKey (b : ℕ) : Measurable (dyadicKey b) := by
  let lift : ℤ → Fin (2 ^ (b + 2)) := fun k =>
    if h : k.toNat < 2 ^ (b + 2) then ⟨k.toNat, h⟩ else ⟨0, by positivity⟩
  have hlift : Measurable lift := measurable_of_countable _
  have h := hlift.comp (measurable_periodicKey ((2 ^ (b + 2) : ℕ) : ℝ))
  have heq : (fun x => lift (periodicKey ((2 ^ (b + 2) : ℕ) : ℝ) x)) =
      dyadicKey b := by
    funext x
    have hlt : (periodicKey ((2 ^ (b + 2) : ℕ) : ℝ) x).toNat < 2 ^ (b + 2) :=
      (dyadicKey b x).isLt
    simp only [lift, dite_eq_left hlt, dyadicKey]
  simpa only [Function.comp_def, heq] using h

/-- The left endpoint of a cell has exactly that finite address. -/
lemma dyadicKey_cell_left (b : ℕ) (k : Fin (2 ^ (b + 2))) :
    dyadicKey b ((k.val : ℝ) / (2 : ℝ) ^ (b + 2)) = k := by
  have hq : (0 : ℝ) < 2 ^ (b + 2) := by positivity
  have hk0 : (0 : ℝ) ≤ k.val := by positivity
  have hkq : (k.val : ℝ) < (2 : ℝ) ^ (b + 2) := by exact_mod_cast k.isLt
  have hfract : Int.fract ((k.val : ℝ) / (2 : ℝ) ^ (b + 2)) =
      (k.val : ℝ) / (2 : ℝ) ^ (b + 2) :=
    Int.fract_eq_self.mpr ⟨div_nonneg hk0 hq.le, (div_lt_one hq).mpr hkq⟩
  apply Fin.ext
  dsimp [dyadicKey, periodicKey]
  push_cast
  rw [hfract]
  have hmul : (2 : ℝ) ^ (b + 2) * ((k.val : ℝ) / (2 : ℝ) ^ (b + 2)) =
      (k.val : ℝ) := by field_simp
  rw [hmul]
  simp

lemma dyadicKey_surjective (b : ℕ) : Function.Surjective (dyadicKey b) := by
  intro k
  exact ⟨(k.val : ℝ) / (2 : ℝ) ^ (b + 2), dyadicKey_cell_left b k⟩

/-- Every function determined by the finest address is literally a finite table.
The table is obtained by evaluating at the cell's left endpoint. -/
lemma factors_through_dyadicKey {α : Type u_α} {b : ℕ} (f : ℝ → α)
    (hf : ∀ x y, dyadicKey b x = dyadicKey b y → f x = f y) :
    ∃ F : Fin (2 ^ (b + 2)) → α, ∀ x, f x = F (dyadicKey b x) := by
  refine ⟨fun k => f ((k.val : ℝ) / (2 : ℝ) ^ (b + 2)), ?_⟩
  intro x
  apply hf
  exact (dyadicKey_cell_left b (dyadicKey b x)).symm

end Problem310.GridSeparation

end

end OAI
