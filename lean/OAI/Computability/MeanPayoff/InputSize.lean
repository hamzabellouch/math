import OAI.Computability.MeanPayoff.RootBox

namespace OAI

section

namespace MeanPayoff

@[simp] theorem encodeNat_length (n : ℕ) :
    (encodeNat n).length = 2 * Nat.size (n + 1) + 1 := by
  simp [encodeNat, Nat.size_eq_bits_len]
  omega

@[simp] theorem encodeInt_length (z : ℤ) :
    (encodeInt z).length = 2 * Nat.size (z.natAbs + 1) + 2 := by
  simp [encodeInt]

theorem input_n_le (G : Game) : G.n ≤ (input G).length := by
  simp only [input, List.length_append, List.length_ofFn]
  omega

theorem length_le_flatten {α : Type} {x : List α} {l : List (List α)}
    (h : x ∈ l) : x.length ≤ l.flatten.length := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have hh := ih h
      simp only [List.flatten_cons, List.length_append]
      omega

theorem input_weight_size_le (G : Game) (e : Fin G.m) :
    Nat.size ((G.weight e).natAbs + 1) ≤ (input G).length := by
  let f := fun e : Fin G.m =>
    encodeNat ((G.tail e).val + 1) ++ encodeNat ((G.head e).val + 1) ++ encodeInt (G.weight e)
  have hm : f e ∈ List.ofFn f := List.mem_ofFn.mpr ⟨e, rfl⟩
  have h := length_le_flatten hm
  dsimp [f] at h
  simp only [List.length_append, encodeNat_length, encodeInt_length] at h
  simp only [input, List.length_append, List.length_ofFn]
  omega

theorem input_weight_lt_pow (G : Game) (e : Fin G.m) :
    (G.weight e).natAbs + 1 < 2 ^ (input G).length :=
  Nat.size_le.mp (input_weight_size_le G e)



theorem input_weightBound_le (G : Game) :
    weightBound G ≤ ((G.n + 1) * 2 ^ (input G).length : ℕ) := by
  apply max_le
  · have hp : 1 ≤ 2 ^ (input G).length := Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast (by nlinarith : 1 ≤ (G.n + 1) * 2 ^ (input G).length)
  · have hs : Finset.univ.sup (fun e : Fin G.m => (transformed G e).natAbs) ≤
        (G.n + 1) * 2 ^ (input G).length := by
      apply Finset.sup_le
      intro e _
      have hw := input_weight_lt_pow G e
      have ht := Int.natAbs_add_le ((G.n + 1) * G.weight e) 1
      simp only [Int.natAbs_mul, Int.natAbs_one] at ht
      change (transformed G e).natAbs ≤ _
      dsimp only [transformed]
      have hn : (G.n + 1 : ℤ) = ((G.n + 1 : ℕ) : ℤ) := by norm_cast
      rw [hn] at ht ⊢
      simp only [Int.natAbs_natCast] at ht
      exact ht.trans (by nlinarith)
    exact_mod_cast hs

theorem width_growth_bound {n w L : ℕ} (hn : n ≤ L) (hw : w ≤ (n + 1) * 2 ^ L) :
    8 * n * w ≤ 2 ^ (3 * L + 5) := by
  have hl : L + 1 ≤ 2 ^ (L + 1) := (Nat.lt_two_pow_self).le
  have hn2 : n * (n + 1) ≤ (L + 1) ^ 2 := by nlinarith
  have hb : 8 * n * w ≤ 8 * (L + 1) ^ 2 * 2 ^ L := by
    have hh := Nat.mul_le_mul_left (8 * n) hw
    have hh' := Nat.mul_le_mul_right (2 ^ L) (Nat.mul_le_mul_left 8 hn2)
    nlinarith only [hh, hh']
  have hp := Nat.pow_le_pow_left hl 2
  have hmul := Nat.mul_le_mul_left (8 * 2 ^ L) hp
  have hex : 8 * (2 ^ (L + 1)) ^ 2 * 2 ^ L = 2 ^ (3 * L + 5) := by
    rw [← pow_mul]
    calc
      _ = 2 ^ 3 * 2 ^ ((L + 1) * 2) * 2 ^ L := by rfl
      _ = 2 ^ (3 + (L + 1) * 2 + L) := by rw [← pow_add, ← pow_add]
      _ = _ := by congr 1; omega
  exact hb.trans (calc
    _ ≤ 8 * (2 ^ (L + 1)) ^ 2 * 2 ^ L := by
      simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    _ = _ := hex)

theorem input_topWidth_le (G : Game) :
    (topWidth G).toNat ≤ 2 ^ (3 * (input G).length + 5) := by
  have hw := input_weightBound_le G
  have hw0 := (weightBound_positive G).le
  have hwN : (weightBound G).toNat ≤ (G.n + 1) * 2 ^ (input G).length :=
    Int.toNat_le.mpr hw
  have h := width_growth_bound (input_n_le G) hwN
  apply Int.toNat_le.mpr
  have hc : (8 : ℤ) * G.n * (weightBound G).toNat ≤ (2 : ℤ) ^ (3 * (input G).length + 5) :=
    by exact_mod_cast h
  rw [Int.toNat_of_nonneg hw0] at hc
  simpa only [topWidth, Nat.cast_pow, Nat.cast_ofNat] using hc

theorem input_globalG_le (G : Game) :
    globalG (topWidth G).toNat ≤ 3 * (input G).length + 7 := by
  have hb := input_topWidth_le G
  have hp : (topWidth G).toNat + 1 ≤ 2 ^ (3 * (input G).length + 6) := by
    rw [show 3 * (input G).length + 6 = (3 * (input G).length + 5) + 1 by omega, pow_succ]
    have hpos := Nat.one_le_pow (3 * (input G).length + 5) 2 (by norm_num)
    omega
  have hc := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr hp
  unfold globalG
  omega

theorem globalS_upper (Bmax : ℕ) : globalS Bmax < 2 ^ 18 * (globalG Bmax + 1) := by
  let a := 2 ^ 17 * (globalG Bmax + 1)
  have ha : 1 < a := by dsimp [a]; omega
  have he : 0 < Nat.clog 2 a :=
    (Nat.lt_clog_iff_pow_lt (by norm_num : 1 < 2)).mpr (by simpa using ha)
  have hh := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) ha
  calc
    globalS Bmax = 2 ^ (Nat.clog 2 a).pred * 2 := by
      change 2 ^ Nat.clog 2 a = _
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos he]
      rw [pow_succ]
    _ < a * 2 := Nat.mul_lt_mul_of_pos_right hh (by norm_num)
    _ = 2 ^ 18 * (globalG Bmax + 1) := by dsimp [a]; ring

def inputScale (G : Game) : ℕ := 2 ^ 24 * ((input G).length + 2)

theorem inputScale_large (G : Game) : 32 ≤ inputScale G := by unfold inputScale; omega

theorem inputScale_n (G : Game) : G.n + 1 ≤ inputScale G := by
  have hn := input_n_le G
  unfold inputScale
  omega

theorem inputScale_g (G : Game) : globalG (topWidth G).toNat + 1 ≤ inputScale G := by
  have hn := input_globalG_le G
  unfold inputScale
  omega

theorem inputScale_s (G : Game) : globalS (topWidth G).toNat ≤ inputScale G := by
  have hs := globalS_upper (topWidth G).toNat
  have hg := input_globalG_le G
  unfold inputScale
  omega

theorem inputScale_log (G : Game) : Nat.log 2 (topWidth G).toNat + 2 ≤ inputScale G := by
  have hm := Nat.log_mono_right (b := 2) (Nat.le_succ (topWidth G).toNat)
  change Nat.log 2 (topWidth G).toNat ≤ Nat.log 2 ((topWidth G).toNat + 1) at hm
  have hc := Nat.log_le_clog 2 ((topWidth G).toNat + 1)
  have hg := inputScale_g G
  unfold globalG at hg
  omega



theorem globalJ_scale {n B X : ℕ} (hX : 32 ≤ X) (hn : n + 1 ≤ X)
    (hs : globalS B ≤ X) : globalJ n B ≤ X ^ 14 := by
  have hx : 1 ≤ X := by omega
  have hp : globalS B * (n + 1) ≤ X ^ 2 := by nlinarith
  have hp6 := Nat.pow_le_pow_left hp 6
  rw [← pow_mul] at hp6
  change (globalS B * (n + 1)) ^ 6 ≤ X ^ 12 at hp6
  have hcoef : 2 * X ^ 12 + 1 ≤ X ^ 14 := by
    have h12 : 1 ≤ X ^ 12 := Nat.one_le_pow _ _ hx
    have hsq : 3 ≤ X ^ 2 := by nlinarith
    rw [show (14 : ℕ) = 12 + 2 by norm_num, pow_add]
    nlinarith only [h12, hsq]
  exact (by unfold globalJ; omega : globalJ n B ≤ 2 * X ^ 12 + 1).trans hcoef

theorem chainBound_scale {B X : ℕ} (hX : 32 ≤ X) (hs : globalS B ≤ X)
    (hl : Nat.log 2 B + 2 ≤ X) : chainBound B ≤ X ^ 3 := by
  have hsl := Nat.mul_le_mul hs hl
  have hx3 : 8 * X ^ 2 + 1 ≤ X ^ 3 := by
    have hsq : 1 ≤ X ^ 2 := by nlinarith
    nlinarith
  have hh : chainBound B ≤ 8 * X ^ 2 + 1 := by unfold chainBound; nlinarith only [hsl]
  exact hh.trans hx3

theorem globalListBound_scale {n B X : ℕ} (hX : 32 ≤ X)
    (hg : globalG B + 1 ≤ X) (hj : globalJ n B ≤ X ^ 14) :
    globalListBound n B ≤ X ^ 16 := by
  have hgg : 2 * globalG B + 3 ≤ X ^ 2 := by nlinarith
  have hmul := Nat.mul_le_mul hj hgg
  simpa only [globalListBound, ← pow_add] using hmul

theorem auxiliaryCalls_scale {n B X : ℕ} (hX : 32 ≤ X) (hn : n + 1 ≤ X)
    (hg : globalG B + 1 ≤ X) (hs : globalS B ≤ X) : auxiliaryCalls n B ≤ X ^ 32 := by
  have hx : 1 ≤ X := by omega
  have hj := globalJ_scale hX hn hs
  have hl := globalListBound_scale hX hg hj
  have hns := Nat.mul_le_mul (by omega : n ≤ X) hs
  have ht : 16 * n * globalS B + 2 ≤ X ^ 3 := by
    have hsq : 1 ≤ X ^ 2 := by nlinarith
    nlinarith
  have h1 : (16 * n * globalS B + 2) * globalJ n B ≤ X ^ 17 := by
    simpa only [← pow_add] using Nat.mul_le_mul ht hj
  have h2j : 2 * globalJ n B ≤ X ^ 15 := by
    have hp := Nat.mul_le_mul (by omega : 2 ≤ X) hj
    simpa only [← pow_succ'] using hp
  have h2 : globalJ n B * ((globalG B + 1) * (globalS B * (2 * globalJ n B))) ≤ X ^ 31 := by
    have hp := Nat.mul_le_mul hj (Nat.mul_le_mul hg (Nat.mul_le_mul hs h2j))
    have he : X ^ 14 * (X * (X * X ^ 15)) = X ^ 31 := by ring
    exact he ▸ hp
  have h3 : globalListBound n B * globalJ n B ≤ X ^ 30 := by
    simpa only [← pow_add] using Nat.mul_le_mul hl hj
  have hp17 : X ^ 17 ≤ X ^ 31 := Nat.pow_le_pow_right hx (by norm_num)
  have hp30 : X ^ 30 ≤ X ^ 31 := Nat.pow_le_pow_right hx (by norm_num)
  have hxmul : 3 * X ^ 31 ≤ X ^ 32 := by
    conv_rhs => rw [pow_succ']
    exact Nat.mul_le_mul_right (X ^ 31) (by omega : 3 ≤ X)
  unfold auxiliaryCalls
  omega

theorem callBase_scale {n B X : ℕ} (hX : 32 ≤ X) (hn : n + 1 ≤ X)
    (hg : globalG B + 1 ≤ X) (hs : globalS B ≤ X) (hl : Nat.log 2 B + 2 ≤ X) :
    callBase n B ≤ X ^ 37 := by
  have hx : 1 ≤ X := by omega
  have ha := auxiliaryCalls_scale hX hn hg hs
  have hk := chainBound_scale hX hs hl
  have hp : 1 ≤ X ^ 32 := Nat.one_le_pow _ _ hx
  have ha1 : auxiliaryCalls n B + 1 ≤ X ^ 33 := by
    rw [pow_succ]
    nlinarith only [hX, ha, hp]
  have hh := Nat.mul_le_mul hk ha1
  rw [← pow_add] at hh
  change chainBound B * (auxiliaryCalls n B + 1) ≤ X ^ 36 at hh
  have hp36 : 1 ≤ X ^ 36 := Nat.one_le_pow _ _ hx
  have hh1 : X ^ 36 + 1 ≤ X ^ 37 := by
    rw [pow_succ]
    nlinarith only [hX, hp36]
  unfold callBase
  omega



structure BudgetCode (n : ℕ) where
  a : Fin n → ℕ
  b : Fin n → ℕ
  uk : ℕ
  vk : ℕ
  um : ℕ
  vm : ℕ

namespace BudgetCode

def depth {n : ℕ} (p : BudgetCode n) : ℕ := p.uk + p.vk + p.um + p.vm

def Good {n : ℕ} (p : BudgetCode n) : Prop := ∀ i, p.a i + p.b i ≤ p.vk + p.vm

def zero (n : ℕ) : BudgetCode n := ⟨fun _ => 0, fun _ => 0, 0, 0, 0, 0⟩

def value {n : ℕ} (hn : 0 < n) (p : BudgetCode n) : Budgets n where
  alpha i := (1 / 2) ^ p.a i
  beta i := (1 / 2) ^ p.b i
  k := n * (4 / 5) ^ p.uk * (3 / 5) ^ p.vk
  m := n * (4 / 5) ^ p.um * (3 / 5) ^ p.vm
  alpha_pos _ := by positivity
  beta_pos _ := by positivity
  k_pos := by
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    positivity
  m_pos := by
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    positivity

def reduceK {n : ℕ} (p : BudgetCode n) : BudgetCode n := {p with uk := p.uk + 1}
def reduceM {n : ℕ} (p : BudgetCode n) : BudgetCode n := {p with um := p.um + 1}
def reweightK {n : ℕ} (p : BudgetCode n) (H : Finset (Fin n)) : BudgetCode n :=
  {p with a := fun i => p.a i + if i ∈ H then 1 else 0, vk := p.vk + 1}
def reweightM {n : ℕ} (p : BudgetCode n) (H : Finset (Fin n)) : BudgetCode n :=
  {p with b := fun i => p.b i + if i ∈ H then 1 else 0, vm := p.vm + 1}

theorem value_zero (G : Game) : (zero G.n).value G.positive = rootBudgets G := by
  cases G
  simp [value, zero, rootBudgets]

theorem value_reduceK {n : ℕ} (hn : 0 < n) (p : BudgetCode n) :
    p.reduceK.value hn = (p.value hn).reduceK := by
  unfold value reduceK Budgets.reduceK
  congr 1
  rw [pow_succ]
  ring

theorem value_reduceM {n : ℕ} (hn : 0 < n) (p : BudgetCode n) :
    p.reduceM.value hn = (p.value hn).reduceM := by
  unfold value reduceM Budgets.reduceM
  congr 1
  rw [pow_succ]
  ring

theorem value_reweightK {n : ℕ} (hn : 0 < n) (p : BudgetCode n) (H : Finset (Fin n)) :
    (p.reweightK H).value hn = (p.value hn).reweightK H := by
  unfold value reweightK Budgets.reweightK
  congr 1
  · funext i
    unfold halve
    by_cases hi : i ∈ H <;> simp [hi, pow_succ] ; ring
  · rw [pow_succ]
    ring

theorem value_reweightM {n : ℕ} (hn : 0 < n) (p : BudgetCode n) (H : Finset (Fin n)) :
    (p.reweightM H).value hn = (p.value hn).reweightM H := by
  unfold value reweightM Budgets.reweightM
  congr 1
  · funext i
    unfold halve
    by_cases hi : i ∈ H <;> simp [hi, pow_succ] ; ring
  · rw [pow_succ]
    ring

@[simp] theorem depth_zero (n : ℕ) : (zero n).depth = 0 := rfl
@[simp] theorem depth_reduceK {n : ℕ} (p : BudgetCode n) : p.reduceK.depth = p.depth + 1 := by
  simp only [depth, reduceK]; omega
@[simp] theorem depth_reduceM {n : ℕ} (p : BudgetCode n) : p.reduceM.depth = p.depth + 1 := by
  simp only [depth, reduceM]; omega
@[simp] theorem depth_reweightK {n : ℕ} (p : BudgetCode n) (H : Finset (Fin n)) :
    (p.reweightK H).depth = p.depth + 1 := by simp only [depth, reweightK]; omega
@[simp] theorem depth_reweightM {n : ℕ} (p : BudgetCode n) (H : Finset (Fin n)) :
    (p.reweightM H).depth = p.depth + 1 := by simp only [depth, reweightM]; omega

theorem good_zero (n : ℕ) : (zero n).Good := fun _ => Nat.zero_le _
theorem good_reduceK {n : ℕ} {p : BudgetCode n} (hp : p.Good) : p.reduceK.Good := hp
theorem good_reduceM {n : ℕ} {p : BudgetCode n} (hp : p.Good) : p.reduceM.Good := hp

theorem good_reweightK {n : ℕ} {p : BudgetCode n} (hp : p.Good) (H : Finset (Fin n)) :
    (p.reweightK H).Good := by
  intro i
  have hi := hp i
  dsimp only [reweightK]
  split_ifs <;> omega

theorem good_reweightM {n : ℕ} {p : BudgetCode n} (hp : p.Good) (H : Finset (Fin n)) :
    (p.reweightM H).Good := by
  intro i
  have hi := hp i
  dsimp only [reweightM]
  split_ifs <;> omega

theorem coordinate_depth {n : ℕ} {p : BudgetCode n} (hp : p.Good) (i : Fin n) :
    p.a i + p.b i ≤ p.depth := by
  have hi := hp i
  unfold depth
  omega

theorem value_k_fraction {n : ℕ} (hn : 0 < n) (p : BudgetCode n) :
    (p.value hn).k = (n * 4 ^ p.uk * 3 ^ p.vk : ℚ) / 5 ^ (p.uk + p.vk) := by
  simp only [value, div_pow, pow_add]
  ring

theorem value_m_fraction {n : ℕ} (hn : 0 < n) (p : BudgetCode n) :
    (p.value hn).m = (n * 4 ^ p.um * 3 ^ p.vm : ℚ) / 5 ^ (p.um + p.vm) := by
  simp only [value, div_pow, pow_add]
  ring

theorem value_density {n : ℕ} (hn : 0 < n) (p : BudgetCode n) (i : Fin n) :
    (p.value hn).density i = (2 : ℚ) ^ (p.a i + p.b i) := by
  simp only [Budgets.density, value, one_div, inv_pow, mul_inv_rev, inv_inv, pow_add]
  ring

theorem value_density_sum_bound {n : ℕ} (hn : 0 < n) (p : BudgetCode n) (hp : p.Good)
    (S : Finset (Fin n)) : mass (p.value hn).density S ≤ (n : ℚ) * 2 ^ p.depth := by
  unfold mass
  have hh : ∑ i ∈ S, (p.value hn).density i ≤ ∑ _i ∈ S, (2 : ℚ) ^ p.depth := by
    apply Finset.sum_le_sum
    intro i _
    rw [value_density]
    exact pow_le_pow_right₀ (by norm_num) (coordinate_depth hp i)
  have hc : (S.card : ℚ) ≤ n := by
    have hc := Finset.card_le_card (Finset.subset_univ S)
    simpa only [Finset.card_univ, Fintype.card_fin, Nat.cast_le] using hc
  simp only [Finset.sum_const, nsmul_eq_mul] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hc (by positivity : (0 : ℚ) ≤ 2 ^ p.depth))

end BudgetCode

inductive ReachableBudget (G : Game) : ℕ → Budgets G.n → Prop
  | root : ReachableBudget G 0 (rootBudgets G)
  | reduceK {d P} : ReachableBudget G d P → 1 ≤ P.parameter →
      ReachableBudget G (d + 1) P.reduceK
  | reduceM {d P} : ReachableBudget G d P → 1 ≤ P.parameter →
      ReachableBudget G (d + 1) P.reduceM
  | reweightK {d P} (H : Finset (Fin G.n)) : ReachableBudget G d P → 1 ≤ P.parameter →
      P.measure H ≤ 1 / 2 → ReachableBudget G (d + 1) (P.reweightK H)
  | reweightM {d P} (H : Finset (Fin G.n)) : ReachableBudget G d P → 1 ≤ P.parameter →
      P.measure H ≤ 1 / 2 → ReachableBudget G (d + 1) (P.reweightM H)

theorem ReachableBudget.depth_rank {G : Game} {d P} (h : ReachableBudget G d P) :
    d + parameterRank P.parameter ≤ parameterRank (rootBudgets G).parameter := by
  induction h with
  | root => omega
  | reduceK _ hR ih => have hr := Budgets.reduceK_rank _ hR; omega
  | reduceM _ hR ih => have hr := Budgets.reduceM_rank _ hR; omega
  | reweightK H _ hR hH ih => have hr := Budgets.reweightK_rank _ G.positive hR hH; omega
  | reweightM H _ hR hH ih => have hr := Budgets.reweightM_rank _ G.positive hR hH; omega

theorem ReachableBudget.presentation {G : Game} {d P} (h : ReachableBudget G d P) :
    ∃ p : BudgetCode G.n, p.value G.positive = P ∧ p.Good ∧ p.depth = d := by
  induction h with
  | root => exact ⟨.zero G.n, BudgetCode.value_zero G, BudgetCode.good_zero G.n, rfl⟩
  | reduceK _ hR ih =>
    obtain ⟨p, rfl, hp, hd⟩ := ih
    exact ⟨p.reduceK, p.value_reduceK G.positive, BudgetCode.good_reduceK hp, by simp [hd]⟩
  | reduceM _ hR ih =>
    obtain ⟨p, rfl, hp, hd⟩ := ih
    exact ⟨p.reduceM, p.value_reduceM G.positive, BudgetCode.good_reduceM hp, by simp [hd]⟩
  | reweightK H _ hR hH ih =>
    obtain ⟨p, rfl, hp, hd⟩ := ih
    exact ⟨p.reweightK H, p.value_reweightK G.positive H, BudgetCode.good_reweightK hp H, by simp [hd]⟩
  | reweightM H _ hR hH ih =>
    obtain ⟨p, rfl, hp, hd⟩ := ih
    exact ⟨p.reweightM H, p.value_reweightM G.positive H, BudgetCode.good_reweightM hp H, by simp [hd]⟩

end MeanPayoff
end

end OAI
