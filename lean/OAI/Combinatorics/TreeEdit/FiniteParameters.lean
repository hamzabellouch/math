import OAI.Combinatorics.TreeEdit.FinitePrimes
import OAI.Combinatorics.TreeEdit.FiniteSpectrum
import OAI.Combinatorics.TreeEdit.DistortionTransfer
import OAI.Combinatorics.TreeEdit.RandomCode

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace FiniteTree

variable {m : ℕ} {p : ℕ → Fin m → ℕ} [∀ j i, NeZero (p j i)]

lemma symbol_card_bound {h q U : ℕ} [NeZero q]
    (hp : ∀ j, j < h → ∀ i, p j i ≤ U) :
    Fintype.card (Symbol m p h q) ≤ m ^ h * q * U ^ h := by
  induction h generalizing q with
  | zero => simp [Symbol, ZMod.card]
  | succ h ih =>
    change Fintype.card (Σ i : Fin m, Symbol m p h (q * p h i)) ≤ _
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _i : Fin m, m ^ h * (q * U) * U ^ h := by
        apply Finset.sum_le_sum
        intro i _
        calc
          _ ≤ m ^ h * (q * p h i) * U ^ h := ih (fun j hj => hp j (by omega))
          _ ≤ _ := by gcongr; exact hp h (by omega) i
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id, pow_succ]; ring

omit [∀ j i, NeZero (p j i)] in
lemma symbol_nonempty {h q : ℕ} (hm : 0 < m) : Nonempty (Symbol m p h q) := by
  induction h generalizing q with
  | zero => exact ⟨0⟩
  | succ h ih => exact ⟨⟨⟨0, hm⟩, Classical.choice (ih (q := q * p h ⟨0, hm⟩))⟩⟩

theorem displacement_bound {T h q K U Qcap J : ℕ} [NeZero q]
    (hK : 1 ≤ K) (hU : 1 ≤ U) (hp : ∀ j, j < h → ∀ i, p j i ≤ U)
    (hq : q * U ^ h ≤ Qcap) (hJ : 2 * (Qcap * U ^ K) ≤ J)
    (hJT : J ≤ T) (hJpos : 0 < J)
    (F : State m p h q → RealL1) (C : ℝ) (hC : 0 ≤ C)
    (hlip : ∀ x y, dist (F x) (F y) ≤ C * ed (word p T h q x).val (word p T h q y).val) :
    FiniteFourier.average (fun x => dist (F x) (F (x + w p h q))) ≤
      C * length m T h * (4 * ((K : ℝ)⁻¹ ^ h + 2 * h * J / T)) := by
  obtain ⟨H, hH, _, he⟩ := FiniteFourier.l1_displacement_spectrum F
  have hbound : SpectralBound T h q H C := by
    intro z b hb
    rw [FiniteFourier.energy, ← he]
    apply FiniteFourier.average_le
    intro x
    rw [dist_comm]
    exact (hlip x (x + z)).trans (mul_le_mul_of_nonneg_left (hb x) hC)
  have hh := mass_bound hH hC hbound hK hU hp hq hJ hJT hJpos
  calc
    _ = FiniteFourier.energy H (w p h q) := by simpa only [dist_comm, FiniteFourier.energy] using he (w p h q)
    _ ≤ 4 * FiniteFourier.activeMass H (w p h q) := FiniteFourier.energy_le_mass hH _
    _ ≤ 4 * (C * length m T h * ((K : ℝ)⁻¹ ^ h + 2 * h * J / T)) := by gcongr
    _ = _ := by ring

end FiniteTree

namespace FiniteTree

def branching (k : ℕ) : ℕ := 20 * k
def repetitions (k : ℕ) : ℕ := k ^ (20 * k)
def wordLength (k : ℕ) : ℕ := (branching k * repetitions k) ^ k
def binaryLength (k : ℕ) : ℕ := wordLength k ^ 3

lemma wordLength_upper_start {k : ℕ} (hk : 2 ≤ k) : k ≤ wordLength k := by
  have hT : 1 ≤ repetitions k := Nat.one_le_pow _ _ (by omega)
  have hbase : k ≤ branching k * repetitions k := by
    exact (show k ≤ branching k by dsimp [branching]; omega).trans (Nat.le_mul_of_pos_right _ hT)
  calc
    k ≤ branching k * repetitions k := hbase
    _ = (branching k * repetitions k) ^ 1 := by simp
    _ ≤ wordLength k := pow_le_pow_right₀ (by omega) (by omega)

lemma parameter_gap {k : ℕ} (hk : 2 ≤ k) :
    4 * k ^ (10 * k) ≤ repetitions k ∧ 2 * k ^ 5 ≤ repetitions k := by
  have hk1 : 1 ≤ k := by omega
  have h4 : 4 ≤ k ^ (10 * k) := by
    calc
      4 ≤ k ^ 2 := by nlinarith
      _ ≤ k ^ (10 * k) := pow_le_pow_right₀ hk1 (by omega)
  have hpow : repetitions k = k ^ (10 * k) * k ^ (10 * k) := by
    rw [repetitions, ← pow_add]
    congr 1
    omega
  constructor
  · rw [hpow]
    exact Nat.mul_le_mul_right _ h4
  · calc
      2 * k ^ 5 ≤ k * k ^ 5 := Nat.mul_le_mul_right _ hk
      _ = k ^ 6 := by ring
      _ ≤ repetitions k := pow_le_pow_right₀ hk1 (by omega)

lemma spectral_coefficient {k : ℕ} (hk : 2 ≤ k) :
    4 * ((k : ℝ)⁻¹ ^ k + 2 * k * (4 * k ^ (10 * k)) / k ^ (20 * k)) ≤
      40 * (k : ℝ)⁻¹ ^ k := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hp : (k : ℝ) ^ (k + 1) ≤ (k : ℝ) ^ (10 * k) := pow_le_pow_right₀ hk1 (by omega)
  have hp20 : (k : ℝ) ^ (20 * k) = (k : ℝ) ^ (10 * k) * (k : ℝ) ^ (10 * k) := by
    rw [← pow_add]
    congr 1
    omega
  have he : 2 * (k : ℝ) * (4 * k ^ (10 * k)) / k ^ (20 * k) = 8 * k / k ^ (10 * k) := by
    rw [hp20]
    field_simp
    ring
  rw [he]
  have hh : 8 * (k : ℝ) / k ^ (10 * k) ≤ 8 * (k : ℝ)⁻¹ ^ k := by
    rw [inv_pow, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    rw [pow_succ] at hp
    nlinarith
  have hh0 : 0 ≤ (k : ℝ)⁻¹ ^ k := by positivity
  linarith

theorem witnesses_eventually : ∀ᶠ k : ℕ in Filter.atTop,
    ∃ W : Finset (List Bool), 2 ≤ W.card ∧ (∀ w ∈ W, w.length = binaryLength k) ∧
      ((k : ℝ) / 4) ^ k / 32160 ≤ c1 W := by
  obtain ⟨M₀, hconvert⟩ := binary_conversion
  filter_upwards [PrimeSupply.finite_lists_eventually, Filter.eventually_ge_atTop 2,
    Filter.eventually_ge_atTop M₀] with k hprimes hk hkM
  obtain ⟨p, hp0, ha, hp⟩ := hprimes
  have : ∀ (j : ℕ) (i : Fin (20 * k)), NeZero (p j i) := fun j i => ⟨ne_of_gt (hp0 j i)⟩
  let : Fintype (Symbol (20 * k) p k 2) := symbolFintype p hp0 k 2 (by omega)
  let : Fintype (State (20 * k) p k 2) := stateFintype p hp0 k 2 (by omega)
  let T := repetitions k
  let M := length (20 * k) T k
  have hM : M = wordLength k := length_eq (20 * k) T k
  have hm : 0 < 20 * k := by omega
  have hT : 0 < T := pow_pos (by omega) _
  have hkp : 0 < k := by omega
  have hMge : k ≤ M := hM ▸ wordLength_upper_start hk
  have hMpos : 0 < M := hkp.trans_le hMge
  have hcardpos : 1 ≤ Fintype.card (Symbol (20 * k) p k 2) := by
    exact Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Fintype.card_pos_iff.mpr (symbol_nonempty hm)))
  have hcard : Fintype.card (Symbol (20 * k) p k 2) ≤ M := by
    calc
      _ ≤ (20 * k) ^ k * 2 * (k ^ 5) ^ k := symbol_card_bound hp
      _ ≤ (20 * k) ^ k * (2 ^ k * (k ^ 5) ^ k) := by
        have hh : 2 ≤ 2 ^ k := by
          calc 2 = 2 ^ 1 := by norm_num
               _ ≤ 2 ^ k := pow_le_pow_right₀ (by omega) (by omega)
        calc
          _ = (20 * k) ^ k * (2 * (k ^ 5) ^ k) := by ring
          _ ≤ _ := by gcongr
      _ = (20 * k) ^ k * (2 * k ^ 5) ^ k := by simp only [mul_pow, mul_assoc]
      _ ≤ (20 * k) ^ k * T ^ k := by gcongr; exact (parameter_gap hk).2
      _ = M := by
        change (20 * k) ^ k * T ^ k = length (20 * k) T k
        simp only [length_eq, mul_pow, mul_assoc]
  obtain ⟨c, hc⟩ := hconvert M (hkM.trans hMge) (Symbol (20 * k) p k 2) hcardpos hcard
  have hsep (x : State (20 * k) p k 2) : (Nat.cast M : ℝ) ≤ (4 : ℝ) ^ k *
      ed (word p T k 2 x).val (word p T k 2 (x + w p k 2)).val := by
    have hTbound : T ≤ (k ^ 4) ^ (10 * k) := by
      change k ^ (20 * k) ≤ (k ^ 4) ^ (10 * k)
      rw [← pow_mul]
      exact pow_le_pow_right₀ (by omega) (by omega)
    have hh := separation (m := 20 * k) (s := 10 * k) (T := T)
      (by omega) (by omega) hT (Nat.one_le_pow _ _ (by omega)) hTbound ha x 1 (by norm_num)
    simp only [one_zsmul] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast deficit_le_ed _ _) (by positivity))
  have hobs (F : State (20 * k) p k 2 → RealL1) (C : ℝ) (hC : 0 ≤ C)
      (hlip : ∀ x y, dist (F x) (F y) ≤ C * ed (word p T k 2 x).val (word p T k 2 y).val) :
      FiniteFourier.average (fun x => dist (F x) (F (x + w p k 2))) ≤
        C * (Nat.cast M : ℝ) * (40 * (k : ℝ)⁻¹ ^ k) := by
    have hJ : 2 * ((2 * (k ^ 5) ^ k) * (k ^ 5) ^ k) ≤ 4 * k ^ (10 * k) := by
      have he : (k ^ 5) ^ k * (k ^ 5) ^ k = k ^ (10 * k) := by
        rw [← pow_add, ← pow_mul]
        congr 1
        omega
      calc
        _ = 4 * ((k ^ 5) ^ k * (k ^ 5) ^ k) := by ring
        _ ≤ _ := by rw [he]
    have hh := displacement_bound (p := p) (h := k) (q := 2) (T := T)
      (K := k) (U := k ^ 5) (Qcap := 2 * (k ^ 5) ^ k) (J := 4 * k ^ (10 * k))
      (by omega) (Nat.one_le_pow _ _ (by omega)) hp le_rfl hJ (parameter_gap hk).1 (by positivity) F C hC hlip
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Nat.cast_nonneg _))
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, T, repetitions] using spectral_coefficient hk
  obtain ⟨W, hW, hl, hd⟩ := binary_transfer hMpos (pow_pos hMpos _) (word p T k 2) (w p k 2) c
    ((4 : ℝ) ^ k) (40 * (k : ℝ)⁻¹ ^ k) (by positivity) (by positivity)
    (fun x y => (hc x y).2.2.1) hsep hobs
  refine ⟨W, hW, ?_, ?_⟩
  · intro v hv
    rw [hl v hv, binaryLength, ← hM]
    ring
  · have he : (804 * (4 : ℝ) ^ k * (40 * (k : ℝ)⁻¹ ^ k))⁻¹ = ((k : ℝ) / 4) ^ k / 32160 := by
      rw [div_pow, inv_pow]
      field_simp
      ring
    exact he ▸ hd

end FiniteTree

end TreeEdit

end OAI
