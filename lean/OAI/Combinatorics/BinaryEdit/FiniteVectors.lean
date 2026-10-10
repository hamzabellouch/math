import Mathlib

namespace OAI

/-! Concrete vectors for the finite tree (finite-tree.tex, finite-vectors).
A prefix is represented by its depth and any full leaf path extending it.
All definitions ignore the unused tail of that representative. No primality
assumption is needed for the annihilation and recursive vector identities. -/

namespace TreeEdit.BinaryLower.FiniteVectors

open scoped BigOperators

variable {m k : ℕ}

abbrev Leaf (m k : ℕ) := Fin k → Fin m

def Agrees (j : ℕ) (a b : Leaf m k) : Prop :=
  ∀ q : Fin k, q.val < j → b q = a q

instance (j : ℕ) (a b : Leaf m k) : Decidable (Agrees j a b) :=
  inferInstanceAs (Decidable (∀ q : Fin k, q.val < j → b q = a q))

def levelProduct (p : Fin k → Fin m → ℕ) (q : Fin k) : ℕ := ∏ i, p q i

def suffixScale (p : Fin k → Fin m → ℕ) (j : ℕ) : ℕ :=
  ∏ q ∈ Finset.univ.filter (fun q : Fin k => j ≤ q.val), levelProduct p q

def prefixPeriod (p : Fin k → Fin m → ℕ) (j : ℕ) (a : Leaf m k) : ℕ :=
  2 * ∏ q ∈ Finset.univ.filter (fun q : Fin k => q.val < j), p q (a q)

def leafPeriod (p : Fin k → Fin m → ℕ) (a : Leaf m k) : ℕ :=
  2 * ∏ q, p q (a q)

abbrev State (p : Fin k → Fin m → ℕ) := (a : Leaf m k) → ZMod (leafPeriod p a)

/-- Distinguished subtree vector, with the common suffix coefficient. -/
def w (p : Fin k → Fin m → ℕ) (j : ℕ) (a : Leaf m k) : State p :=
  fun b => if Agrees j a b then (suffixScale p j : ZMod (leafPeriod p b)) else 0

/-- Cheap row-advancing vector. -/
def u (p : Fin k → Fin m → ℕ) (j : ℕ) (a : Leaf m k) : State p :=
  fun b => if Agrees j a b then (suffixScale p (j + 1) : ZMod (leafPeriod p b)) else 0

@[simp] lemma prefixPeriod_zero (p : Fin k → Fin m → ℕ) (a : Leaf m k) :
    prefixPeriod p 0 a = 2 := by simp [prefixPeriod]

@[simp] lemma suffixScale_top (p : Fin k → Fin m → ℕ) : suffixScale p k = 1 := by
  have h : Finset.univ.filter (fun q : Fin k => k ≤ q.val) = ∅ := by
    ext q
    simp [Nat.not_le_of_gt q.isLt]
  simp [suffixScale, h]

lemma suffixScale_succ (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j < k) :
    suffixScale p j = levelProduct p ⟨j, hj⟩ * suffixScale p (j + 1) := by
  have hs : Finset.univ.filter (fun q : Fin k => j ≤ q.val) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun q : Fin k => j + 1 ≤ q.val)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hq
      by_cases he : q.val = j
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (by omega)
    · rintro (rfl | hq)
      · exact le_rfl
      · omega
  have hn : (⟨j, hj⟩ : Fin k) ∉
      Finset.univ.filter (fun q : Fin k => j + 1 ≤ q.val) := by simp
  simp only [suffixScale, hs, Finset.prod_insert hn]

/-- The full leaf modulus divides its prefix period times the suffix scale. -/
lemma leafPeriod_dvd (p : Fin k → Fin m → ℕ) (j : ℕ) (a b : Leaf m k)
    (hab : Agrees j a b) : leafPeriod p b ∣ prefixPeriod p j a * suffixScale p j := by
  have hprod : (∏ q, p q (b q)) ∣
      ∏ q : Fin k, if q.val < j then p q (a q) else levelProduct p q := by
    apply Finset.prod_dvd_prod_of_dvd
    intro q hq
    by_cases hj : q.val < j
    · simp only [ite_eq_left hj, hab q hj]
      exact dvd_rfl
    · simp only [ite_eq_right hj, levelProduct]
      exact Finset.dvd_prod_of_mem (fun i => p q i) (Finset.mem_univ (b q))
  rw [Finset.prod_ite] at hprod
  have h := Nat.mul_dvd_mul_left 2 hprod
  simpa only [leafPeriod, prefixPeriod, suffixScale, Nat.not_lt, mul_assoc] using h

/-- Every node vector is annihilated by its prescribed prefix period. -/
theorem prefixPeriod_nsmul_w (p : Fin k → Fin m → ℕ) (j : ℕ) (a : Leaf m k) :
    prefixPeriod p j a • w p j a = 0 := by
  funext b
  change prefixPeriod p j a • (if Agrees j a b then
    (suffixScale p j : ZMod (leafPeriod p b)) else 0) = 0
  by_cases hab : Agrees j a b
  · rw [ite_eq_left hab, nsmul_eq_mul, ← Nat.cast_mul]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (leafPeriod_dvd p j a b hab)
  · simp [hab]

/-- Multiplication of the cheap vector by the current level product gives `w`. -/
theorem w_eq_level_nsmul_u (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j < k)
    (a : Leaf m k) : w p j a = levelProduct p ⟨j, hj⟩ • u p j a := by
  funext b
  change (if Agrees j a b then (suffixScale p j : ZMod (leafPeriod p b)) else 0) =
    levelProduct p ⟨j, hj⟩ • (if Agrees j a b then
      (suffixScale p (j + 1) : ZMod (leafPeriod p b)) else 0)
  by_cases hab : Agrees j a b
  · simp only [ite_eq_left hab, nsmul_eq_mul, suffixScale_succ p j hj, Nat.cast_mul]
  · simp [hab]

lemma agrees_child_iff (j : ℕ) (hj : j < k) (a b : Leaf m k) (i : Fin m) :
    Agrees (j + 1) (Function.update a ⟨j, hj⟩ i) b ↔
      Agrees j a b ∧ b ⟨j, hj⟩ = i := by
  constructor
  · intro h
    constructor
    · intro q hq
      have hne : q ≠ ⟨j, hj⟩ := by intro he; subst q; simp at hq
      simpa only [Function.update_of_ne hne] using h q (by omega)
    · simpa using h ⟨j, hj⟩ (Nat.lt_succ_self j)
  · rintro ⟨h, hi⟩ q hq
    by_cases he : q = ⟨j, hj⟩
    · subst q
      simpa using hi
    · have hval : q.val ≠ j := by intro hv; exact he (Fin.ext hv)
      rw [Function.update_of_ne he]
      exact h q (by omega)

/-- The cheap vector is exactly the sum of the children's distinguished vectors. -/
theorem u_eq_sum_child_w (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j < k)
    (a : Leaf m k) :
    u p j a = ∑ i : Fin m, w p (j + 1) (Function.update a ⟨j, hj⟩ i) := by
  funext b
  simp only [u, w, Finset.sum_apply, agrees_child_iff j hj a b]
  by_cases hab : Agrees j a b
  · simp [hab]
  · simp [hab]

@[simp] lemma agrees_top_iff (a b : Leaf m k) : Agrees k a b ↔ b = a := by
  constructor
  · intro h
    funext q
    exact h q q.isLt
  · rintro rfl q hq
    rfl

/-- At a leaf, the distinguished vector is the coordinate unit vector. -/
theorem w_leaf (p : Fin k → Fin m → ℕ) (a b : Leaf m k) :
    w p k a b = if b = a then 1 else 0 := by
  simp [w]

lemma agrees_refl (j : ℕ) (a : Leaf m k) : Agrees j a a := by
  intro q hq
  rfl

lemma agrees_symm {j : ℕ} {a b : Leaf m k} (h : Agrees j a b) : Agrees j b a := by
  intro q hq
  exact (h q hq).symm

lemma agrees_trans {j : ℕ} {a b c : Leaf m k}
    (hab : Agrees j a b) (hbc : Agrees j b c) : Agrees j a c := by
  intro q hq
  exact (hbc q hq).trans (hab q hq)

lemma agrees_iff_of_agrees {j : ℕ} {a b : Leaf m k} (h : Agrees j a b)
    (c : Leaf m k) : Agrees j a c ↔ Agrees j b c :=
  ⟨fun hac => agrees_trans (agrees_symm h) hac, fun hbc => agrees_trans h hbc⟩

lemma prefixPeriod_eq_of_agrees (p : Fin k → Fin m → ℕ) {j : ℕ}
    {a b : Leaf m k} (h : Agrees j a b) : prefixPeriod p j a = prefixPeriod p j b := by
  unfold prefixPeriod
  congr 1
  apply Finset.prod_congr rfl
  intro q hq
  rw [h q (Finset.mem_filter.mp hq).2]

lemma w_eq_of_agrees (p : Fin k → Fin m → ℕ) {j : ℕ}
    {a b : Leaf m k} (h : Agrees j a b) : w p j a = w p j b := by
  funext c
  simp only [w, agrees_iff_of_agrees h c]

lemma u_eq_of_agrees (p : Fin k → Fin m → ℕ) {j : ℕ}
    {a b : Leaf m k} (h : Agrees j a b) : u p j a = u p j b := by
  funext c
  simp only [u, agrees_iff_of_agrees h c]

lemma prefixPeriod_child (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j < k)
    (a : Leaf m k) (i : Fin m) :
    prefixPeriod p (j + 1) (Function.update a ⟨j, hj⟩ i) =
      prefixPeriod p j a * p ⟨j, hj⟩ i := by
  have hs : Finset.univ.filter (fun q : Fin k => q.val < j + 1) =
      insert ⟨j, hj⟩ (Finset.univ.filter (fun q : Fin k => q.val < j)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hq
      by_cases he : q.val = j
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (by omega)
    · rintro (rfl | hq)
      · exact Nat.lt_succ_self j
      · omega
  have hn : (⟨j, hj⟩ : Fin k) ∉ Finset.univ.filter (fun q : Fin k => q.val < j) := by simp
  have hp : (∏ q ∈ Finset.univ.filter (fun q : Fin k => q.val < j),
      p q (Function.update a ⟨j, hj⟩ i q)) =
      ∏ q ∈ Finset.univ.filter (fun q : Fin k => q.val < j), p q (a q) := by
    apply Finset.prod_congr rfl
    intro q hq
    have hlt := (Finset.mem_filter.mp hq).2
    have he : q ≠ ⟨j, hj⟩ := by intro he; subst q; simp at hlt
    rw [Function.update_of_ne he]
  simp only [prefixPeriod, hs, Finset.prod_insert hn, Function.update_self, hp]
  ring

@[simp] lemma prefixPeriod_top (p : Fin k → Fin m → ℕ) (a : Leaf m k) :
    prefixPeriod p k a = leafPeriod p a := by
  simp [prefixPeriod, leafPeriod]

lemma leafPeriod_pos (p : Fin k → Fin m → ℕ) (hp : ∀ q i, 0 < p q i) (a : Leaf m k) :
    0 < leafPeriod p a := by
  unfold leafPeriod
  apply Nat.mul_pos (by norm_num)
  apply Finset.prod_pos
  intro q hq
  exact hp q (a q)

lemma prefixPeriod_pos (p : Fin k → Fin m → ℕ) (hp : ∀ q i, 0 < p q i)
    (j : ℕ) (a : Leaf m k) : 0 < prefixPeriod p j a := by
  unfold prefixPeriod
  apply Nat.mul_pos (by norm_num)
  apply Finset.prod_pos
  intro q hq
  exact hp q (a q)

/-- Positive leaf moduli make the manuscript's parameter group finite. -/
theorem state_finite (p : Fin k → Fin m → ℕ) (hp : ∀ q i, 0 < p q i) :
    Finite (State p) := by
  let : ∀ a : Leaf m k, NeZero (leafPeriod p a) :=
    fun a => ⟨ne_of_gt (leafPeriod_pos p hp a)⟩
  infer_instance

/-- Prefix products agree with the usual dependent `Fin j` path product. -/
lemma prefixPeriod_eq_prod_cast (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j ≤ k)
    (a : Leaf m k) : prefixPeriod p j a =
      2 * ∏ q : Fin j, p (Fin.castLE hj q) (a (Fin.castLE hj q)) := by
  unfold prefixPeriod
  congr 1
  apply Finset.prod_bij (fun q hq => (⟨q.val, (Finset.mem_filter.mp hq).2⟩ : Fin j))
  · intro q hq
    exact Finset.mem_univ _
  · intro q₁ h₁ q₂ h₂ he
    exact Fin.ext (congrArg (fun r : Fin j => r.val) he)
  · intro q hq
    refine ⟨Fin.castLE hj q, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castLE]
      exact q.isLt
    · rfl
  · intro q hq
    rfl

/-- The source's period upper bound, on the concrete vector prefix periods. -/
lemma prefixPeriod_le (p : Fin k → Fin m → ℕ) (hp : ∀ q i, p q i ≤ k ^ 5)
    (j : ℕ) (hj : j ≤ k) (a : Leaf m k) : prefixPeriod p j a ≤ 2 * k ^ (5 * j) := by
  rw [prefixPeriod_eq_prod_cast p j hj a]
  apply Nat.mul_le_mul_left
  calc
    _ ≤ ∏ _q : Fin j, k ^ 5 := Finset.prod_le_prod fun q _ => hp _ _
    _ = k ^ (5 * j) := by simp [← pow_mul]

/-- Distinct odd depth/child primes make the prefix period coprime to the
current level. This is a specialization to the concrete vector API of the
prime-product coprimality calculation in `lem:orders`. -/
lemma prefixPeriod_coprime_level (p : Fin k → Fin m → ℕ)
    (hinj : Function.Injective (fun z : Fin k × Fin m => p z.1 z.2))
    (hprime : ∀ q i, Nat.Prime (p q i)) (hodd : ∀ q i, p q i ≠ 2)
    (j : ℕ) (hj : j < k) (a : Leaf m k) :
    Nat.Coprime (prefixPeriod p j a) (levelProduct p ⟨j, hj⟩) := by
  rw [prefixPeriod_eq_prod_cast p j hj.le a]
  unfold levelProduct
  apply Nat.Coprime.mul_left
  · apply Nat.Coprime.prod_right
    intro i hi
    exact (Nat.coprime_primes Nat.prime_two (hprime _ i)).mpr (Ne.symm (hodd _ i))
  · apply Nat.Coprime.prod_left
    intro q hq
    apply Nat.Coprime.prod_right
    intro i hi
    apply (Nat.coprime_primes (hprime _ _) (hprime _ _)).mpr
    intro he
    have hpair := @hinj (Fin.castLE hj.le q, a (Fin.castLE hj.le q)) (⟨j, hj⟩, i) he
    have hval := congrArg (fun z : Fin k × Fin m => z.1.val) hpair
    simp only [Fin.val_castLE] at hval
    exact (Nat.ne_of_lt q.isLt) hval

lemma prefixPeriod_zsmul_w (p : Fin k → Fin m → ℕ) (j : ℕ) (a : Leaf m k) :
    (prefixPeriod p j a : ℤ) • w p j a = 0 := by
  simpa only [natCast_zsmul] using prefixPeriod_nsmul_w p j a

lemma zsmul_w_eq_mul_u (p : Fin k → Fin m → ℕ) (j : ℕ) (hj : j < k)
    (a : Leaf m k) (t : ℤ) :
    t • w p j a = (t * (levelProduct p ⟨j, hj⟩ : ℤ)) • u p j a := by
  calc
    _ = t • ((levelProduct p ⟨j, hj⟩ : ℤ) • u p j a) := by
      rw [natCast_zsmul, w_eq_level_nsmul_u p j hj a]
    _ = _ := (mul_smul t (levelProduct p ⟨j, hj⟩ : ℤ) (u p j a)).symm

/-- The leaf coordinate changes under exactly the nonzero period residues,
including negative translations. This is the base case of separation. -/
lemma leaf_shift_eq_iff (p : Fin k → Fin m → ℕ) (a : Leaf m k)
    (x : State p) (t : ℤ) :
    (x + t • w p k a) a = x a ↔ (leafPeriod p a : ℤ) ∣ t := by
  simpa [w_leaf, zsmul_eq_mul] using
    ZMod.intCast_zmod_eq_zero_iff_dvd t (leafPeriod p a)

lemma leaf_shift_ne_iff (p : Fin k → Fin m → ℕ) (a : Leaf m k)
    (x : State p) (t : ℤ) :
    (x + t • w p k a) a ≠ x a ↔ ¬ (leafPeriod p a : ℤ) ∣ t :=
  (leaf_shift_eq_iff p a x t).not

end TreeEdit.BinaryLower.FiniteVectors

end OAI
