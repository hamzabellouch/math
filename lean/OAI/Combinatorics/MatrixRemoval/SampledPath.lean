import Mathlib

namespace OAI

/-!
Concrete common-leaf path positions.
The variable-position type is `Fin (2*h+1) × Fin (2^h)`: even classes are
plus, odd classes are minus, and class `2*h` is the shared leaf class.
-/

namespace Problem348.SampledPath

abbrev VariablePosition (h : ℕ) := Fin (2 * h + 1) × Fin (2 ^ h)

def blockSize (h i : ℕ) : ℕ := 2 ^ (h - i)

theorem blockSize_pos (h i : ℕ) : 0 < blockSize h i := by
  exact pow_pos (by decide) _

theorem blockSize_mul_nodes {h i : ℕ} (hi : i ≤ h) :
    blockSize h i * 2 ^ i = 2 ^ h :=
  Nat.pow_sub_mul_pow 2 hi

/-- Retain the sampled leaf's node but choose the within-node offset from `u`. -/
def mix (b z u : ℕ) : ℕ := z / b * b + u % b

theorem mix_lt {b n z u : ℕ} (hb : 0 < b) (hz : z < n * b) :
    mix b z u < n * b := by
  have hq : z / b < n := (Nat.div_lt_iff_lt_mul hb).2 hz
  have hr : u % b < b := Nat.mod_lt u hb
  unfold mix
  nlinarith

theorem mix_div {b : ℕ} (hb : 0 < b) (z u : ℕ) :
    mix b z u / b = z / b := by
  unfold mix
  rw [Nat.mul_comm (z / b) b, Nat.mul_add_div hb]
  simp [Nat.div_eq_of_lt (Nat.mod_lt u hb)]

theorem mix_mod {b : ℕ} (hb : 0 < b) (z u : ℕ) :
    mix b z u % b = u % b := by
  calc
    mix b z u % b = (u % b) % b := by simp [mix, Nat.add_mod]
    _ = u % b := Nat.mod_eq_of_lt (Nat.mod_lt u hb)

def mixFin (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) : Fin (2 ^ h) :=
  ⟨mix (blockSize h i) z.val u.val, by
    have hm : 2 ^ h = 2 ^ i * blockSize h i := by
      rw [Nat.mul_comm, blockSize_mul_nodes hi]
    calc
      mix (blockSize h i) z.val u.val < 2 ^ i * blockSize h i :=
        mix_lt (blockSize_pos h i) (lt_of_lt_of_eq z.isLt hm)
      _ = 2 ^ h := hm.symm⟩

@[simp] theorem mixFin_node (h i : ℕ) (hi : i ≤ h) (z u : Fin (2 ^ h)) :
    (mixFin h i hi z u).val / blockSize h i = z.val / blockSize h i :=
  mix_div (blockSize_pos h i) z.val u.val

@[simp] theorem mixFin_root (h : ℕ) (z u : Fin (2 ^ h)) :
    mixFin h 0 (Nat.zero_le h) z u = u := by
  apply Fin.ext
  simp [mixFin, mix, blockSize, Nat.div_eq_of_lt z.isLt, Nat.mod_eq_of_lt u.isLt]

@[simp] theorem mixFin_leaf (h : ℕ) (z u : Fin (2 ^ h)) :
    mixFin h h le_rfl z u = z := by
  apply Fin.ext
  simp [mixFin, mix, blockSize, Nat.mod_one]

/-- The plus and minus names coincide precisely at the leaf level. -/
def classAt (h i : ℕ) (hi : i ≤ h) (plus : Bool) : Fin (2 * h + 1) :=
  ⟨if i = h then 2 * h else 2 * i + (!plus).toNat, by
    split_ifs with heq
    · omega
    · cases plus <;> simp <;> omega⟩

@[simp] theorem classAt_depth (h i : ℕ) (hi : i ≤ h) (plus : Bool) :
    (classAt h i hi plus).val / 2 = i := by
  unfold classAt
  split_ifs with heq
  · subst i
    change 2 * h / 2 = h
    omega
  · cases plus <;> simp; omega

@[simp] theorem classAt_leaf (h : ℕ) (plus : Bool) :
    (classAt h h le_rfl plus).val = 2 * h := by
  simp [classAt]

theorem classAt_internal (h i : ℕ) (hi : i < h) (plus : Bool) :
    (classAt h i hi.le plus).val = 2 * i + (!plus).toNat := by
  simp [classAt, Nat.ne_of_lt hi]

theorem classAt_leaf_iff (h i : ℕ) (hi : i ≤ h) (plus : Bool) :
    (classAt h i hi plus).val = 2 * h ↔ i = h := by
  constructor
  · intro heq
    have hd := classAt_depth h i hi plus
    rw [heq] at hd
    omega
  · rintro rfl
    simp

theorem classAt_signs_eq_iff (h i : ℕ) (hi : i ≤ h) :
    classAt h i hi true = classAt h i hi false ↔ i = h := by
  by_cases heq : i = h
  · subst i
    simp [classAt]
  · simp [classAt, heq, Fin.ext_iff]

def sample (h i : ℕ) (hi : i ≤ h) (plus : Bool)
    (z u : Fin (2 ^ h)) : VariablePosition h :=
  (classAt h i hi plus, mixFin h i hi z u)

def depth {h : ℕ} (p : VariablePosition h) : ℕ := p.1.val / 2

def node {h : ℕ} (p : VariablePosition h) : ℕ :=
  p.2.val / blockSize h (depth p)

@[simp] theorem sample_depth (h i : ℕ) (hi : i ≤ h) (plus : Bool)
    (z u : Fin (2 ^ h)) : depth (sample h i hi plus z u) = i :=
  classAt_depth h i hi plus

@[simp] theorem sample_node (h i : ℕ) (hi : i ≤ h) (plus : Bool)
    (z u : Fin (2 ^ h)) :
    node (sample h i hi plus z u) = z.val / blockSize h i := by
  unfold node
  rw [sample_depth]
  exact mixFin_node h i hi z u

theorem sample_node_lt (h i : ℕ) (hi : i ≤ h) (plus : Bool)
    (z u : Fin (2 ^ h)) : node (sample h i hi plus z u) < 2 ^ i := by
  rw [sample_node]
  apply (Nat.div_lt_iff_lt_mul (blockSize_pos h i)).2
  rw [Nat.mul_comm, blockSize_mul_nodes hi]
  exact z.isLt

/-- The two axes may use different offset seeds and still follow one common path. -/
theorem sample_nodes_eq (h i : ℕ) (hi : i ≤ h) (s t : Bool)
    (z u v : Fin (2 ^ h)) :
    node (sample h i hi s z u) = node (sample h i hi t z v) := by
  simp

theorem ancestor_parent (h i z : ℕ) (hi : i + 1 ≤ h) :
    z / blockSize h (i + 1) / 2 = z / blockSize h i := by
  have he : h - i = h - (i + 1) + 1 := by omega
  simp only [blockSize, Nat.div_div_eq_div_mul]
  rw [he, pow_succ]

theorem sample_parent (h i : ℕ) (hi : i + 1 ≤ h) (s t : Bool)
    (z u v : Fin (2 ^ h)) :
    node (sample h (i + 1) hi s z u) / 2 =
      node (sample h i (by omega) t z v) := by
  simp only [sample_node]
  exact ancestor_parent h i z.val hi

@[simp] theorem sample_shared_leaf (h : ℕ) (s t : Bool)
    (z u v : Fin (2 ^ h)) :
    sample h h le_rfl s z u = sample h h le_rfl t z v := by
  simp [sample, classAt]

@[simp] theorem sample_leaf_offset (h : ℕ) (s : Bool) (z u : Fin (2 ^ h)) :
    (sample h h le_rfl s z u).2 = z := by
  simp [sample]

@[simp] theorem sample_root_offset (h : ℕ) (s : Bool) (z u : Fin (2 ^ h)) :
    (sample h 0 (Nat.zero_le h) s z u).2 = u := by
  simp [sample]

@[simp] theorem sample_root_node (h : ℕ) (s : Bool) (z u : Fin (2 ^ h)) :
    node (sample h 0 (Nat.zero_le h) s z u) = 0 := by
  simp [blockSize, Nat.div_eq_of_lt z.isLt]

end Problem348.SampledPath

end OAI
