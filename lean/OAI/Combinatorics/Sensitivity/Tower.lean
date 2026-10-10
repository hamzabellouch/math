import OAI.Combinatorics.Sensitivity.Recursive

namespace OAI

/-! An indexed tower of the literal recursive construction and its common blocks. -/

noncomputable section
open scoped Classical

namespace Paper320

def TowerCoordinates (k r : ℕ) (I : Type) : ℕ → Type
  | 0 => I
  | n + 1 => (Fin k × Fin r) × TowerCoordinates k r I n

instance towerCoordinatesFintype (k r : ℕ) (I : Type) [Fintype I] :
    (n : ℕ) → Fintype (TowerCoordinates k r I n)
  | 0 => inferInstanceAs (Fintype I)
  | n + 1 => by
    letI := towerCoordinatesFintype k r I n
    exact inferInstanceAs (Fintype ((Fin k × Fin r) × TowerCoordinates k r I n))

def TowerBlockIndex (k : ℕ) (K : Type) : ℕ → Type
  | 0 => K
  | n + 1 => Fin k × TowerBlockIndex k K n

instance towerBlockIndexFintype (k : ℕ) (K : Type) [Fintype K] :
    (n : ℕ) → Fintype (TowerBlockIndex k K n)
  | 0 => inferInstanceAs (Fintype K)
  | n + 1 => by
    letI := towerBlockIndexFintype k K n
    exact inferInstanceAs (Fintype (Fin k × TowerBlockIndex k K n))

def towerFamily {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool) :
    (n h : ℕ) → Fin h → (TowerCoordinates k r I n → Bool) → Bool
  | 0, h => base h
  | n + 1, h => recursiveFamily T label (towerFamily T label base n (h + 1))

def towerBlocks {k r : ℕ} {I K : Type} (blocks : K → Finset I) :
    (n : ℕ) → TowerBlockIndex k K n → Finset (TowerCoordinates k r I n)
  | 0, b => blocks b
  | n + 1, b => rowLift b.1 (towerBlocks blocks n b.2)

/-- Extend a prescribed initial family to unused index counts without adding assumptions. -/
def baseExtension {I : Type} (D : ℕ) (F : Fin D → (I → Bool) → Bool)
    (h : ℕ) (q : Fin h) (x : I → Bool) : Bool :=
  if he : h = D then F (Fin.cast he q) x else false

@[simp] theorem baseExtension_same {I : Type} (D : ℕ) (F : Fin D → (I → Bool) → Bool) :
    baseExtension D F D = F := by
  funext q x
  simp [baseExtension]

theorem tower_coordinates_card {k r : ℕ} {I : Type} [Fintype I] (n : ℕ) :
    Fintype.card (TowerCoordinates k r I n) = (k * r) ^ n * Fintype.card I := by
  induction n with
  | zero =>
    change Fintype.card I = (k * r) ^ 0 * Fintype.card I
    simp
  | succ n ih =>
    change Fintype.card ((Fin k × Fin r) × TowerCoordinates k r I n) = _
    simp only [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
    ring

theorem tower_block_index_card {k : ℕ} {K : Type} [Fintype K] (n : ℕ) :
    Fintype.card (TowerBlockIndex k K n) = k ^ n * Fintype.card K := by
  induction n with
  | zero =>
    change Fintype.card K = k ^ 0 * Fintype.card K
    simp
  | succ n ih =>
    change Fintype.card (Fin k × TowerBlockIndex k K n) = _
    simp only [Fintype.card_prod, Fintype.card_fin, ih, pow_succ]
    ring

theorem towerBlocks_card {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (L : ℕ) (hL : ∀ b, (blocks b).card = L) (n : ℕ) (b : TowerBlockIndex k K n) :
    (towerBlocks (r := r) blocks n b).card = r ^ n * L := by
  induction n with
  | zero =>
    change (blocks b).card = r ^ 0 * L
    simpa only [pow_zero, one_mul] using hL b
  | succ n ih =>
    change (rowLift b.1 (towerBlocks blocks n b.2)).card = _
    rw [rowLift_card, ih]
    ring

theorem towerBlocks_nonempty {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hr : 0 < r) (hne : ∀ b, (blocks b).Nonempty) (n : ℕ) (b : TowerBlockIndex k K n) :
    (towerBlocks (r := r) blocks n b).Nonempty := by
  induction n with
  | zero => exact hne b
  | succ n ih => exact rowLift_nonempty b.1 _ hr (ih b.2)

theorem towerBlocks_pairwise {k r : ℕ} {I K : Type} (blocks : K → Finset I)
    (hd : Pairwise fun a b => Disjoint (blocks a) (blocks b)) (n : ℕ) :
    Pairwise fun a b => Disjoint (towerBlocks (k := k) (r := r) blocks n a) (towerBlocks blocks n b) := by
  induction n with
  | zero => exact hd
  | succ n ih => exact rowLift_family_disjoint (towerBlocks blocks n) ih

theorem towerFamily_nested {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (n h : ℕ) (hbase : NestedFamily (base (h + n))) :
    NestedFamily (towerFamily T label base n h) := by
  induction n generalizing h with
  | zero =>
    change NestedFamily (base h)
    simpa only [Nat.add_zero] using hbase
  | succ n ih =>
    apply recursiveFamily_nested
    apply ih
    have he : (h + 1) + n = h + (n + 1) := by omega
    rw [he]
    exact hbase

theorem towerFamily_zero {k r : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (hr : 0 < r) (n h : ℕ) (hbase : ∀ q, base (h + n) q (fun _ => false) = false) :
    ∀ q, towerFamily T label base n h q (fun _ => false) = false := by
  induction n generalizing h with
  | zero =>
    change ∀ q, base h q (fun _ => false) = false
    simpa only [Nat.add_zero] using hbase
  | succ n ih =>
    apply recursiveFamily_zero T label _ hr
    apply ih
    have he : (h + 1) + n = h + (n + 1) := by omega
    rw [he]
    exact hbase

theorem towerFamily_blocks {k r : ℕ} {I K : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (base : (h : ℕ) → Fin h → (I → Bool) → Bool)
    (blocks : K → Finset I) (hr : 0 < r) (n h : ℕ)
    (hzero : ∀ q, base (h + n) q (fun _ => false) = false)
    (hblocks : ∀ b q, base (h + n) q (flip (fun _ => false) (blocks b)) = true) :
    ∀ b q, towerFamily T label base n h q
      (flip (fun _ => false) (towerBlocks blocks n b)) = true := by
  induction n generalizing h with
  | zero =>
    change ∀ b q, base h q (flip (fun _ => false) (blocks b)) = true
    simpa only [Nat.add_zero] using hblocks
  | succ n ih =>
    intro b q
    have he : (h + 1) + n = h + (n + 1) := by omega
    have hz : ∀ q, base ((h + 1) + n) q (fun _ => false) = false := by
      rw [he]
      exact hzero
    have hb : ∀ b q, base ((h + 1) + n) q (flip (fun _ => false) (blocks b)) = true := by
      rw [he]
      exact hblocks
    exact recursiveFamily_rowLift T label _
      (towerFamily_zero T label base hr n (h + 1) hz)
      (towerBlocks blocks n b.2) (ih (h + 1) hz hb b.2) b.1 q

end Paper320

end

end OAI
