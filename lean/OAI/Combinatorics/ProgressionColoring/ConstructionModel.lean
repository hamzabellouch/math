import OAI.Combinatorics.ProgressionColoring.ConstructionArithmetic
import OAI.Combinatorics.ProgressionColoring.ScalarAdaptiveMesh
import OAI.Combinatorics.ProgressionColoring.LiteralLabelRectangles
import Mathlib.Data.Fintype.BigOperators

namespace OAI

noncomputable section

namespace QuantitativeVanDerWaerden.ConstructionModel

open Parameters

variable {k : ℕ}

/-- The number of first-system intervals: exactly `1 / Hx`. -/
def uniformCount (k : ℕ) : ℕ := k ^ 2 * lambda k

theorem uniformCount_pos (hk : 3 ≤ k) : 0 < uniformCount k :=
  Nat.mul_pos (pow_pos (by omega : 0 < k) _) (lambda_pos k)

/-- The actual exponential second-system mesh, using the selected base. -/
def mesh (s : Data k) (hk : 3 ≤ k) : AdaptiveMesh :=
  selectedAdaptiveMesh hk s.two_le

@[simp] theorem mesh_H (s : Data k) (hk : 3 ≤ k) :
    (mesh s hk).H = meshScale k := rfl

@[simp] theorem mesh_alpha (s : Data k) (hk : 3 ≤ k) :
    (mesh s hk).alpha = 1 / (s.q : ℝ) ^ (dimension k + 1) := rfl

@[simp] theorem mesh_R (s : Data k) (hk : 3 ≤ k) :
    (mesh s hk).R = scalarRadius k s.q := rfl

@[simp] theorem mesh_m (s : Data k) (hk : 3 ≤ k) :
    (mesh s hk).m = scalarMeshSize k s.q :=
  selectedAdaptiveMesh_m hk s.two_le

theorem mesh_small (s : Data k) (hk : 3 ≤ k) :
    2 * (k : ℝ) * (mesh s hk).H < 1 := affine_box_small hk

abbrev Label (s : Data k) (hk : 3 ≤ k) :=
  (Fin (dimension k) → Fin (uniformCount k)) ×
    (Fin (dimension k) → (mesh s hk).Label)

/-- Actual full labels of actual cyclic points. This specializes the generic
literal-label definition also used in the heavy-label return proof. -/
def fullLabel (s : Data k) (hk : 3 ≤ k) (n : Group s) : Label s hk :=
  literalFullLabel (mesh s hk) s.q (dimension k) (lambda k)
    (uniformCount k) (uniformCount_pos hk) n

def firstLabel (s : Data k) (hk : 3 ≤ k) (n : Group s) :
    Fin (dimension k) → Fin (uniformCount k) := (fullLabel s hk n).1

def secondLabel (s : Data k) (hk : 3 ≤ k) (n : Group s) :
    Fin (dimension k) → (mesh s hk).Label := (fullLabel s hk n).2

@[simp] theorem firstLabel_apply (s : Data k) (hk : 3 ≤ k)
    (n : Group s) (i : Fin (dimension k)) :
    firstLabel s hk n i = UniformMesh.label (uniformCount k)
      (uniformCount_pos hk) (xRep s.q (dimension k) n i) := rfl

@[simp] theorem secondLabel_apply (s : Data k) (hk : 3 ≤ k)
    (n : Group s) (i : Fin (dimension k)) :
    secondLabel s hk n i =
      (mesh s hk).meshLabel (yRep s.q (dimension k) (lambda k) n i) := rfl

theorem fullLabel_eq_pair (s : Data k) (hk : 3 ≤ k) (n : Group s) :
    fullLabel s hk n = (firstLabel s hk n, secondLabel s hk n) := rfl

theorem firstLabel_contains (s : Data k) (hk : 3 ≤ k)
    (n : Group s) (i : Fin (dimension k)) :
    UniformMesh.Contains (uniformCount k) (firstLabel s hk n i)
      (xRep s.q (dimension k) n i) :=
  literalFullLabel_first_mem (mesh s hk) s.q (dimension k) (lambda k)
    (uniformCount k) (uniformCount_pos hk) n i

theorem secondLabel_contains (s : Data k) (hk : 3 ≤ k)
    (n : Group s) (i : Fin (dimension k)) :
    (mesh s hk).Contains (secondLabel s hk n i)
      (yRep s.q (dimension k) (lambda k) n i) :=
  literalFullLabel_second_mem (mesh s hk) s.q (dimension k) (lambda k)
    (uniformCount k) (uniformCount_pos hk) n i

/-- Full-label equality means exactly membership in all the specified
half-open coordinate intervals, including their boundary conventions. -/
theorem fullLabel_eq_iff (s : Data k) (hk : 3 ≤ k)
    (n : Group s) (label : Label s hk) :
    fullLabel s hk n = label ↔
      (∀ i, UniformMesh.Contains (uniformCount k) (label.1 i)
        (xRep s.q (dimension k) n i)) ∧
      (∀ i, (mesh s hk).Contains (label.2 i)
        (yRep s.q (dimension k) (lambda k) n i)) :=
  literalFullLabel_eq_iff (mesh s hk) s.q (dimension k) (lambda k)
    (uniformCount k) (uniformCount_pos hk) n label

theorem uniformWidth_eq :
    1 / (uniformCount k : ℝ) = meshScale k / (lambda k : ℝ) := by
  simp only [uniformCount, Nat.cast_mul, Nat.cast_pow, meshScale, div_div]

theorem first_width (i : Fin (uniformCount k)) :
    UniformMesh.right (uniformCount k) i - UniformMesh.left (uniformCount k) i =
      meshScale k / (lambda k : ℝ) := by
  rw [UniformMesh.width_eq, uniformWidth_eq]

theorem fullLabel_same_first_distance (s : Data k) (hk : 3 ≤ k)
    {a b : Group s} (h : fullLabel s hk a = fullLabel s hk b)
    (i : Fin (dimension k)) :
    |xRep s.q (dimension k) a i - xRep s.q (dimension k) b i| ≤
      meshScale k / (lambda k : ℝ) := by
  rw [← uniformWidth_eq]
  exact literalFullLabel_same_first_distance (mesh s hk) s.q (dimension k)
    (lambda k) (uniformCount k) (uniformCount_pos hk) h i

theorem fullLabel_same_second_distance (s : Data k) (hk : 3 ≤ k)
    {a b : Group s} (h : fullLabel s hk a = fullLabel s hk b)
    (i : Fin (dimension k)) :
    |yRep s.q (dimension k) (lambda k) a i -
      yRep s.q (dimension k) (lambda k) b i| ≤ 2 * meshScale k :=
  literalFullLabel_same_second_distance (mesh s hk) s.q (dimension k)
    (lambda k) (uniformCount k) (uniformCount_pos hk) h i

@[simp] theorem card_first_labels : Fintype.card (Fin (uniformCount k)) = uniformCount k :=
  Fintype.card_fin _

@[simp] theorem card_second_labels (s : Data k) (hk : 3 ≤ k) :
    Fintype.card (mesh s hk).Label = 2 * scalarMeshSize k s.q :=
  selectedAdaptiveMesh_card hk s.two_le

theorem card_labels (s : Data k) (hk : 3 ≤ k) :
    Fintype.card (Label s hk) =
      (uniformCount k) ^ dimension k * (2 * scalarMeshSize k s.q) ^ dimension k := by
  simp only [Label, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, mesh_m]

theorem card_second_labels_le (s : Data k) (hk : 3 ≤ k) :
    (Fintype.card (mesh s hk).Label : ℝ) ≤ 28 * (k : ℝ) ^ 3 * Real.log k :=
  selectedAdaptiveMesh_card_le hk s.two_le (one_le_log_length hk)
    (s.log_upper (by omega) (by have := dimension_pos (show 1 ≤ k by omega); omega))

/-- The actual label word of an ordered cyclic progression. No nonzero-step
condition is needed to define the word; event families impose it separately. -/
def fullLabelWord (s : Data k) (hk : 3 ≤ k) (ad : Group s × Group s) :
    Fin k → Label s hk :=
  fun j => fullLabel s hk (ad.1 + (j.val : Group s) * ad.2)

end QuantitativeVanDerWaerden.ConstructionModel

end

end OAI
