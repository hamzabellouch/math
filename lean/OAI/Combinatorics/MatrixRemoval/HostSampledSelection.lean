import OAI.Combinatorics.MatrixRemoval.HostAnchorFrames
import OAI.Combinatorics.MatrixRemoval.HostSampledPath
import OAI.Combinatorics.MatrixRemoval.HostRootLeaf
import OAI.Combinatorics.MatrixRemoval.GuardedPath
import OAI.Combinatorics.MatrixRemoval.SamplingDistance

namespace OAI

/-!
# The concrete common-leaf selection in the canonical host

The row/column enumerations are independent. `AxisConditions` records only the
order properties required of those enumerations; entries, role memberships,
root values, shared leaves, and the resulting guarded-path validity are proved
from the actual canonical host and the concrete sampled positions.
-/

noncomputable section
namespace Problem348.Construction.SampledSelection

open HostSampledPath

/-- The ten order facts used by the sampled-path construction.  These are
separate from matrix entries and can be supplied by any correct enumeration
of the two recursively ordered axes. -/
structure AxisConditions {h n : ℕ} (er ec : Position h ≃ Fin n) : Prop where
  anchor_rows : ∀ (t : Mode h) (a : Fin (2 ^ h)),
    StrictMono (fun u : Fin 64 => er (.inl (t, u, a)))
  anchor_cols : ∀ (t : Mode h) (a : Fin (2 ^ h)),
    StrictMono (fun u : Fin 64 => ec (.inl (t, u, a)))
  anchor_before_rows : ∀ (t : Mode h) (u : Fin 64) (a : Fin (2 ^ h))
    (x : VariablePosition h ⊕ Fin (2 ^ h)), er (.inl (t, u, a)) < er (.inr x)
  anchor_before_cols : ∀ (t : Mode h) (u : Fin 64) (a : Fin (2 ^ h))
    (x : VariablePosition h ⊕ Fin (2 ^ h)), ec (.inl (t, u, a)) < ec (.inr x)
  variable_before_dummy : ∀ (x : VariablePosition h) (a : Fin (2 ^ h)),
    er (.inr (.inl x)) < er (dummy h a)
  dummy_before_variable : ∀ (x : VariablePosition h) (a : Fin (2 ^ h)),
    ec (dummy h a) < ec (.inr (.inl x))
  row_plus : ∀ (i : Fin h) (z u : Fin (2 ^ h)),
    er (position h (i.val + 1) (by omega) true z u) <
      er (position h i.val (by omega) true z u)
  row_minus : ∀ (i : Fin h) (z u : Fin (2 ^ h)),
    er (position h i.val (by omega) false z u) <
      er (position h (i.val + 1) (by omega) false z u)
  col_plus : ∀ (i : Fin h) (z u : Fin (2 ^ h)),
    ec (position h i.val (by omega) true z u) <
      ec (position h (i.val + 1) (by omega) true z u)
  col_minus : ∀ (i : Fin h) (z u : Fin (2 ^ h)),
    ec (position h (i.val + 1) (by omega) false z u) <
      ec (position h i.val (by omega) false z u)

/-- A total path; indices beyond the tree depth repeat the common leaf. -/
def path (h i : ℕ) (s : Bool) (z u : Fin (2 ^ h)) : Position h :=
  position h (min i h) (Nat.min_le_right i h) s z u

@[simp] theorem path_of_le {h i : ℕ} (hi : i ≤ h) (s : Bool)
    (z u : Fin (2 ^ h)) : path h i s z u = position h i hi s z u := by
  simp [path, Nat.min_eq_left hi]

/-- A harmless total extension of the edge index; it equals `i` for `i<h`. -/
def edge {h : ℕ} (hh : 1 ≤ h) (i : ℕ) : Fin h :=
  ⟨i % h, Nat.mod_lt _ (by omega)⟩

@[simp] theorem edge_of_lt {h i : ℕ} (hh : 1 ≤ h) (hi : i < h) :
    edge hh i = (⟨i, hi⟩ : Fin h) := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt hi

/-- The anchor mode for one of the horizontal propagation steps. -/
def horizontalMode {h : ℕ} (hh : 1 ≤ h) (z : Fin (2 ^ h))
    (i : ℕ) (s : Bool) : Mode h :=
  horizontal (edge hh i) s
    (parity (z.val / SampledPath.blockSize h ((edge hh i).val + 1)))

/-- The selected anchor representatives use the same row/column seed in every
anchor group. This correlation does not affect the cellwise sampling proof. -/
def frame {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (t : Mode h) (u v : Fin (2 ^ h)) :
    GuardedPath.AnchorFrame n :=
  SelectedAnchor.frame er ec t (fun _ => u) (fun _ => v)
    (ha.anchor_rows t u) (ha.anchor_cols t v)

/-- The actual selected path and four anchor frames at each edge. -/
def selection {h n : ℕ} (hh : 1 ≤ h) (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (z u v : Fin (2 ^ h)) : GuardedPath.Selection n where
  xp i := er (path h i true z u)
  xm i := er (path h i false z u)
  yp i := ec (path h i true z v)
  ym i := ec (path h i false z v)
  xd := er (dummy h u)
  yd := ec (dummy h v)
  vPlus i := frame er ec ha (vertical (edge hh i) true) u v
  vMinus i := frame er ec ha (vertical (edge hh i) false) u v
  wPlus i := frame er ec ha (horizontalMode hh z i true) u v
  wMinus i := frame er ec ha (horizontalMode hh z i false) u v

/-- For named body roles, all anchor/signature data follow from the host;
only the two body order inequalities need to be supplied. -/
theorem frame_valid {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (t : Mode h) (u v : Fin (2 ^ h))
    (r₀ r₁ c₀ c₁ : Position h)
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hrs : er r₀ < er r₁) (hcs : ec c₀ < ec c₁) :
    (frame er ec ha t u v).Valid (SelectedAnchor.matrix er ec)
      (er r₀) (er r₁) (ec c₀) (ec c₁) := by
  apply SelectedAnchor.frame_valid er ec t (fun _ => u) (fun _ => v)
    (ha.anchor_rows t u) (ha.anchor_cols t v) r₀ r₁ c₀ c₁ hr₀ hr₁ hc₀ hc₁
  · intro j
    cases r₀ with
    | inl a => simp [rowRole] at hr₀
    | inr x => exact ha.anchor_before_rows t j u x
  · exact hrs
  · intro j
    cases c₀ with
    | inl a => simp [colRole] at hc₀
    | inr x => exact ha.anchor_before_cols t j v x
  · exact hcs

theorem vertical_plus_valid {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (i : Fin h) (z u v : Fin (2 ^ h)) :
    (frame er ec ha (vertical i true) u v).Valid (SelectedAnchor.matrix er ec)
      (er (position h (i.val + 1) (by omega) true z u))
      (er (position h i.val (by omega) true z u))
      (ec (dummy h v)) (ec (position h i.val (by omega) true z v)) := by
  apply frame_valid er ec ha
  · exact vertical_plus_row_first i z u
  · exact vertical_plus_row_second i z u
  · exact vertical_col_first i true v
  · exact vertical_col_second i true z v
  · exact ha.row_plus i z u
  · exact ha.dummy_before_variable _ v

theorem vertical_minus_valid {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (i : Fin h) (z u v : Fin (2 ^ h)) :
    (frame er ec ha (vertical i false) u v).Valid (SelectedAnchor.matrix er ec)
      (er (position h i.val (by omega) false z u))
      (er (position h (i.val + 1) (by omega) false z u))
      (ec (dummy h v)) (ec (position h i.val (by omega) false z v)) := by
  apply frame_valid er ec ha
  · exact vertical_minus_row_first i z u
  · exact vertical_minus_row_second i z u
  · exact vertical_col_first i false v
  · exact vertical_col_second i false z v
  · exact ha.row_minus i z u
  · exact ha.dummy_before_variable _ v

theorem horizontal_plus_valid {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (i : Fin h) (z u v : Fin (2 ^ h)) :
    (frame er ec ha
      (horizontal i true (parity (z.val / SampledPath.blockSize h (i.val + 1)))) u v).Valid
      (SelectedAnchor.matrix er ec)
      (er (position h (i.val + 1) (by omega) true z u)) (er (dummy h u))
      (ec (position h i.val (by omega) true z v))
      (ec (position h (i.val + 1) (by omega) true z v)) := by
  apply frame_valid er ec ha
  · exact horizontal_row_first i true z u
  · exact horizontal_row_second i true _ u
  · exact horizontal_plus_col_first i _ z v
  · exact horizontal_plus_col_second i z v
  · exact ha.variable_before_dummy _ u
  · exact ha.col_plus i z v

theorem horizontal_minus_valid {h n : ℕ} (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (i : Fin h) (z u v : Fin (2 ^ h)) :
    (frame er ec ha
      (horizontal i false (parity (z.val / SampledPath.blockSize h (i.val + 1)))) u v).Valid
      (SelectedAnchor.matrix er ec)
      (er (position h (i.val + 1) (by omega) false z u)) (er (dummy h u))
      (ec (position h (i.val + 1) (by omega) false z v))
      (ec (position h i.val (by omega) false z v)) := by
  apply frame_valid er ec ha
  · exact horizontal_row_first i false z u
  · exact horizontal_row_second i false _ u
  · exact horizontal_minus_col_first i z v
  · exact horizontal_minus_col_second i _ z v
  · exact ha.variable_before_dummy _ u
  · exact ha.col_minus i z v

/-- Every concrete three-seed selection satisfies all guarded-path hypotheses.
Only the axis order laws were assumed; the entire original-matrix certificate
is derived from the exact host entries and the sampled common-leaf path. -/
theorem selection_valid {h n : ℕ} (hh : 1 ≤ h) (er ec : Position h ≃ Fin n)
    (ha : AxisConditions er ec) (z u v : Fin (2 ^ h)) :
    (selection hh er ec ha z u v).Valid (SelectedAnchor.matrix er ec) h := by
  constructor
  · simp only [selection, SelectedAnchor.matrix_apply,
      path_of_le (Nat.zero_le h)]
    exact variableEntry_root_plus_of_atLevel hh _ _
      (sample_atLevel h 0 (Nat.zero_le h) true z u)
      (sample_atLevel h 0 (Nat.zero_le h) true z v)
  · simp only [selection, SelectedAnchor.matrix_apply,
      path_of_le (Nat.zero_le h)]
    exact variableEntry_root_minus_of_atLevel hh _ _
      (sample_atLevel h 0 (Nat.zero_le h) false z u)
      (sample_atLevel h 0 (Nat.zero_le h) false z v)
  · intro i hi
    simp [selection, SelectedAnchor.matrix_apply, path, position, dummy, host]
  · intro i hi
    simp [selection, SelectedAnchor.matrix_apply, path, position, dummy, host]
  · simp only [selection, path_of_le (Nat.le_refl h)]
    exact congrArg er (position_shared_leaf h true false z u u)
  · simp only [selection, path_of_le (Nat.le_refl h)]
    exact congrArg ec (position_shared_leaf h true false z v v)
  · intro i hi
    simpa only [selection, edge_of_lt hh hi, path_of_le hi.le,
      path_of_le (show i + 1 ≤ h by omega)] using
      vertical_plus_valid er ec ha ⟨i, hi⟩ z u v
  · intro i hi
    simpa only [selection, edge_of_lt hh hi, path_of_le hi.le,
      path_of_le (show i + 1 ≤ h by omega)] using
      vertical_minus_valid er ec ha ⟨i, hi⟩ z u v
  · intro i hi
    simpa only [selection, horizontalMode, edge_of_lt hh hi, path_of_le hi.le,
      path_of_le (show i + 1 ≤ h by omega)] using
      horizontal_plus_valid er ec ha ⟨i, hi⟩ z u v
  · intro i hi
    simpa only [selection, horizontalMode, edge_of_lt hh hi, path_of_le hi.le,
      path_of_le (show i + 1 ≤ h by omega)] using
      horizontal_minus_valid er ec ha ⟨i, hi⟩ z u v

end Problem348.Construction.SampledSelection

end

end OAI
