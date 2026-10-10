import OAI.Combinatorics.ContingencyTables.Dense.GridMeasure
import OAI.Combinatorics.ContingencyTables.Transport.BoxGeometry
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Pi

namespace OAI

/-!
# Finite cut-face cover of the interpolation shell

The continuous shell in the conductance argument is covered, except for
the null grid hyperplanes, by the finite collection of interior cut-face
tubes. No exterior faces or segment general-position hypotheses occur.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory

variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Grid (K : ℕ) := I → Set.Icc (0 : ℤ) ((K : ℤ) - 1)

def corner {K : ℕ} (a : Grid (I := I) K) : I → ℤ := fun j => (a j).val

def mixGrid {K : ℕ} (a b : Grid (I := I) K) (S : Finset I) : Grid (I := I) K :=
  fun j => if j ∈ S then b j else a j

omit [Fintype I] in
private theorem corner_mix {K : ℕ} (a b : Grid (I := I) K) (S : Finset I) :
    corner (mixGrid a b S) = mixed (corner a) (corner b) S := by
  ext j
  by_cases hj : j ∈ S <;> simp [corner, mixGrid, mixed, hj]

def Cube (K : ℕ) (x : I → ℝ) : Prop := ∀ j, 0 < x j ∧ x j < (K : ℝ)

def selectedBins (K : ℕ) (P : (I → ℤ) → Prop) : Set (I → ℝ) :=
  {x | ∃ a : Grid K, P (corner a) ∧ OpenBin (corner a) x}

def IsGridEdge {K : ℕ} (p : Grid (I := I) K × Grid (I := I) K × I) : Prop :=
  corner p.2.1 p.2.2 = corner p.1 p.2.2 + 1 ∧
    ∀ j, j ≠ p.2.2 → p.2.1 j = p.1 j

abbrev CutEdge (K : ℕ) (P : (I → ℤ) → Prop) :=
  {p : Grid (I := I) K × Grid (I := I) K × I //
    IsGridEdge p ∧ (P (corner p.1) ↔ ¬ P (corner p.2.1))}

noncomputable instance (K : ℕ) (P : (I → ℤ) → Prop) : Fintype (CutEdge K P) :=
  Fintype.ofFinite _

def edgeTube {K : ℕ} {P : (I → ℤ) → Prop} (e : CutEdge K P) (r : ℝ) : Set (I → ℝ) :=
  faceTube (corner e.val.1) e.val.2.2 r

omit [Fintype I] [DecidableEq I] in
theorem openBin_in_cube {K : ℕ} (a : Grid (I := I) K) (x : I → ℝ)
    (hx : OpenBin (corner a) x) : Cube K x := by
  intro j
  have hl : (0 : ℝ) ≤ (corner a j : ℝ) := by exact_mod_cast (a j).property.1
  have hu : (corner a j : ℝ) ≤ (K : ℝ) - 1 := by exact_mod_cast (a j).property.2
  exact ⟨by linarith [(hx j).1], by linarith [(hx j).2]⟩

theorem near_finite_cut_tube {K : ℕ} (P : (I → ℤ) → Prop)
    (a b : Grid (I := I) K) (x z : I → ℝ) (r : ℝ)
    (ha : OpenBin (corner a) x) (hb : OpenBin (corner b) z)
    (hd : ∀ j, |z j - x j| < r) (hr : r ≤ 1)
    (hPa : P (corner a)) (hPb : ¬ P (corner b)) :
    ∃ e : CutEdge K P, z ∈ edgeTube e r := by
  classical
  obtain ⟨S, i, w, hi, hS, hSi, hadj, hw, hw', hdw⟩ :=
    near_cut_face P (corner a) (corner b) x z r ha hb hd hr hPa hPb
  let u := mixGrid a b S
  let v := mixGrid a b (insert i S)
  have hui : corner u i = corner a i := by simp [u, corner, mixGrid, hi]
  have hvi : corner v i = corner b i := by simp [v, corner, mixGrid]
  have hsame (j : I) (hj : j ≠ i) : v j = u j := by simp [v, u, mixGrid, hj]
  have hPu : P (corner u) := by simpa [u, corner_mix] using hS
  have hPv : ¬ P (corner v) := by simpa [v, corner_mix] using hSi
  have hwu : ClosedBin (corner u) w := by simpa [u, corner_mix] using hw
  have hwv : ClosedBin (corner v) w := by simpa [v, corner_mix] using hw'
  rcases hadj with hab | hab
  · have he : corner v i = corner u i + 1 := by rw [hui, hvi]; exact hab
    let e : CutEdge K P := ⟨(u, v, i), ⟨he, hsame⟩, by simp [hPu, hPv]⟩
    refine ⟨e, mem_faceTube_of_near (corner u) i r z w hwu ?_ hdw⟩
    have he' : (corner v i : ℝ) = (corner u i : ℝ) + 1 := by exact_mod_cast he
    exact le_antisymm (hwu i).2 (by linarith [(hwv i).1])
  · have he : corner u i = corner v i + 1 := by rw [hui, hvi]; exact hab
    let e : CutEdge K P := ⟨(v, u, i), ⟨he, fun j hj => (hsame j hj).symm⟩,
      by simp [hPu, hPv]⟩
    refine ⟨e, mem_faceTube_of_near (corner v) i r z w hwv ?_ hdw⟩
    have he' : (corner u i : ℝ) = (corner v i : ℝ) + 1 := by exact_mod_cast he
    exact le_antisymm (hwv i).2 (by linarith [(hwu i).1])

omit [Fintype I] [DecidableEq I] in
private theorem floor_grid {K : ℕ} (z : I → ℝ) (hz : Cube K z) :
    ∃ b : Grid (I := I) K, ∀ j, corner b j = ⌊z j⌋ := by
  have h (j : I) : ⌊z j⌋ ∈ Set.Icc (0 : ℤ) ((K : ℤ) - 1) := by
    refine ⟨Int.floor_nonneg.mpr (hz j).1.le, ?_⟩
    have hlt : ⌊z j⌋ < (K : ℤ) := Int.floor_lt.mpr (by simpa using (hz j).2)
    omega
  exact ⟨fun j => ⟨⌊z j⌋, h j⟩, fun _ => rfl⟩

omit [Fintype I] [DecidableEq I] in
private theorem interpolation_short {K : ℕ} (x y : I → ℝ) (t : ℝ)
    (hx : Cube K x) (hy : Cube K y) (ht : 0 < t) (ht₁ : t < 1) :
    Cube K (fun j => (1 - t) * x j + t * y j) ∧
      ∀ j, |((1 - t) * x j + t * y j) - x j| < t * K := by
  constructor
  · intro j
    have hxt := mul_pos (sub_pos.mpr ht₁) (hx j).1
    have hyt := mul_pos ht (hy j).1
    have hxu := mul_lt_mul_of_pos_left (hx j).2 (sub_pos.mpr ht₁)
    have hyu := mul_lt_mul_of_pos_left (hy j).2 ht
    constructor <;> nlinarith
  · intro j
    have hdiff : |y j - x j| < (K : ℝ) := by
      apply abs_lt.mpr
      constructor <;> linarith [(hx j).1, (hx j).2, (hy j).1, (hy j).2]
    have heq : (1 - t) * x j + t * y j - x j = t * (y j - x j) := by ring
    rw [heq, abs_mul, abs_of_pos ht]
    exact mul_lt_mul_of_pos_left hdiff ht

/-- Every shell point off the grid hyperplanes belongs to an interior
cut-face tube. This is the actual cover used by the manuscript. -/
theorem interpolation_shell_cover {q K : ℕ} (P : (Fin q → ℤ) → Prop)
    (t : ℝ) (ht : 0 < t) (ht₁ : t < 1) (hr : t * K ≤ 1)
    (z : Fin q → ℝ)
    (hz : z ∈ PublishedInputs.interpolate t (selectedBins K P) {y | Cube K y} \
      selectedBins K P)
    (hoff : ∀ j (k : ℤ), z j ≠ (k : ℝ)) :
    ∃ e : CutEdge K P, z ∈ edgeTube e (t * K) := by
  obtain ⟨⟨x, ⟨a, hPa, hax⟩, y, hy, rfl⟩, hnot⟩ := hz
  have hx := openBin_in_cube a x hax
  obtain ⟨hzCube, hd⟩ := interpolation_short x y t hx hy ht ht₁
  obtain ⟨b, hb⟩ := floor_grid _ hzCube
  have hzb : OpenBin (corner b) (fun j => (1 - t) * x j + t * y j) := by
    intro j
    rw [hb j]
    refine ⟨?_, Int.lt_floor_add_one _⟩
    exact lt_of_le_of_ne (Int.floor_le _) (Ne.symm (hoff j _))
  have hPb : ¬ P (corner b) := by
    intro hPb
    exact hnot ⟨b, hPb, hzb⟩
  exact near_finite_cut_tube P a b x _ (t * K) hax hzb hd hr hPa hPb

omit [DecidableEq I] in
/-- The only excluded points lie on countably many null hyperplanes. -/
theorem ae_off_grid : ∀ᵐ z : I → ℝ ∂volume, ∀ j (k : ℤ), z j ≠ (k : ℝ) := by
  apply ae_all_iff.mpr
  intro j
  apply ae_all_iff.mpr
  intro k
  simpa only [MeasureTheory.volume_pi] using
    (MeasureTheory.Measure.ae_eval_ne (fun _ : I => (volume : Measure ℝ)) j (k : ℝ))

theorem interpolation_shell_cover_ae {q K : ℕ} (P : (Fin q → ℤ) → Prop)
    (t : ℝ) (ht : 0 < t) (ht₁ : t < 1) (hr : t * K ≤ 1) :
    ∀ᵐ z ∂volume, z ∈ PublishedInputs.interpolate t (selectedBins K P) {y | Cube K y} \
      selectedBins K P → ∃ e : CutEdge K P, z ∈ edgeTube e (t * K) := by
  filter_upwards [ae_off_grid (I := Fin q)] with z hz
  exact fun h => interpolation_shell_cover P t ht ht₁ hr z h hz

end ContingencyTables.GridBoundary

end OAI
