import OAI.Combinatorics.ContingencyTables.Dense.GridCover

namespace OAI

/-!
# Continuous mass and weighted grid cuts

Unit bins have disjoint interiors and exact volume one. Their continuous
mass is compared with the discrete weights, and the finite shell cover
converts interpolation gain into a weighted cut-face sum.
-/

namespace ContingencyTables.GridBoundary

open MeasureTheory
open scoped BigOperators

variable {q K : ℕ}

def binSet (a : Grid (I := Fin q) K) : Set (Fin q → ℝ) :=
  {x | OpenBin (corner a) x}

def ambientBox (q K : ℕ) : Set (Fin q → ℝ) :=
  Set.Icc (fun _ => 0) (fun _ => (K : ℝ))

abbrev Selected (K : ℕ) (P : (Fin q → ℤ) → Prop) :=
  {a : Grid (I := Fin q) K // P (corner a)}

noncomputable instance (P : (Fin q → ℤ) → Prop) : Fintype (Selected K P) :=
  Fintype.ofFinite _

private theorem binSet_pi (a : Grid (I := Fin q) K) :
    binSet a = Set.pi Set.univ (fun j => Set.Ioo (corner a j : ℝ) ((corner a j : ℝ) + 1)) := by
  ext x
  simp [binSet, OpenBin]

theorem binSet_measurable (a : Grid (I := Fin q) K) : MeasurableSet (binSet a) := by
  rw [binSet_pi]
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioo

theorem binSet_volume (a : Grid (I := Fin q) K) : volume (binSet a) = 1 := by
  rw [binSet_pi, Real.volume_pi_Ioo]
  simp

theorem binSet_disjoint (a b : Grid (I := Fin q) K) (hab : a ≠ b) :
    Disjoint (binSet a) (binSet b) := by
  apply Set.disjoint_left.mpr
  intro x hax hbx
  apply hab
  funext j
  apply Subtype.ext
  have ha : ⌊x j⌋ = corner a j := Int.floor_eq_iff.mpr ⟨(hax j).1.le, (hax j).2⟩
  have hb : ⌊x j⌋ = corner b j := Int.floor_eq_iff.mpr ⟨(hbx j).1.le, (hbx j).2⟩
  exact ha.symm.trans hb

theorem binSet_subset_ambient (a : Grid (I := Fin q) K) : binSet a ⊆ ambientBox q K := by
  intro x hx
  have h := openBin_in_cube a x hx
  exact ⟨fun j => (h j).1.le, fun j => (h j).2.le⟩

theorem selectedBins_finiteBox (P : (Fin q → ℤ) → Prop) :
    PublishedInputs.IsFiniteBoxUnion (selectedBins K P) := by
  classical
  let e := (Fintype.equivFin (Selected K P)).symm
  refine ⟨Fintype.card (Selected K P), (fun k j => (corner (e k).val j : ℝ)),
    (fun k j => (corner (e k).val j : ℝ) + 1), ?_⟩
  ext x
  constructor
  · rintro ⟨a, ha, hx⟩
    exact ⟨e.symm ⟨a, ha⟩, by simpa [OpenBin] using hx⟩
  · rintro ⟨k, hk⟩
    exact ⟨(e k).val, (e k).property, hk⟩

theorem cube_finiteBox : PublishedInputs.IsFiniteBoxUnion {x : Fin q → ℝ | Cube K x} := by
  refine ⟨1, (fun _ _ => 0), (fun _ _ => (K : ℝ)), ?_⟩
  ext x
  simp [Cube]

theorem selectedBins_closure (P : (Fin q → ℤ) → Prop) :
    closure (selectedBins K P) ⊆ ambientBox q K := by
  apply isClosed_Icc.closure_subset_iff.mpr
  rintro x ⟨a, _, hx⟩
  exact binSet_subset_ambient a hx

theorem cube_closure : closure {x : Fin q → ℝ | Cube K x} ⊆ ambientBox q K := by
  apply isClosed_Icc.closure_subset_iff.mpr
  intro x hx
  exact ⟨fun j => (hx j).1.le, fun j => (hx j).2.le⟩

theorem selectedBins_integral (P : (Fin q → ℤ) → Prop) (ρ : (Fin q → ℝ) → ℝ)
    (hi : IntegrableOn ρ (ambientBox q K)) :
    (∫ x in selectedBins K P, ρ x) = ∑ a : Selected K P, ∫ x in binSet a.val, ρ x := by
  have heq : selectedBins K P = ⋃ a : Selected K P, binSet a.val := by
    ext x
    simp only [selectedBins, binSet, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨a, ha, hx⟩
      exact ⟨⟨a, ha⟩, hx⟩
    · rintro ⟨a, hx⟩
      exact ⟨a.val, a.property, hx⟩
  rw [heq]
  apply integral_iUnion_fintype
  · exact fun a => binSet_measurable a.val
  · intro a b hab
    exact binSet_disjoint a.val b.val (fun h => hab (Subtype.ext h))
  · exact fun a => hi.mono_set (binSet_subset_ambient a.val)

/-- The selected side has at least one quarter of its own discrete mass;
it need not be the smaller side for the discrete weights. -/
theorem selectedBins_mass_lower (P : (Fin q → ℤ) → Prop) (ρ : (Fin q → ℝ) → ℝ)
    (w : Grid (I := Fin q) K → ℝ) (hi : IntegrableOn ρ (ambientBox q K))
    (hbin : ∀ a x, x ∈ binSet a → w a / 4 ≤ ρ x) :
    (∑ a : Selected K P, w a.val) / 4 ≤ ∫ x in selectedBins K P, ρ x := by
  rw [selectedBins_integral P ρ hi, Finset.sum_div]
  apply Finset.sum_le_sum
  intro a _
  have h := setIntegral_ge_of_const_le_real (binSet_measurable a.val)
    (show volume (binSet a.val) ≠ ⊤ by rw [binSet_volume]; simp)
    (hbin a.val) (hi.mono_set (binSet_subset_ambient a.val))
  simpa [Measure.real, binSet_volume] using h

theorem edgeTube_mass_upper (P : (Fin q → ℤ) → Prop) (e : CutEdge K P)
    (r : ℝ) (hr : 0 ≤ r) (hr₁ : r ≤ 1 / 4)
    (hsize : (q - 1 : ℕ) * (2 * r) ≤ (1 / 2 : ℝ))
    (ρ : (Fin q → ℝ) → ℝ) (w : Grid (I := Fin q) K → ℝ)
    (hw : ∀ a, 0 ≤ w a) (hi : IntegrableOn ρ (ambientBox q K))
    (hbound : ∀ x, x ∈ edgeTube e r ∩ {x | Cube K x} →
      ρ x ≤ 4 * min (w e.val.1) (w e.val.2.1)) :
    (∫ x in edgeTube e r ∩ {x | Cube K x}, ρ x) ≤
      4 * min (w e.val.1) (w e.val.2.1) := by
  let E := edgeTube e r ∩ {x | Cube K x}
  have hE : MeasurableSet E := (faceTube_measurable _ _ _).inter
    (cube_finiteBox (q := q) (K := K)).isOpen.measurableSet
  have hsub : E ⊆ ambientBox q K := fun x hx =>
    ⟨fun j => (hx.2 j).1.le, fun j => (hx.2 j).2.le⟩
  have hfin : volume (edgeTube e r) ≠ ⊤ := by
    rw [edgeTube, faceTube_volume _ _ _ hr]
    exact ENNReal.ofReal_ne_top
  have hfinE : volume E ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hvol : (volume E).toReal ≤ 1 := by
    calc
      _ ≤ (volume (edgeTube e r)).toReal := ENNReal.toReal_mono hfin
        (measure_mono Set.inter_subset_left)
      _ ≤ 1 := by
        exact faceTube_volume_le_one (corner e.val.1) e.val.2.2 r hr hr₁ (by simpa using hsize)
  have hb := setIntegral_mono_on (hi.mono_set hsub)
    (integrableOn_const hfinE) hE hbound
  rw [setIntegral_const, smul_eq_mul] at hb
  have hw' : 0 ≤ 4 * min (w e.val.1) (w e.val.2.1) :=
    mul_nonneg (by norm_num) (le_min (hw _) (hw _))
  exact hb.trans (by simpa [Measure.real] using mul_le_mul_of_nonneg_right hvol hw')

end ContingencyTables.GridBoundary

end OAI
