import OAI.Analysis.LipschitzHilbert.Trees.SourceWhitneyIntervals
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-! Glue stripwise estimates over the actual countable Whitney partition.
Finite-subfamily bounds imply integrability and the same global bound. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert.SourceWhitney
open DyadicLineGrid
variable {ι : Type*} (tiles : Finset ι) (x ell : ι → ℝ)

abbrev CellIndex := {p : ℤ×ℤ // Whitney tiles x ell p.1 p.2}

variable (hne : tiles.Nonempty) (hpos : ∀ i∈tiles, 0<ell i)

include hne hpos in
theorem exists_cellIndex (z : ℝ) :
    ∃ i : CellIndex tiles x ell, z∈cell 0 i.val.1 i.val.2 := by
  obtain ⟨k,j,hj,hz⟩ := exists_whitney_cover tiles x ell hne hpos z
  exact ⟨⟨(k,j),hj⟩,hz⟩

/-- The unique maximal allowed dyadic cell containing a given point. -/
def indexAt (z : ℝ) : CellIndex tiles x ell :=
  Classical.choose (exists_cellIndex tiles x ell hne hpos z)

theorem indexAt_mem (z : ℝ) :
    z∈cell 0 (indexAt tiles x ell hne hpos z).val.1 (indexAt tiles x ell hne hpos z).val.2 :=
  Classical.choose_spec (exists_cellIndex tiles x ell hne hpos z)

theorem indexAt_eq_of_mem (i : CellIndex tiles x ell) {z : ℝ}
    (hz : z∈cell 0 i.val.1 i.val.2) : indexAt tiles x ell hne hpos z=i := by
  apply Subtype.ext
  by_contra hne'
  exact Set.disjoint_left.mp
    (whitney_disjoint tiles x ell (indexAt tiles x ell hne hpos z).property i.property hne')
    (indexAt_mem tiles x ell hne hpos z) hz

def strip (E : Set (ℝ×ℝ)) (i : CellIndex tiles x ell) : Set (ℝ×ℝ) :=
  E∩Prod.fst ⁻¹' cell 0 i.val.1 i.val.2

theorem strip_measurable {E : Set (ℝ×ℝ)} (hE : MeasurableSet E) (i : CellIndex tiles x ell) :
    MeasurableSet (strip tiles x ell E i) :=
  hE.inter ((cell_measurable 0 i.val.1 i.val.2).preimage measurable_fst)

theorem strip_disjoint (E : Set (ℝ×ℝ)) :
    Pairwise (fun i j : CellIndex tiles x ell => Disjoint (strip tiles x ell E i) (strip tiles x ell E j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  have hne' : i.val≠j.val := fun h => hij (Subtype.ext h)
  exact Set.disjoint_left.mp (whitney_disjoint tiles x ell i.property j.property hne') hzi.2 hzj.2

include hne hpos in
theorem strip_iUnion (E : Set (ℝ×ℝ)) : ⋃ i : CellIndex tiles x ell, strip tiles x ell E i = E := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact hi.1
  · intro z hz
    exact mem_iUnion.mpr ⟨indexAt tiles x ell hne hpos z.1,hz,indexAt_mem tiles x ell hne hpos z.1⟩

variable {V : Type*}

/-- Evaluate the local function belonging to the unique Whitney strip. -/
def paste (F : CellIndex tiles x ell → ℝ×ℝ → V) (z : ℝ×ℝ) : V :=
  F (indexAt tiles x ell hne hpos z.1) z

theorem paste_eq (F : CellIndex tiles x ell → ℝ×ℝ → V)
    (i : CellIndex tiles x ell) {z : ℝ×ℝ} {E : Set (ℝ×ℝ)} (hz : z∈strip tiles x ell E i) :
    paste tiles x ell hne hpos F z=F i z := by
  unfold paste
  rw [indexAt_eq_of_mem tiles x ell hne hpos i hz.2]

variable [NormedAddCommGroup V]

/-- Uniform bounds for finite collections of local norm integrals give
integrability and the identical estimate on the full Whitney partition. -/
theorem paste_integrable_bound (E : Set (ℝ×ℝ)) (hE : MeasurableSet E)
    (F : CellIndex tiles x ell → ℝ×ℝ → V)
    (hF : ∀ i, IntegrableOn (F i) (strip tiles x ell E i) (volume.prod volume))
    (C : ℝ) (hbound : ∀ S : Finset (CellIndex tiles x ell),
      (∑ i∈S, ∫ z in strip tiles x ell E i, ‖F i z‖ ∂volume.prod volume) ≤ C) :
    IntegrableOn (paste tiles x ell hne hpos F) E (volume.prod volume) ∧
    (∫ z in E, ‖paste tiles x ell hne hpos F z‖ ∂volume.prod volume) ≤ C := by
  let G := paste tiles x ell hne hpos F
  have heq (i : CellIndex tiles x ell) (z : ℝ×ℝ) (hz : z∈strip tiles x ell E i) : G z=F i z :=
    paste_eq tiles x ell hne hpos F i hz
  have hlocal (i : CellIndex tiles x ell) : IntegrableOn G (strip tiles x ell E i) (volume.prod volume) := by
    exact (hF i).congr_fun (fun z hz => (heq i z hz).symm) (strip_measurable tiles x ell hE i)
  have hint (i : CellIndex tiles x ell) :
      (∫ z in strip tiles x ell E i, ‖G z‖ ∂volume.prod volume) =
      (∫ z in strip tiles x ell E i, ‖F i z‖ ∂volume.prod volume) :=
    setIntegral_congr_fun (strip_measurable tiles x ell hE i) (fun z hz => congrArg norm (heq i z hz))
  have hsum : Summable (fun i : CellIndex tiles x ell =>
      ∫ z in strip tiles x ell E i, ‖G z‖ ∂volume.prod volume) := by
    apply summable_of_sum_le (fun i => integral_nonneg (fun z => norm_nonneg (G z)))
    intro S
    simpa only [hint] using hbound S
  have hglobal := integrableOn_iUnion_of_summable_integral_norm hlocal hsum
  rw [strip_iUnion tiles x ell hne hpos E] at hglobal
  refine ⟨hglobal,?_⟩
  have hglobalnorm : IntegrableOn (fun z => ‖G z‖) E (volume.prod volume) := hglobal.norm
  have hpartition := integral_iUnion (μ:=volume.prod volume)
    (f:=fun z => ‖G z‖) (strip_measurable tiles x ell hE) (strip_disjoint tiles x ell E)
    (by simpa only [strip_iUnion tiles x ell hne hpos E] using hglobalnorm)
  rw [strip_iUnion tiles x ell hne hpos E] at hpartition
  rw [hpartition]
  apply Real.tsum_le_of_sum_le (fun i => integral_nonneg (fun z => norm_nonneg (G z)))
  intro S
  simpa only [hint] using hbound S

end LipschitzHilbert.SourceWhitney

end

end OAI
