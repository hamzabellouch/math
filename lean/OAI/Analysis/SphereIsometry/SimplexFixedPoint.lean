import OAI.Analysis.SphereIsometry.SimplexLimit
import OAI.Analysis.SphereIsometry.IteratedPoints
import OAI.Analysis.SphereIsometry.Sperner
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.EquivFin

namespace OAI

/-!
# Fixed points in finite probability simplexes

The finite-coordinate theorem constructs its approximating points from the actual iterated
subdivision and the proved Sperner theorem. Positive coordinates enforce the boundary condition
on labels. The shrinking mesh and the labelled inequalities then give an exact fixed point.
Coordinate reindexing transports the result to every nonempty finite index type.
-/

open Filter
open scoped Topology

namespace Tingley

/-- Every continuous self-map of a probability simplex with `m + 1` coordinates has a fixed
point. The construction includes `m = 0`, the one-point simplex. -/
theorem continuous_fin_probabilitySimplex_fixedPoint (m : ℕ)
    (P : ProbabilitySimplex (Fin (m + 1)) → ProbabilitySimplex (Fin (m + 1)))
    (hP : Continuous P) : ∃ a, P a = a := by
  classical
  let point : (k : ℕ) → IterVertex m k → ProbabilitySimplex (Fin (m + 1)) :=
    fun k v => ⟨iterPoint m k v, iterPoint_mem_stdSimplex m k v⟩
  let label : (k : ℕ) → IterVertex m k → Fin (m + 1) :=
    fun k v => Classical.choose
      (exists_positive_dominating_coordinate (point k v) (P (point k v)))
  have hlabel (k : ℕ) (v : IterVertex m k) :
      0 < (point k v).val (label k v) ∧
        (P (point k v)).val (label k v) ≤ (point k v).val (label k v) :=
    Classical.choose_spec
      (exists_positive_dominating_coordinate (point k v) (P (point k v)))
  have hcarrier (k : ℕ) (v : IterVertex m k) : label k v ∈ iterCarrier m k v :=
    (iterPoint_pos_iff m k v (label k v)).mp (hlabel k v).1
  have hcells (k : ℕ) :
      ∃ s, s ∈ topCells m k ∧ s.image (label k) = Finset.univ :=
    iterated_sperner_exists m k (label k) (hcarrier k)
  let cell (k : ℕ) : Finset (IterVertex m k) := Classical.choose (hcells k)
  have hcell_mem (k : ℕ) : cell k ∈ topCells m k :=
    (Classical.choose_spec (hcells k)).1
  have hcell_labels (k : ℕ) : (cell k).image (label k) = Finset.univ :=
    (Classical.choose_spec (hcells k)).2
  have hvertices (k : ℕ) (i : Fin (m + 1)) :
      ∃ v, v ∈ cell k ∧ label k v = i := by
    apply Finset.mem_image.mp
    rw [hcell_labels k]
    exact Finset.mem_univ i
  let vertex (k : ℕ) (i : Fin (m + 1)) : IterVertex m k :=
    Classical.choose (hvertices k i)
  have hvertex_mem (k : ℕ) (i : Fin (m + 1)) : vertex k i ∈ cell k :=
    (Classical.choose_spec (hvertices k i)).1
  have hvertex_label (k : ℕ) (i : Fin (m + 1)) : label k (vertex k i) = i :=
    (Classical.choose_spec (hvertices k i)).2
  let a : ℕ → Fin (m + 1) → ProbabilitySimplex (Fin (m + 1)) :=
    fun k i => point k (vertex k i)
  have hden : (0 : ℝ) < (m : ℝ) + 1 :=
    add_pos_of_nonneg_of_pos (Nat.cast_nonneg m) zero_lt_one
  have hq₀ : (0 : ℝ) ≤ (m : ℝ) / ((m : ℝ) + 1) :=
    div_nonneg (Nat.cast_nonneg m) hden.le
  have hq₁ : (m : ℝ) / ((m : ℝ) + 1) < 1 :=
    (div_lt_one hden).mpr (lt_add_of_pos_right (m : ℝ) zero_lt_one)
  apply probabilitySimplex_fixedPoint_of_shrinking_family P hP a
    (fun k => ((m : ℝ) / ((m : ℝ) + 1)) ^ k)
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁)
  · intro k i j
    change dist (iterPoint m k (vertex k i)) (iterPoint m k (vertex k j)) ≤
      ((m : ℝ) / ((m : ℝ) + 1)) ^ k
    rw [dist_eq_norm]
    exact iterPoint_mesh m k (cell k) (mem_topCells.mp (hcell_mem k)).1
      (vertex k i) (hvertex_mem k i) (vertex k j) (hvertex_mem k j)
  · intro k i
    change (P (point k (vertex k i))).val i ≤ (point k (vertex k i)).val i
    simpa only [hvertex_label k i] using (hlabel k (vertex k i)).2

/-- Every continuous self-map of a probability simplex indexed by a nonempty finite type has
a fixed point. All geometric and finite-incidence inputs are discharged by the finite theorem. -/
theorem continuous_probabilitySimplex_fixedPoint
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (P : ProbabilitySimplex ι → ProbabilitySimplex ι) (hP : Continuous P) :
    ∃ a, P a = a := by
  classical
  let m := Fintype.card ι - 1
  have hc : Fintype.card ι = m + 1 := by
    dsimp [m]
    exact (Nat.sub_add_cancel (Nat.succ_le_of_lt
      (Fintype.card_pos : 0 < Fintype.card ι))).symm
  let e : ι ≃ Fin (m + 1) := Fintype.equivFinOfCardEq hc
  let h := probabilitySimplexReindex e
  let Q : ProbabilitySimplex (Fin (m + 1)) → ProbabilitySimplex (Fin (m + 1)) :=
    fun b => h (P (h.symm b))
  have hQ : Continuous Q :=
    h.continuous.comp (hP.comp h.symm.continuous)
  obtain ⟨b, hb⟩ := continuous_fin_probabilitySimplex_fixedPoint m Q hQ
  refine ⟨h.symm b, ?_⟩
  simpa only [Q, Homeomorph.symm_apply_apply] using congrArg h.symm hb

end Tingley

end OAI
