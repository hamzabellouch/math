import OAI.Analysis.SphereIsometry.ProbabilitySimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Sequences

namespace OAI

/-!
# Extracting a fixed point from shrinking labelled simplex cells

The analytic limit step of the simplex fixed-point argument starts with
a concrete family of simplex points, one for each coordinate at every subdivision level.
The finite Sperner argument supplies this family, and the subdivision estimates supply its
shrinking diameter. No fixed-point principle is assumed here.
-/

open Filter
open scoped BigOperators Topology

namespace Tingley

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Relabelling the coordinates is a homeomorphism of probability simplexes. -/
def probabilitySimplexReindex (e : ι ≃ κ) : ProbabilitySimplex ι ≃ₜ ProbabilitySimplex κ where
  toFun x :=
    ⟨fun j => x.val (e.symm j),
      ⟨fun j => x.property.1 _, (e.symm.sum_comp x.val).trans x.property.2⟩⟩
  invFun y :=
    ⟨fun i => y.val (e i),
      ⟨fun i => y.property.1 _, (e.sum_comp y.val).trans y.property.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.val (e.symm_apply_apply i)
  right_inv y := by
    apply Subtype.ext
    funext j
    exact congrArg y.val (e.apply_symm_apply j)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun j =>
      (continuous_apply (e.symm j)).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i =>
      (continuous_apply (e i)).comp continuous_subtype_val

@[simp]
theorem probabilitySimplexReindex_apply_val (e : ι ≃ κ) (x : ProbabilitySimplex ι) (j : κ) :
    (probabilitySimplexReindex e x).val j = x.val (e.symm j) := rfl

@[simp]
theorem probabilitySimplexReindex_symm_apply_val (e : ι ≃ κ) (y : ProbabilitySimplex κ) (i : ι) :
    ((probabilitySimplexReindex e).symm y).val i = y.val (e i) := rfl

variable [Nonempty ι]

/-- Coordinate inequalities at points in shrinking cells produce an actual fixed point.

Only one sequence is passed to compactness. The mesh estimate forces all the coordinate-labelled
sequences along that same subsequence to converge to the same simplex point. -/
theorem probabilitySimplex_fixedPoint_of_shrinking_family
    (P : ProbabilitySimplex ι → ProbabilitySimplex ι) (hP : Continuous P)
    (a : ℕ → ι → ProbabilitySimplex ι) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ k i j, dist (a k i) (a k j) ≤ δ k)
    (hcoordinate : ∀ k i, (P (a k i)).val i ≤ (a k i).val i) :
    ∃ x, P x = x := by
  classical
  let i₀ : ι := Classical.choice inferInstance
  obtain ⟨x, φ, hφ, hx⟩ := CompactSpace.tendsto_subseq (fun k => a k i₀)
  have hδφ : Tendsto (fun k => δ (φ k)) atTop (𝓝 0) :=
    hδ.comp hφ.tendsto_atTop
  have ha : ∀ i, Tendsto (fun k => a (φ k) i) atTop (𝓝 x) := by
    intro i
    apply hx.congr_dist
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun k => hmesh (φ k) i₀ i) hδφ
  have hle : ∀ i, (P x).val i ≤ x.val i := by
    intro i
    have hc : Continuous (fun y : ProbabilitySimplex ι => y.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact le_of_tendsto_of_tendsto'
      (((hc.comp hP).tendsto x).comp (ha i))
      ((hc.tendsto x).comp (ha i))
      (fun k => hcoordinate (φ k) i)
  have hsum : (∑ i, (x.val i - (P x).val i)) = 0 := by
    rw [Finset.sum_sub_distrib, x.property.2, (P x).property.2, sub_self]
  have hzero : ∀ i ∈ Finset.univ, x.val i - (P x).val i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.mpr (hle i))).mp hsum
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext i
  exact (sub_eq_zero.mp (hzero i (Finset.mem_univ i))).symm

end Tingley

end OAI
