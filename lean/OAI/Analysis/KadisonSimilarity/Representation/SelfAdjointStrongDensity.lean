import OAI.Analysis.FactorGeneration.Bicommutant
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

namespace OAI

/-! Selfadjoint strong density in the bicommutant. The real orbit is tested
against its orthogonal complement; adjoints only occur in scalar products. -/
noncomputable section
namespace KadisonSimilarity
open Filter ContinuousLinearMap
open scoped Topology BigOperators

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Fintype ι]

private def symmetrize (A : H →L[ℂ] H) : H →L[ℂ] H :=
  (1 / 2 : ℝ) • (A + star A)

private theorem symmetrize_selfAdjoint (A : H →L[ℂ] H) :
    IsSelfAdjoint (symmetrize A) := (IsSelfAdjoint.all (1 / 2 : ℝ)).smul (IsSelfAdjoint.add_star_self A)

private def realTupleOrbitMap (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (x : Generator.FiniteHilbert ι H) : S →ₗ[ℝ] Generator.FiniteHilbert ι H where
  toFun a := Generator.diagonalOperator (symmetrize a.val) x
  map_add' a b := by
    apply PiLp.ext
    intro i
    change (1 / 2 : ℝ) • (((a : H →L[ℂ] H) + b + star ((a : H →L[ℂ] H) + b)) (x i)) = _
    simp only [star_add, add_apply, smul_apply, PiLp.add_apply,
      Generator.diagonalOperator_apply, symmetrize]
    module
  map_smul' c a := by
    apply PiLp.ext
    intro i
    change (1 / 2 : ℝ) • (((c • (a : H →L[ℂ] H)) + star (c • (a : H →L[ℂ] H))) (x i)) =
      c • ((1 / 2 : ℝ) • (((a : H →L[ℂ] H) + star (a : H →L[ℂ] H)) (x i)))
    simp only [star_smul, star_trivial, smul_apply, add_apply]
    module

/-- Simultaneous approximation of a selfadjoint bicommutant element by
selfadjoint elements of the original star algebra, without a norm bound. -/
theorem selfAdjoint_bicommutant_tuple_mem_closure
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hTs : IsSelfAdjoint T) (x : Generator.FiniteHilbert ι H) :
    Generator.diagonalOperator T x ∈ (realTupleOrbitMap S x).range.topologicalClosure := by
  classical
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  apply (Submodule.mem_orthogonal _ _).mpr
  intro y hy
  obtain ⟨a, ha⟩ := Generator.bicommutant_exists_strong_net S T hT
  have hlim (i : ι) : Tendsto
      (fun d => inner ℝ (symmetrize (a d).val (x i)) (y i)) atTop
      (𝓝 (inner ℝ (T (x i)) (y i))) := by
    have h₁ := (ha (x i)).inner (𝕜 := ℝ) (tendsto_const_nhds (x := y i))
    have h₂ := (tendsto_const_nhds (x := x i)).inner (𝕜 := ℝ) (ha (y i))
    have hadj (A : H →L[ℂ] H) :
        inner ℝ (star A (x i)) (y i) = inner ℝ (x i) (A (y i)) := by
      simp only [real_inner_eq_re_inner (𝕜 := ℂ), star_eq_adjoint,
        adjoint_inner_left]
    have htadj : inner ℝ (x i) (T (y i)) = inner ℝ (T (x i)) (y i) := by
      rw [← hadj, hTs.star_eq]
    have hlim := (tendsto_const_nhds (x := (1 / 2 : ℝ))).mul (h₁.add h₂)
    convert hlim using 1
    · funext d
      simp only [symmetrize, smul_apply, add_apply, real_inner_smul_left,
        inner_add_left, hadj]
    · congr 1
      rw [htadj]
      ring
  have hsum : Tendsto
      (fun d : Finset H × ℕ => ∑ i, inner ℝ (symmetrize (a d).val (x i)) (y i))
      atTop (𝓝 (∑ i, inner ℝ (T (x i)) (y i))) :=
    tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  have hz (d : Finset H × ℕ) :
      (∑ i, inner ℝ (symmetrize (a d).val (x i)) (y i)) = 0 := by
    have hh := (Submodule.mem_orthogonal _ _).mp hy _
      (show realTupleOrbitMap S x (a d) ∈ (realTupleOrbitMap S x).range from ⟨a d, rfl⟩)
    simpa only [PiLp.inner_apply, realTupleOrbitMap, LinearMap.coe_mk,
      AddHom.coe_mk, Generator.diagonalOperator_apply] using hh
  have heq : (∑ i, inner ℝ (T (x i)) (y i)) = 0 :=
    tendsto_nhds_unique hsum (by simpa only [hz] using tendsto_const_nhds)
  rw [real_inner_comm, PiLp.inner_apply]
  simpa only [Generator.diagonalOperator_apply] using heq

/-- Finite-vector version of selfadjoint strong density. -/
theorem selfAdjoint_bicommutant_finite_approximation
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))))
    (hTs : IsSelfAdjoint T) (s : Finset H) (ε : ℝ) (hε : 0 < ε) :
    ∃ a : S, IsSelfAdjoint a.val ∧ ∀ x ∈ s, ‖T x - a.val x‖ < ε := by
  classical
  let x : Generator.FiniteHilbert s H := WithLp.toLp 2 (fun i : s => i.val)
  have h := selfAdjoint_bicommutant_tuple_mem_closure S T hT hTs x
  obtain ⟨z, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp h ε hε
  refine ⟨⟨symmetrize a.val, S.smul_mem (S.add_mem a.property
    (S.star_mem' a.property)) _⟩, symmetrize_selfAdjoint _, ?_⟩
  intro y hy
  have hb := PiLp.norm_apply_le
    (Generator.diagonalOperator T x - realTupleOrbitMap S x a) (⟨y, hy⟩ : s)
  exact hb.trans_lt (by simpa only [dist_eq_norm] using ha)

end KadisonSimilarity

end

end OAI
