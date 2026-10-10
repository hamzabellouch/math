import OAI.Analysis.KadisonKastler.PublishedKaplansky
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace OAI

/-! # Self-adjoint strong approximation

This is the first step in discharging bounded density. The existing
bicommutant theorem gives unbounded strong approximation. Taking real
parts preserves weak convergence; orthogonal complements of the finite
tuple orbit then recover strong approximation by self-adjoint elements.
-/

namespace KadisonKastler

open Generator Filter
open scoped Topology ComplexOrder BigOperators

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem inner_realPart (a : H →L[ℂ] H) (x y : H) :
    inner ℂ y ((realPart a : H →L[ℂ] H) x) =
      (2 : ℂ)⁻¹ * (inner ℂ y (a x) + inner ℂ (a y) x) := by
  rw [realPart_apply_coe]
  simp only [smul_apply, add_apply]
  norm_num
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  ring


/-- Strong convergence implies weak convergence of the real parts, even
when no uniform norm bound on the original net is available. -/
theorem tendsto_inner_realPart_of_strong
    {ι : Type*} {l : Filter ι} {a : ι → H →L[ℂ] H} {T : H →L[ℂ] H}
    (ha : ∀ x, Tendsto (fun i => a i x) l (𝓝 (T x))) (x y : H) :
    Tendsto (fun i => inner ℂ y ((realPart (a i) : H →L[ℂ] H) x)) l
      (𝓝 (inner ℂ y ((realPart T : H →L[ℂ] H) x))) := by
  simp only [inner_realPart]
  exact (((continuous_const.inner continuous_id).continuousAt.tendsto.comp (ha x)).add
    ((continuous_id.inner continuous_const).continuousAt.tendsto.comp (ha y))).const_mul _

private def selfAdjointTupleMap {ι : Type*} [Fintype ι]
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (x : FiniteHilbert ι H) :
    selfAdjoint A →ₗ[ℝ] FiniteHilbert ι H where
  toFun a := diagonalOperator (a.val : H →L[ℂ] H) x
  map_add' a b := by ext i; rfl
  map_smul' c a := by
    ext i
    change (c • (a.val : H →L[ℂ] H)) (x i) = c • ((a.val : H →L[ℂ] H) (x i))
    rfl

/-- The finite tuple of values of a self-adjoint bicommutant element lies
in the real-linear closure of the self-adjoint algebra orbit. -/
theorem selfAdjoint_bicommutant_tuple_mem_closure
    {ι : Type*} [Fintype ι] (A : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint T) (x : FiniteHilbert ι H) :
    diagonalOperator T x ∈ (selfAdjointTupleMap A x).range.topologicalClosure := by
  classical
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let W := (selfAdjointTupleMap A x).range.topologicalClosure
  have hW : IsClosed (W : Set (FiniteHilbert ι H)) := Submodule.isClosed_topologicalClosure _
  change diagonalOperator T x ∈ W
  have hWW : Wᗮᗮ = W := Submodule.orthogonal_orthogonal W
  rw [← hWW]
  apply (W.orthogonal.mem_orthogonal _).mpr
  intro y hy
  obtain ⟨a, ha⟩ := bicommutant_exists_strong_net A T hT
  have hlim : Tendsto
      (fun d => inner ℝ (diagonalOperator ((realPart (a d) : A) : H →L[ℂ] H) x) y)
      atTop (𝓝 (inner ℝ (diagonalOperator T x) y)) := by
    simp only [PiLp.inner_apply]
    apply tendsto_finsetSum
    intro i _
    have h := tendsto_inner_realPart_of_strong (fun z => ha z) (x i) (y i)
    have he (d) : (((realPart (a d) : A) : H →L[ℂ] H)) =
        (realPart ((a d).val) : H →L[ℂ] H) := by
      simp only [realPart_apply_coe, ← Complex.coe_smul]
      rfl
    simp only [diagonalOperator_apply, he]
    have hr := Complex.continuous_re.continuousAt.tendsto.comp h
    simpa only [hsa.coe_realPart, real_inner_eq_re_inner, inner_re_symm, RCLike.re_eq_complex_re, Function.comp_def] using hr
  have hzero : ∀ d, inner ℝ
      (diagonalOperator ((realPart (a d) : A) : H →L[ℂ] H) x) y = 0 := by
    intro d
    exact (W.mem_orthogonal y).mp hy _
      (Submodule.le_topologicalClosure _ ⟨realPart (a d), rfl⟩)
  have hz := tendsto_nhds_unique (hlim.congr hzero) tendsto_const_nhds
  exact (real_inner_comm _ _).trans hz

/-- Finite strong tests can be met by a self-adjoint element of the original
algebra. This step has no bounded-density hypothesis. -/
theorem selfAdjoint_bicommutant_finite_strong_approximation
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint T) (V : Finset H) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, IsSelfAdjoint (a : H →L[ℂ] H) ∧
      ∀ x ∈ V, ‖T x - (a : H →L[ℂ] H) x‖ < ε := by
  classical
  let x : FiniteHilbert V H := WithLp.toLp 2 (fun i : V => i.val)
  have hc := selfAdjoint_bicommutant_tuple_mem_closure A T hT hsa x
  obtain ⟨z, ⟨a, rfl⟩, ha⟩ := Metric.mem_closure_iff.mp hc ε hε
  refine ⟨a.val, ?_, ?_⟩
  · change star (a.val : H →L[ℂ] H) = (a.val : H →L[ℂ] H)
    exact congrArg (fun b : A => (b : H →L[ℂ] H)) a.property
  · intro y hy
    have hb := PiLp.norm_apply_le
      (diagonalOperator T x - selfAdjointTupleMap A x a) (⟨y, hy⟩ : V)
    exact hb.trans_lt (by simpa only [dist_eq_norm] using ha)

/-- A self-adjoint strongly convergent net, indexed independently of any
norm bound. Bounded transforms will supply the missing norm control. -/
theorem selfAdjoint_bicommutant_exists_strong_net
    (A : StarSubalgebra ℂ (H →L[ℂ] H)) (T : H →L[ℂ] H)
    (hT : T ∈ Set.centralizer (Set.centralizer (A : Set (H →L[ℂ] H))))
    (hsa : IsSelfAdjoint T) :
    ∃ a : Finset H × ℕ → A,
      (∀ i, IsSelfAdjoint (a i : H →L[ℂ] H)) ∧
      ∀ x : H, Tendsto (fun i => (a i : H →L[ℂ] H) x) atTop (𝓝 (T x)) := by
  classical
  have hex (i : Finset H × ℕ) := selfAdjoint_bicommutant_finite_strong_approximation
    A T hT hsa i.1 (show 0 < 1 / ((i.2 : ℝ) + 1) by positivity)
  choose a hsa' ha using hex
  refine ⟨a, hsa', ?_⟩
  intro x
  apply (tendsto_iff_dist_tendsto_zero).mpr
  have hsnd : Tendsto (fun i : Finset H × ℕ => i.2) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  apply squeeze_zero' (Eventually.of_forall (fun _ => dist_nonneg)) ?_
    (tendsto_one_div_add_atTop_nhds_zero_nat.comp hsnd)
  filter_upwards [eventually_ge_atTop (({x} : Finset H), 0)] with i hi
  rw [dist_comm, dist_eq_norm]
  exact (ha i x (hi.1 (Finset.mem_singleton_self x))).le

end

end KadisonKastler

end OAI
