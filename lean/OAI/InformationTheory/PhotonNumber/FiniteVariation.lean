import OAI.InformationTheory.PhotonNumber.GibbsVariational
import OAI.InformationTheory.PhotonNumber.Contraction

namespace OAI

noncomputable section

section
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix

namespace FiniteBlock

section
variable {I J E : Type*} [Fintype I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def embedLinear (b : HilbertBasis (I ⊕ J) ℂ E) : EuclideanSpace ℂ I →ₗ[ℂ] E :=
  (EuclideanSpace.basisFun I ℂ).toBasis.constr ℂ (fun i => b (Sum.inl i))

@[simp] theorem embedLinear_basis (b : HilbertBasis (I ⊕ J) ℂ E) (i : I) :
    embedLinear b ((EuclideanSpace.basisFun I ℂ) i) = b (Sum.inl i) := by
  exact (EuclideanSpace.basisFun I ℂ).toBasis.constr_basis ℂ _ i

theorem embedLinear_orthonormal (b : HilbertBasis (I ⊕ J) ℂ E) :
    Orthonormal ℂ (embedLinear b ∘ (EuclideanSpace.basisFun I ℂ).toBasis) := by
  have he : embedLinear b ∘ (EuclideanSpace.basisFun I ℂ).toBasis = (fun i => b (Sum.inl i)) := by
    funext i
    exact embedLinear_basis b i
  rw [he]
  exact b.orthonormal.comp Sum.inl Sum.inl_injective

def embed (b : HilbertBasis (I ⊕ J) ℂ E) : EuclideanSpace ℂ I →ₗᵢ[ℂ] E :=
  (embedLinear b).isometryOfOrthonormal (v := (EuclideanSpace.basisFun I ℂ).toBasis)
    (EuclideanSpace.basisFun I ℂ).orthonormal (embedLinear_orthonormal b)

@[simp] theorem embed_basis (b : HilbertBasis (I ⊕ J) ℂ E) (i : I) :
    embed b ((EuclideanSpace.basisFun I ℂ) i) = b (Sum.inl i) := embedLinear_basis b i

theorem embed_apply (b : HilbertBasis (I ⊕ J) ℂ E) (x : EuclideanSpace ℂ I) :
    embed b x = ∑ i, x i • b (Sum.inl i) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun I ℂ).sum_repr x]
  simp only [map_sum, map_smul, embed_basis]
  rfl

variable (b : HilbertBasis (I ⊕ J) ℂ E) (c : OrthonormalBasis I ℂ (EuclideanSpace ℂ I))

def vectors : I ⊕ J → E := Sum.elim (fun i => embed b (c i)) (fun j => b (Sum.inr j))

theorem vectors_orthonormal : Orthonormal ℂ (vectors b c) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simpa only [vectors, Sum.elim_inl, (embed b).inner_map_map,
        Sum.inl.injEq] using (orthonormal_iff_ite.mp c.orthonormal i j)
    | inr j =>
      simp only [vectors, Sum.elim_inl, Sum.elim_inr, Sum.inl_ne_inr, ↓reduceIte,
        embed_apply, sum_inner, inner_smul_left, orthonormal_iff_ite.mp b.orthonormal,
        mul_zero, Finset.sum_const_zero]
  | inr i =>
    cases j with
    | inl j =>
      simp only [vectors, Sum.elim_inl, Sum.elim_inr, Sum.inr_ne_inl, ↓reduceIte,
        embed_apply, inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal,
        mul_zero, Finset.sum_const_zero]
    | inr j => simpa only [vectors, Sum.elim_inr, Sum.inr.injEq] using
        (orthonormal_iff_ite.mp b.orthonormal (Sum.inr i) (Sum.inr j))

variable [CompleteSpace E]

def basis : HilbertBasis (I ⊕ J) ℂ E := HilbertBasis.mk (vectors_orthonormal b c) (by
  have hsub : Submodule.span ℂ (Set.range b) ≤ Submodule.span ℂ (Set.range (vectors b c)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    cases i with
    | inr j => exact Submodule.subset_span ⟨Sum.inr j,rfl⟩
    | inl i =>
      rw [← embed_basis b i, ← c.sum_repr ((EuclideanSpace.basisFun I ℂ) i), map_sum]
      apply Submodule.sum_mem
      intro j _
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl j,rfl⟩)
  exact b.dense_span.ge.trans (Submodule.topologicalClosure_mono hsub))

@[simp] theorem basis_inl (i : I) : basis b c (Sum.inl i) = embed b (c i) :=
  congrFun (HilbertBasis.coe_mk _ _) _
@[simp] theorem basis_inr (j : J) : basis b c (Sum.inr j) = b (Sum.inr j) :=
  congrFun (HilbertBasis.coe_mk _ _) _

omit [CompleteSpace E] in

def block (M : Matrix I I ℂ) : E →L[ℂ] E :=
  ∑ i, ∑ j, M i j • InnerProductSpace.rankOne ℂ (b (Sum.inl i)) (b (Sum.inl j))

omit [CompleteSpace E] in
theorem inner_basis_embed (i : I) (x : EuclideanSpace ℂ I) :
    inner ℂ (b (Sum.inl i)) (embed b x) = x i := by
  classical
  simp [embed_apply, orthonormal_iff_ite.mp b.orthonormal]

omit [CompleteSpace E] in
theorem block_embed (M : Matrix I I ℂ) (x : EuclideanSpace ℂ I) :
    block b M (embed b x) = embed b (WithLp.toLp 2 (M *ᵥ ⇑x)) := by
  classical
  simp only [block, sum_apply, smul_apply,
    InnerProductSpace.rankOne_apply, inner_basis_embed, smul_smul]
  rw [embed_apply]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul]

omit [CompleteSpace E] in
theorem block_tail (M : Matrix I I ℂ) (j : J) : block b M (b (Sum.inr j)) = 0 := by
  classical
  simp [block, InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]

variable [DecidableEq I]

theorem block_eigen (M : Matrix I I ℂ) (hM : M.IsHermitian) (i : I) :
    block b M (basis b hM.eigenvectorBasis (Sum.inl i)) =
      (hM.eigenvalues i : ℂ) • basis b hM.eigenvectorBasis (Sum.inl i) := by
  rw [basis_inl, block_embed, hM.mulVec_eigenvectorBasis]
  simp only [WithLp.toLp_smul, WithLp.toLp_ofLp]
  change embed b ((hM.eigenvalues i : ℂ) • hM.eigenvectorBasis i) = _
  exact map_smul (embed b) _ _

end

open NormedSpace Matrix
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem exp_spectral (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    exp M = (hM.eigenvectorUnitary : Matrix I I ℂ) *
      Matrix.diagonal (fun i => (Real.exp (hM.eigenvalues i) : ℂ)) *
      star (hM.eigenvectorUnitary : Matrix I I ℂ) := by
  let f := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) hM.eigenvectorUnitary
  have hf : Continuous f := f.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
  calc
    exp M = exp (f (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues))) :=
      congrArg NormedSpace.exp hM.spectral_theorem
    _ = f (exp (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues))) := (map_exp f hf _).symm
    _ = f (Matrix.diagonal (fun i => (Real.exp (hM.eigenvalues i) : ℂ))) := by
      congr 1
      rw [Matrix.exp_diagonal]
      congr 1
      funext i
      simp [Pi.coe_exp, Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]
    _ = _ := rfl

theorem exp_eigenvector (M : Matrix I I ℂ) (hM : M.IsHermitian) (i : I) :
    exp M *ᵥ ⇑(hM.eigenvectorBasis i) =
      (Real.exp (hM.eigenvalues i) : ℂ) • ⇑(hM.eigenvectorBasis i) := by
  rw [exp_spectral M hM, ← Matrix.mulVec_mulVec, hM.star_eigenvectorUnitary_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.diagonal_mulVec_single]
  rw [show (Real.exp (hM.eigenvalues i) : ℂ)*1 =
    (Real.exp (hM.eigenvalues i) : ℂ) • (1:ℂ) by rfl,
    Pi.single_smul, Matrix.mulVec_smul, hM.eigenvectorUnitary_mulVec]

theorem trace_exp (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    (Matrix.trace (exp M)).re = ∑ i, Real.exp (hM.eigenvalues i) := by
  rw [exp_spectral M hM, Matrix.trace_mul_comm]
  rw [← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]

def partition {J : Type*} (p : I ⊕ J → ℝ) (M : Matrix I I ℂ) (hM : M.IsHermitian) : ℝ :=
  (∑' j, p (Sum.inr j)) + ∑ i, Real.exp (hM.eigenvalues i)

def weights {J : Type*} (p : I ⊕ J → ℝ) (M : Matrix I I ℂ) (hM : M.IsHermitian) : I ⊕ J → ℝ :=
  Sum.elim (fun i => Real.exp (hM.eigenvalues i) / partition p M hM)
    (fun j => p (Sum.inr j) / partition p M hM)

theorem partition_pos {J : Type*} (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    0 < partition p M hM := by
  classical
  have htail := hs.summable.comp_injective Sum.inr_injective
  obtain ⟨j,hj⟩ : ∃ j, p j ≠ 0 := by
    by_contra! h
    have he : p = fun _ => 0 := funext h
    have : HasSum p 0 := by rw [he]; exact hasSum_zero
    exact zero_ne_one (this.unique hs)
  unfold partition
  cases j with
  | inl i =>
    exact add_pos_of_nonneg_of_pos (tsum_nonneg (fun j => (hp (Sum.inr j)).le))
      (Finset.sum_pos' (fun j _ => (Real.exp_pos _).le) ⟨i,Finset.mem_univ _,Real.exp_pos _⟩)
  | inr j =>
    exact add_pos_of_pos_of_nonneg
      ((hp (Sum.inr j)).trans_le (htail.le_tsum j (fun i _ => (hp _).le)))
      (Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))

theorem weights_pos {J : Type*} (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (M : Matrix I I ℂ) (hM : M.IsHermitian) (j : I ⊕ J) :
    0 < weights p M hM j := by
  cases j with
  | inl i => exact div_pos (Real.exp_pos _) (partition_pos p hp hs M hM)
  | inr j => exact div_pos (hp _) (partition_pos p hp hs M hM)

theorem weights_hasSum {J : Type*} (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1) (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    HasSum (weights p M hM) 1 := by
  have ht := hs.summable.comp_injective Sum.inr_injective
  have hf : HasSum (Sum.elim (fun i => Real.exp (hM.eigenvalues i)) (fun j => p (Sum.inr j)))
      ((∑ i, Real.exp (hM.eigenvalues i)) + ∑' j, p (Sum.inr j)) :=
    HasSum.sum (hasSum_fintype _) ht.hasSum
  have hh := hf.div_const (partition p M hM)
  convert! hh using 1
  · funext j
    cases j <;> rfl
  · rw [add_comm]
    change 1 = partition p M hM / partition p M hM
    exact (div_self (partition_pos p hp hs M hM).ne').symm

end FiniteBlock

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {I J : Type*}

theorem basisMoment_smul_coeff (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) (z : ℂ) (x : E) :
    basisMoment b w (z • x) = ENNReal.ofReal (‖z‖^2)*basisMoment b w x := by
  simp only [basisMoment, inner_smul_right, norm_mul, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _)]
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext i
  exact mul_left_comm _ _ _

theorem basisMoment_add_le (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) (x y : E) :
    basisMoment b w (x+y) ≤ 2*basisMoment b w x+2*basisMoment b w y := by
  simp only [basisMoment, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro i
  have hn : ‖inner ℂ (b i) (x+y)‖^2 ≤
      2*‖inner ℂ (b i) x‖^2+2*‖inner ℂ (b i) y‖^2 := by
    rw [inner_add_right]
    calc
      _ ≤ (‖inner ℂ (b i) x‖+‖inner ℂ (b i) y‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) _
      _ ≤ _ := by nlinarith [sq_nonneg (‖inner ℂ (b i) x‖-‖inner ℂ (b i) y‖)]
  calc
    _ ≤ w i*ENNReal.ofReal (2*‖inner ℂ (b i) x‖^2+2*‖inner ℂ (b i) y‖^2) :=
      mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hn)
    _ = _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      simp only [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2), ENNReal.ofReal_ofNat]
      ring

def momentDomain (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) : Submodule ℂ E where
  carrier := {x | basisMoment b w x < ⊤}
  zero_mem' := by simp [basisMoment]
  add_mem' := by
    intro x y hx hy
    exact (basisMoment_add_le b w x y).trans_lt (ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top (by norm_num) hx, ENNReal.mul_lt_top (by norm_num) hy⟩)
  smul_mem' := by
    intro z x hx
    change basisMoment b w (z • x) < ⊤
    rw [basisMoment_smul_coeff]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hx

@[simp] theorem mem_momentDomain (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞) (x : E) :
    x ∈ momentDomain b w ↔ basisMoment b w x < ⊤ := Iff.rfl

variable [CompleteSpace E]

theorem basisExpectation_diagonal (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞)
    (c : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : Summable p) :
    basisExpectation b w (TraceEnsemble.operator (TraceEnsemble.diagonalVector c p)) =
      ∑' j, ENNReal.ofReal (p j)*basisMoment b w (c j) := by
  rw [basisExpectation_ensemble b w (by simpa only [TraceEnsemble.diagonalVector_norm_sq c p hp] using hs)]
  congr 1
  funext j
  rw [TraceEnsemble.diagonalVector, basisMoment_smul_coeff]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (hp _)]

theorem eigenvector_moment_finite (b : HilbertBasis I ℂ E) (w : I → ℝ≥0∞)
    (c : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀ j, 0 < p j) (hs : Summable p)
    (hm : basisExpectation b w (TraceEnsemble.operator (TraceEnsemble.diagonalVector c p)) < ⊤)
    (j : J) : basisMoment b w (c j) < ⊤ := by
  rw [basisExpectation_diagonal b w c p (fun j => (hp j).le) hs] at hm
  have hj := (ENNReal.le_tsum j).trans_lt hm
  by_contra hn
  have he : basisMoment b w (c j) = ⊤ := top_le_iff.mp (not_lt.mp hn)
  rw [he] at hj
  simp [ENNReal.ofReal_pos.mpr (hp j) |>.ne'] at hj

end QuantumTrace

namespace TraceEnsemble
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {I J : Type*}

omit [CompleteSpace E] in
theorem summable_basis_square (b : HilbertBasis J ℂ E) {v : I → E}
    (hv : Summable (fun i => ‖v i‖^2)) :
    Summable (fun ij : I × J => ‖inner ℂ (b ij.2) (v ij.1)‖^2) := by
  rw [summable_prod_of_nonneg (fun _ => sq_nonneg _)]
  exact ⟨fun i => (basis_hasSum_norm_sq b (v i)).summable,
    by simpa only [(basis_hasSum_norm_sq b _).tsum_eq] using hv⟩

omit [CompleteSpace E] in
theorem summable_map_square {v : I → E} (hv : Summable (fun i => ‖v i‖^2))
    (Z : E →L[ℂ] E) : Summable (fun i => ‖Z (v i)‖^2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (hv.mul_left (‖Z‖^2))
  intro i
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (Z.le_opNorm (v i)) 2

omit [CompleteSpace E] in
theorem summable_trace_pair (b : HilbertBasis J ℂ E) {v : I → E}
    (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    Summable (fun ij : I × J => inner ℂ (v ij.1) (b ij.2)*inner ℂ (b ij.2) (Z (v ij.1))) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (((summable_basis_square b hv).add
      (summable_basis_square b (summable_map_square hv Z))).div_const 2)
  intro ij
  simp only [norm_mul, norm_inner_symm (v ij.1) (b ij.2)]
  nlinarith [sq_nonneg (‖inner ℂ (b ij.2) (v ij.1)‖-‖inner ℂ (b ij.2) (Z (v ij.1))‖)]

def expectation (v : I → E) (Z : E →L[ℂ] E) : ℂ :=
  ∑' i, inner ℂ (v i) (Z (v i))

omit [CompleteSpace E] in
theorem hasSum_expectation {v : I → E} (hv : Summable (fun i => ‖v i‖^2))
    (Z : E →L[ℂ] E) : HasSum (fun i => inner ℂ (v i) (Z (v i))) (expectation v Z) :=
  (summable_expectation_norm hv Z).of_norm.hasSum

theorem hasSum_expectation_basis (b : HilbertBasis J ℂ E) {v : I → E}
    (hv : Summable (fun i => ‖v i‖^2)) (Z : E →L[ℂ] E) :
    HasSum (fun j => inner ℂ (b j) (Z (operator v (b j)))) (expectation v Z) := by
  have hd := summable_trace_pair b hv Z
  have hrow (i : I) : HasSum (fun j => inner ℂ (v i) (b j)*inner ℂ (b j) (Z (v i)))
      (inner ℂ (v i) (Z (v i))) := b.hasSum_inner_mul_inner (v i) (Z (v i))
  have hcol (j : J) : HasSum (fun i => inner ℂ (v i) (b j)*inner ℂ (b j) (Z (v i)))
      (inner ℂ (b j) (Z (operator v (b j)))) := by
    have hh := (((ContinuousLinearMap.apply ℂ E (b j)).hasSum (hasSum_rankOne hv)).mapL Z).mapL
      (innerSL ℂ (b j))
    simpa only [ContinuousLinearMap.apply_apply, InnerProductSpace.rankOne_apply,
      map_smul, innerSL_apply_apply, inner_smul_right, smul_eq_mul] using hh
  have he : (∑' ij : I × J, inner ℂ (v ij.1) (b ij.2)*inner ℂ (b ij.2) (Z (v ij.1))) =
      expectation v Z := by
    rw [hd.tsum_prod]
    simp only [(hrow _).tsum_eq, expectation]
  rw [← he]
  exact ((Equiv.prodComm J I).hasSum_iff.2 hd.hasSum).prod_fiberwise hcol

theorem expectation_eq_of_operator_eq (b : HilbertBasis J ℂ E)
    {K : Type*} {v : I → E} {w : K → E}
    (hv : Summable (fun i => ‖v i‖^2)) (hw : Summable (fun j => ‖w j‖^2))
    (h : operator v = operator w) (Z : E →L[ℂ] E) : expectation v Z = expectation w Z := by
  have hh := hasSum_expectation_basis b hv Z
  rw [h] at hh
  exact hh.unique (hasSum_expectation_basis b hw Z)

end TraceEnsemble

namespace EntropyPhotonNumber

section
open TraceEnsemble

def expectation {n : ℕ} (ρ : State n) (Z : Fock n →L[ℂ] Fock n) : ℂ :=
  TraceEnsemble.expectation (rootColumn ρ) Z

theorem expectation_ensemble {n : ℕ} (ρ : State n) {I : Type*} (v : I → Fock n)
    (hv : Summable (fun i => ‖v i‖^2)) (he : TraceEnsemble.operator v = ρ.op)
    (Z : Fock n →L[ℂ] Fock n) : expectation ρ Z = TraceEnsemble.expectation v Z := by
  exact TraceEnsemble.expectation_eq_of_operator_eq (channelNumberBasis n) (rootColumn_norm ρ).summable hv
    ((rootColumn_operator ρ).trans he.symm) Z

theorem hasSum_expectation_basis {n : ℕ} {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (ρ : State n) (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun j => inner ℂ (b j) (Z (ρ.op (b j)))) (expectation ρ Z) := by
  simpa only [rootColumn_operator, expectation] using
    TraceEnsemble.hasSum_expectation_basis b (rootColumn_norm ρ).summable Z

theorem expectation_add {n : ℕ} (ρ : State n) (X Y : Fock n →L[ℂ] Fock n) :
    expectation ρ (X+Y) = expectation ρ X+expectation ρ Y := by
  exact (hasSum_expectation_basis (channelNumberBasis n) ρ (X+Y)).unique (by
    simpa only [add_apply, inner_add_right] using
      (hasSum_expectation_basis (channelNumberBasis n) ρ X).add (hasSum_expectation_basis (channelNumberBasis n) ρ Y))

theorem expectation_smul {n : ℕ} (ρ : State n) (a : ℂ) (Z : Fock n →L[ℂ] Fock n) :
    expectation ρ (a • Z) = a*expectation ρ Z := by
  exact (hasSum_expectation_basis (channelNumberBasis n) ρ (a • Z)).unique (by
    simpa only [smul_apply, inner_smul_right] using
      (hasSum_expectation_basis (channelNumberBasis n) ρ Z).mul_left a)

end

open QuantumTrace TraceEnsemble

def spectralState {n : ℕ} {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1) : State n where
  op := TraceEnsemble.operator (diagonalVector b p)
  positive := TraceEnsemble.positive (by simpa only [diagonalVector_norm_sq b p hp] using hs.summable)
  trace_one := by
    simpa only [numberBasis_apply, entry] using TraceEnsemble.trace
      (by simpa only [diagonalVector_norm_sq b p hp] using hs :
        HasSum (fun j => ‖diagonalVector b p j‖^2) 1) (numberBasis n)

@[simp] theorem spectralState_eigen {n : ℕ} {J : Type*} (b : HilbertBasis J ℂ (Fock n))
    (p : J → ℝ) (hp : ∀ j, 0 ≤ p j) (hs : HasSum p 1) (j : J) :
    (spectralState b p hp hs).op (b j) = (p j : ℂ) • b j :=
  diagonalVector_eigen b p hp hs.summable j

def blockState {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1) (M : Matrix I I ℂ) (hM : M.IsHermitian) : State n :=
  spectralState (FiniteBlock.basis b hM.eigenvectorBasis) (FiniteBlock.weights p M hM)
    (fun j => (FiniteBlock.weights_pos p hp hs M hM j).le) (FiniteBlock.weights_hasSum p hp hs M hM)

end EntropyPhotonNumber

namespace FiniteBlock

section
open QuantumTrace
variable {I J E K : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [DecidableEq I] in
 theorem basis_domain (a : HilbertBasis K ℂ E) (w : K → ℝ≥0∞)
    (b : HilbertBasis (I ⊕ J) ℂ E) (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1)
    (hm : basisExpectation a w (TraceEnsemble.operator (TraceEnsemble.diagonalVector b p)) < ⊤)
    (c : OrthonormalBasis I ℂ (EuclideanSpace ℂ I)) (j : I ⊕ J) :
    basisMoment a w (basis b c j) < ⊤ := by
  have hv (j : I ⊕ J) : b j ∈ momentDomain a w :=
    eigenvector_moment_finite a w b p hp hs.summable hm j
  change basis b c j ∈ momentDomain a w
  cases j with
  | inr j => simpa only [basis_inr] using hv (Sum.inr j)
  | inl i =>
    rw [basis_inl, embed_apply]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hv (Sum.inl j)))

 theorem tilted_moment_finite (a : HilbertBasis K ℂ E) (w : K → ℝ≥0∞)
    (b : HilbertBasis (I ⊕ J) ℂ E) (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j)
    (hs : HasSum p 1)
    (hm : basisExpectation a w (TraceEnsemble.operator (TraceEnsemble.diagonalVector b p)) < ⊤)
    (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    basisExpectation a w (TraceEnsemble.operator
      (TraceEnsemble.diagonalVector (basis b hM.eigenvectorBasis) (weights p M hM))) < ⊤ := by
  rw [basisExpectation_diagonal a w _ _ (fun j => (weights_pos p hp hs M hM j).le)
    (weights_hasSum p hp hs M hM).summable]
  let P := (ENNReal.ofReal (partition p M hM))⁻¹
  have hP : P < ⊤ := by
    exact ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr (partition_pos p hp hs M hM))
  have htail : (∑' j, ENNReal.ofReal (p (Sum.inr j))*basisMoment a w (b (Sum.inr j))) < ⊤ := by
    rw [basisExpectation_diagonal a w b p (fun j => (hp j).le) hs.summable] at hm
    exact (ENNReal.tsum_comp_le_tsum_of_injective Sum.inr_injective _).trans_lt hm
  have hh : HasSum (fun j : I ⊕ J => ENNReal.ofReal (weights p M hM j)*
      basisMoment a w (basis b hM.eigenvectorBasis j))
      ((∑ i, ENNReal.ofReal (weights p M hM (Sum.inl i))*
          basisMoment a w (basis b hM.eigenvectorBasis (Sum.inl i)))+
        ∑' j, ENNReal.ofReal (weights p M hM (Sum.inr j))*
          basisMoment a w (basis b hM.eigenvectorBasis (Sum.inr j))) :=
    HasSum.sum (hasSum_fintype _) ENNReal.summable.hasSum
  rw [hh.tsum_eq]
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.sum_lt_top.mpr (fun i _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (basis_domain a w b p hp hs hm hM.eigenvectorBasis (Sum.inl i)))
  · have he (j : J) : ENNReal.ofReal (weights p M hM (Sum.inr j))*
        basisMoment a w (basis b hM.eigenvectorBasis (Sum.inr j)) =
        P*(ENNReal.ofReal (p (Sum.inr j))*basisMoment a w (b (Sum.inr j))) := by
      rw [basis_inr]
      change ENNReal.ofReal (p (Sum.inr j)/partition p M hM)*_ = _
      rw [ENNReal.ofReal_div_of_pos (partition_pos p hp hs M hM), div_eq_mul_inv]
      dsimp only [P]
      ac_rfl
    simp only [he, ENNReal.tsum_mul_left]
    exact ENNReal.mul_lt_top hP htail

end

variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [DecidableEq I] in
 theorem block_adjoint (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ) :
    (block b M).adjoint = block b M.conjTranspose := by
  classical
  simp only [block, map_sum, map_smulₛₗ, InnerProductSpace.adjoint_rankOne]
  rw [Finset.sum_comm]
  rfl

omit [DecidableEq I] in
 theorem block_symmetric (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ)
    (hM : M.IsHermitian) : (block b M).IsSymmetric := by
  rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric, isSelfAdjoint_iff]
  change (block b M).adjoint = block b M
  rw [block_adjoint, hM.eq]

omit [DecidableEq I] [CompleteSpace E] in
 theorem block_add (b : HilbertBasis (I ⊕ J) ℂ E) (M N : Matrix I I ℂ) :
    block b (M+N) = block b M+block b N := by
  simp [block, add_smul, Finset.sum_add_distrib]

omit [DecidableEq I] [CompleteSpace E] in
 theorem block_smul (b : HilbertBasis (I ⊕ J) ℂ E) (t : ℂ) (M : Matrix I I ℂ) :
    block b (t • M) = t • block b M := by
  simp [block, Finset.smul_sum, smul_smul]

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

 theorem expectation_block_eigen (σ : State n) (b : HilbertBasis (I ⊕ J) ℂ (Fock n))
    (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    (expectation σ (FiniteBlock.block b M)).re = ∑ i, hM.eigenvalues i*
      (inner ℂ (FiniteBlock.basis b hM.eigenvectorBasis (Sum.inl i))
        (σ.op (FiniteBlock.basis b hM.eigenvectorBasis (Sum.inl i)))).re := by
  let a := FiniteBlock.basis b hM.eigenvectorBasis
  have hh := (hasSum_expectation_basis a σ (FiniteBlock.block b M)).mapL Complex.reCLM
  have he (j : I ⊕ J) :
      (inner ℂ (a j) (FiniteBlock.block b M (σ.op (a j)))).re =
        Sum.elim (fun i => hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re)
          (fun _ => 0) j := by
    erw [← FiniteBlock.block_symmetric b M hM (a j) (σ.op (a j))]
    cases j with
    | inl i =>
      change (inner ℂ (FiniteBlock.block b M (FiniteBlock.basis b hM.eigenvectorBasis (Sum.inl i))) (σ.op (a (Sum.inl i)))).re = _
      rw [FiniteBlock.block_eigen b M hM i, inner_smul_left]
      simp [a]
    | inr j => simp [a, FiniteBlock.block_tail]
  have hz : HasSum (Sum.elim
      (fun i => hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re)
      (fun _ : J => (0:ℝ)))
      (∑ i, hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re) := by
    simpa only [Function.comp_def, Sum.elim_inl, add_zero] using HasSum.sum (f := Sum.elim (fun i => hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re) (fun _ : J => (0:ℝ))) (hasSum_fintype _) (hasSum_zero : HasSum (fun _ : J => (0:ℝ)) 0)
  exact (by simpa only [Complex.reCLM_apply, he] using hh : HasSum _ _).unique hz

 theorem expectation_block_diagonal (σ : State n) (b : HilbertBasis (I ⊕ J) ℂ (Fock n))
    (d : I → ℝ) :
    (expectation σ (FiniteBlock.block b (Matrix.diagonal (fun i => (d i : ℂ))))).re =
      ∑ i, d i*(inner ℂ (b (Sum.inl i)) (σ.op (b (Sum.inl i)))).re := by
  have hs : (Matrix.diagonal (fun i => (d i : ℂ))).IsHermitian := Matrix.isHermitian_diagonal_iff.mpr (by intro i; exact isSelfAdjoint_iff.mpr (Complex.conj_ofReal _))
  have he (j : I ⊕ J) :
      (inner ℂ (b j) (FiniteBlock.block b (Matrix.diagonal (fun i => (d i : ℂ))) (σ.op (b j)))).re =
        Sum.elim (fun i => d i*(inner ℂ (b (Sum.inl i)) (σ.op (b (Sum.inl i)))).re)
          (fun _ => 0) j := by
    erw [← FiniteBlock.block_symmetric b _ hs (b j) (σ.op (b j))]
    cases j with
    | inl i =>
      have hb : FiniteBlock.block b (Matrix.diagonal (fun i => (d i : ℂ))) (b (Sum.inl i)) =
          (d i : ℂ) • b (Sum.inl i) := by
        classical
        simp only [FiniteBlock.block, sum_apply, smul_apply,
          InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]
        simp [Matrix.diagonal_apply]
      change (inner ℂ (FiniteBlock.block b (Matrix.diagonal (fun i => (d i : ℂ))) (b (Sum.inl i))) (σ.op (b (Sum.inl i)))).re = _
      rw [hb, inner_smul_left]
      simp
    | inr j => simp [FiniteBlock.block_tail]
  have hh := (hasSum_expectation_basis b σ (FiniteBlock.block b (Matrix.diagonal (fun i => (d i : ℂ))))).mapL Complex.reCLM
  have hz := HasSum.sum (f := Sum.elim (fun i => d i*(inner ℂ (b (Sum.inl i)) (σ.op (b (Sum.inl i)))).re) (fun _ : J => (0:ℝ))) (hasSum_fintype (fun i => d i*(inner ℂ (b (Sum.inl i)) (σ.op (b (Sum.inl i)))).re))
    (hasSum_zero : HasSum (fun _ : J => (0:ℝ)) 0)
  exact (by simpa only [Complex.reCLM_apply, he] using hh : HasSum _ _).unique
    (by simpa only [Function.comp_def, Sum.elim_inl, add_zero] using hz)

end EntropyPhotonNumber

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator

namespace FiniteBlock
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
 theorem inner_block (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ) (x : E) (i : I) :
    inner ℂ (b (Sum.inl i)) (block b M x) = ∑ j, M i j*inner ℂ (b (Sum.inl j)) x := by
  classical
  simp [block, InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]

omit [CompleteSpace E] [DecidableEq I] in
 theorem inner_tail_block (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ) (x : E) (j : J) :
    inner ℂ (b (Sum.inr j)) (block b M x) = 0 := by
  simp [block, InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]

 omit [CompleteSpace E] [DecidableEq I] in
 theorem block_sub (b : HilbertBasis (I ⊕ J) ℂ E) (M N : Matrix I I ℂ) :
    block b (M-N) = block b M-block b N := by
  simp [block, sub_smul, Finset.sum_sub_distrib]

 theorem block_exp_eigen (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ)
    (hM : M.IsHermitian) (i : I) :
    block b (exp M) (basis b hM.eigenvectorBasis (Sum.inl i)) =
      (Real.exp (hM.eigenvalues i) : ℂ) • basis b hM.eigenvectorBasis (Sum.inl i) := by
  rw [basis_inl, block_embed, exp_eigenvector M hM i]
  simp only [WithLp.toLp_smul, WithLp.toLp_ofLp]
  change embed b ((Real.exp (hM.eigenvalues i) : ℂ) • hM.eigenvectorBasis i) = _
  exact map_smul (embed b) _ _

omit [CompleteSpace E] in
 theorem reference_on_block (b : HilbertBasis (I ⊕ J) ℂ E) (p : I ⊕ J → ℝ)
    (T : E →L[ℂ] E) (he : ∀ j, T (b j) = (p j : ℂ) • b j)
    (x : EuclideanSpace ℂ I) :
    T (embed b x) = block b (Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ))) (embed b x) := by
  rw [block_embed, embed_apply b x, map_sum, embed_apply]
  simp only [map_smul, he, smul_smul]
  simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply, ite_mul, mul_comm]

end FiniteBlock

namespace EntropyPhotonNumber

section
open QuantumTrace TraceEnsemble
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

 theorem expectation_block_matrix (σ : State n) (b : HilbertBasis (I ⊕ J) ℂ (Fock n))
    (M : Matrix I I ℂ) :
    expectation σ (FiniteBlock.block b M) =
      ∑ i, ∑ j, M i j*inner ℂ (b (Sum.inl j)) (σ.op (b (Sum.inl i))) := by
  have he (j : I ⊕ J) : inner ℂ (b j) (FiniteBlock.block b M (σ.op (b j))) =
      Sum.elim (fun i => ∑ k, M i k*inner ℂ (b (Sum.inl k)) (σ.op (b (Sum.inl i))))
        (fun _ => 0) j := by
    cases j with
    | inl i => exact FiniteBlock.inner_block b M _ i
    | inr j => exact FiniteBlock.inner_tail_block b M _ j
  have hh := hasSum_expectation_basis b σ (FiniteBlock.block b M)
  simp only [he] at hh
  have ht : HasSum (Sum.elim
      (fun i => ∑ k, M i k*inner ℂ (b (Sum.inl k)) (σ.op (b (Sum.inl i)))) (fun _ : J => (0:ℂ)))
      ((∑ i, ∑ k, M i k*inner ℂ (b (Sum.inl k)) (σ.op (b (Sum.inl i))))+0) :=
    HasSum.sum (hasSum_fintype _) hasSum_zero
  simpa only [add_zero] using hh.unique ht

 theorem blockState_operator (ρ : State n) (b : HilbertBasis (I ⊕ J) ℂ (Fock n))
    (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    (blockState b p hp hs M hM).op = ((FiniteBlock.partition p M hM : ℂ)⁻¹) •
      (ρ.op+FiniteBlock.block b (exp M)-FiniteBlock.block b (Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ)))) := by
  let a := FiniteBlock.basis b hM.eigenvectorBasis
  apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr a.dense_span)
  rintro _ ⟨j,rfl⟩
  change (spectralState a _ _ _).op (a j) = _
  rw [spectralState_eigen]
  simp only [smul_apply, sub_apply, add_apply]
  cases j with
  | inl i =>
    have ht : ρ.op (a (Sum.inl i)) =
        FiniteBlock.block b (Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ))) (a (Sum.inl i)) := by
      simpa only [a, FiniteBlock.basis_inl] using
        FiniteBlock.reference_on_block b p ρ.op he (hM.eigenvectorBasis i)
    rw [ht, add_sub_cancel_left]
    rw [FiniteBlock.block_exp_eigen b M hM i, smul_smul]
    congr 1
    simp only [FiniteBlock.weights, Sum.elim_inl]
    push_cast
    ring
  | inr j =>
    simp only [a, FiniteBlock.basis_inr, he, FiniteBlock.block_tail, add_zero, sub_zero,
      smul_smul, FiniteBlock.weights, Sum.elim_inr]
    push_cast
    congr 1
    ring

end

section
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

theorem block_crossEntropy (σ : State n) (b : HilbertBasis (I ⊕ J) ℂ (Fock n))
    (p : I ⊕ J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (hc : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re))
    (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    HasSum (fun j => (-Real.log (FiniteBlock.weights p M hM j))*
      (inner ℂ (FiniteBlock.basis b hM.eigenvectorBasis j)
        (σ.op (FiniteBlock.basis b hM.eigenvectorBasis j))).re)
      (crossEntropy b p σ+
        (expectation σ (FiniteBlock.block b (Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ))))).re-
        (expectation σ (FiniteBlock.block b M)).re+Real.log (FiniteBlock.partition p M hM)) := by
  let a := FiniteBlock.basis b hM.eigenvectorBasis
  let C := ∑' j, (-Real.log (p (Sum.inr j)))*(inner ℂ (b (Sum.inr j)) (σ.op (b (Sum.inr j)))).re
  have ht : HasSum (fun j => (-Real.log (p (Sum.inr j)))*
      (inner ℂ (b (Sum.inr j)) (σ.op (b (Sum.inr j)))).re) C :=
    (hc.comp_injective Sum.inr_injective).hasSum
  have ho : HasSum (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re)
      ((∑ i, (-Real.log (p (Sum.inl i)))*(inner ℂ (b (Sum.inl i)) (σ.op (b (Sum.inl i)))).re)+C) :=
    HasSum.sum (hasSum_fintype _) ht
  have hC : C = crossEntropy b p σ+
      (expectation σ (FiniteBlock.block b (Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ))))).re := by
    have hh := ho.unique hc.hasSum
    rw [expectation_block_diagonal]
    dsimp only [crossEntropy]
    simp only [neg_mul, Finset.sum_neg_distrib] at hh ⊢
    linarith
  have h0 : HasSum (Sum.elim (fun _ : I => (0:ℝ))
      (fun j => (-Real.log (p (Sum.inr j)))*(inner ℂ (b (Sum.inr j)) (σ.op (b (Sum.inr j)))).re)) C := by
    simpa only [Function.comp_def, Sum.elim_inr, zero_add] using HasSum.sum (f := Sum.elim (fun _ : I => (0:ℝ)) (fun j => (-Real.log (p (Sum.inr j)))*(inner ℂ (b (Sum.inr j)) (σ.op (b (Sum.inr j)))).re)) (hasSum_zero : HasSum (fun _ : I => (0:ℝ)) 0) ht
  have h1 : HasSum (Sum.elim
      (fun i => hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re)
      (fun _ : J => (0:ℝ))) (expectation σ (FiniteBlock.block b M)).re := by
    rw [expectation_block_eigen]
    simpa only [Function.comp_def, Sum.elim_inl, add_zero] using HasSum.sum (f := Sum.elim (fun i => hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re) (fun _ : J => (0:ℝ))) (hasSum_fintype
      (fun i => hM.eigenvalues i*(inner ℂ (a (Sum.inl i)) (σ.op (a (Sum.inl i)))).re))
      (hasSum_zero : HasSum (fun _ : J => (0:ℝ)) 0)
  have h2 := (hasSum_trace_basis (numberBasis n) a σ.positive (trace_one_numberBasis σ)).mul_left
    (Real.log (FiniteBlock.partition p M hM))
  have hh := (h0.sub h1).add h2
  rw [mul_one, hC] at hh
  convert! hh using 1
  funext j
  cases j with
  | inl i =>
    simp only [FiniteBlock.weights, Sum.elim_inl,
      Real.log_div (Real.exp_pos _).ne' (FiniteBlock.partition_pos p hp hs M hM).ne', Real.log_exp]
    ring
  | inr j =>
    simp only [FiniteBlock.weights, Sum.elim_inr,
      Real.log_div (hp _).ne' (FiniteBlock.partition_pos p hp hs M hM).ne', a, FiniteBlock.basis_inr]
    ring

theorem block_relativeEntropy_lower (σ : State n) (hσ : FiniteEnergy σ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (hc : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re))
    (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    (expectation σ (FiniteBlock.block b M)).re-
      (expectation σ (FiniteBlock.block b (Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ))))).re-
      Real.log (FiniteBlock.partition p M hM) ≤ relativeEntropy b p σ := by
  have ht := block_crossEntropy σ b p hp hs hc M hM
  have hK := (entropy_le_crossEntropy (blockState b p hp hs M hM) σ hσ _ _
    (FiniteBlock.weights_pos p hp hs M hM) (FiniteBlock.weights_hasSum p hp hs M hM)
    (spectralState_eigen _ _ _ _) ht.summable).1
  change entropy σ ≤ ∑' j, _ at hK
  rw [ht.tsum_eq] at hK
  dsimp only [relativeEntropy]
  linarith

end

open QuantumTrace TraceEnsemble
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

 theorem blockState_finiteMoment (ρ : State n) {m : ℕ} (hm : FiniteMoment m ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    FiniteMoment m (blockState b p hp hs M hM) := by
  rw [finiteMoment_iff] at hm ⊢
  have ht := FiniteBlock.tilted_moment_finite (numberBasis n)
    (fun k => (1+(totalNumber k : ℝ≥0∞))^m) b p hp hs ?_ M hM
  · simpa only [powerMoment, TensorLp.matrixMoment, basisExpectation,
      numberBasis_apply, numberKet, blockState, spectralState] using ht
  · rw [diagonalVector_operator b p (fun j => (hp j).le) hs.summable ρ.op he]
    simpa only [powerMoment, TensorLp.matrixMoment, basisExpectation,
      numberBasis_apply, numberKet] using hm

omit [Fintype I] [DecidableEq I] in
 theorem crossEntropy_self_summable (ρ : State n) (hρ : FiniteEnergy ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) :
    Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (ρ.op (b j))).re) := by
  have h := hasSum_entropy_eigenvalues (numberBasis n) b ρ.positive
    (trace_one_numberBasis ρ) p he (entropy_hasSum ρ hρ)
  convert h.summable using 1
  funext j
  rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  simp [Real.negMulLog]
  ring

 theorem blockState_crossEntropy_finite (ρ : State n) (hρ : FiniteEnergy ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    Summable (fun j => (-Real.log (p j))*
      (inner ℂ (b j) ((blockState b p hp hs M hM).op (b j))).re) := by
  have hc := (crossEntropy_self_summable ρ hρ b p he).comp_injective Sum.inr_injective
  apply Summable.sum _ (hasSum_fintype _).summable
  apply (hc.div_const (FiniteBlock.partition p M hM)).congr
  intro j
  dsimp only [Function.comp_def]
  rw [blockState_operator ρ b p hp hs he M hM]
  simp only [smul_apply, sub_apply, add_apply, FiniteBlock.block_tail, add_zero, sub_zero,
    inner_smul_right, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  ring

 theorem blockState_relativeEntropy (ρ : State n) (hρ : FiniteEnergy ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian)
    (hσ : FiniteEnergy (blockState b p hp hs M hM)) :
    relativeEntropy b p (blockState b p hp hs M hM) =
      (expectation (blockState b p hp hs M hM) (FiniteBlock.block b M)).re-
      (expectation (blockState b p hp hs M hM)
        (FiniteBlock.block b (Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ))))).re-
      Real.log (FiniteBlock.partition p M hM) := by
  have hc := block_crossEntropy (blockState b p hp hs M hM) b p hp hs
    (blockState_crossEntropy_finite ρ hρ b p hp hs he M hM) M hM
  have hh := crossEntropy_self (blockState b p hp hs M hM) hσ
    (FiniteBlock.basis b hM.eigenvectorBasis) (FiniteBlock.weights p M hM)
    (spectralState_eigen _ _ _ _)
  change (∑' j, _) = _ at hh
  rw [hc.tsum_eq] at hh
  dsimp only [relativeEntropy]
  linarith

 theorem blockState_block_entry (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian)
    (i j : I) :
    inner ℂ (b (Sum.inl i)) ((blockState b p hp hs M hM).op (b (Sum.inl j))) =
      exp M i j/(FiniteBlock.partition p M hM : ℂ) := by
  rw [blockState_operator ρ b p hp hs he M hM]
  simp only [smul_apply, sub_apply, add_apply, inner_smul_right, inner_sub_right, inner_add_right,
    he, inner_smul_right, FiniteBlock.inner_block]
  simp [orthonormal_iff_ite.mp b.orthonormal, Matrix.diagonal_apply,
    mul_ite, div_eq_mul_inv, mul_comm]
  by_cases h : i = j <;> simp [h]

 theorem blockState_block_expectation (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian)
    (Z : Matrix I I ℂ) :
    expectation (blockState b p hp hs M hM) (FiniteBlock.block b Z) =
      Matrix.trace (Z*exp M)/(FiniteBlock.partition p M hM : ℂ) := by
  rw [expectation_block_matrix]
  simp only [blockState_block_entry ρ b p hp hs he M hM, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Finset.sum_div, mul_div_assoc]

end EntropyPhotonNumber

end

section
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace

namespace QuantumCalculus

section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

theorem exp_sub_eq_integral (a b : A) :
    exp b - exp a = ∫ s in (0 : ℝ)..1, exp ((1-s) • a) * (b-a) * exp (s • b) := by
  have hd (s : ℝ) : HasDerivAt (fun t : ℝ => exp ((1-t) • a) * exp (t • b))
      (exp ((1-s) • a) * (b-a) * exp (s • b)) s := by
    have hleft : HasDerivAt (fun t : ℝ => exp ((1-t) • a))
        (-(exp ((1-s) • a) * a)) s := by
      simpa [Function.comp_def] using (hasDerivAt_exp_smul_const a (1-s)).scomp s
        ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s))
    have hright := hasDerivAt_exp_smul_const' b s
    have heq : exp ((1-s) • a) * (b-a) * exp (s • b) =
        -(exp ((1-s) • a) * a) * exp (s • b) +
          exp ((1-s) • a) * (b * exp (s • b)) := by noncomm_ring
    rw [heq]
    exact hleft.mul hright
  have hc : Continuous (fun s : ℝ => exp ((1-s) • a) * (b-a) * exp (s • b)) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 1)
  simpa using h.symm

theorem exp_add_smul_sub (a z : A) (t : ℝ) :
    exp (a+t • z) - exp a =
      t • (∫ s in (0 : ℝ)..1, exp ((1-s) • a) * z * exp (s • (a+t • z))) := by
  rw [exp_sub_eq_integral, ← intervalIntegral.integral_smul]
  congr 1
  funext s
  simp

theorem continuous_duhamel (a z : A) :
    Continuous (fun t : ℝ =>
      ∫ s in (0 : ℝ)..1, exp ((1-s) • a) * z * exp (s • (a+t • z))) := by
  have hc : Continuous (Function.uncurry (fun t s : ℝ =>
      exp ((1-s) • a) * z * exp (s • (a+t • z)))) := by fun_prop
  have hh := continuous_parametric_integral_of_continuous (μ := volume) hc (s := Set.Icc (0:ℝ) 1) isCompact_Icc
  convert! hh using 1
  funext t
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]

theorem hasDerivAt_exp_add_smul_zero (a z : A) :
    HasDerivAt (fun t : ℝ => exp (a+t • z))
      (∫ s in (0 : ℝ)..1, exp ((1-s) • a) * z * exp (s • a)) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hc := (continuous_duhamel a z).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] (0:ℝ) ≤ 𝓝 0)
  apply Filter.Tendsto.congr' ?_ (by simpa only [zero_smul, add_zero] using hc)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  rw [slope_def_module]
  simp only [zero_smul, add_zero, sub_zero, exp_add_smul_sub, smul_smul, inv_mul_cancel₀ ht0,
    one_smul]

theorem hasDerivAt_exp_add_smul (a z : A) (t : ℝ) :
    HasDerivAt (fun u : ℝ => exp (a+u • z))
      (∫ s in (0 : ℝ)..1, exp ((1-s) • (a+t • z)) * z * exp (s • (a+t • z))) t := by
  have hh := (hasDerivAt_exp_add_smul_zero (a+t • z) z).scomp_of_eq t
    ((hasDerivAt_id t).sub_const t) (by simp)
  convert! hh using 1
  · funext u
    simp [sub_smul]
  · simp

end

section
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

theorem trace_duhamel (τ : A →L[ℝ] ℝ) (hτ : ∀ x y, τ (x*y) = τ (y*x))
    (a z : A) :
    τ (∫ s in (0 : ℝ)..1, exp ((1-s) • a) * z * exp (s • a)) = τ (exp a * z) := by
  have hc : Continuous (fun s : ℝ => exp ((1-s) • a) * z * exp (s • a)) := by fun_prop
  rw [← τ.intervalIntegral_comp_comm (hc.intervalIntegrable 0 1)]
  have heq (s : ℝ) : τ (exp ((1-s) • a) * z * exp (s • a)) = τ (exp a * z) := by
    rw [hτ, ← mul_assoc, ← exp_add_of_commute
      (((Commute.refl a).smul_left s).smul_right (1-s)), ← add_smul]
    simp
  simp_rw [heq]
  simp

theorem hasDerivAt_trace_exp (τ : A →L[ℝ] ℝ) (hτ : ∀ x y, τ (x*y) = τ (y*x))
    (a z : A) (t : ℝ) :
    HasDerivAt (fun u : ℝ => τ (exp (a+u • z))) (τ (exp (a+t • z)*z)) t := by
  have hh := τ.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_add_smul a z t)
  simpa only [Function.comp_def, trace_duhamel τ hτ] using hh

theorem hasDerivAt_trace_exp_mul (τ : A →L[ℝ] ℝ)
    (a z : A) (t : ℝ) :
    HasDerivAt (fun u : ℝ => τ (exp (a+u • z)*z))
      (τ ((∫ s in (0 : ℝ)..1,
         exp ((1-s) • (a+t • z))*z*exp (s • (a+t • z)))*z)) t := by
  exact τ.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_exp_add_smul a z t).mul_const z)

end

section
open scoped Matrix.Norms.Operator ComplexConjugate
open Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def matrixReTrace : Matrix I I ℂ →L[ℝ] ℝ :=
  Complex.reCLM.comp (Matrix.traceLinearMap I ℝ ℂ).toContinuousLinearMap

omit [DecidableEq I] in
@[simp] theorem matrixReTrace_apply (M : Matrix I I ℂ) :
    matrixReTrace M = (Matrix.trace M).re := rfl

omit [DecidableEq I] in
theorem matrixReTrace_cyclic (M N : Matrix I I ℂ) :
    matrixReTrace (M*N) = matrixReTrace (N*M) := by
  simp only [matrixReTrace_apply, Matrix.trace_mul_comm M N]

theorem exp_real_diagonal (v : I → ℝ) (s : ℝ) :
    exp (s • Matrix.diagonal (fun i => (v i : ℂ))) =
      Matrix.diagonal (fun i => (Real.exp (s*v i) : ℂ)) := by
  rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 1
  funext i
  simp [← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp]

theorem matrix_duhamel_integrand (v : I → ℝ) (Z : Matrix I I ℂ)
    (hZ : Z.IsHermitian) (s : ℝ) :
    matrixReTrace (exp ((1-s) • Matrix.diagonal (fun i => (v i : ℂ))) * Z *
      exp (s • Matrix.diagonal (fun i => (v i : ℂ))) * Z) =
        ∑ i, ∑ j, Real.exp ((1-s)*v i+s*v j) * Complex.normSq (Z i j) := by
  rw [exp_real_diagonal, exp_real_diagonal, matrixReTrace_apply]
  have heq :
      (Matrix.diagonal (fun i => (↑(Real.exp ((1-s)*v i)) : ℂ)) * Z *
         Matrix.diagonal (fun i => (↑(Real.exp (s*v i)) : ℂ)) * Z).trace =
      ∑ i, ∑ j, (↑(Real.exp ((1-s)*v i)) : ℂ) * Z i j *
        ↑(Real.exp (s*v j)) * Z j i := by
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [heq]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hZ.apply j i, Real.exp_add]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

theorem matrix_duhamel_hessian (p : I → ℝ) (hp : ∀ i, 0 < p i)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) :
    matrixReTrace ((∫ s in (0 : ℝ)..1,
      exp ((1-s) • Matrix.diagonal (fun i => (Real.log (p i) : ℂ))) * Z *
      exp (s • Matrix.diagonal (fun i => (Real.log (p i) : ℂ)))) * Z) =
        ∑ i, ∑ j, DiagonalForms.System.logMean (p i) (p j) * Complex.normSq (Z i j) := by
  let a : Matrix I I ℂ := Matrix.diagonal (fun i => (Real.log (p i) : ℂ))
  have hc : Continuous (fun s : ℝ => exp ((1-s) • a) * Z * exp (s • a)) := by fun_prop
  have hm := ((ContinuousLinearMap.mul ℝ (Matrix I I ℂ)).flip Z).intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := volume) 0 1)
  change (∫ s in (0:ℝ)..1, (exp ((1-s) • a)*Z*exp (s • a))*Z) =
    (∫ s in (0:ℝ)..1, exp ((1-s) • a)*Z*exp (s • a))*Z at hm
  change matrixReTrace ((∫ s in (0:ℝ)..1, exp ((1-s) • a)*Z*exp (s • a))*Z) = _
  rw [← hm]
  have hc' : Continuous (fun s : ℝ => exp ((1-s) • a)*Z*exp (s • a)*Z) :=
    hc.mul continuous_const
  trans ∫ s in (0:ℝ)..1, matrixReTrace (exp ((1-s) • a)*Z*exp (s • a)*Z)
  · exact (matrixReTrace.intervalIntegral_comp_comm
      (hc'.intervalIntegrable (μ := volume) 0 1)).symm
  simp_rw [a, matrix_duhamel_integrand _ Z hZ]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_mul_const, integral_exp_affine_log (hp i) (hp j)]
    · intro j _
      exact (by fun_prop : Continuous (fun s : ℝ =>
        Real.exp ((1-s)*Real.log (p i)+s*Real.log (p j))*Complex.normSq (Z i j))).intervalIntegrable 0 1
  · intro i _
    apply Continuous.intervalIntegrable
    fun_prop

end

section
open Filter Asymptotics

theorem quadratic_expansion {f f' : ℝ → ℝ} {d : ℝ}
    (hff' : ∀ᶠ t in 𝓝 (0:ℝ), HasDerivAt f (f' t) t)
    (hd : HasDerivAt f' d 0) :
    (fun t => f t-f 0-f' 0*t-d/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp hff'
  let R : ℝ → ℝ := fun t => f t-f 0-f' 0*t-d/2*t^2
  let R' : ℝ → ℝ := fun t => f' t-f' 0-d*t
  have he : R' =o[𝓝 (0:ℝ)] (fun t => t) := by
    simpa only [R', sub_zero, smul_eq_mul, mul_comm d] using hd.isLittleO
  have hs := (convex_ball (0:ℝ) δ).isLittleO_pow_succ_real
    (Metric.mem_ball_self hδ) (n := 1) (f := R) (f' := R') ?_ ?_
  · have hn : 𝓝[Metric.ball (0:ℝ) δ] (0:ℝ) = 𝓝 0 :=
      nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds 0 hδ)
    simpa [R, hn] using hs
  · intro t ht
    have hf := hh ht
    have hpoly := ((hasDerivAt_const t (f' 0)).mul (hasDerivAt_id t))
    have hquad := ((hasDerivAt_id t).pow 2).const_mul (d/2)
    convert (((hf.sub_const (f 0)).sub hpoly).sub hquad).hasDerivWithinAt using 1
    · funext u
      dsimp [R]
    · dsimp [R']
      ring
  · simpa only [sub_zero, pow_one] using he.mono nhdsWithin_le_nhds

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

theorem log_partition_expansion (τ : A →L[ℝ] ℝ)
    (hτ : ∀ x y, τ (x*y) = τ (y*x)) (a z : A) (c : ℝ)
    (hn : c+τ (exp a) = 1) :
    (fun t : ℝ => Real.log (c+τ (exp (a+t • z))) -
      τ (exp a*z)*t -
      (τ ((∫ s in (0:ℝ)..1, exp ((1-s) • a)*z*exp (s • a))*z) -
        (τ (exp a*z))^2)/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
  let P : ℝ → ℝ := fun t => c+τ (exp (a+t • z))
  let M : ℝ → ℝ := fun t => τ (exp (a+t • z)*z)
  have hP (t : ℝ) : HasDerivAt P (M t) t := (hasDerivAt_trace_exp τ hτ a z t).const_add c
  have hP0 : P 0 = 1 := by simpa [P] using hn
  have hnz : ∀ᶠ t in 𝓝 (0:ℝ), P t ≠ 0 :=
    (hP 0).continuousAt.eventually_ne (by simp [hP0])
  have hlog : ∀ᶠ t in 𝓝 (0:ℝ),
      HasDerivAt (fun t => Real.log (P t)) (M t/P t) t := by
    filter_upwards [hnz] with t ht using (hP t).log ht
  have hd := (hasDerivAt_trace_exp_mul τ a z 0).div (hP 0) (by simp [hP0])
  have hd' : HasDerivAt (fun t => M t/P t)
      (τ ((∫ s in (0:ℝ)..1, exp ((1-s) • a)*z*exp (s • a))*z) -
        (τ (exp a*z))^2) 0 := by
    convert hd using 1
    first | rfl |
      simp only [M, zero_smul, add_zero, hP0, mul_one, div_one, pow_two]
  have hh := quadratic_expansion hlog hd'
  simpa only [P, M, zero_smul, add_zero, hn, Real.log_one, sub_zero, div_one] using hh

end

section
open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem finite_block_partition_expansion (p : I → ℝ) (hp : ∀ i, 0 < p i)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (c : ℝ)
    (hn : c + ∑ i, p i = 1) :
    (fun t : ℝ => Real.log (c + matrixReTrace
        (exp (Matrix.diagonal (fun i => (Real.log (p i) : ℂ)) + t • Z))) -
      (∑ i, p i*(Z i i).re)*t -
      ((∑ i, ∑ j, DiagonalForms.System.logMean (p i) (p j) * Complex.normSq (Z i j)) -
        (∑ i, p i*(Z i i).re)^2)/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
  let a := Matrix.diagonal (fun i => (Real.log (p i) : ℂ))
  have hea : exp a = Matrix.diagonal (fun i => (p i : ℂ)) := by
    simpa only [one_smul, one_mul, Real.exp_log (hp _)] using
      exp_real_diagonal (fun i => Real.log (p i)) 1
  have htr : matrixReTrace (exp a) = ∑ i, p i := by
    rw [hea, matrixReTrace_apply, Matrix.trace_diagonal]
    simp
  have hm : matrixReTrace (exp a*Z) = ∑ i, p i*(Z i i).re := by
    rw [hea, matrixReTrace_apply]
    simp [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  have hh := log_partition_expansion (matrixReTrace (I := I)) matrixReTrace_cyclic a Z c
    (by erw [htr]; exact hn)
  erw [hm, matrix_duhamel_hessian p hp Z hZ] at hh
  exact hh

end

section
open Filter Asymptotics
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
local instance : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A

theorem relative_partition_expansion (τ : A →L[ℝ] ℝ)
    (hτ : ∀ x y, τ (x*y) = τ (y*x)) (a z : A) (c : ℝ)
    (hn : c+τ (exp a) = 1) :
    (fun t : ℝ => t*(τ (exp (a+t • z)*z)/(c+τ (exp (a+t • z))))-
      Real.log (c+τ (exp (a+t • z)))-
      (τ ((∫ s in (0:ℝ)..1, exp ((1-s) • a)*z*exp (s • a))*z)-
        (τ (exp a*z))^2)/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
  let P : ℝ → ℝ := fun t => c+τ (exp (a+t • z))
  let M : ℝ → ℝ := fun t => τ (exp (a+t • z)*z)
  let d : ℝ := τ ((∫ s in (0:ℝ)..1, exp ((1-s) • a)*z*exp (s • a))*z)-
    (τ (exp a*z))^2
  have hP (t : ℝ) : HasDerivAt P (M t) t := (hasDerivAt_trace_exp τ hτ a z t).const_add c
  have hP0 : P 0 = 1 := by simpa [P] using hn
  have hd := (hasDerivAt_trace_exp_mul τ a z 0).div (hP 0) (by simp [hP0])
  have hd' : HasDerivAt (fun t => M t/P t) d 0 := by
    convert hd using 1
    first | rfl |
      simp only [d, M, zero_smul, add_zero, hP0, mul_one, div_one, pow_two]
  have he : (fun t => M t/P t-M 0-d*t) =o[𝓝 (0:ℝ)] (fun t => t) := by
    simpa only [hP0, div_one, sub_zero, smul_eq_mul, mul_comm d] using hd'.isLittleO
  have he2 : (fun t => (M t/P t-M 0-d*t)*t) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
    simpa only [pow_two] using he.mul_isBigO (isBigO_refl (fun t : ℝ => t) (𝓝 0))
  have hq := log_partition_expansion τ hτ a z c hn
  have hh := he2.sub hq
  convert! hh using 1
  · funext t
    dsimp only [P, M, d]
    simp only [zero_smul, add_zero]
    ring

end

open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

 theorem finite_block_relative_expansion (p : I → ℝ) (hp : ∀ i, 0 < p i)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (c : ℝ)
    (hn : c + ∑ i, p i = 1) :
    (fun t : ℝ => t*(matrixReTrace
        (exp (Matrix.diagonal (fun i => (Real.log (p i) : ℂ))+t • Z)*Z)/
        (c+matrixReTrace (exp (Matrix.diagonal (fun i => (Real.log (p i) : ℂ))+t • Z))))-
      Real.log (c+matrixReTrace (exp (Matrix.diagonal (fun i => (Real.log (p i) : ℂ))+t • Z)))-
      ((∑ i, ∑ j, DiagonalForms.System.logMean (p i) (p j) * Complex.normSq (Z i j)) -
        (∑ i, p i*(Z i i).re)^2)/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
  let a := Matrix.diagonal (fun i => (Real.log (p i) : ℂ))
  have hea : exp a = Matrix.diagonal (fun i => (p i : ℂ)) := by
    simpa only [one_smul, one_mul, Real.exp_log (hp _)] using
      exp_real_diagonal (fun i => Real.log (p i)) 1
  have htr : matrixReTrace (exp a) = ∑ i, p i := by
    rw [hea, matrixReTrace_apply, Matrix.trace_diagonal]
    simp
  have hm : matrixReTrace (exp a*Z) = ∑ i, p i*(Z i i).re := by
    rw [hea, matrixReTrace_apply]
    simp [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  have hh := relative_partition_expansion (matrixReTrace (I := I)) matrixReTrace_cyclic a Z c
    (by erw [htr]; exact hn)
  erw [hm, matrix_duhamel_hessian p hp Z hZ] at hh
  exact hh

end QuantumCalculus

namespace FiniteBlock
open QuantumCalculus
variable {I J : Type*} [Fintype I] [DecidableEq I]

def tiltMatrix (p : I ⊕ J → ℝ) (Z : Matrix I I ℂ) (t : ℝ) : Matrix I I ℂ :=
  Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ))+t • Z

omit [Fintype I] in
 theorem tiltMatrix_hermitian (p : I ⊕ J → ℝ) (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (t : ℝ) :
    (tiltMatrix p Z t).IsHermitian := by
  exact (Matrix.isHermitian_diagonal_iff.mpr
    (by intro i; exact isSelfAdjoint_iff.mpr (Complex.conj_ofReal _))).add
      (hZ.smul (isSelfAdjoint_iff.mpr rfl))

 theorem partition_trace (p : I ⊕ J → ℝ) (M : Matrix I I ℂ) (hM : M.IsHermitian) :
    partition p M hM = (∑' j, p (Sum.inr j))+matrixReTrace (exp M) := by
  rw [matrixReTrace_apply, trace_exp]
  rfl

omit [DecidableEq I] in
 theorem tail_normalization (p : I ⊕ J → ℝ) (hs : HasSum p 1) :
    (∑' j, p (Sum.inr j)) + ∑ i, p (Sum.inl i) = 1 := by
  have hh := HasSum.sum (f := p) (hasSum_fintype (fun i => p (Sum.inl i)))
    (hs.summable.comp_injective Sum.inr_injective).hasSum
  rw [add_comm]
  exact hh.unique hs

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumCalculus QuantumTrace Filter Asymptotics
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

def blockTilt (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1) (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (t : ℝ) : State n :=
  blockState b p hp hs (FiniteBlock.tiltMatrix p Z t) (FiniteBlock.tiltMatrix_hermitian p Z hZ t)

 theorem blockTilt_relativeEntropy (ρ : State n) (hρ : FiniteEnergy ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (t : ℝ)
    (ht : FiniteEnergy (blockTilt b p hp hs Z hZ t)) :
    relativeEntropy b p (blockTilt b p hp hs Z hZ t) =
      t*(matrixReTrace (exp (FiniteBlock.tiltMatrix p Z t)*Z)/
        ((∑' j, p (Sum.inr j))+matrixReTrace (exp (FiniteBlock.tiltMatrix p Z t))))-
      Real.log ((∑' j, p (Sum.inr j))+matrixReTrace (exp (FiniteBlock.tiltMatrix p Z t))) := by
  rw [blockTilt, blockState_relativeEntropy ρ hρ b p hp hs he _ _ ht]
  have hsZ : t • Z = (t : ℂ) • Z := by ext i j; simp
  rw [show FiniteBlock.block b (FiniteBlock.tiltMatrix p Z t) =
      FiniteBlock.block b (Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ)))+
      (t:ℂ) • FiniteBlock.block b Z by
        rw [FiniteBlock.tiltMatrix, FiniteBlock.block_add, hsZ, FiniteBlock.block_smul]]
  rw [expectation_add, expectation_smul]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [blockState_block_expectation ρ b p hp hs he _ _ Z]
  rw [Matrix.trace_mul_comm Z, Complex.div_ofReal_re,
    FiniteBlock.partition_trace]
  simp only [matrixReTrace_apply]
  ring

 theorem blockTilt_relativeEntropy_expansion (ρ : State n) (hρ : FiniteEnergy ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian)
    (ht : ∀ t, FiniteEnergy (blockTilt b p hp hs Z hZ t)) :
    (fun t : ℝ => relativeEntropy b p (blockTilt b p hp hs Z hZ t)-
      ((∑ i, ∑ j, DiagonalForms.System.logMean (p (Sum.inl i)) (p (Sum.inl j)) * Complex.normSq (Z i j)) -
        (∑ i, p (Sum.inl i)*(Z i i).re)^2)/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
  simp_rw [blockTilt_relativeEntropy ρ hρ b p hp hs he Z hZ _ (ht _), FiniteBlock.tiltMatrix]
  exact finite_block_relative_expansion _ (fun i => hp (Sum.inl i)) Z hZ _
    (FiniteBlock.tail_normalization p hs)

 theorem blockTilt_finiteMoment (ρ : State n) {m : ℕ} (hm : FiniteMoment m ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (t : ℝ) :
    FiniteMoment m (blockTilt b p hp hs Z hZ t) :=
  blockState_finiteMoment ρ hm b p hp hs he _ _

 theorem blockTilt_relativeEntropy_expansion_of_moment (ρ : State n) (hm : FiniteMoment 4 ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) :
    (fun t : ℝ => relativeEntropy b p (blockTilt b p hp hs Z hZ t)-
      ((∑ i, ∑ j, DiagonalForms.System.logMean (p (Sum.inl i)) (p (Sum.inl j)) * Complex.normSq (Z i j)) -
        (∑ i, p (Sum.inl i)*(Z i i).re)^2)/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2) :=
  blockTilt_relativeEntropy_expansion ρ (finiteMoment_finiteEnergy (by norm_num) hm)
    b p hp hs he Z hZ (fun t => finiteMoment_finiteEnergy (by norm_num)
      (blockTilt_finiteMoment ρ hm b p hp hs he Z hZ t))

 theorem block_relativeEntropy_tilt_lower (σ : State n) (hσ : FiniteEnergy σ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (hc : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re))
    (Z : Matrix I I ℂ) (hZ : Z.IsHermitian) (t : ℝ) :
    t*(expectation σ (FiniteBlock.block b Z)).re-
      Real.log ((∑' j, p (Sum.inr j))+matrixReTrace (exp (FiniteBlock.tiltMatrix p Z t))) ≤
      relativeEntropy b p σ := by
  have hh := block_relativeEntropy_lower σ hσ b p hp hs hc
    (FiniteBlock.tiltMatrix p Z t) (FiniteBlock.tiltMatrix_hermitian p Z hZ t)
  have hsZ : t • Z = (t : ℂ) • Z := by ext i j; simp
  rw [show FiniteBlock.block b (FiniteBlock.tiltMatrix p Z t) =
      FiniteBlock.block b (Matrix.diagonal (fun i => (Real.log (p (Sum.inl i)) : ℂ)))+
      (t:ℂ) • FiniteBlock.block b Z by
        rw [FiniteBlock.tiltMatrix, FiniteBlock.block_add, hsZ, FiniteBlock.block_smul],
    expectation_add, expectation_smul] at hh
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hh
  rw [FiniteBlock.partition_trace] at hh
  linarith

end EntropyPhotonNumber

namespace FiniteBlock
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
 theorem block_basis (b : HilbertBasis (I ⊕ J) ℂ E) (M : Matrix I I ℂ) (j : I) :
    block b M (b (Sum.inl j)) = ∑ i, M i j • b (Sum.inl i) := by
  simp [block, InnerProductSpace.rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]

def entries (b : HilbertBasis (I ⊕ J) ℂ E) (Z : E →L[ℂ] E) : Matrix I I ℂ :=
  fun i j => inner ℂ (b (Sum.inl i)) (Z (b (Sum.inl j)))

omit [CompleteSpace E] [DecidableEq I] in
 theorem trace_block_bounded (b : HilbertBasis (I ⊕ J) ℂ E) (A : Matrix I I ℂ)
    (Z : E →L[ℂ] E) :
    HasSum (fun j => inner ℂ (b j) (Z (block b A (b j))))
      (Matrix.trace (A * entries b Z)) := by
  classical
  have he (j : I ⊕ J) : inner ℂ (b j) (Z (block b A (b j))) =
      Sum.elim (fun j => ∑ i, A i j*inner ℂ (b (Sum.inl j)) (Z (b (Sum.inl i)))) (fun _ => 0) j := by
    cases j with
    | inl j => simp [block_basis]
    | inr j => simp only [block_tail, map_zero, inner_zero_right, Sum.elim_inr]
  simp_rw [he]
  have h := HasSum.sum (f := Sum.elim (fun j => ∑ i, A i j*inner ℂ (b (Sum.inl j)) (Z (b (Sum.inl i)))) (fun _ : J => (0:ℂ)))
    (hasSum_fintype _) (hasSum_zero : HasSum (fun _ : J => (0:ℂ)) 0)
  have heq : (∑ j, ∑ i, A i j * inner ℂ (b (Sum.inl j)) (Z (b (Sum.inl i)))) =
      Matrix.trace (A * entries b Z) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, entries]
    exact Finset.sum_comm
  simpa only [Function.comp_def, Sum.elim_inl, add_zero, heq] using h

end FiniteBlock

namespace EntropyPhotonNumber
open QuantumTrace
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

 theorem blockState_expectation (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (M : Matrix I I ℂ) (hM : M.IsHermitian)
    (Z : Fock n →L[ℂ] Fock n) :
    expectation (blockState b p hp hs M hM) Z =
      (expectation ρ Z + Matrix.trace ((exp M-Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ)))*
        FiniteBlock.entries b Z))/(FiniteBlock.partition p M hM : ℂ) := by
  have hρ := hasSum_expectation_basis b ρ Z
  have hA := FiniteBlock.trace_block_bounded b
    (exp M-Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ))) Z
  have hσ := hasSum_expectation_basis b (blockState b p hp hs M hM) Z
  rw [blockState_operator ρ b p hp hs he M hM] at hσ
  simp only [smul_apply, sub_apply, add_apply, map_smul, map_sub, map_add,
    inner_smul_right, inner_sub_right, inner_add_right] at hσ
  have hh := (hρ.add hA).mul_left ((FiniteBlock.partition p M hM : ℂ)⁻¹)
  simp only [FiniteBlock.block_sub, sub_apply, map_sub, inner_sub_right] at hh
  apply hσ.unique
  rw [div_eq_mul_inv, mul_comm]
  convert! hh using 1
  funext j
  ring

end EntropyPhotonNumber

namespace QuantumCalculus
open Matrix Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {I : Type*} [Fintype I] [DecidableEq I]

 theorem matrix_duhamel_mixed_integrand (v : I → ℝ) (X Y : Matrix I I ℂ) (s : ℝ) :
    matrixReTrace (exp ((1-s) • Matrix.diagonal (fun i => (v i : ℂ)))*X*
      exp (s • Matrix.diagonal (fun i => (v i : ℂ)))*Y) =
      ∑ i, ∑ j, Real.exp ((1-s)*v i+s*v j)*(X i j*Y j i).re := by
  rw [exp_real_diagonal, exp_real_diagonal, matrixReTrace_apply]
  have he : (Matrix.diagonal (fun i => (Real.exp ((1-s)*v i) : ℂ))*X*
      Matrix.diagonal (fun i => (Real.exp (s*v i) : ℂ))*Y).trace =
      ∑ i, ∑ j, (Real.exp ((1-s)*v i) : ℂ)*X i j*(Real.exp (s*v j) : ℂ)*Y j i := by
    unfold Matrix.trace
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.diag_apply, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [he]
  simp only [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Real.exp_add]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

 theorem matrix_duhamel_mixed (p : I → ℝ) (hp : ∀ i, 0 < p i) (X Y : Matrix I I ℂ) :
    matrixReTrace ((∫ s in (0:ℝ)..1,
      exp ((1-s) • Matrix.diagonal (fun i => (Real.log (p i) : ℂ)))*X*
      exp (s • Matrix.diagonal (fun i => (Real.log (p i) : ℂ))))*Y) =
      ∑ i, ∑ j, DiagonalForms.System.logMean (p i) (p j)*(X i j*Y j i).re := by
  let a : Matrix I I ℂ := Matrix.diagonal (fun i => (Real.log (p i) : ℂ))
  have hc : Continuous (fun s : ℝ => exp ((1-s) • a)*X*exp (s • a)) := by fun_prop
  have hm := ((ContinuousLinearMap.mul ℝ (Matrix I I ℂ)).flip Y).intervalIntegral_comp_comm
    (hc.intervalIntegrable (μ := volume) 0 1)
  change (∫ s in (0:ℝ)..1, (exp ((1-s) • a)*X*exp (s • a))*Y) =
    (∫ s in (0:ℝ)..1, exp ((1-s) • a)*X*exp (s • a))*Y at hm
  change matrixReTrace ((∫ s in (0:ℝ)..1, exp ((1-s) • a)*X*exp (s • a))*Y) = _
  rw [← hm]
  have hcy : Continuous (fun s : ℝ => exp ((1-s) • a)*X*exp (s • a)*Y) := hc.mul continuous_const
  trans ∫ s in (0:ℝ)..1, matrixReTrace (exp ((1-s) • a)*X*exp (s • a)*Y)
  · exact (matrixReTrace.intervalIntegral_comp_comm (hcy.intervalIntegrable (μ := volume) 0 1)).symm
  simp_rw [a, matrix_duhamel_mixed_integrand]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_mul_const, integral_exp_affine_log (hp i) (hp j)]
    · intro j _
      exact (by fun_prop : Continuous (fun s : ℝ =>
        Real.exp ((1-s)*Real.log (p i)+s*Real.log (p j))*(X i j*Y j i).re)).intervalIntegrable 0 1
  · intro i _
    apply Continuous.intervalIntegrable
    fun_prop

 theorem normalized_expectation_deriv (p : I → ℝ) (hp : ∀ i, 0 < p i)
    (X Y : Matrix I I ℂ) (c μ : ℝ) (hn : c+∑ i, p i = 1) :
    HasDerivAt (fun t : ℝ =>
      (μ+matrixReTrace ((exp (Matrix.diagonal (fun i => (Real.log (p i) : ℂ))+t • X)-
        Matrix.diagonal (fun i => (p i : ℂ)))*Y))/
      (c+matrixReTrace (exp (Matrix.diagonal (fun i => (Real.log (p i) : ℂ))+t • X))))
      ((∑ i, ∑ j, DiagonalForms.System.logMean (p i) (p j)*(X i j*Y j i).re)-
        μ*(∑ i, p i*(X i i).re)) 0 := by
  let a : Matrix I I ℂ := Matrix.diagonal (fun i => (Real.log (p i) : ℂ))
  have hea : exp a = Matrix.diagonal (fun i => (p i : ℂ)) := by
    simpa only [one_smul, one_mul, Real.exp_log (hp _)] using
      exp_real_diagonal (fun i => Real.log (p i)) 1
  have htr : matrixReTrace (exp a) = ∑ i, p i := by
    rw [hea, matrixReTrace_apply, Matrix.trace_diagonal]
    simp
  have hm : matrixReTrace (exp a*X) = ∑ i, p i*(X i i).re := by
    rw [hea, matrixReTrace_apply]
    simp [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  have hd := (hasDerivAt_trace_exp matrixReTrace matrixReTrace_cyclic a X 0).const_add c
  have hv := matrixReTrace.hasFDerivAt.comp_hasDerivAt 0
    (((hasDerivAt_exp_add_smul a X 0).sub_const (Matrix.diagonal (fun i => (p i : ℂ)))).mul_const Y)
  simp only [zero_smul, add_zero] at hd hv
  have hnorm : c+matrixReTrace (exp a) = 1 := htr ▸ hn
  have hbase : exp a-Matrix.diagonal (fun i => (p i : ℂ)) = 0 := by rw [hea, sub_self]
  have hh := (hv.const_add μ).div hd (by
    change c+matrixReTrace (exp (a+(0:ℝ) • X)) ≠ 0
    rw [zero_smul, add_zero, hnorm]
    exact one_ne_zero)
  simp only [Function.comp_def, zero_smul, add_zero] at hh
  erw [hbase, zero_mul, map_zero, hnorm, hm, matrix_duhamel_mixed p hp X Y] at hh
  simp only [add_zero, mul_one, one_pow, div_one] at hh
  convert! hh using 1

end QuantumCalculus

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics Topology

namespace QuantumCalculus

theorem quadratic_coefficient_nonneg {f : ℝ → ℝ} {a : ℝ}
    (he : (fun t => f t-a*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2))
    (hf : ∀ᶠ t in 𝓝 (0:ℝ), 0 ≤ f t) : 0 ≤ a := by
  by_contra h
  have ha : 0 < -a/2 := by linarith
  have hh := he.bound ha
  obtain ⟨δ,hδ,heδ⟩ := Metric.eventually_nhds_iff.mp (hh.and hf)
  have ht : dist (δ/2) (0:ℝ) < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith
  obtain ⟨h1,h2⟩ := heδ ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (δ/2))] at h1
  have hp : 0 < (δ/2)^2 := sq_pos_of_pos (by positivity)
  have h3 := (le_abs_self (f (δ/2)-a*(δ/2)^2)).trans h1
  nlinarith

theorem hessian_comparison {D P E : ℝ → ℝ} {α Qi Qo m d : ℝ}
    (hD : (fun t => D t-Qi/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2))
    (hP : (fun t => P t-m*t-Qo/2*t^2) =o[𝓝 (0:ℝ)] (fun t => t^2))
    (hE : HasDerivAt E d 0) (hE0 : E 0 = m)
    (hle : ∀ᶠ t in 𝓝 (0:ℝ), t*E t-P t ≤ α*D t) :
    2*d ≤ α*Qi+Qo := by
  have hE' : (fun t => E t-m-d*t) =o[𝓝 (0:ℝ)] (fun t => t) := by
    simpa only [hE0, sub_zero, smul_eq_mul, mul_comm d] using hE.isLittleO
  have hE2 : (fun t => t*(E t-m-d*t)) =o[𝓝 (0:ℝ)] (fun t => t^2) := by
    simpa only [pow_two] using (isBigO_refl (fun t : ℝ => t) (𝓝 0)).mul_isLittleO hE'
  have hh := ((hD.const_mul_left α).add hP).sub hE2
  have hh' : (fun t => (α*D t-(t*E t-P t))-(α*Qi/2+Qo/2-d)*t^2)
      =o[𝓝 (0:ℝ)] (fun t => t^2) := by
    convert! hh using 1
    funext t
    ring
  have hn := quadratic_coefficient_nonneg hh' (hle.mono (fun _ h => sub_nonneg.mpr h))
  linarith
end QuantumCalculus

end

open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open Module
open scoped ComplexConjugate BigOperators Matrix
open NormedSpace
open scoped Matrix.Norms.Operator
open scoped Topology
open MeasureTheory NormedSpace
open Filter Asymptotics Topology
open ContinuousLinearMap

namespace EntropyPhotonNumber

section
open QuantumTrace TraceEnsemble
variable {n : ℕ}

def KrausFlow.dual (F : KrausFlow n) (Z : Fock n →L[ℂ] Fock n) : Fock n →L[ℂ] Fock n :=
  KrausBounded.dual F.V F.norm Z

 theorem KrausFlow.dual_entry (F : KrausFlow n) (Z : Fock n →L[ℂ] Fock n) (x y : Fock n) :
    HasSum (fun i => inner ℂ (F.V i x) (Z (F.V i y))) (inner ℂ x (F.dual Z y)) :=
  KrausBounded.dual_entry F.V F.norm Z x y

 theorem KrausFlow.expectation_dual (F : KrausFlow n) (ρ : State n)
    (Z : Fock n →L[ℂ] Fock n) : expectation (F.map ρ) Z = expectation ρ (F.dual Z) := by
  have hn := TraceEnsemble.kraus_hasSum F.norm (rootColumn_norm ρ)
  have he := F.ensemble (NumberIndex n) (rootColumn ρ) ρ (rootColumn_norm ρ) (rootColumn_operator ρ)
  rw [expectation_ensemble (F.map ρ) _ hn.summable he]
  have hs := (TraceEnsemble.summable_expectation_norm hn.summable Z).of_norm
  change (∑' z : F.I × NumberIndex n, inner ℂ (F.V z.1 (rootColumn ρ z.2))
    (Z (F.V z.1 (rootColumn ρ z.2)))) = _
  have hc (j : NumberIndex n) := F.dual_entry Z (rootColumn ρ j) (rootColumn ρ j)
  have hh := ((Equiv.prodComm (NumberIndex n) F.I).hasSum_iff.2 hs.hasSum).prod_fiberwise hc
  exact hh.tsum_eq.symm

 theorem KrausFlow.dual_selfAdjoint (F : KrausFlow n) {Z : Fock n →L[ℂ] Fock n}
    (hZ : IsSelfAdjoint Z) : IsSelfAdjoint (F.dual Z) :=
  KrausBounded.dual_selfAdjoint F.V F.norm hZ

 theorem expectation_mixture (α : ℝ) (hα : α ∈ Set.Icc 0 1) (ρ σ : State n)
    (Z : Fock n →L[ℂ] Fock n) :
    expectation (mixture α hα ρ σ) Z = (α : ℂ)*expectation ρ Z+(1-α : ℂ)*expectation σ Z := by
  have hh := ((hasSum_expectation_basis (numberBasis n) ρ Z).mul_left (α : ℂ)).add
    ((hasSum_expectation_basis (numberBasis n) σ Z).mul_left (1-α : ℂ))
  apply (hasSum_expectation_basis (numberBasis n) (mixture α hα ρ σ) Z).unique
  simpa only [mixture, smul_apply, add_apply, map_add, map_smul, inner_add_right, inner_smul_right, Complex.ofReal_sub, Complex.ofReal_one] using hh

end

section
open QuantumCalculus QuantumTrace Filter Asymptotics
open scoped Matrix.Norms.Operator
variable {n : ℕ} {I J : Type*} [Fintype I] [DecidableEq I]

 theorem blockTilt_expectation_formula (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (Z : Fock n →L[ℂ] Fock n) (t : ℝ) :
    (expectation (blockTilt b p hp hs X hX t) Z).re =
      ((expectation ρ Z).re+matrixReTrace
        ((exp (FiniteBlock.tiltMatrix p X t)-Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ)))*
          FiniteBlock.entries b Z))/
      ((∑' j, p (Sum.inr j))+matrixReTrace (exp (FiniteBlock.tiltMatrix p X t))) := by
  rw [blockTilt, blockState_expectation ρ b p hp hs he,
    Complex.div_ofReal_re, Complex.add_re, FiniteBlock.partition_trace]
  rfl

 theorem blockTilt_expectation_deriv (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (Z : Fock n →L[ℂ] Fock n) :
    HasDerivAt (fun t : ℝ => (expectation (blockTilt b p hp hs X hX t) Z).re)
      ((∑ i, ∑ j, DiagonalForms.System.logMean (p (Sum.inl i)) (p (Sum.inl j))*
        (X i j*inner ℂ (b (Sum.inl j)) (Z (b (Sum.inl i)))).re)-
          (expectation ρ Z).re*(∑ i, p (Sum.inl i)*(X i i).re)) 0 := by
  simp_rw [blockTilt_expectation_formula ρ b p hp hs he X hX Z]
  exact normalized_expectation_deriv (fun i => p (Sum.inl i)) (fun i => hp (Sum.inl i))
    X (FiniteBlock.entries b Z) _ _ (FiniteBlock.tail_normalization p hs)

 theorem blockTilt_expectation_zero (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (Z : Fock n →L[ℂ] Fock n) :
    (expectation (blockTilt b p hp hs X hX 0) Z).re = (expectation ρ Z).re := by
  rw [blockTilt_expectation_formula ρ b p hp hs he X hX Z]
  have h0 : exp (FiniteBlock.tiltMatrix p X 0) = Matrix.diagonal (fun i => (p (Sum.inl i) : ℂ)) := by
    simpa only [FiniteBlock.tiltMatrix, zero_smul, add_zero, one_smul, one_mul,
      Real.exp_log (hp _)] using exp_real_diagonal (fun i => Real.log (p (Sum.inl i))) 1
  rw [h0, sub_self, zero_mul, map_zero, add_zero, matrixReTrace_apply, Matrix.trace_diagonal]
  simp only [Complex.re_sum, Complex.ofReal_re]
  rw [FiniteBlock.tail_normalization p hs, div_one]

 theorem expectation_block_of_eigen (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (Z : Matrix I I ℂ) :
    expectation ρ (FiniteBlock.block b Z) = ∑ i, (p (Sum.inl i) : ℂ)*Z i i := by
  have heq (j : I ⊕ J) : inner ℂ (b j) (FiniteBlock.block b Z (ρ.op (b j))) =
      Sum.elim (fun i => (p (Sum.inl i) : ℂ)*Z i i) (fun _ => 0) j := by
    rw [he, map_smul, inner_smul_right]
    cases j with
    | inl i => simp [FiniteBlock.block_basis, inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
    | inr j => simp [FiniteBlock.block_tail]
  have hh := HasSum.sum (f := Sum.elim (fun i => (p (Sum.inl i) : ℂ)*Z i i) (fun _ : J => (0:ℂ)))
    (hasSum_fintype _) (hasSum_zero : HasSum (fun _ : J => (0:ℂ)) 0)
  exact (hasSum_expectation_basis b ρ (FiniteBlock.block b Z)).unique (by
    simpa only [heq, Function.comp_def, Sum.elim_inl, add_zero] using hh)

 theorem expectation_block_of_eigen_re (ρ : State n)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (Z : Matrix I I ℂ) :
    (expectation ρ (FiniteBlock.block b Z)).re = ∑ i, p (Sum.inl i)*(Z i i).re := by
  rw [expectation_block_of_eigen ρ b p he]
  simp

end

open QuantumCalculus QuantumTrace Filter Asymptotics

 theorem crossEntropy_mixture_summable {n : ℕ} {J : Type*}
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (t : ℝ) (ht : t ∈ Set.Icc 0 1)
    (ρ σ : State n)
    (hρ : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (ρ.op (b j))).re))
    (hσ : Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) (σ.op (b j))).re)) :
    Summable (fun j => (-Real.log (p j))*(inner ℂ (b j) ((mixture t ht ρ σ).op (b j))).re) := by
  apply ((hρ.mul_left t).add (hσ.mul_left (1-t))).congr
  intro j
  simp only [mixture, add_apply, smul_apply, inner_add_right, inner_smul_right,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

 theorem one_port_relative_entropy_bound {n : ℕ} {J L : Type*}
    (F : KrausFlow n) (τ : State n) (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1)
    (c a β ζ C : ℝ) (hc : 0 < c) (ha : 0 < a)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (d : HilbertBasis L ℂ (Fock n)) (q : L → ℝ)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hτ : FiniteEnergy τ)
    (hcross : ∀ σ, FiniteMoment 4 σ →
      Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((F.map σ).op (d j))).re))
    (hcτ : Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) (τ.op (d j))).re))
    (hlog : ∀ σ, FiniteMoment 4 σ → crossEntropy b p σ =
      (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+C)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-
        a*entropy ρ+β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-
        a*entropy σ+β*energy σ+ζ*numberMoment 4 σ)
    (σ : State n) (hmσ : FiniteMoment 4 σ) :
    relativeEntropy d q (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ) ≤
      (a/c)*relativeEntropy b p σ := by
  let ht : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  have hself := crossEntropy_self ρ (finiteMoment_finiteEnergy (by norm_num) hmρ) b p he
  have hself0 := crossEntropy_self (mixture (1-κ) ht (F.map ρ) τ)
    (mixture_finiteEnergy _ _ (F.finiteEnergy _ (finiteMoment_finiteEnergy (by norm_num) hmρ)) hτ) d q he0
  rw [crossEntropy_mixture d q (1-κ) ht (F.map ρ) τ (hcross ρ hmρ) hcτ] at hself0
  rw [hlog ρ hmρ] at hself
  have hself' := congrArg (fun x => a*x) hself
  have hcancel (x : ℝ) : a*(x/a) = x := mul_div_cancel₀ x ha.ne'
  simp only [mul_add, ← mul_assoc, hcancel] at hself'
  have hσ := hmin σ hmσ
  have hid : a*relativeEntropy b p σ-c*relativeEntropy d q (mixture (1-κ) ht (F.map σ) τ) =
      (c*entropy (mixture (1-κ) ht (F.map σ) τ)-a*entropy σ+β*energy σ+ζ*numberMoment 4 σ)-
      (c*entropy (mixture (1-κ) ht (F.map ρ) τ)-a*entropy ρ+β*energy ρ+ζ*numberMoment 4 ρ) := by
    unfold relativeEntropy
    rw [hlog σ hmσ, crossEntropy_mixture d q (1-κ) ht (F.map σ) τ (hcross σ hmσ) hcτ]
    field_simp [ha.ne']
    linear_combination hself'-c*hself0
  have hb : 0 ≤ a*relativeEntropy b p σ-c*relativeEntropy d q (mixture (1-κ) ht (F.map σ) τ) := by
    rw [hid]
    exact sub_nonneg.mpr hσ
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hc).mpr (by nlinarith)

end EntropyPhotonNumber

namespace FiniteBlock
open DiagonalForms.System
variable {I J : Type*} [Fintype I]
def mean (p : I ⊕ J → ℝ) (X : Matrix I I ℂ) : ℝ := ∑ i, p (Sum.inl i)*(X i i).re

def variance (p : I ⊕ J → ℝ) (X : Matrix I I ℂ) : ℝ :=
  (∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j))-mean p X^2

def covariance (p : I ⊕ J → ℝ) (X Y : Matrix I I ℂ) (μ : ℝ) : ℝ :=
  (∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*(X i j*Y j i).re)-μ*mean p X
end FiniteBlock

namespace EntropyPhotonNumber
open QuantumCalculus QuantumTrace Filter Asymptotics
open scoped Matrix.Norms.Operator

 theorem flow_finite_hessian {n : ℕ} {I J K L : Type*}
    [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    (F : KrausFlow n) (τ : State n) (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1)
    (c a β ζ C : ℝ) (hc : 0 < c) (ha : 0 < a)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis (I ⊕ J) ℂ (Fock n)) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (d : HilbertBasis (K ⊕ L) ℂ (Fock n)) (q : K ⊕ L → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hτ : FiniteEnergy τ)
    (hcross : ∀ σ, FiniteMoment 4 σ →
      Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((F.map σ).op (d j))).re))
    (hcτ : Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) (τ.op (d j))).re))
    (hlog : ∀ σ, FiniteMoment 4 σ → crossEntropy b p σ =
      (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+C)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-
        a*entropy ρ+β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-
        a*entropy σ+β*energy σ+ζ*numberMoment 4 σ)
    (X : Matrix I I ℂ) (hX : X.IsHermitian) (Z : Matrix K K ℂ) (hZ : Z.IsHermitian) :
    2*((1-κ)*FiniteBlock.covariance p X (FiniteBlock.entries b (F.dual (FiniteBlock.block d Z)))
      (expectation ρ (F.dual (FiniteBlock.block d Z))).re) ≤
      (a/c)*FiniteBlock.variance p X+FiniteBlock.variance q Z := by
  let hκ' : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  let σ := fun t => blockTilt b p hp hs X hX t
  let ω := fun t => mixture (1-κ) hκ' (F.map (σ t)) τ
  let Y := FiniteBlock.block d Z
  have hm (t : ℝ) : FiniteMoment 4 (σ t) := blockTilt_finiteMoment ρ hmρ b p hp hs he X hX t
  have hf (t : ℝ) : FiniteEnergy (ω t) := mixture_finiteEnergy _ _
    (F.finiteEnergy _ (finiteMoment_finiteEnergy (by norm_num) (hm t))) hτ
  have hcro (t : ℝ) : Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((ω t).op (d j))).re) :=
    crossEntropy_mixture_summable d q (1-κ) hκ' (F.map (σ t)) τ (hcross _ (hm t)) hcτ
  have hD := blockTilt_relativeEntropy_expansion_of_moment ρ hmρ b p hp hs he X hX
  have hP := finite_block_partition_expansion (fun i => q (Sum.inl i)) (fun i => hq (Sum.inl i)) Z hZ
    (∑' j, q (Sum.inr j)) (FiniteBlock.tail_normalization q ht)
  have hd := blockTilt_expectation_deriv ρ b p hp hs he X hX (F.dual Y)
  have hE : HasDerivAt (fun t => (expectation (ω t) Y).re)
      ((1-κ)*FiniteBlock.covariance p X (FiniteBlock.entries b (F.dual Y)) (expectation ρ (F.dual Y)).re) 0 := by
    convert! (hd.const_mul (1-κ)).add_const (κ*(expectation τ Y).re) using 1
    funext t
    dsimp only [ω]
    rw [expectation_mixture, F.expectation_dual]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_mul, sub_self, sub_zero]
    ring
  have hE0 : (expectation (ω 0) Y).re = FiniteBlock.mean q Z := by
    trans (expectation (mixture (1-κ) hκ' (F.map ρ) τ) Y).re
    · dsimp only [ω]
      rw [expectation_mixture, expectation_mixture, F.expectation_dual, F.expectation_dual]
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, zero_mul, sub_self, sub_zero]
      rw [show (expectation (σ 0) (F.dual Y)).re = (expectation ρ (F.dual Y)).re from
        blockTilt_expectation_zero ρ b p hp hs he X hX (F.dual Y)]
    · exact expectation_block_of_eigen_re _ d q he0 Z
  have hi (t : ℝ) : t*(expectation (ω t) Y).re-
      Real.log ((∑' j, q (Sum.inr j))+matrixReTrace (exp (FiniteBlock.tiltMatrix q Z t))) ≤
      (a/c)*relativeEntropy b p (σ t) := by
    have hlo := block_relativeEntropy_tilt_lower (ω t) (hf t) d q hq ht (hcro t) Z hZ t
    exact hlo.trans (one_port_relative_entropy_bound F τ κ hκ c a β ζ C hc ha ρ hmρ b p d q
      he he0 hτ hcross hcτ hlog hmin (σ t) (hm t))
  exact hessian_comparison hD hP hE hE0 (Filter.Eventually.of_forall hi)

end EntropyPhotonNumber

namespace FiniteBlock
open DiagonalForms.System
open scoped ComplexConjugate
variable {I J : Type*} [Fintype I]

 theorem mean_scale (p : I ⊕ J → ℝ) (X : Matrix I I ℂ) (t : ℝ) :
    mean p ((t:ℂ) • X) = t*mean p X := by
  simp only [mean, Matrix.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _; ring

 theorem variance_scale (p : I ⊕ J → ℝ) (X : Matrix I I ℂ) (t : ℝ) :
    variance p ((t:ℂ) • X) = t^2*variance p X := by
  rw [variance, mean_scale, variance]
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
  have hh : (∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j)) *
      (t^2*Complex.normSq (X i j))) =
      t^2*(∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j)) := by
    simp_rw [Finset.mul_sum]
    congr 1; ext i; congr 1; ext j; ring
  simp only [← pow_two]
  rw [hh]
  ring

 theorem covariance_scale_self (p : I ⊕ J → ℝ) (X : Matrix I I ℂ) (hX : X.IsHermitian)
    (μ t : ℝ) : covariance p ((t:ℂ) • X) X μ =
      t*((∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j))-μ*mean p X) := by
  have hc (i j : I) : (X j i) = conj (X i j) := by
    exact (congrFun (congrFun hX.eq j) i).symm
  rw [covariance, mean_scale]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hh (i j : I) : ((t:ℂ)*X i j*X j i).re = t*Complex.normSq (X i j) := by
    rw [hc i j, mul_assoc, Complex.mul_conj]
    simp
  simp_rw [hh]
  have he : (∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j)) *
      (t*Complex.normSq (X i j))) =
      t*(∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j)) := by
    simp_rw [Finset.mul_sum]
    congr 1; ext i; congr 1; ext j; ring
  rw [he]
  ring
end FiniteBlock

namespace BKM
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

 theorem compression_mean (b : HilbertBasis J ℂ E) (p : J → ℝ) (Y : E →L[ℂ] E) (s : Finset J) :
    FiniteBlock.mean (p ∘ Equiv.sumCompl (fun j => j ∈ s))
      (FiniteBlock.entries (reindexBasis b (Equiv.sumCompl (fun j => j ∈ s))) Y) =
      ∑ j ∈ s, p j*(entry b Y j j).re := by
  classical
  simp only [FiniteBlock.mean, FiniteBlock.entries, reindexBasis_apply, Function.comp_apply,
    Equiv.sumCompl_apply_inl, entry]
  exact (Finset.sum_subtype s (fun _ => Iff.rfl) (fun j => p j*(inner ℂ (b j) (Y (b j))).re)).symm

 theorem compression_quadratic (b : HilbertBasis J ℂ E) (p : J → ℝ) (Y : E →L[ℂ] E) (s : Finset J) :
    (∑ i : s, ∑ j : s, logMean (p i.val) (p j.val)*Complex.normSq
      (FiniteBlock.entries (reindexBasis b (Equiv.sumCompl (fun j => j ∈ s))) Y i j)) =
      ∑ i ∈ s, ∑ j ∈ s, logMean (p i) (p j)*Complex.normSq (entry b Y i j) := by
  classical
  simp only [FiniteBlock.entries, reindexBasis_apply, Equiv.sumCompl_apply_inl, entry,
    Finset.sum_subtype s (fun _ => Iff.rfl)]

 theorem compression_hessian_to_variance (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (hp : ∀ j, 0 < p j) (hs : Summable p) (Y : E →L[ℂ] E) (μ α γ W : ℝ)
    (hm : HasSum (fun j => p j*(entry b Y j j).re) μ) (hα : 0 < α)
    (hY : IsSelfAdjoint Y)
    (h : ∀ (s : Finset J) (t : ℝ),
      let b' := reindexBasis b (Equiv.sumCompl (fun j => j ∈ s))
      let p' := p ∘ Equiv.sumCompl (fun j => j ∈ s)
      let X := FiniteBlock.entries b' Y
      2*(γ*FiniteBlock.covariance p' ((t:ℂ) • X) X μ) ≤
        α*FiniteBlock.variance p' ((t:ℂ) • X)+W) :
    γ^2*((∑' ij : J × J, logMean (p ij.1) (p ij.2)*Complex.normSq (entry b Y ij.1 ij.2))-μ^2) ≤ α*W := by
  classical
  apply finite_hessian_to_variance _ _ μ _ α γ W (logMean_summable b p hp hs Y).hasSum hm hα
  intro s t
  have hh := h s t
  dsimp only at hh
  have hX : (FiniteBlock.entries (reindexBasis b (Equiv.sumCompl (fun j => j ∈ s))) Y).IsHermitian := by
    ext i j
    change conj (inner ℂ (reindexBasis b _ (Sum.inl j)) (Y (reindexBasis b _ (Sum.inl i)))) =
      inner ℂ (reindexBasis b _ (Sum.inl i)) (Y (reindexBasis b _ (Sum.inl j)))
    rw [inner_conj_symm]
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hY) _ _
  rw [FiniteBlock.covariance_scale_self _ _ hX, FiniteBlock.variance_scale,
    FiniteBlock.variance, compression_mean] at hh
  simp only [Function.comp_apply, Equiv.sumCompl_apply_inl, compression_quadratic] at hh
  nlinarith
end BKM

namespace EntropyPhotonNumber

section
open QuantumTrace DiagonalForms.System
open scoped ComplexConjugate
variable {n : ℕ} {J K L : Type*} [Fintype K] [DecidableEq K]

 theorem crossEntropy_reindex {M : Type*} (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (e : M ≃ J) (ρ : State n) : crossEntropy (BKM.reindexBasis b e) (p ∘ e) ρ = crossEntropy b p ρ := by
  simp only [crossEntropy, BKM.reindexBasis_apply, Function.comp_def]
  exact e.tsum_eq (fun j : J => (-Real.log (p j))*(inner ℂ (b j) (ρ.op (b j))).re)

 theorem finite_entries_selfAdjoint {I T E : Type*} [Fintype I] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (b : HilbertBasis (I ⊕ T) ℂ E)
    (Z : E →L[ℂ] E) (hZ : IsSelfAdjoint Z) : (FiniteBlock.entries b Z).IsHermitian := by
  ext i j
  change conj (inner ℂ (b (Sum.inl j)) (Z (b (Sum.inl i)))) = inner ℂ (b (Sum.inl i)) (Z (b (Sum.inl j)))
  rw [inner_conj_symm]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hZ) _ _

 theorem expectation_eigen_hasSum (ρ : State n) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j) (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun j => p j*(BKM.entry b Z j j).re) (expectation ρ Z).re := by
  have h := (hasSum_expectation_basis b ρ Z).mapL Complex.reCLM
  simpa only [he, map_smul, inner_smul_right, Complex.reCLM_apply, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, BKM.entry] using h

 theorem flow_full_hessian (F : KrausFlow n) (τ : State n) (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1)
    (c a β ζ C : ℝ) (hc : 0 < c) (ha : 0 < a) (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (d : HilbertBasis (K ⊕ L) ℂ (Fock n)) (q : K ⊕ L → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hτ : FiniteEnergy τ)
    (hcross : ∀ σ, FiniteMoment 4 σ →
      Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((F.map σ).op (d j))).re))
    (hcτ : Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) (τ.op (d j))).re))
    (hlog : ∀ σ, FiniteMoment 4 σ → crossEntropy b p σ =
      (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+C)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-
        a*entropy ρ+β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-
        a*entropy σ+β*energy σ+ζ*numberMoment 4 σ)
    (Z : Matrix K K ℂ) (hZ : Z.IsHermitian) :
    (1-κ)^2*((∑' ij : J × J, logMean (p ij.1) (p ij.2)*
      Complex.normSq (BKM.entry b (F.dual (FiniteBlock.block d Z)) ij.1 ij.2))-
        (expectation ρ (F.dual (FiniteBlock.block d Z))).re^2) ≤ (a/c)*FiniteBlock.variance q Z := by
  classical
  let Y := F.dual (FiniteBlock.block d Z)
  let μ := (expectation ρ Y).re
  have hY : IsSelfAdjoint Y := F.dual_selfAdjoint (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (FiniteBlock.block_symmetric d Z hZ))
  apply BKM.compression_hessian_to_variance b p hp hs.summable Y μ (a/c) (1-κ)
    (FiniteBlock.variance q Z) (expectation_eigen_hasSum ρ b p he Y) (div_pos ha hc) hY
  intro s t
  let e := Equiv.sumCompl (fun j => j ∈ s)
  let b' := BKM.reindexBasis b e
  let p' := p ∘ e
  let X := FiniteBlock.entries b' Y
  have hX := finite_entries_selfAdjoint b' Y hY
  have hl' (σ : State n) (hh : FiniteMoment 4 σ) : crossEntropy b' p' σ =
      (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+C := by
    rw [crossEntropy_reindex]
    exact hlog σ hh
  have he' (j) : ρ.op (b' j) = (p' j : ℂ) • b' j := by
    simpa only [b', p', BKM.reindexBasis_apply, Function.comp_apply] using he (e j)
  have htself : IsSelfAdjoint (t : ℂ) := by
    change conj (t : ℂ) = (t : ℂ)
    exact Complex.conj_ofReal t
  have hh := flow_finite_hessian F τ κ hκ c a β ζ C hc ha ρ hmρ b' p'
    (fun j => hp (e j)) (e.hasSum_iff.mpr hs) d q hq ht he' he0 hτ hcross hcτ hl'
    hmin ((t:ℂ) • X) (hX.smul htself) Z hZ
  exact hh

end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {K L : Type*} [Fintype K] [DecidableEq K]

theorem minimum_component_hessian
    (F : KrausFlow n) (τ : State n) {r : ℝ} (hr : 0 < r) (hτ : τ = thermalState n r hr)
    (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1) (hκ0 : 0 < κ)
    (c a β ζ : ℝ) (hc : 0 < c) (ha : 0 < a) (hβ : 0 ≤ β) (hζ : 0 < ζ)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (d : HilbertBasis (K ⊕ L) ℂ (Fock n)) (q : K ⊕ L → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-a*entropy ρ+
        β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-a*entropy σ+
        β*energy σ+ζ*numberMoment 4 σ) :
    ∃ G : GibbsData n (ζ/a) ρ, ∀ (Z : Matrix K K ℂ), Z.IsHermitian →
      (1-κ)^2*((∑' ij : G.J × G.J, logMean (gibbsWeight G.eigenval ij.1)
        (gibbsWeight G.eigenval ij.2)*
        Complex.normSq (BKM.entry G.basis (F.dual (FiniteBlock.block d Z)) ij.1 ij.2))-
          (expectation ρ (F.dual (FiniteBlock.block d Z))).re^2) ≤ (a/c)*FiniteBlock.variance q Z := by
  obtain ⟨G,hG⟩ := flow_minimum_gibbs F τ hr hτ κ hκ hκ0 c a β ζ hc ha hβ hζ ρ hmρ
    d q hq ht he0 hmin
  let _ := G.nonempty
  let htκ : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  let ρ0 := mixture (1-κ) htκ (F.map ρ) τ
  have hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ0.op := by
    rw [← hτ]
    exact mixture_replacement_le κ hκ (F.map ρ) τ
  have hfτ : FiniteEnergy τ := by simpa only [hτ] using thermalState_finiteEnergy n r hr
  have hcross (σ : State n) (hm : FiniteMoment 4 σ) :
      Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((F.map σ).op (d j))).re) :=
    crossEntropy_finite ρ0 (F.map σ) (F.finiteEnergy _ (finiteMoment_finiteEnergy (by norm_num) hm))
      hr hκ0 hκ.2 hle d q hq ht he0
  have hcτ := crossEntropy_finite ρ0 τ hfτ hr hκ0 hκ.2 hle d q hq ht he0
  have hα : 0 ≤ c*(1-κ)/a := div_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hκ.2)) ha.le
  have hlog (σ : State n) (hm : FiniteMoment 4 σ) :
      crossEntropy G.basis (gibbsWeight G.eigenval) σ =
        (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+
          Real.log (heatPartition G.eigenval) :=
    (G.crossEntropy_hamiltonian d q hq ht F hα (div_nonneg hβ ha.le) (div_pos hζ ha)
      hG σ hm (hcross σ hm)).tsum_eq
  refine ⟨G, fun Z hZ => ?_⟩
  exact flow_full_hessian F τ κ hκ c a β ζ (Real.log (heatPartition G.eigenval)) hc ha
    ρ hmρ G.basis (gibbsWeight G.eigenval) (gibbsWeight_pos G.eigenval G.heat)
    (gibbsWeight_hasSum G.eigenval G.heat) d q hq ht G.eigen he0 hfτ hcross hcτ hlog hmin Z hZ

end EntropyPhotonNumber

namespace BKM
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem entry_real_smul (b : HilbertBasis J ℂ E) (c : ℝ) (Z : E →L[ℂ] E) (i j : J) :
    entry b (c • Z) i j=(c:ℂ)*entry b Z i j := by
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), entry_smul]
  rfl

variable [CompleteSpace E]

theorem entry_realPart (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (i j : J) :
    entry b (realPart Z : E →L[ℂ] E) i j=(entry b Z i j+conj (entry b Z j i))/2 := by
  rw [realPart_apply_coe, entry_real_smul, entry_add, ContinuousLinearMap.star_eq_adjoint, entry_adjoint]
  push_cast
  ring

theorem entry_imaginaryPart (b : HilbertBasis J ℂ E) (Z : E →L[ℂ] E) (i j : J) :
    entry b (imaginaryPart Z : E →L[ℂ] E) i j=-Complex.I*(entry b Z i j-conj (entry b Z j i))/2 := by
  rw [imaginaryPart_apply_coe, entry_smul, entry_real_smul, entry_sub,
    ContinuousLinearMap.star_eq_adjoint, entry_adjoint]
  push_cast
  ring

end BKM

namespace Complex
open scoped _root_.Complex
open scoped ComplexConjugate
 theorem normSq_polar_parts (z w : ℂ) :
    _root_.Complex.normSq ((z+conj w)/2)+_root_.Complex.normSq (-_root_.Complex.I*(z-conj w)/2)=(_root_.Complex.normSq z+_root_.Complex.normSq w)/2 := by
  simp only [div_eq_mul_inv, _root_.Complex.normSq_apply, _root_.Complex.add_re, _root_.Complex.add_im, _root_.Complex.mul_re, _root_.Complex.mul_im, _root_.Complex.sub_re, _root_.Complex.sub_im,
    _root_.Complex.conj_re, _root_.Complex.conj_im, _root_.Complex.neg_re, _root_.Complex.neg_im, _root_.Complex.I_re, _root_.Complex.I_im, _root_.Complex.inv_re, _root_.Complex.inv_im]
  norm_num
  ring
end Complex

namespace BKM

section
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem quadratic_adjoint (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) :
    quadratic b p Z.adjoint=quadratic b p Z := by
  simp only [quadratic, entry_adjoint, Complex.normSq_conj]
  have h := (Equiv.prodComm J J).tsum_eq (fun ij : J × J => logMean (p ij.1) (p ij.2)*Complex.normSq (entry b Z ij.1 ij.2))
  convert! h using 1
  congr 1
  ext ij
  exact congrArg (fun x => x*Complex.normSq (entry b Z ij.2 ij.1)) (logMean_symm _ _)

theorem quadratic_parts (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀ j,0 < p j) (hs : Summable p)
    (Z : E →L[ℂ] E) :
    quadratic b p (realPart Z : E →L[ℂ] E)+quadratic b p (imaginaryPart Z : E →L[ℂ] E)=quadratic b p Z := by
  have hr := logMean_summable b p hp hs (realPart Z : E →L[ℂ] E)
  have hi := logMean_summable b p hp hs (imaginaryPart Z : E →L[ℂ] E)
  have hz := logMean_summable b p hp hs Z
  have ha := logMean_summable b p hp hs Z.adjoint
  have he (ij : J × J) :
      logMean (p ij.1) (p ij.2)*Complex.normSq (entry b (realPart Z : E →L[ℂ] E) ij.1 ij.2)+
      logMean (p ij.1) (p ij.2)*Complex.normSq (entry b (imaginaryPart Z : E →L[ℂ] E) ij.1 ij.2)=
      (logMean (p ij.1) (p ij.2)*Complex.normSq (entry b Z ij.1 ij.2)+
      logMean (p ij.1) (p ij.2)*Complex.normSq (entry b Z.adjoint ij.1 ij.2))/2 := by
    rw [← mul_add, entry_realPart, entry_imaginaryPart, Complex.normSq_polar_parts, entry_adjoint, Complex.normSq_conj]
    ring
  have hh := hr.hasSum.add hi.hasSum
  simp_rw [he] at hh
  have ht := (hz.hasSum.add ha.hasSum).div_const 2
  have heq := hh.unique ht
  change quadratic b p (realPart Z : E →L[ℂ] E)+quadratic b p (imaginaryPart Z : E →L[ℂ] E)=
    (quadratic b p Z+quadratic b p Z.adjoint)/2 at heq
  rw [quadratic_adjoint] at heq
  linarith

end

section
open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]

theorem mean_adjoint (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) :
    mean b p Z.adjoint=conj (mean b p Z) := by
  simp only [mean, entry_adjoint, Complex.conj_tsum, map_mul, Complex.conj_ofReal]

theorem mean_parts (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    (Z : E →L[ℂ] E) :
    mean b p (realPart Z : E →L[ℂ] E)=(mean b p Z).re ∧
    mean b p (imaginaryPart Z : E →L[ℂ] E)=(mean b p Z).im := by
  have hr (j : J) :
      (p j : ℂ)*entry b (realPart Z : E →L[ℂ] E) j j =
        (p j : ℂ)*(entry b Z j j + conj (entry b Z j j))/2 := by rw [entry_realPart]; ring
  have hi (j : J) :
      (p j : ℂ)*entry b (imaginaryPart Z : E →L[ℂ] E) j j =
        -Complex.I*((p j : ℂ)*entry b Z j j-conj ((p j : ℂ)*entry b Z j j))/2 := by
    rw [entry_imaginaryPart]
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have h := mean_summable b p hp hs Z
  have hc := (h.hasSum.mapL Complex.conjCLE.toContinuousLinearMap)
  change HasSum (fun j => conj ((p j : ℂ)*entry b Z j j)) (conj (mean b p Z)) at hc
  constructor
  · have hh := (h.hasSum.add hc).div_const 2
    have he (j : J) :
        ((p j : ℂ)*entry b Z j j+conj ((p j : ℂ)*entry b Z j j))/2=
          (p j : ℂ)*entry b (realPart Z : E →L[ℂ] E) j j := by
      rw [hr, map_mul, Complex.conj_ofReal]; ring
    simp_rw [he] at hh
    rw [mean, hh.tsum_eq]
    change (mean b p Z+conj (mean b p Z))/2=((mean b p Z).re:ℂ)
    rw [Complex.add_conj]
    push_cast
    ring
  · have hh := ((h.hasSum.sub hc).mul_left (-Complex.I)).div_const 2
    simp_rw [← hi] at hh
    rw [mean, hh.tsum_eq]
    change -Complex.I*(mean b p Z-conj (mean b p Z))/2=((mean b p Z).im:ℂ)
    rw [Complex.sub_conj]
    push_cast
    ring_nf
    simp only [Complex.I_sq]
    ring

def variance (b : HilbertBasis J ℂ E) (p : J → ℝ) (Z : E →L[ℂ] E) : ℝ :=
  quadratic b p Z - Complex.normSq (mean b p Z)

theorem variance_parts (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (Z : E →L[ℂ] E) :
    variance b p (realPart Z : E →L[ℂ] E)+variance b p (imaginaryPart Z : E →L[ℂ] E)=variance b p Z := by
  obtain ⟨hr,hi⟩ := mean_parts b p (fun j => (hp j).le) hs Z
  simp only [variance, hr, hi, Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have h := quadratic_parts b p hp hs Z
  linarith

end

open scoped BigOperators ComplexConjugate ComplexStarModule
open DiagonalForms.System
variable {I J E : Type*} [Fintype I] [DecidableEq I]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem entry_block (b : HilbertBasis (I ⊕ J) ℂ E) (X : Matrix I I ℂ) (i j : I ⊕ J) :
    entry b (FiniteBlock.block b X) i j=match i,j with
      | Sum.inl a,Sum.inl c => X a c
      | _,_ => 0 := by
  classical
  cases i <;> cases j <;>
    simp [entry, FiniteBlock.block_basis, FiniteBlock.block_tail,
      orthonormal_iff_ite.mp b.orthonormal]

omit [CompleteSpace E] in
theorem mean_block (b : HilbertBasis (I ⊕ J) ℂ E) (p : I ⊕ J → ℝ) (X : Matrix I I ℂ) :
    mean b p (FiniteBlock.block b X)=∑ i, (p (Sum.inl i):ℂ)*X i i := by
  have hh := HasSum.sum (f := fun j : I ⊕ J => (p j:ℂ)*entry b (FiniteBlock.block b X) j j)
    (by simpa only [Function.comp_def, entry_block] using hasSum_fintype (fun i : I => (p (Sum.inl i):ℂ)*X i i))
    (by simpa only [Function.comp_def, entry_block, mul_zero] using (hasSum_zero : HasSum (fun _ : J => (0:ℂ)) 0))
  simpa only [add_zero, mean] using hh.tsum_eq

theorem quadratic_block (b : HilbertBasis (I ⊕ J) ℂ E) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (X : Matrix I I ℂ) :
    quadratic b p (FiniteBlock.block b X)=
      ∑ i, ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j) := by
  rw [quadratic, (logMean_summable b p hp hs (FiniteBlock.block b X)).tsum_prod]
  have row (i : I) :
      (∑' j : I ⊕ J, logMean (p (Sum.inl i)) (p j)*Complex.normSq (entry b (FiniteBlock.block b X) (Sum.inl i) j))=
      ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j) := by
    have hh := HasSum.sum (f := fun j : I ⊕ J => logMean (p (Sum.inl i)) (p j)*Complex.normSq (entry b (FiniteBlock.block b X) (Sum.inl i) j))
      (by simpa only [Function.comp_def, entry_block] using hasSum_fintype (fun j : I => logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j)))
      (by simpa only [Function.comp_def, entry_block, Complex.normSq_zero, mul_zero] using (hasSum_zero : HasSum (fun _ : J => (0:ℝ)) 0))
    simpa only [add_zero] using hh.tsum_eq
  have hh := HasSum.sum (f := fun i : I ⊕ J => ∑' j : I ⊕ J, logMean (p i) (p j)*Complex.normSq (entry b (FiniteBlock.block b X) i j))
    (by simpa only [Function.comp_def, row] using hasSum_fintype (fun i : I => ∑ j, logMean (p (Sum.inl i)) (p (Sum.inl j))*Complex.normSq (X i j)))
    (by simpa only [Function.comp_def, entry_block, Complex.normSq_zero, mul_zero, tsum_zero] using (hasSum_zero : HasSum (fun _ : J => (0:ℝ)) 0))
  simpa only [add_zero] using hh.tsum_eq

omit [Fintype I] [DecidableEq I] in
theorem normSq_mean_selfAdjoint (b : HilbertBasis J ℂ E) (p : J → ℝ)
    (Z : E →L[ℂ] E) (hZ : IsSelfAdjoint Z) : Complex.normSq (mean b p Z)=(mean b p Z).re^2 := by
  have hh := mean_adjoint b p Z
  rw [show Z.adjoint=Z from hZ] at hh
  have hi := congrArg Complex.im hh
  simp only [Complex.conj_im] at hi
  rw [Complex.normSq_apply]
  nlinarith

theorem variance_block (b : HilbertBasis (I ⊕ J) ℂ E) (p : I ⊕ J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (X : Matrix I I ℂ) (hX : X.IsHermitian) :
    variance b p (FiniteBlock.block b X)=FiniteBlock.variance p X := by
  rw [variance, quadratic_block b p hp hs, normSq_mean_selfAdjoint b p _
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr (FiniteBlock.block_symmetric b X hX)), mean_block]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, FiniteBlock.variance, FiniteBlock.mean]

omit [DecidableEq I] in
 theorem block_realPart (b : HilbertBasis (I ⊕ J) ℂ E) (X : Matrix I I ℂ) :
    FiniteBlock.block b (realPart X : Matrix I I ℂ)=(realPart (FiniteBlock.block b X) : E →L[ℂ] E) := by
  simp only [realPart_apply_coe, RCLike.real_smul_eq_coe_smul (K := ℂ),
    FiniteBlock.block_smul, FiniteBlock.block_add, ContinuousLinearMap.star_eq_adjoint,
    Matrix.star_eq_conjTranspose, FiniteBlock.block_adjoint]

omit [DecidableEq I] in
 theorem block_imaginaryPart (b : HilbertBasis (I ⊕ J) ℂ E) (X : Matrix I I ℂ) :
    FiniteBlock.block b (imaginaryPart X : Matrix I I ℂ)=(imaginaryPart (FiniteBlock.block b X) : E →L[ℂ] E) := by
  simp only [imaginaryPart_apply_coe, RCLike.real_smul_eq_coe_smul (K := ℂ),
    FiniteBlock.block_smul, FiniteBlock.block_sub, ContinuousLinearMap.star_eq_adjoint,
    Matrix.star_eq_conjTranspose, FiniteBlock.block_adjoint]
end BKM

namespace EntropyPhotonNumber

section
open scoped ComplexConjugate ComplexStarModule
variable {n : ℕ} {J : Type*}

theorem mean_expectation (ρ : State n) (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (he : ∀j, ρ.op (b j)=(p j:ℂ) • b j) (Z : Fock n →L[ℂ] Fock n) :
    BKM.mean b p Z=expectation ρ Z := by
  have hh := hasSum_expectation_basis b ρ Z
  simp only [he, map_smul, inner_smul_right] at hh
  exact hh.tsum_eq

 theorem KrausFlow.dual_add (F : KrausFlow n) (Z T : Fock n →L[ℂ] Fock n) :
    F.dual (Z+T)=F.dual Z+F.dual T := KrausBounded.dual_add F.V F.norm Z T
 theorem KrausFlow.dual_smul (F : KrausFlow n) (c : ℂ) (Z : Fock n →L[ℂ] Fock n) :
    F.dual (c • Z)=c • F.dual Z := KrausBounded.dual_smul F.V F.norm c Z
 theorem KrausFlow.dual_real_smul (F : KrausFlow n) (c : ℝ) (Z : Fock n →L[ℂ] Fock n) :
    F.dual (c • Z)=c • F.dual Z := by
  change F.dual ((c:ℂ) • Z)=(c:ℂ) • F.dual Z
  exact F.dual_smul _ _
 theorem KrausFlow.dual_sub (F : KrausFlow n) (Z T : Fock n →L[ℂ] Fock n) :
    F.dual (Z-T)=F.dual Z-F.dual T := by
  have hneg (operator : Fock n →L[ℂ] Fock n) : (-1:ℂ) • operator = -operator := by
    apply ContinuousLinearMap.ext
    intro vector
    simp only [smul_apply, neg_apply, neg_one_smul]
  rw [sub_eq_add_neg, ← hneg T, F.dual_add, F.dual_smul, hneg, ← sub_eq_add_neg]
 theorem KrausFlow.dual_adjoint (F : KrausFlow n) (Z : Fock n →L[ℂ] Fock n) :
    F.dual Z.adjoint=(F.dual Z).adjoint := KrausBounded.dual_adjoint F.V F.norm Z
 theorem KrausFlow.dual_realPart (F : KrausFlow n) (Z : Fock n →L[ℂ] Fock n) :
    F.dual (realPart Z : Fock n →L[ℂ] Fock n)=(realPart (F.dual Z) : Fock n →L[ℂ] Fock n) := by
  simp only [realPart_apply_coe, ← Complex.coe_smul,
    ContinuousLinearMap.star_eq_adjoint, F.dual_smul, F.dual_add, F.dual_adjoint]

 theorem KrausFlow.dual_imaginaryPart (F : KrausFlow n) (Z : Fock n →L[ℂ] Fock n) :
    F.dual (imaginaryPart Z : Fock n →L[ℂ] Fock n)=(imaginaryPart (F.dual Z) : Fock n →L[ℂ] Fock n) := by
  simp only [imaginaryPart_apply_coe, ← Complex.coe_smul,
    ContinuousLinearMap.star_eq_adjoint, F.dual_smul, F.dual_sub, F.dual_adjoint]

end

section
open QuantumTrace DiagonalForms.System
open scoped ComplexStarModule
variable {n : ℕ} {K L J : Type*} [Fintype K] [DecidableEq K]

theorem complex_component_hessian (F : KrausFlow n) (c a κ : ℝ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (d : HilbertBasis (K ⊕ L) ℂ (Fock n)) (q : K ⊕ L → ℝ)
    (hq : ∀j,0 < q j) (ht : Summable q)
    (h : ∀ (Z : Matrix K K ℂ), Z.IsHermitian →
      (1-κ)^2*BKM.variance b p (F.dual (FiniteBlock.block d Z)) ≤ (a/c)*FiniteBlock.variance q Z)
    (Z : Matrix K K ℂ) :
    (1-κ)^2*BKM.variance b p (F.dual (FiniteBlock.block d Z)) ≤
      (a/c)*BKM.variance d q (FiniteBlock.block d Z) := by
  have hr : (realPart Z : Matrix K K ℂ).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr selfAdjoint.isSelfAdjoint
  have hi : (imaginaryPart Z : Matrix K K ℂ).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr selfAdjoint.isSelfAdjoint
  have h1 := h (realPart Z) hr
  have h2 := h (imaginaryPart Z) hi
  rw [← BKM.variance_block d q hq ht _ hr, BKM.block_realPart, F.dual_realPart] at h1
  rw [← BKM.variance_block d q hq ht _ hi, BKM.block_imaginaryPart, F.dual_imaginaryPart] at h2
  have hh := add_le_add h1 h2
  rw [← mul_add, ← mul_add, BKM.variance_parts b p hp hs, BKM.variance_parts d q hq ht] at hh
  exact hh

theorem minimum_complex_hessian
    (F : KrausFlow n) (τ : State n) {r : ℝ} (hr : 0 < r) (hτ : τ = thermalState n r hr)
    (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1) (hκ0 : 0 < κ)
    (c a β ζ : ℝ) (hc : 0 < c) (ha : 0 < a) (hβ : 0 ≤ β) (hζ : 0 < ζ)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (d : HilbertBasis (K ⊕ L) ℂ (Fock n)) (q : K ⊕ L → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-a*entropy ρ+
        β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-a*entropy σ+
        β*energy σ+ζ*numberMoment 4 σ) :
    ∃ G : GibbsData n (ζ/a) ρ, ∀ (Z : Matrix K K ℂ),
      (1-κ)^2*BKM.variance G.basis (gibbsWeight G.eigenval) (F.dual (FiniteBlock.block d Z)) ≤
        (a/c)*BKM.variance d q (FiniteBlock.block d Z) := by
  obtain ⟨G,hG⟩ := minimum_component_hessian F τ hr hτ κ hκ hκ0 c a β ζ hc ha hβ hζ ρ hmρ
    d q hq ht he0 hmin
  let _ := G.nonempty
  refine ⟨G,?_⟩
  apply complex_component_hessian F c a κ G.basis (gibbsWeight G.eigenval)
    (gibbsWeight_pos G.eigenval G.heat) (gibbsWeight_hasSum G.eigenval G.heat).summable d q hq ht.summable
  intro Z hZ
  have hh := hG Z hZ
  rw [BKM.variance, BKM.normSq_mean_selfAdjoint G.basis _ _
    (F.dual_selfAdjoint (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (FiniteBlock.block_symmetric d Z hZ))), mean_expectation ρ G.basis (gibbsWeight G.eigenval) G.eigen]
  exact hh
end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J K L : Type*} [Fintype K] [DecidableEq K]
 theorem flow_complex_hessian (F : KrausFlow n) (τ : State n) (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1)
    (c a β ζ C : ℝ) (hc : 0 < c) (ha : 0 < a) (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀ j, 0 < p j) (hs : HasSum p 1)
    (d : HilbertBasis (K ⊕ L) ℂ (Fock n)) (q : K ⊕ L → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he : ∀ j, ρ.op (b j) = (p j : ℂ) • b j)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hτ : FiniteEnergy τ)
    (hcross : ∀ σ, FiniteMoment 4 σ →
      Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((F.map σ).op (d j))).re))
    (hcτ : Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) (τ.op (d j))).re))
    (hlog : ∀ σ, FiniteMoment 4 σ → crossEntropy b p σ =
      (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+C)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-
        a*entropy ρ+β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-
        a*entropy σ+β*energy σ+ζ*numberMoment 4 σ)
    (Z : Matrix K K ℂ) :
    (1-κ)^2*BKM.variance b p (F.dual (FiniteBlock.block d Z)) ≤
      (a/c)*BKM.variance d q (FiniteBlock.block d Z) := by
  apply complex_component_hessian F c a κ b p hp hs.summable d q hq ht.summable
  intro T hT
  rw [BKM.variance, BKM.normSq_mean_selfAdjoint b p _
    (F.dual_selfAdjoint (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (FiniteBlock.block_symmetric d T hT))), mean_expectation ρ b p he]
  exact flow_full_hessian F τ κ hκ c a β ζ C hc ha ρ hmρ b p hp hs d q hq ht
    he he0 hτ hcross hcτ hlog hmin T hT
end EntropyPhotonNumber

namespace BKM
open scoped BigOperators
open DiagonalForms.System
variable {I J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem mean_reindex (b : HilbertBasis J ℂ E) (p : J → ℝ) (e : I ≃ J) (Z : E →L[ℂ] E) :
    mean (reindexBasis b e) (p ∘ e) Z=mean b p Z := by
  simp only [mean, entry, reindexBasis_apply, Function.comp_def]
  exact e.tsum_eq (fun j : J => (p j : ℂ)*inner ℂ (b j) (Z (b j)))

theorem quadratic_reindex (b : HilbertBasis J ℂ E) (p : J → ℝ) (e : I ≃ J) (Z : E →L[ℂ] E) :
    quadratic (reindexBasis b e) (p ∘ e) Z=quadratic b p Z := by
  simp only [quadratic, entry, reindexBasis_apply, Function.comp_def]
  exact (Equiv.prodCongr e e).tsum_eq (fun ij : J × J => logMean (p ij.1) (p ij.2)*Complex.normSq (inner ℂ (b ij.1) (Z (b ij.2))))

theorem variance_reindex (b : HilbertBasis J ℂ E) (p : J → ℝ) (e : I ≃ J) (Z : E →L[ℂ] E) :
    variance (reindexBasis b e) (p ∘ e) Z=variance b p Z := by
  rw [variance, quadratic_reindex, mean_reindex, variance]
end BKM

namespace EntropyPhotonNumber
open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J : Type*} [DecidableEq J]

theorem minimum_all_blocks_hessian
    (F : KrausFlow n) (τ : State n) {r : ℝ} (hr : 0 < r) (hτ : τ = thermalState n r hr)
    (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1) (hκ0 : 0 < κ)
    (c a β ζ : ℝ) (hc : 0 < c) (ha : 0 < a) (hβ : 0 ≤ β) (hζ : 0 < ζ)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (d : HilbertBasis J ℂ (Fock n)) (q : J → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-a*entropy ρ+
        β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-a*entropy σ+
        β*energy σ+ζ*numberMoment 4 σ) :
    ∃ G : GibbsData n (ζ/a) ρ, ∀ (s : Finset J) (Z : Matrix s s ℂ),
      (1-κ)^2*BKM.variance G.basis (gibbsWeight G.eigenval)
        (F.dual (FiniteBlock.block (BKM.reindexBasis d (Equiv.sumCompl (· ∈ s))) Z)) ≤
      (a/c)*BKM.variance d q (FiniteBlock.block (BKM.reindexBasis d (Equiv.sumCompl (· ∈ s))) Z) := by
  classical
  obtain ⟨G,hG⟩ := flow_minimum_gibbs F τ hr hτ κ hκ hκ0 c a β ζ hc ha hβ hζ ρ hmρ
    d q hq ht he0 hmin
  let _ := G.nonempty
  let htκ : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  let ρ0 := mixture (1-κ) htκ (F.map ρ) τ
  have hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ0.op := by
    rw [← hτ]
    exact mixture_replacement_le κ hκ (F.map ρ) τ
  have hfτ : FiniteEnergy τ := by simpa only [hτ] using thermalState_finiteEnergy n r hr
  have hcross (σ : State n) (hm : FiniteMoment 4 σ) :
      Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((F.map σ).op (d j))).re) :=
    crossEntropy_finite ρ0 (F.map σ) (F.finiteEnergy _ (finiteMoment_finiteEnergy (by norm_num) hm))
      hr hκ0 hκ.2 hle d q hq ht he0
  have hcτ := crossEntropy_finite ρ0 τ hfτ hr hκ0 hκ.2 hle d q hq ht he0
  have hα : 0 ≤ c*(1-κ)/a := div_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hκ.2)) ha.le
  have hlog (σ : State n) (hm : FiniteMoment 4 σ) :
      crossEntropy G.basis (gibbsWeight G.eigenval) σ =
        (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+
          Real.log (heatPartition G.eigenval) :=
    (G.crossEntropy_hamiltonian d q hq ht F hα (div_nonneg hβ ha.le) (div_pos hζ ha)
      hG σ hm (hcross σ hm)).tsum_eq
  refine ⟨G, fun s Z => ?_⟩
  let e := Equiv.sumCompl (fun j => j ∈ s)
  let d' := BKM.reindexBasis d e
  have hq' : ∀ j, 0 < (q ∘ e) j := fun j => hq (e j)
  have ht' : HasSum (q ∘ e) 1 := e.hasSum_iff.mpr ht
  have he0' : ∀ j, (mixture (1-κ) htκ (F.map ρ) τ).op (d' j)=((q ∘ e) j:ℂ) • d' j := by
    intro j
    simpa only [d', BKM.reindexBasis_apply, Function.comp_def] using he0 (e j)
  have hcross' (σ : State n) (hm : FiniteMoment 4 σ) :
      Summable (fun j => (-Real.log ((q ∘ e) j))*(inner ℂ (d' j) ((F.map σ).op (d' j))).re) := by
    simpa only [d', BKM.reindexBasis_apply, Function.comp_def] using
      (hcross σ hm).comp_injective e.injective
  have hcτ' : Summable (fun j => (-Real.log ((q ∘ e) j))*(inner ℂ (d' j) (τ.op (d' j))).re) := by
    simpa only [d', BKM.reindexBasis_apply, Function.comp_def] using hcτ.comp_injective e.injective
  have hlog' (σ : State n) (hm : FiniteMoment 4 σ) :
      crossEntropy G.basis (gibbsWeight G.eigenval) σ =
        (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d' (q ∘ e) (F.map σ)+(β/a)*energy σ+
          Real.log (heatPartition G.eigenval) := by
    simpa only [d', crossEntropy_reindex] using hlog σ hm
  have hh := flow_complex_hessian F τ κ hκ c a β ζ (Real.log (heatPartition G.eigenval)) hc ha
    ρ hmρ G.basis (gibbsWeight G.eigenval) (gibbsWeight_pos G.eigenval G.heat)
    (gibbsWeight_hasSum G.eigenval G.heat) d' (q ∘ e) hq' ht' G.eigen he0' hfτ hcross' hcτ' hlog' hmin Z
  simpa only [d', BKM.variance_reindex] using hh
end EntropyPhotonNumber

namespace BKM

section
open scoped BigOperators ComplexConjugate
open DiagonalForms.System
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def vector (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (Z : E →L[ℂ] E) : lp (fun _ : J × J => ℂ) 2 :=
  EnsembleL2.vector (fun ij => (Real.sqrt (logMean (p ij.1) (p ij.2)):ℂ)*entry b Z ij.1 ij.2) (by
    convert! logMean_summable b p hp hs Z using 1
    ext ij
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (logMean_pos (hp _) (hp _)).le])

@[simp] theorem vector_apply (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (Z : E →L[ℂ] E) (ij : J × J) :
    vector b p hp hs Z ij=(Real.sqrt (logMean (p ij.1) (p ij.2)):ℂ)*entry b Z ij.1 ij.2 := rfl

theorem vector_add (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (Z T : E →L[ℂ] E) : vector b p hp hs (Z+T)=vector b p hp hs Z+vector b p hp hs T := by
  apply lp.ext
  ext ij
  simp [entry_add, mul_add]

theorem vector_sub (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (Z T : E →L[ℂ] E) : vector b p hp hs (Z-T)=vector b p hp hs Z-vector b p hp hs T := by
  apply lp.ext
  ext ij
  simp [entry_sub, mul_sub]

theorem vector_smul (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (c : ℂ) (Z : E →L[ℂ] E) : vector b p hp hs (c • Z)=c • vector b p hp hs Z := by
  apply lp.ext
  ext ij
  simp [entry_smul, mul_left_comm]

theorem vector_norm (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (Z : E →L[ℂ] E) : ‖vector b p hp hs Z‖^2=quadratic b p Z := by
  have hh := lp.hasSum_norm (p := (2:ENNReal)) (by norm_num) (vector b p hp hs Z)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, vector_apply, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_mul, Complex.normSq_ofReal,
    Real.mul_self_sqrt (logMean_pos (hp _) (hp _)).le] at hh
  exact hh.tsum_eq.symm
theorem vector_id_inner (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : Summable p)
    (Z : E →L[ℂ] E) :
    inner ℂ (vector b p hp hs (ContinuousLinearMap.id ℂ E)) (vector b p hp hs Z)=mean b p Z := by
  classical
  have hh := lp.hasSum_inner (𝕜 := ℂ) (vector b p hp hs (ContinuousLinearMap.id ℂ E)) (vector b p hp hs Z)
  rw [← hh.tsum_eq, hh.summable.tsum_prod]
  unfold mean
  congr 1
  ext i
  calc
    _ = (p i:ℂ)*entry b Z i i := by
      rw [tsum_eq_single i]
      · simp only [vector_apply, entry_id, ite_true, mul_one, logMean_self,
          RCLike.inner_apply, Complex.conj_ofReal]
        rw [show (Real.sqrt (p i):ℂ)*entry b Z i i*(Real.sqrt (p i):ℂ)=
          ((Real.sqrt (p i)*Real.sqrt (p i):ℝ):ℂ)*entry b Z i i by push_cast; ring]
        rw [Real.mul_self_sqrt (hp i).le]
      · intro j hj
        simp [Ne.symm hj, entry_id]
theorem vector_id_norm (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : HasSum p 1) :
    ‖vector b p hp hs.summable (ContinuousLinearMap.id ℂ E)‖^2=1 := by
  have hh := vector_id_inner b p hp hs.summable (ContinuousLinearMap.id ℂ E)
  rw [mean_id b p hs, inner_self_eq_norm_sq_to_K] at hh
  have hh' := congrArg Complex.re hh
  change ((‖vector b p hp hs.summable (ContinuousLinearMap.id ℂ E)‖ : ℂ)^2).re=1 at hh'
  rw [← Complex.ofReal_pow, Complex.ofReal_re] at hh'
  exact hh'
theorem quadratic_center (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : HasSum p 1)
    (Z : E →L[ℂ] E) : quadratic b p (center b p Z)=variance b p Z := by
  rw [← vector_norm b p hp hs.summable, center, vector_sub, vector_smul, norm_sub_sq (𝕜 := ℂ)]
  have hi : inner ℂ (vector b p hp hs.summable Z) (vector b p hp hs.summable (ContinuousLinearMap.id ℂ E))=
      conj (mean b p Z) := by
    rw [← inner_conj_symm, vector_id_inner]
  rw [vector_norm, inner_smul_right, hi, norm_smul, mul_pow, vector_id_norm b p hp hs, mul_one]
  simp only [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  change quadratic b p Z-2*Complex.normSq (mean b p Z)+Complex.normSq (mean b p Z)=variance b p Z
  unfold variance
  ring

end

open scoped BigOperators ComplexConjugate
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem center_id (b : HilbertBasis J ℂ E) (p : J → ℝ) (hs : HasSum p 1) :
    center b p (ContinuousLinearMap.id ℂ E)=0 := by simp [center, mean_id b p hs]

theorem center_center (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : HasSum p 1)
    (Z : E →L[ℂ] E) : center b p (center b p Z)=center b p Z := by
  simp only [center, mean_sub b p hp hs.summable, mean_smul, mean_id b p hs, mul_one,
    sub_self, zero_smul, sub_zero]

theorem center_sub_scalar (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : HasSum p 1)
    (Z : E →L[ℂ] E) (c : ℂ) :
    center b p (Z-c • ContinuousLinearMap.id ℂ E)=center b p Z := by
  change centerLM b p hp hs.summable (Z-c • ContinuousLinearMap.id ℂ E)=_
  simp only [map_sub, map_smul, centerLM_apply, center_id b p hs, smul_zero, sub_zero]

variable [CompleteSpace E]

theorem variance_sub_scalar (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 < p j) (hs : HasSum p 1)
    (Z : E →L[ℂ] E) (c : ℂ) :
    variance b p (Z-c • ContinuousLinearMap.id ℂ E)=variance b p Z := by
  rw [← quadratic_center b p hp hs, center_sub_scalar b p (fun j => (hp j).le) hs,
    quadratic_center b p hp hs]
end BKM

namespace CenteredTests
open scoped BigOperators
variable {J E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem exists_block [DecidableEq J] (b : HilbertBasis J ℂ E) (p : J → ℝ) (hp : ∀j,0 ≤ p j) (hs : Summable p)
    {Z : E →L[ℂ] E} (hZ : Z ∈ operatorSpace b p) :
    ∃ (s : Finset J) (M : Matrix s s ℂ),
      Z=BKM.center b p (FiniteBlock.block (BKM.reindexBasis b (Equiv.sumCompl (· ∈ s))) M) := by
  classical
  obtain ⟨c,rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hZ
  let s := c.support.biUnion (fun ij => {ij.1,ij.2})
  have hsub : c.support ⊆ s ×ˢ s := by
    intro ij hij
    simp only [Finset.mem_product]
    constructor
    · exact Finset.mem_biUnion.mpr ⟨ij,hij,by simp⟩
    · exact Finset.mem_biUnion.mpr ⟨ij,hij,by simp⟩
  refine ⟨s, (fun i j => c (i.val,j.val)), ?_⟩
  have hc : (c.sum fun ij a => a • generator b p ij)=
      BKM.centerLM b p hp hs (c.sum fun ij a => a • InnerProductSpace.rankOne ℂ (b ij.1) (b ij.2)) := by
    simp only [Finsupp.sum, map_sum, map_smul, BKM.centerLM_apply, ← generator_eq_center]
  rw [hc, BKM.centerLM_apply]
  congr 1
  rw [c.sum_of_support_subset hsub _ (by intro ij; simp)]
  simp only [FiniteBlock.block, BKM.reindexBasis_apply, Equiv.sumCompl_apply_inl]
  rw [Finset.sum_product]
  simp only [← Finset.sum_coe_sort s]
end CenteredTests

namespace EntropyPhotonNumber

section
open QuantumTrace DiagonalForms.System
variable {n : ℕ} {I J : Type*} [DecidableEq J]

theorem KrausFlow.dual_id (F : KrausFlow n) :
    F.dual (ContinuousLinearMap.id ℂ (Fock n))=ContinuousLinearMap.id ℂ (Fock n) :=
  KrausBounded.dual_id F.V F.norm

theorem blocks_to_centered_hessian
    (F : KrausFlow n) (b : HilbertBasis I ℂ (Fock n)) (p : I → ℝ)
    (hp : ∀ i, 0 < p i) (hs : HasSum p 1)
    (d : HilbertBasis J ℂ (Fock n)) (q : J → ℝ) (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (a κ : ℝ)
    (hh : ∀ (s : Finset J) (M : Matrix s s ℂ),
      (1-κ)^2*BKM.variance b p (F.dual (FiniteBlock.block (BKM.reindexBasis d (Equiv.sumCompl (· ∈ s))) M)) ≤
        a*BKM.variance d q (FiniteBlock.block (BKM.reindexBasis d (Equiv.sumCompl (· ∈ s))) M))
    (Z : Fock n →L[ℂ] Fock n) (hZ : Z ∈ CenteredTests.operatorSpace d q) :
    (1-κ)^2*BKM.quadratic b p (BKM.center b p (F.dual Z)) ≤ a*BKM.quadratic d q Z := by
  rw [BKM.quadratic_center b p hp hs]
  have hz : BKM.variance d q Z=BKM.quadratic d q Z := by
    rw [BKM.variance, CenteredTests.mean_eq_zero d q (fun j => (hq j).le) ht hZ]
    simp
  rw [← hz]
  obtain ⟨s,M,rfl⟩ := CenteredTests.exists_block d q (fun j => (hq j).le) ht.summable hZ
  simp only [BKM.center, F.dual_sub, F.dual_smul, F.dual_id,
    BKM.variance_sub_scalar b p hp hs, BKM.variance_sub_scalar d q hq ht]
  exact hh s M
end

open QuantumTrace DiagonalForms.System
variable {n : ℕ} {J : Type*} [DecidableEq J]
theorem minimum_centered_hessian
    (F : KrausFlow n) (τ : State n) {r : ℝ} (hr : 0 < r) (hτ : τ = thermalState n r hr)
    (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1) (hκ0 : 0 < κ)
    (c a β ζ : ℝ) (hc : 0 < c) (ha : 0 < a) (hβ : 0 ≤ β) (hζ : 0 < ζ)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (d : HilbertBasis J ℂ (Fock n)) (q : J → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-a*entropy ρ+
        β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-a*entropy σ+
        β*energy σ+ζ*numberMoment 4 σ) :
    ∃ G : GibbsData n (ζ/a) ρ, ∀ (Z : Fock n →L[ℂ] Fock n),
      Z ∈ CenteredTests.operatorSpace d q →
      (1-κ)^2*BKM.quadratic G.basis (gibbsWeight G.eigenval)
        (BKM.center G.basis (gibbsWeight G.eigenval) (F.dual Z)) ≤
      (a/c)*BKM.quadratic d q Z := by
  obtain ⟨G,hG⟩ := minimum_all_blocks_hessian F τ hr hτ κ hκ hκ0 c a β ζ hc ha hβ hζ ρ hmρ
    d q hq ht he0 hmin
  let _ := G.nonempty
  refine ⟨G, ?_⟩
  exact blocks_to_centered_hessian F G.basis (gibbsWeight G.eigenval)
    (gibbsWeight_pos G.eigenval G.heat) (gibbsWeight_hasSum G.eigenval G.heat) d q hq ht (a/c) κ hG

theorem minimum_all_blocks_hessian_data
    (F : KrausFlow n) (τ : State n) {r : ℝ} (hr : 0 < r) (hτ : τ = thermalState n r hr)
    (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1) (hκ0 : 0 < κ)
    (c a β ζ : ℝ) (hc : 0 < c) (ha : 0 < a) (hβ : 0 ≤ β) (hζ : 0 < ζ)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (d : HilbertBasis J ℂ (Fock n)) (q : J → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-a*entropy ρ+
        β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-a*entropy σ+
        β*energy σ+ζ*numberMoment 4 σ) :
    ∃ G : GibbsData n (ζ/a) ρ,
      (∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re =
        ENNReal.ofReal (c*(1-κ)/a)*
          sliceMoment d (fun j => ENNReal.ofReal (-Real.log (q j))) F.V (energyInverse n x)+
        ENNReal.ofReal (β/a)*numberVectorMoment (energyInverse n x)) ∧
      ∀ (s : Finset J) (Z : Matrix s s ℂ),
      (1-κ)^2*BKM.variance G.basis (gibbsWeight G.eigenval)
        (F.dual (FiniteBlock.block (BKM.reindexBasis d (Equiv.sumCompl (· ∈ s))) Z)) ≤
      (a/c)*BKM.variance d q (FiniteBlock.block (BKM.reindexBasis d (Equiv.sumCompl (· ∈ s))) Z) := by
  classical
  obtain ⟨G,hG⟩ := flow_minimum_gibbs F τ hr hτ κ hκ hκ0 c a β ζ hc ha hβ hζ ρ hmρ
    d q hq ht he0 hmin
  let _ := G.nonempty
  let htκ : 1-κ ∈ Set.Icc 0 1 := ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩
  let ρ0 := mixture (1-κ) htκ (F.map ρ) τ
  have hle : (κ : ℂ) • (thermalState n r hr).op ≤ ρ0.op := by
    rw [← hτ]
    exact mixture_replacement_le κ hκ (F.map ρ) τ
  have hfτ : FiniteEnergy τ := by simpa only [hτ] using thermalState_finiteEnergy n r hr
  have hcross (σ : State n) (hm : FiniteMoment 4 σ) :
      Summable (fun j => (-Real.log (q j))*(inner ℂ (d j) ((F.map σ).op (d j))).re) :=
    crossEntropy_finite ρ0 (F.map σ) (F.finiteEnergy _ (finiteMoment_finiteEnergy (by norm_num) hm))
      hr hκ0 hκ.2 hle d q hq ht he0
  have hcτ := crossEntropy_finite ρ0 τ hfτ hr hκ0 hκ.2 hle d q hq ht he0
  have hα : 0 ≤ c*(1-κ)/a := div_nonneg (mul_nonneg hc.le (sub_nonneg.mpr hκ.2)) ha.le
  have hlog (σ : State n) (hm : FiniteMoment 4 σ) :
      crossEntropy G.basis (gibbsWeight G.eigenval) σ =
        (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d q (F.map σ)+(β/a)*energy σ+
          Real.log (heatPartition G.eigenval) :=
    (G.crossEntropy_hamiltonian d q hq ht F hα (div_nonneg hβ ha.le) (div_pos hζ ha)
      hG σ hm (hcross σ hm)).tsum_eq
  refine ⟨G, hG, fun s Z => ?_⟩
  let e := Equiv.sumCompl (fun j => j ∈ s)
  let d' := BKM.reindexBasis d e
  have hq' : ∀ j, 0 < (q ∘ e) j := fun j => hq (e j)
  have ht' : HasSum (q ∘ e) 1 := e.hasSum_iff.mpr ht
  have he0' : ∀ j, (mixture (1-κ) htκ (F.map ρ) τ).op (d' j)=((q ∘ e) j:ℂ) • d' j := by
    intro j
    simpa only [d', BKM.reindexBasis_apply, Function.comp_def] using he0 (e j)
  have hcross' (σ : State n) (hm : FiniteMoment 4 σ) :
      Summable (fun j => (-Real.log ((q ∘ e) j))*(inner ℂ (d' j) ((F.map σ).op (d' j))).re) := by
    simpa only [d', BKM.reindexBasis_apply, Function.comp_def] using
      (hcross σ hm).comp_injective e.injective
  have hcτ' : Summable (fun j => (-Real.log ((q ∘ e) j))*(inner ℂ (d' j) (τ.op (d' j))).re) := by
    simpa only [d', BKM.reindexBasis_apply, Function.comp_def] using hcτ.comp_injective e.injective
  have hlog' (σ : State n) (hm : FiniteMoment 4 σ) :
      crossEntropy G.basis (gibbsWeight G.eigenval) σ =
        (ζ/a)*numberMoment 4 σ+(c*(1-κ)/a)*crossEntropy d' (q ∘ e) (F.map σ)+(β/a)*energy σ+
          Real.log (heatPartition G.eigenval) := by
    simpa only [d', crossEntropy_reindex] using hlog σ hm
  have hh := flow_complex_hessian F τ κ hκ c a β ζ (Real.log (heatPartition G.eigenval)) hc ha
    ρ hmρ G.basis (gibbsWeight G.eigenval) (gibbsWeight_pos G.eigenval G.heat)
    (gibbsWeight_hasSum G.eigenval G.heat) d' (q ∘ e) hq' ht' G.eigen he0' hfτ hcross' hcτ' hlog' hmin Z
  simpa only [d', BKM.variance_reindex] using hh

theorem minimum_centered_hessian_data
    (F : KrausFlow n) (τ : State n) {r : ℝ} (hr : 0 < r) (hτ : τ = thermalState n r hr)
    (κ : ℝ) (hκ : κ ∈ Set.Icc 0 1) (hκ0 : 0 < κ)
    (c a β ζ : ℝ) (hc : 0 < c) (ha : 0 < a) (hβ : 0 ≤ β) (hζ : 0 < ζ)
    (ρ : State n) (hmρ : FiniteMoment 4 ρ)
    (d : HilbertBasis J ℂ (Fock n)) (q : J → ℝ)
    (hq : ∀ j, 0 < q j) (ht : HasSum q 1)
    (he0 : ∀ j, (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ).op (d j) =
      (q j : ℂ) • d j)
    (hmin : ∀ σ, FiniteMoment 4 σ →
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map ρ) τ)-a*entropy ρ+
        β*energy ρ+ζ*numberMoment 4 ρ ≤
      c*entropy (mixture (1-κ) ⟨sub_nonneg.mpr hκ.2, sub_le_self _ hκ.1⟩ (F.map σ) τ)-a*entropy σ+
        β*energy σ+ζ*numberMoment 4 σ) :
    ∃ G : GibbsData n (ζ/a) ρ,
      (∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re =
        ENNReal.ofReal (c*(1-κ)/a)*
          sliceMoment d (fun j => ENNReal.ofReal (-Real.log (q j))) F.V (energyInverse n x)+
        ENNReal.ofReal (β/a)*numberVectorMoment (energyInverse n x)) ∧
      ∀ (Z : Fock n →L[ℂ] Fock n),
      Z ∈ CenteredTests.operatorSpace d q →
      (1-κ)^2*BKM.quadratic G.basis (gibbsWeight G.eigenval)
        (BKM.center G.basis (gibbsWeight G.eigenval) (F.dual Z)) ≤
      (a/c)*BKM.quadratic d q Z := by
  obtain ⟨G,hform,hG⟩ := minimum_all_blocks_hessian_data F τ hr hτ κ hκ hκ0 c a β ζ hc ha hβ hζ ρ hmρ
    d q hq ht he0 hmin
  let _ := G.nonempty
  refine ⟨G, hform, ?_⟩
  exact blocks_to_centered_hessian F G.basis (gibbsWeight G.eigenval)
    (gibbsWeight_pos G.eigenval G.heat) (gibbsWeight_hasSum G.eigenval G.heat) d q hq ht (a/c) κ hG
end EntropyPhotonNumber

namespace QuantumTrace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem positive_eq_of_quadratic {A B : E →L[ℂ] E} (hA : A.IsPositive) (hB : B.IsPositive)
    (h : ∀ x, (inner ℂ x (A x)).re=(inner ℂ x (B x)).re) : A=B := by
  apply ContinuousLinearMap.coe_injective
  apply (ext_inner_map A.toLinearMap B.toLinearMap).mp
  intro x
  have hAx := ((ContinuousLinearMap.isPositive_iff_complex A).mp hA x).1
  have hBx := ((ContinuousLinearMap.isPositive_iff_complex B).mp hB x).1
  change inner ℂ (A x) x=inner ℂ (B x) x
  rw [← hAx, ← hBx]
  congr 1
  change (inner ℂ (A x) x).re=(inner ℂ (B x) x).re
  rw [← Complex.conj_re (inner ℂ (A x) x), inner_conj_symm,
    ← Complex.conj_re (inner ℂ (B x) x), inner_conj_symm]
  exact h x
end QuantumTrace

namespace EntropyPhotonNumber
open QuantumTrace
namespace GibbsData
variable {n : ℕ} {k : ℝ} {ρ : State n} (G : GibbsData n k ρ)

def quarticLogarithm : Fock n →L[ℂ] Fock n :=
  logarithmSandwich (gibbsFactor rootNumberWeight rootNumberWeight_one_le k G.B)
    (inversePower rootNumberWeight rootNumberWeight_one_le 4) (Real.log (heatPartition G.eigenval))

theorem quarticLogarithm_parseval (hk : 0<k) (x : Fock n) :
    HasSum (fun j => -Real.log (gibbsWeight G.eigenval j)*
      ‖inner ℂ (G.basis j) (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)‖^2)
      (inner ℂ x (G.quarticLogarithm x)).re := by
  let _ := G.nonempty
  exact gibbs_logarithmSandwich_parseval G.basis _ _
    (gibbsFactor_strictPositive rootNumberWeight rootNumberWeight_one_le hk G.positive)
    (inversePower_positive rootNumberWeight rootNumberWeight_one_le 4).isSymmetric
    (inversePower_injective rootNumberWeight rootNumberWeight_one_le 4)
    G.eigenval G.positive_eigenval G.inverse_eigen G.heat x

theorem exact_logarithmic_identity {J : Type*}
    (F : KrausFlow n) (τ : State n) {r δ : ℝ} (hr : 0<r) (hδ : 0<δ) (hδ1 : δ≤1)
    (hle : (δ:ℂ) • (thermalState n r hr).op ≤ τ.op)
    (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ) (hp : ∀j, 0<p j) (hs : HasSum p 1)
    (he : ∀j, τ.op (b j)=(p j:ℂ) • b j)
    {α β : ℝ} (hα : 0≤α) (hβ : 0≤β)
    (hform : ∀ x, ENNReal.ofReal (inner ℂ x (G.B x)).re = ENNReal.ofReal α*
      sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) F.V (energyInverse n x)+
      ENNReal.ofReal β*numberVectorMoment (energyInverse n x)) :
    ∃ C D : Fock n →L[ℂ] Fock n, C.IsPositive ∧ D.IsPositive ∧
      (∀ x, ENNReal.ofReal (inner ℂ x (C x)).re =
        sliceMoment b (fun j => ENNReal.ofReal (-Real.log (p j))) F.V
          (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
      (∀ x, ENNReal.ofReal (inner ℂ x (D x)).re =
        numberVectorMoment (inversePower rootNumberWeight rootNumberWeight_one_le 4 x)) ∧
      G.quarticLogarithm = (k:ℂ) • (1 : Fock n →L[ℂ] Fock n)+(α:ℂ) • C+(β:ℂ) • D+
        (Real.log (heatPartition G.eigenval):ℂ) •
          (inversePower rootNumberWeight rootNumberWeight_one_le 4 *
            inversePower rootNumberWeight rootNumberWeight_one_le 4) := by
  obtain ⟨C,hC,hCe⟩ := logarithmic_slice_representation τ hr hδ hδ1 hle b p hp hs he
    F.V F.F F.nonneg F.norm F.energy
  obtain ⟨D,hD,hDe⟩ := number_form_representation n
  have hSum : ((α:ℂ) • C+(β:ℂ) • D).IsPositive :=
    (hC.smul_of_nonneg (by exact_mod_cast hα)).add (hD.smul_of_nonneg (by exact_mod_cast hβ))
  have hB : G.B=(α:ℂ) • C+(β:ℂ) • D := by
    apply positive_eq_of_quadratic G.positive hSum
    intro x
    apply (ENNReal.ofReal_eq_ofReal_iff (G.positive.re_inner_nonneg_right x) (hSum.re_inner_nonneg_right x)).mp
    change ENNReal.ofReal (inner ℂ x (G.B x)).re=ENNReal.ofReal (inner ℂ x (((α:ℂ) • C+(β:ℂ) • D) x)).re
    rw [hform]
    have hh : (inner ℂ x (((α:ℂ) • C+(β:ℂ) • D) x)).re =
        α*(inner ℂ x (C x)).re+β*(inner ℂ x (D x)).re := by
      simp only [add_apply,smul_apply,inner_add_right,inner_smul_right,
        Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    have hCn : 0≤(inner ℂ x (C x)).re := hC.re_inner_nonneg_right x
    have hDn : 0≤(inner ℂ x (D x)).re := hD.re_inner_nonneg_right x
    rw [hh,ENNReal.ofReal_add (mul_nonneg hα hCn)
      (mul_nonneg hβ hDn),ENNReal.ofReal_mul hα, ENNReal.ofReal_mul hβ,hCe,hDe]
  let R := inversePower (rootNumberWeight (n:=n)) rootNumberWeight_one_le 3
  have hRa : R.adjoint=R := inversePower_adjoint _ _ _
  have hCR : (R*C*R).IsPositive := by simpa only [hRa, ← ContinuousLinearMap.mul_def, mul_assoc] using hC.adjoint_conj R
  have hDR : (R*D*R).IsPositive := by simpa only [hRa, ← ContinuousLinearMap.mul_def, mul_assoc] using hD.adjoint_conj R
  have hquad (T : Fock n →L[ℂ] Fock n) (x : Fock n) :
      inner ℂ x ((R*T*R) x)=inner ℂ (R x) (T (R x)) := by
    change inner ℂ x (R (T (R x)))=_
    exact ((inversePower_positive rootNumberWeight rootNumberWeight_one_le 3).isSymmetric x (T (R x))).symm
  refine ⟨R*C*R,R*D*R,hCR,hDR,?_,?_,?_⟩
  · intro x
    rw [hquad,hCe,energyInverse_mul_three]
  · intro x
    rw [hquad,hDe,energyInverse_mul_three]
  · simp only [quarticLogarithm, logarithmSandwich, gibbsFactor,hB]
    apply ContinuousLinearMap.ext
    intro x
    simp only [add_apply,smul_apply,mul_apply_eq_comp,map_add,map_smul,one_apply_eq_self]
    simp only [R, RCLike.real_smul_eq_coe_smul (K:=ℂ), add_assoc]
    rfl
end GibbsData
end EntropyPhotonNumber

end

end OAI
