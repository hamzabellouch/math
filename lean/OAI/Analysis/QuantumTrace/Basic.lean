import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

namespace QuantumTrace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

def diagonalTrace (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (inner ℂ (b i) (T (b i))).re

omit [CompleteSpace E] in
theorem basis_hasSum_norm_sq (b : HilbertBasis ι ℂ E) (x : E) :
    HasSum (fun i => ‖inner ℂ (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := (b.hasSum_inner_mul_inner x x).mapL Complex.reCLM
  convert! h using 1
  · ext i
    simp only [Complex.reCLM_apply]
    conv_rhs => rw [← inner_conj_symm x (b i), Complex.conj_mul']
    simp [← Complex.ofReal_pow]
  · simp [← Complex.ofReal_pow]

omit [CompleteSpace E] in
theorem basis_tsum_enorm_sq (b : HilbertBasis ι ℂ E) (x : E) :
    (∑' i, ENNReal.ofReal (‖inner ℂ (b i) x‖ ^ 2)) =
      ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (basis_hasSum_norm_sq b x).summable,
    (basis_hasSum_norm_sq b x).tsum_eq]

theorem sqrt_inner_eq {T : E →L[ℂ] E} (hT : T.IsPositive) (x : E) :
    (inner ℂ x (T x)).re = ‖CFC.sqrt T x‖ ^ 2 := by
  have hn : 0 ≤ T := ContinuousLinearMap.nonneg_iff_isPositive.mpr hT
  have hs : (CFC.sqrt T).IsSymmetric :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)).isSymmetric
  have he : CFC.sqrt T (CFC.sqrt T x) = T x := by
    simpa [pow_two] using congrArg (fun A : E →L[ℂ] E => A x) (CFC.sq_sqrt T hn)
  have hr : inner ℂ x (CFC.sqrt T (CFC.sqrt T x)) =
      inner ℂ (CFC.sqrt T x) (CFC.sqrt T x) := by
    exact (hs x (CFC.sqrt T x)).symm
  rw [← he, hr]
  simp [← Complex.ofReal_pow]

theorem diagonalTrace_eq_sqrt (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) :
    diagonalTrace b T = ∑' i, ENNReal.ofReal (‖CFC.sqrt T (b i)‖ ^ 2) := by
  simp only [diagonalTrace, sqrt_inner_eq hT]

omit [CompleteSpace E] in
theorem sum_norm_sq_basis_independent (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    (T : E →L[ℂ] E) (hT : T.IsSymmetric) :
    (∑' i, ENNReal.ofReal (‖T (b i)‖ ^ 2)) =
      ∑' j, ENNReal.ofReal (‖T (c j)‖ ^ 2) := by
  calc
    _ = ∑' i, ∑' j, ENNReal.ofReal (‖inner ℂ (c j) (T (b i))‖ ^ 2) := by
      simp only [basis_tsum_enorm_sq]
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (c j) (T (b i))‖ ^ 2) := ENNReal.tsum_comm
    _ = ∑' j, ∑' i, ENNReal.ofReal (‖inner ℂ (b i) (T (c j))‖ ^ 2) := by
      congr 1; ext j
      congr 1; ext i
      have he : inner ℂ (c j) (T (b i)) = inner ℂ (T (c j)) (b i) :=
        (hT (c j) (b i)).symm
      rw [he, norm_inner_symm]
    _ = _ := by simp only [basis_tsum_enorm_sq]

theorem diagonalTrace_basis_independent (b : HilbertBasis ι ℂ E)
    (c : HilbertBasis κ ℂ E) {T : E →L[ℂ] E} (hT : T.IsPositive) :
    diagonalTrace b T = diagonalTrace c T := by
  rw [diagonalTrace_eq_sqrt b hT, diagonalTrace_eq_sqrt c hT]
  apply sum_norm_sq_basis_independent
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)).isSymmetric

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

theorem quadratic_le_trace_mul_norm_sq (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) (x : E) :
    (inner ℂ x (T x)).re ≤ τ * ‖x‖ ^ 2 := by
  let S := CFC.sqrt T
  have hs : S.IsSymmetric :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)).isSymmetric
  have ht' : HasSum (fun i => ‖S (b i)‖ ^ 2) τ := by
    simpa only [sqrt_inner_eq hT] using ht
  rw [sqrt_inner_eq hT, ← (basis_hasSum_norm_sq b (S x)).tsum_eq,
    ← ht'.tsum_eq, ← tsum_mul_right]
  apply Summable.tsum_le_tsum
  · intro i
    have he : inner ℂ (b i) (S x) = inner ℂ (S (b i)) x := (hs (b i) x).symm
    rw [he]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) (S (b i)) x) 2
  · exact (basis_hasSum_norm_sq b (S x)).summable
  · exact ht'.summable.mul_right _

theorem operator_le_trace_smul_id (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) :
    T ≤ (τ : ℂ) • ContinuousLinearMap.id ℂ E := by
  rw [ContinuousLinearMap.le_def]
  refine ⟨?_, ?_⟩
  · exact (LinearMap.IsSymmetric.smul (by simp) LinearMap.IsSymmetric.id).sub hT.isSymmetric
  · intro x
    change 0 ≤ (inner ℂ (((τ : ℂ) • ContinuousLinearMap.id ℂ E - T) x) x).re
    rw [sub_apply, smul_apply, ContinuousLinearMap.id_apply, inner_sub_left, inner_smul_left,
      hT.inner_left_eq_inner_right x x]
    simpa [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow] using
      sub_nonneg.mpr (quadratic_le_trace_mul_norm_sq b hT ht x)

theorem norm_le_trace (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) : ‖T‖ ≤ τ := by
  have hn : 0 ≤ τ := ht.nonneg (fun i => hT.re_inner_nonneg_right (b i))
  have h := CStarAlgebra.norm_le_norm_of_le_of_nonneg
    (operator_le_trace_smul_id b hT ht) (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT)
  apply h.trans
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
  exact mul_le_of_le_one_right hn ContinuousLinearMap.norm_id_le

end

section
open Filter

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_apply_sq_le_basis_sum (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    {τ : ℝ} (ht : HasSum (fun i => ‖T (b i)‖ ^ 2) τ) (x : E) :
    ‖T x‖ ^ 2 ≤ τ * ‖x‖ ^ 2 := by
  have hlim := ((T.hasSum (b.hasSum_repr x)).norm).pow 2
  apply le_of_tendsto hlim
  apply Eventually.of_forall
  intro s
  simp only [map_smul]
  calc
    ‖∑ i ∈ s, b.repr x i • T (b i)‖ ^ 2 ≤
        (∑ i ∈ s, ‖b.repr x i‖ * ‖T (b i)‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [norm_smul] using norm_sum_le s (fun i => b.repr x i • T (b i))
    _ ≤ (∑ i ∈ s, ‖b.repr x i‖ ^ 2) * (∑ i ∈ s, ‖T (b i)‖ ^ 2) :=
      Finset.sum_mul_sq_le_sq_mul_sq s _ _
    _ ≤ ‖x‖ ^ 2 * τ := by
      apply mul_le_mul
      · simpa only [b.repr_apply_apply] using b.orthonormal.sum_inner_products_le x (s := s)
      · simpa only [ht.tsum_eq] using ht.summable.sum_le_tsum s (fun _ _ => sq_nonneg _)
      · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      · exact sq_nonneg _
    _ = _ := mul_comm _ _

omit [CompleteSpace E] [CompleteSpace F] in
theorem norm_le_sqrt_basis_sum (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    {τ : ℝ} (ht : HasSum (fun i => ‖T (b i)‖ ^ 2) τ) :
    ‖T‖ ≤ Real.sqrt τ := by
  have hn : 0 ≤ τ := ht.nonneg (fun i => sq_nonneg _)
  apply T.opNorm_le_bound (Real.sqrt_nonneg _)
  intro x
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  rw [← pow_two, ← pow_two, mul_pow, Real.sq_sqrt hn]
  exact norm_apply_sq_le_basis_sum b T ht x

end

section
open Filter ContinuousLinearMap InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {ι : Type*}

def basisApprox (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F) (s : Finset ι) : E →L[ℂ] F :=
  ∑ i ∈ s, rankOne ℂ (T (b i)) (b i)

omit [CompleteSpace E] [CompleteSpace F] in
theorem basisApprox_apply_basis (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    (s : Finset ι) (j : ι) [Decidable (j ∈ s)] : basisApprox b T s (b j) = if j ∈ s then T (b j) else 0 := by
  classical
  simp only [basisApprox, sum_apply, rankOne_apply, orthonormal_iff_ite.mp b.orthonormal]
  simp

omit [CompleteSpace E] [CompleteSpace F] in
theorem basisApprox_isCompactOperator (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    (s : Finset ι) : IsCompactOperator (basisApprox b T s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa [basisApprox] using (isCompactOperator_zero : IsCompactOperator (0 : E →L[ℂ] F))
  | @insert j s hj hs =>
    rw [basisApprox, Finset.sum_insert hj]
    apply IsCompactOperator.add _ hs
    rw [rankOne_def']
    exact (isCompactOperator_of_locallyCompactSpace_rng (toSpanSingleton ℂ (T (b j)))).comp_clm (innerSL ℂ (b j))

omit [CompleteSpace E] [CompleteSpace F] in
theorem basisApprox_norm_sub_le (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    {τ : ℝ} (ht : HasSum (fun i => ‖T (b i)‖ ^ 2) τ) (s : Finset ι) :
    ‖T - basisApprox b T s‖ ≤ Real.sqrt (τ - ∑ i ∈ s, ‖T (b i)‖ ^ 2) := by
  classical
  apply norm_le_sqrt_basis_sum b
  have hfin : HasSum (fun i => if i ∈ s then ‖T (b i)‖ ^ 2 else 0)
      (∑ i ∈ s, ‖T (b i)‖ ^ 2) := by
    have hh := (hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ι) (f := fun i => if i ∈ s then ‖T (b i)‖ ^ 2 else 0)
      (s := s) (by intro i hi; simp [hi]))
    simpa using hh
  convert! ht.sub hfin using 1
  ext i
  simp only [sub_apply, basisApprox_apply_basis]
  split_ifs <;> simp

omit [CompleteSpace E] in
theorem compact_of_summable_basis_norm_sq (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] F)
    (ht : Summable (fun i => ‖T (b i)‖ ^ 2)) : IsCompactOperator T := by
  have hlim : Tendsto (fun s : Finset ι => basisApprox b T s) atTop (𝓝 T) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hzero : Tendsto (fun s : Finset ι =>
        Real.sqrt ((∑' i, ‖T (b i)‖ ^ 2) - ∑ i ∈ s, ‖T (b i)‖ ^ 2)) atTop (𝓝 0) := by
      convert! Real.continuous_sqrt.continuousAt.tendsto.comp
        (tendsto_const_nhds.sub ht.hasSum) using 1
      simp
    apply squeeze_zero (fun _ => norm_nonneg _) ?_ hzero
    intro s
    rw [norm_sub_rev]
    exact basisApprox_norm_sub_le b T ht.hasSum s
  exact isCompactOperator_of_tendsto hlim
    (Eventually.of_forall (fun s => basisApprox_isCompactOperator b T s))

end

section
open ContinuousLinearMap Module.End Submodule
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

theorem compact_of_positive_finite_trace (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hT : T.IsPositive)
    (ht : Summable (fun i => (inner ℂ (b i) (T (b i))).re)) : IsCompactOperator T := by
  have hs : IsCompactOperator (CFC.sqrt T : E →L[ℂ] E) := compact_of_summable_basis_norm_sq b _
    (by simpa only [sqrt_inner_eq hT] using ht)
  have he : (CFC.sqrt T) ∘L CFC.sqrt T = T := by
    simpa only [pow_two, ContinuousLinearMap.mul_def] using CFC.sq_sqrt T
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT)
  rw [← he]
  exact hs.comp_clm _

theorem exists_eigenbasis {T : E →L[ℂ] E} (hc : IsCompactOperator T)
    (hs : T.IsSymmetric) :
    ∃ (J : Type u) (b : HilbertBasis J ℂ E) (e : J → ℂ),
      ∀ j, T (b j) = e j • b j := by
  classical
  let S (μ : ℂ) := eigenspace T.toLinearMap μ
  let α (μ : ℂ) := Classical.choose (exists_hilbertBasis ℂ (S μ))
  let b (μ : ℂ) : HilbertBasis (α μ) ℂ (S μ) :=
    Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ (S μ)))
  let v : (Σ μ, α μ) → E := fun a => (b a.1 a.2 : E)
  have hv : Orthonormal ℂ v :=
    hs.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal (fun μ => (b μ).orthonormal)
  have hsp : (span ℂ (Set.range v))ᗮ = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    have hzero (μ : ℂ) (y : S μ) : inner ℂ x (y : E) = 0 := by
      have hi (i : α μ) : inner ℂ x ((b μ i : S μ) : E) = 0 := by
        exact (mem_orthogonal' _ _).mp hx _ (subset_span ⟨⟨μ, i⟩, rfl⟩)
      have hh := ((innerSL ℂ x).comp (S μ).subtypeL).hasSum ((b μ).hasSum_repr y)
      simpa [ContinuousLinearMap.comp_apply, hi] using hh.tsum_eq.symm
    have hx' : x ∈ (⨆ μ, eigenspace T.toLinearMap μ)ᗮ := by
      rw [← iInf_orthogonal]
      apply (mem_iInf _).mpr
      intro μ
      rw [mem_orthogonal']
      intro y hy
      exact hzero μ ⟨y, hy⟩
    rwa [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hc hs] at hx'
  refine ⟨Σ μ, α μ, HilbertBasis.mkOfOrthogonalEqBot hv hsp, Sigma.fst, ?_⟩
  intro j
  simp only [HilbertBasis.coe_mkOfOrthogonalEqBot]
  exact mem_eigenspace_iff.mp (b j.1 j.2).property

end

section
open ContinuousLinearMap Module.End
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem cfc_apply_eigenvector {T : E →L[ℂ] E} (hs : T.IsSymmetric)
    {x : E} {μ : ℂ} (he : T x = μ • x) (f : ℂ → ℂ)
    (hf : ContinuousOn f (spectrum ℂ T)) : cfc f T x = f μ • x := by
  by_cases hx : x = 0
  · simp [hx]
  have hev : HasEigenvalue T.toLinearMap μ :=
    hasEigenvalue_of_hasEigenvector ⟨mem_eigenspace_iff.mpr he, hx⟩
  have hm : μ ∈ spectrum ℂ T := by
    rw [ContinuousLinearMap.spectrum_eq]
    exact hev.mem_spectrum
  have hr := hs.conj_eigenvalue_eq_self hev
  have allf (g : C(spectrum ℂ T, ℂ)) :
      cfcHom hs.isSelfAdjoint.isStarNormal g x = g ⟨μ, hm⟩ • x := by
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      change cfcHom hs.isSelfAdjoint.isStarNormal (algebraMap ℂ C(spectrum ℂ T, ℂ) r) x = r • x
      rw [AlgHomClass.commutes]
      rfl
    | id => simpa only [cfcHom_id, ContinuousMap.restrict_apply, ContinuousMap.id_apply] using he
    | star_id =>
      rw [map_star, cfcHom_id, hs.isSelfAdjoint.star_eq]
      simpa [hr] using he
    | add g h hg hh => simp [map_add, hg, hh, add_smul]
    | mul g h hg hh =>
      simp only [map_mul, mul_apply_eq_comp, hh, map_smul, hg,
        ContinuousMap.mul_apply, mul_smul]
      exact smul_comm _ _ _
    | frequently g hg =>
      have hc : IsClosed {g : C(spectrum ℂ T, ℂ) |
          cfcHom hs.isSelfAdjoint.isStarNormal g x = g ⟨μ, hm⟩ • x} :=
        isClosed_eq ((cfcHom_continuous _).clm_apply continuous_const)
          ((continuous_eval_const _).smul continuous_const)
      exact hc.closure_eq.le hg.mem_closure
  rw [cfc_apply f T hs.isSelfAdjoint.isStarNormal hf]
  exact allf ⟨_, hf.domRestrict⟩

def entropyOperator (T : E →L[ℂ] E) : E →L[ℂ] E := cfc Real.negMulLog T

theorem entropyOperator_eq_complex {T : E →L[ℂ] E} (hs : T.IsSymmetric) :
    entropyOperator T = cfc (fun z : ℂ => (-(z.re * Real.log z.re) : ℂ)) T := by
  rw [entropyOperator, cfc_real_eq_complex Real.negMulLog hs.isSelfAdjoint]
  congr 1
  funext z
  simp [Real.negMulLog_def]

theorem entropyOperator_positive {T : E →L[ℂ] E} (hp : T.IsPositive) (hn : ‖T‖ ≤ 1) :
    (entropyOperator T).IsPositive := by
  cases subsingleton_or_nontrivial E with
  | inl h =>
    have : entropyOperator T = 0 := Subsingleton.elim _ _
    rw [this]
    exact isPositive_zero
  | inr h =>
    apply ContinuousLinearMap.nonneg_iff_isPositive.mp
    exact cfc_nonneg (fun x hx => Real.negMulLog_nonneg
    (spectrum_nonneg_of_nonneg (ContinuousLinearMap.nonneg_iff_isPositive.mpr hp) hx)
    ((Real.le_norm_self _).trans ((spectrum.norm_le_norm_of_mem hx).trans hn)))

end

section

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

theorem hasSum_trace_basis (b : HilbertBasis ι ℂ E) (c : HilbertBasis κ ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) :
    HasSum (fun i => (inner ℂ (c i) (T (c i))).re) τ := by
  have hnB (i : ι) : 0 ≤ (inner ℂ (b i) (T (b i))).re := hp.re_inner_nonneg_right _
  have hnC (i : κ) : 0 ≤ (inner ℂ (c i) (T (c i))).re := hp.re_inner_nonneg_right _
  have hb : diagonalTrace b T = ENNReal.ofReal τ := by
    rw [diagonalTrace, ← ENNReal.ofReal_tsum_of_nonneg hnB ht.summable, ht.tsum_eq]
  have hc : diagonalTrace c T = ENNReal.ofReal τ :=
    (diagonalTrace_basis_independent b c hp).symm.trans hb
  have hn : τ ≥ 0 := le_of_tendsto_of_tendsto tendsto_const_nhds ht
    (Filter.Eventually.of_forall (fun s => Finset.sum_nonneg (fun i _ => hp.re_inner_nonneg_right (b i))))
  have hfin : (∑' i, ENNReal.ofReal (inner ℂ (c i) (T (c i))).re) ≠ ⊤ := by
    rw [← diagonalTrace, hc]
    exact ENNReal.ofReal_ne_top
  have hh := ENNReal.hasSum_toReal hfin
  simp only [ENNReal.toReal_ofReal (hnC _)] at hh
  have he : (∑' i, (inner ℂ (c i) (T (c i))).re) = τ := by
    rw [← ENNReal.toReal_ofReal hn, ← hc, diagonalTrace, ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (hnC _)]
  exact he ▸ hh

theorem exists_positive_eigenbasis (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) :
    ∃ (J : Type u) (c : HilbertBasis J ℂ E) (p : J → ℝ),
      (∀ j, 0 ≤ p j) ∧ HasSum p τ ∧ ∀ j, T (c j) = (p j : ℂ) • c j := by
  obtain ⟨J, c, e, he⟩ := exists_eigenbasis
    (compact_of_positive_finite_trace b hp ht.summable) hp.isSymmetric
  have hie (j : J) : inner ℂ (c j) (T (c j)) = e j := by
    rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, c.orthonormal.norm_eq_one]
    simp
  have her (j : J) : (e j).re ≥ 0 := by
    rw [← hie]
    exact hp.re_inner_nonneg_right _
  have hec (j : J) : (e j).re = e j := by
    have hr := hp.isSymmetric.conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (he j), c.orthonormal.ne_zero j⟩)
    apply Complex.ext
    · rfl
    · have := congrArg Complex.im hr
      simp only [Complex.conj_im] at this
      simpa using (show (0 : ℝ) = (e j).im by linarith)
  refine ⟨J, c, fun j => (e j).re, her, ?_, ?_⟩
  · simpa only [hie] using hasSum_trace_basis b c hp ht
  · intro j
    rw [hec, he]

omit [CompleteSpace E] in

theorem hasSum_quadratic_eigenbasis (b : HilbertBasis ι ℂ E) (T : E →L[ℂ] E)
    (p : ι → ℝ) (he : ∀ j, T (b j) = (p j : ℂ) • b j) (x : E) :
    HasSum (fun j => p j * ‖inner ℂ (b j) x‖ ^ 2) (inner ℂ x (T x)).re := by
  have hh := ((T.hasSum (b.hasSum_repr x)).mapL (innerSL ℂ x)).mapL Complex.reCLM
  convert! hh using 1
  ext j
  simp only [Complex.reCLM_apply, innerSL_apply_apply, b.repr_apply_apply,
    ContinuousLinearMap.map_smul, he, smul_eq_mul]
  rw [← inner_conj_symm x (b j)]
  have hn := Complex.mul_conj (inner ℂ (b j) x)
  rw [← mul_assoc, mul_right_comm, hn]
  simp [Complex.normSq_eq_norm_sq, -Complex.ofReal_pow, mul_comm]

end

section

variable {ι : Type*}

theorem entropy_jensen_hasSum {p w : ι → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hw : ∀ i, 0 ≤ w i) (hw1 : HasSum w 1) {a s : ℝ}
    (ha : HasSum (fun i => w i * p i) a)
    (hs : HasSum (fun i => w i * Real.negMulLog (p i)) s) :
    s ≤ Real.negMulLog a := by
  apply le_of_tendsto_of_tendsto hs (Real.continuous_negMulLog.tendsto a |>.comp ha)
  apply Filter.Eventually.of_forall
  intro t
  have ht : ∑ i ∈ t, w i ≤ 1 := by
    rw [← hw1.tsum_eq]
    exact hw1.summable.sum_le_tsum t (fun i _ => hw i)
  have hf := Real.concaveOn_negMulLog.map_add_sum_le
    (t := t) (w := w) (p := p) (v := 1 - ∑ i ∈ t, w i) (q := 0)
    (fun i _ => hw i) (by ring) (fun i _ => hp i) (sub_nonneg.mpr ht) (by simp)
  simpa [Function.comp_def] using hf

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem entropyOperator_apply_eigenvector {T : E →L[ℂ] E} (hs : T.IsSymmetric)
    {x : E} {p : ℝ} (he : T x = (p : ℂ) • x) :
    entropyOperator T x = (Real.negMulLog p : ℂ) • x := by
  rw [entropyOperator_eq_complex hs]
  have hf : Continuous (fun z : ℂ => (Real.negMulLog z.re : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_negMulLog.comp Complex.continuous_re)
  simpa [Real.negMulLog_def] using cfc_apply_eigenvector hs he _ hf.continuousOn

theorem entropyOperator_quadratic_le (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ)
    (x : E) (hx : ‖x‖ = 1) :
    (inner ℂ x (entropyOperator T x)).re ≤ Real.negMulLog (inner ℂ x (T x)).re := by
  obtain ⟨J, c, p, hpn, _, he⟩ := exists_positive_eigenbasis b hp ht
  apply entropy_jensen_hasSum hpn (fun j => sq_nonneg ‖inner ℂ (c j) x‖)
  · simpa only [hx, one_pow] using basis_hasSum_norm_sq c x
  · simpa only [mul_comm] using hasSum_quadratic_eigenbasis c T p he x
  · simpa only [mul_comm] using hasSum_quadratic_eigenbasis c (entropyOperator T)
      (fun j => Real.negMulLog (p j)) (fun j => entropyOperator_apply_eigenvector hp.isSymmetric (he j)) x

end

section

theorem negMulLog_le_crossEntropy {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    Real.negMulLog p ≤ q - p + p * (-Real.log q) := by
  by_cases hz : p = 0
  · simp [hz, le_of_lt hq]
  have h := mul_le_mul_of_nonneg_left
    (Real.negMulLog_le_one_sub_self (div_nonneg hp hq.le)) hq.le
  change q * (-(p / q) * Real.log (p / q)) ≤ q * (1 - p / q) at h
  rw [Real.log_div hz hq.ne'] at h
  have hl : q * (-(p / q) * (Real.log p - Real.log q)) =
      -p * Real.log p + p * Real.log q := by field_simp; ring
  have hr : q * (1 - p / q) = q - p := by field_simp
  rw [hl, hr] at h
  dsimp [Real.negMulLog]
  linarith

theorem entropy_summable_and_le_crossEntropy {ι : Type*} (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : HasSum p 1) (hq1 : HasSum q 1)
    (hcross : Summable (fun i => p i * (-Real.log (q i)))) :
    Summable (fun i => Real.negMulLog (p i)) ∧
      (∑' i, Real.negMulLog (p i)) ≤ ∑' i, p i * (-Real.log (q i)) := by
  have hp_le (i : ι) : p i ≤ 1 := by
    simpa only [hp1.tsum_eq] using hp1.summable.le_tsum i (fun j _ => hp j)
  have he0 (i : ι) : 0 ≤ Real.negMulLog (p i) := Real.negMulLog_nonneg (hp i) (hp_le i)
  have hle (i : ι) := negMulLog_le_crossEntropy (hp i) (hq i)
  have hsum := (hq1.summable.sub hp1.summable).add hcross
  have he : Summable (fun i => Real.negMulLog (p i)) :=
    Summable.of_nonneg_of_le he0 hle hsum
  refine ⟨he, ?_⟩
  have hh := he.tsum_le_tsum hle hsum
  rw [(hq1.summable.sub hp1.summable).tsum_add hcross,
    hq1.summable.tsum_sub hp1.summable, hp1.tsum_eq, hq1.tsum_eq] at hh
  simpa only [sub_self, zero_add] using hh

theorem tsum_finite_product (n : ℕ) (w : ℕ → ℝ≥0∞) :
    (∑' k : Fin n → ℕ, ∏ j, w (k j)) = (∑' m, w m) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).tsum_eq]
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [ENNReal.tsum_prod' ]
    simp only [ENNReal.tsum_mul_left, ih, ENNReal.tsum_mul_right, pow_succ']

def thermalWeight (n : ℕ) (r : ℝ) (k : Fin n → ℕ) : ℝ :=
  ∏ j, ((r + 1)⁻¹ * (r / (r + 1)) ^ (k j))

theorem thermalWeight_pos (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin n → ℕ) :
    0 < thermalWeight n r k := by
  apply Finset.prod_pos
  intro j _
  positivity

theorem hasSum_thermalWeight (n : ℕ) {r : ℝ} (hr : 0 < r) :
    HasSum (thermalWeight n r) 1 := by
  have hr1 : 0 < r + 1 := by linarith
  have hz : r / (r + 1) < 1 := (div_lt_one hr1).mpr (by linarith)
  have hw : HasSum (fun m : ℕ => (r + 1)⁻¹ * (r / (r + 1)) ^ m) 1 := by
    convert! (hasSum_geometric_of_lt_one (div_nonneg hr.le hr1.le) hz).mul_left (r + 1)⁻¹ using 1
    field_simp
    ring
  have he : (∑' m : ℕ, ENNReal.ofReal ((r + 1)⁻¹ * (r / (r + 1)) ^ m)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity) hw.summable, hw.tsum_eq]
    simp
  have ht : (∑' k : Fin n → ℕ, ENNReal.ofReal (thermalWeight n r k)) = 1 := by
    calc
      _ = ∑' k : Fin n → ℕ, ∏ j, ENNReal.ofReal ((r + 1)⁻¹ * (r / (r + 1)) ^ k j) := by
        congr 1; ext k
        exact ENNReal.ofReal_prod_of_nonneg (fun _ _ => by positivity)
      _ = 1 := by rw [tsum_finite_product n (fun m => ENNReal.ofReal ((r + 1)⁻¹ * (r / (r + 1)) ^ m)), he, one_pow]
  have hf : (∑' k : Fin n → ℕ, ENNReal.ofReal (thermalWeight n r k)) ≠ ⊤ := by
    rw [ht]; exact ENNReal.one_ne_top
  have hs := ENNReal.hasSum_toReal hf
  rw [← ENNReal.tsum_toReal_eq (fun _ => ENNReal.ofReal_ne_top), ht] at hs
  simpa only [ENNReal.toReal_ofReal (thermalWeight_pos n hr _).le, ENNReal.toReal_one] using hs

theorem log_thermalWeight (n : ℕ) {r : ℝ} (hr : 0 < r) (k : Fin n → ℕ) :
    -Real.log (thermalWeight n r k) =
      n * Real.log (r + 1) + (∑ j, (k j : ℝ)) * Real.log ((r + 1) / r) := by
  have hr1 : 0 < r + 1 := by linarith
  rw [thermalWeight, Real.log_prod (fun _ _ => by positivity)]
  simp only [Real.log_mul (inv_ne_zero hr1.ne') (pow_ne_zero _ (div_ne_zero hr.ne' hr1.ne')),
    Real.log_inv, Real.log_pow, Real.log_div hr.ne' hr1.ne',
    Real.log_div hr1.ne' hr.ne', Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.sum_mul]
  ring

theorem summable_thermal_crossEntropy {n : ℕ} {p : (Fin n → ℕ) → ℝ}
    (hp : Summable p) (hE : Summable (fun k => (∑ j, (k j : ℝ)) * p k))
    {r : ℝ} (hr : 0 < r) :
    Summable (fun k => p k * (-Real.log (thermalWeight n r k))) := by
  have hh := (hp.mul_right (n * Real.log (r + 1))).add
    (hE.mul_right (Real.log ((r + 1) / r)))
  convert! hh using 1
  ext k
  rw [log_thermalWeight n hr k]
  ring

theorem tsum_thermal_crossEntropy {n : ℕ} {p : (Fin n → ℕ) → ℝ}
    (hp : HasSum p 1) (hE : Summable (fun k => (∑ j, (k j : ℝ)) * p k))
    {r : ℝ} (hr : 0 < r) :
    (∑' k, p k * (-Real.log (thermalWeight n r k))) =
      n * Real.log (r + 1) + (∑' k, (∑ j, (k j : ℝ)) * p k) * Real.log ((r + 1) / r) := by
  have he (k : Fin n → ℕ) : p k * (-Real.log (thermalWeight n r k)) =
      p k * (n * Real.log (r + 1)) + ((∑ j, (k j : ℝ)) * p k) * Real.log ((r + 1) / r) := by
    rw [log_thermalWeight n hr k]; ring
  simp only [he]
  rw [(hp.summable.mul_right _).tsum_add (hE.mul_right _), tsum_mul_right,
    tsum_mul_right, hp.tsum_eq, one_mul]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem entropy_summable_finite_energy {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive)
    (ht : HasSum (fun k => (inner ℂ (b k) (T (b k))).re) 1)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re)) :
    Summable (fun k => (inner ℂ (b k) (entropyOperator T (b k))).re) := by
  have hc := (entropy_summable_and_le_crossEntropy
    (fun k => (inner ℂ (b k) (T (b k))).re) (thermalWeight n 1)
    (fun k => hp.re_inner_nonneg_right (b k)) (thermalWeight_pos n zero_lt_one)
    ht (hasSum_thermalWeight n zero_lt_one)
    (summable_thermal_crossEntropy ht.summable hE zero_lt_one)).1
  have hn : ‖T‖ ≤ 1 := by
    exact norm_le_trace b hp ht
  exact Summable.of_nonneg_of_le
    (fun k => (entropyOperator_positive hp hn).re_inner_nonneg_right (b k))
    (fun k => entropyOperator_quadratic_le b hp ht (b k) (b.orthonormal.norm_eq_one k)) hc

theorem entropy_le_thermal_crossEntropy {n : ℕ} (b : HilbertBasis (Fin n → ℕ) ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive)
    (ht : HasSum (fun k => (inner ℂ (b k) (T (b k))).re) 1)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re))
    {r : ℝ} (hr : 0 < r) :
    (∑' k, (inner ℂ (b k) (entropyOperator T (b k))).re) ≤
      n * Real.log (r + 1) +
      (∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re) * Real.log ((r + 1) / r) := by
  have hc := entropy_summable_and_le_crossEntropy
    (fun k => (inner ℂ (b k) (T (b k))).re) (thermalWeight n r)
    (fun k => hp.re_inner_nonneg_right (b k)) (thermalWeight_pos n hr)
    ht (hasSum_thermalWeight n hr) (summable_thermal_crossEntropy ht.summable hE hr)
  calc
    _ ≤ ∑' k, Real.negMulLog (inner ℂ (b k) (T (b k))).re :=
      (entropy_summable_finite_energy b hp ht hE).tsum_le_tsum
        (fun k => entropyOperator_quadratic_le b hp ht (b k) (b.orthonormal.norm_eq_one k)) hc.1
    _ ≤ _ := by
      rw [← tsum_thermal_crossEntropy ht hE hr]
      exact hc.2

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι : Type*}

theorem entropy_nonneg (b : HilbertBasis ι ℂ E) {T : E →L[ℂ] E} (hp : T.IsPositive)
    (ht : HasSum (fun k => (inner ℂ (b k) (T (b k))).re) 1) :
    0 ≤ ∑' k, (inner ℂ (b k) (entropyOperator T (b k))).re := by
  exact tsum_nonneg (fun k =>
    (entropyOperator_positive hp (norm_le_trace b hp ht)).re_inner_nonneg_right (b k))

theorem entropy_energy_bound {n : ℕ} (hn : 0 < n) (b : HilbertBasis (Fin n → ℕ) ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive)
    (ht : HasSum (fun k => (inner ℂ (b k) (T (b k))).re) 1)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re)) :
    let e := ∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re
    (∑' k, (inner ℂ (b k) (entropyOperator T (b k))).re) ≤
      n * ((e / n + 1) * Real.log (e / n + 1) - (e / n) * Real.log (e / n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let e := ∑' k, (∑ j, (k j : ℝ)) * (inner ℂ (b k) (T (b k))).re
  have he : 0 ≤ e := tsum_nonneg (fun k =>
    mul_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (hp.re_inner_nonneg_right _))
  change _ ≤ n * ((e / n + 1) * Real.log (e / n + 1) - e / n * Real.log (e / n))
  rcases eq_or_lt_of_le he with he0 | hepos
  · have hez : e = 0 := he0.symm
    simp only [hez, zero_div, zero_add, Real.log_one, mul_zero, zero_mul, sub_zero]
    by_contra h
    have hS : 0 < ∑' k, (inner ℂ (b k) (entropyOperator T (b k))).re := lt_of_not_ge h
    let r := (∑' k, (inner ℂ (b k) (entropyOperator T (b k))).re) / (2 * n)
    have hr : 0 < r := div_pos hS (mul_pos (by norm_num) hnR)
    have hu := entropy_le_thermal_crossEntropy b hp ht hE hr
    change _ ≤ n * Real.log (r + 1) + e * _ at hu
    rw [hez, zero_mul, add_zero] at hu
    have hl : n * Real.log (r + 1) ≤ n * r := by
      exact mul_le_mul_of_nonneg_left
        (by simpa only [add_sub_cancel_right] using Real.log_le_sub_one_of_pos (by linarith : 0 < r + 1)) hnR.le
    have hrval : n * r = (∑' k, (inner ℂ (b k) (entropyOperator T (b k))).re) / 2 := by
      dsimp [r]
      field_simp
    linarith
  · have hr : 0 < e / n := div_pos hepos hnR
    have hu := entropy_le_thermal_crossEntropy b hp ht hE hr
    change _ ≤ n * Real.log (e / n + 1) + e * _ at hu
    convert hu using 1
    rw [Real.log_div (by positivity : e / n + 1 ≠ 0) hr.ne']
    field_simp
    ring

end

section

theorem entropy_summable_le_reference {ι : Type*} (p a : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpu : ∀ i, p i ≤ 1) (ha : ∀ i, 0 < a i)
    {m : ℝ} (hpm : HasSum p m) (ham : HasSum a m)
    (hc : Summable (fun i => p i * (-Real.log (a i)))) :
    Summable (fun i => Real.negMulLog (p i)) ∧
    (∑' i, Real.negMulLog (p i)) ≤ ∑' i, p i * (-Real.log (a i)) := by
  have he0 (i : ι) : 0 ≤ Real.negMulLog (p i) := Real.negMulLog_nonneg (hp i) (hpu i)
  have hle (i : ι) := negMulLog_le_crossEntropy (hp i) (ha i)
  have hsum := (ham.summable.sub hpm.summable).add hc
  have he : Summable (fun i => Real.negMulLog (p i)) :=
    Summable.of_nonneg_of_le he0 hle hsum
  refine ⟨he, ?_⟩
  have hh := he.tsum_le_tsum hle hsum
  rw [(ham.summable.sub hpm.summable).tsum_add hc,
    ham.summable.tsum_sub hpm.summable, hpm.tsum_eq, ham.tsum_eq] at hh
  simpa only [sub_self, zero_add] using hh

theorem entropy_small_mass_bound {n : ℕ} (p : (Fin n → ℕ) → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hpu : ∀ k, p k ≤ 1) {q : ℝ} (hq : HasSum p q)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * p k)) :
    Summable (fun k => Real.negMulLog (p k)) ∧
    (∑' k, Real.negMulLog (p k)) ≤
      (n + 1 : ℝ) * Real.negMulLog q + n * q ^ 2 +
        (∑' k, (∑ j, (k j : ℝ)) * p k) * q := by
  have hq0 : 0 ≤ q := hq.nonneg hp
  by_cases hz : q = 0
  · have hpz : ∀ k, p k = 0 := by
      intro k
      apply le_antisymm _ (hp k)
      simpa only [hq.tsum_eq, hz] using hq.summable.le_tsum k (fun j _ => hp j)
    simp only [hpz, Real.negMulLog_zero, tsum_zero, hz, zero_pow (by omega : 2 ≠ 0),
      mul_zero, zero_add, le_refl, and_true]
    exact summable_zero
  have hqp : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hz)
  have hr : 0 < q⁻¹ := inv_pos.mpr hqp
  let a : (Fin n → ℕ) → ℝ := fun k => q * thermalWeight n q⁻¹ k
  have ha : ∀ k, 0 < a k := fun k => mul_pos hqp (thermalWeight_pos n hr k)
  have haq : HasSum a q := by
    simpa only [mul_one] using (hasSum_thermalWeight n hr).mul_left q
  have hlog (k : Fin n → ℕ) : -Real.log (a k) =
      -Real.log q + (-Real.log (thermalWeight n q⁻¹ k)) := by
    change -Real.log (q * thermalWeight n q⁻¹ k) = _
    rw [Real.log_mul hz (thermalWeight_pos n hr k).ne']
    ring
  have hcross : Summable (fun k => p k * (-Real.log (a k))) := by
    simp only [hlog, mul_add]
    exact (hq.summable.mul_right _).add (summable_thermal_crossEntropy hq.summable hE hr)
  obtain ⟨he, hbound⟩ := entropy_summable_le_reference p a hp hpu ha hq haq hcross
  refine ⟨he, hbound.trans ?_⟩
  have hlog1 : Real.log (q⁻¹ + 1) = Real.log (q + 1) - Real.log q := by
    rw [← Real.log_div (by positivity : q + 1 ≠ 0) hz]
    congr 1
    field_simp
    ring
  have hlog2 : Real.log ((q⁻¹ + 1) / q⁻¹) = Real.log (q + 1) := by
    congr 1
    field_simp
    ring
  have hex (k : Fin n → ℕ) : p k * (-Real.log (a k)) =
      p k * (-(n + 1) * Real.log q) +
      (((n : ℝ) * p k) + (∑ j, (k j : ℝ)) * p k) * Real.log (q + 1) := by
    rw [hlog, log_thermalWeight n hr k, hlog1, hlog2]
    ring
  simp only [hex]
  rw [(hq.summable.mul_right _).tsum_add (((hq.summable.mul_left _).add hE).mul_right _),
    tsum_mul_right, tsum_mul_right, (hq.summable.mul_left _).tsum_add hE,
    tsum_mul_left, hq.tsum_eq]
  have hepos : 0 ≤ ∑' k, (∑ j, (k j : ℝ)) * p k :=
    tsum_nonneg (fun k => mul_nonneg (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)) (hp k))
  have hl : Real.log (q + 1) ≤ q := by
    simpa only [add_sub_cancel_right] using Real.log_le_sub_one_of_pos (by linarith : 0 < q + 1)
  have hh := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ (n : ℝ) * q + ∑' k, (∑ j, (k j : ℝ)) * p k)
  dsimp [Real.negMulLog]
  nlinarith

open Filter Topology
open scoped Classical
variable {ι : Type*}
abbrev SequenceHilbert (ι : Type*) : Type _ := ↥(lp (fun _ : ι => ℂ) 2)

def diagonalMap (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) :
    SequenceHilbert ι →L[ℂ] SequenceHilbert ι := by
  let C := |ha.choose|
  have hC : 0 ≤ C := abs_nonneg _
  have hab (i : ι) : ‖a i‖ ≤ C := (ha.choose_spec i).trans (le_abs_self _)
  let f : SequenceHilbert ι →ₗ[ℂ] SequenceHilbert ι :=
    { toFun := fun x => ⟨fun i => a i*x i, ((lp.memℓp x).norm.const_mul C).mono (by
        intro i
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hab i) (norm_nonneg _))⟩
      map_add' := by intro x y; ext i; exact mul_add _ _ _
      map_smul' := by intro c x; ext i; exact mul_left_comm _ _ _ }
  refine f.mkContinuous C (fun x => ?_)
  have h := lp.norm_mono (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (x := f x) (y := (C : ℂ) • x) (fun i => by
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, lp.coeFn_smul, Pi.smul_apply,
        smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hab i) (norm_nonneg _))
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC] using h

@[simp] theorem diagonalMap_apply (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (x : SequenceHilbert ι) (i : ι) : diagonalMap a ha x i = a i*x i := rfl

theorem diagonalMap_norm_le (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    {C : ℝ} (hC : 0 ≤ C) (hab : ∀ i, ‖a i‖ ≤ C) : ‖diagonalMap a ha‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have h := lp.norm_mono (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (x := diagonalMap a ha x) (y := (C : ℂ) • x) (fun i => by
      simp only [diagonalMap_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hab i) (norm_nonneg _))
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC] using h

theorem diagonalMap_injective (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (hn : ∀ i, a i ≠ 0) : Function.Injective (diagonalMap a ha) := by
  intro x y h
  ext i
  exact mul_left_cancel₀ (hn i) (congrArg (fun z : SequenceHilbert ι => z i) h)

theorem diagonalMap_single [DecidableEq ι] (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (i : ι) (z : ℂ) : diagonalMap a ha (lp.single 2 i z) = lp.single 2 i (a i*z) := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [h]

theorem diagonalMap_symmetric (a : ι → ℝ) (ha : ∃ C : ℝ, ∀ i, ‖(a i : ℂ)‖ ≤ C) :
    (diagonalMap (fun i => (a i : ℂ)) ha).IsSymmetric := by
  intro x y
  change (∑' i, inner ℂ (((a i : ℂ)*x i)) (y i)) =
    ∑' i, inner ℂ (x i) ((a i : ℂ)*y i)
  congr 1
  funext i
  change inner ℂ ((a i : ℂ) • x i) (y i) = inner ℂ (x i) ((a i : ℂ) • y i)
  simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

theorem diagonalMap_positive (a : ι → ℝ) (ha : ∃ C : ℝ, ∀ i, ‖(a i : ℂ)‖ ≤ C)
    (hp : ∀ i, 0 ≤ a i) : (diagonalMap (fun i => (a i : ℂ)) ha).IsPositive := by
  refine ⟨diagonalMap_symmetric a ha, ?_⟩
  intro x
  rw [ContinuousLinearMap.reApplyInnerSelf_apply]
  have hsym : inner ℂ (diagonalMap (fun i => (a i : ℂ)) ha x) x =
      inner ℂ x (diagonalMap (fun i => (a i : ℂ)) ha x) := diagonalMap_symmetric a ha x x
  rw [hsym]
  change 0 ≤ (∑' i, inner ℂ (x i) ((a i : ℂ)*x i)).re
  have ht : Summable (fun i => inner ℂ (x i) ((a i : ℂ)*x i)) := by
    simpa only [diagonalMap_apply] using lp.summable_inner x (diagonalMap (fun i => (a i : ℂ)) ha x)
  rw [Complex.re_tsum ht]
  apply tsum_nonneg
  intro i
  have he : (inner ℂ (x i) ((a i : ℂ)*x i)).re = a i*‖x i‖^2 := by
    rw [show (a i : ℂ)*x i = (a i : ℂ) • x i from rfl, inner_smul_right,
      inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [he]
  exact mul_nonneg (hp i) (sq_nonneg _)

end

section
open Filter Topology
open scoped Classical
variable {ι : Type*}

def sequenceBasis (ι : Type*) : HilbertBasis ι ℂ (SequenceHilbert ι) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

@[simp] theorem sequenceBasis_apply (i : ι) : sequenceBasis ι i = lp.single 2 i 1 := rfl

theorem diagonalMap_cut (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C) (s : Finset ι) :
    ∃ hb : ∃ C : ℝ, ∀ i, ‖(if i ∈ s then a i else 0 : ℂ)‖ ≤ C,
      diagonalMap (fun i => if i ∈ s then a i else 0) hb =
        basisApprox (sequenceBasis ι) (diagonalMap a ha) s := by
  classical
  have hb : ∃ C : ℝ, ∀ i, ‖(if i ∈ s then a i else 0 : ℂ)‖ ≤ C := by
    refine ⟨|ha.choose|, fun i => ?_⟩
    split_ifs
    · exact (ha.choose_spec i).trans (le_abs_self _)
    · simp only [norm_zero]; exact abs_nonneg _
  refine ⟨hb, ?_⟩
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro z
  have hz : lp.single (E := fun _ : ι => ℂ) 2 i z = z • sequenceBasis ι i := by
    simp only [sequenceBasis_apply, ← lp.single_smul, smul_eq_mul, mul_one]
  simp only [ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply, hz,
    map_smul, basisApprox_apply_basis]
  rw [sequenceBasis_apply, diagonalMap_single, diagonalMap_single]
  by_cases hi : i ∈ s
  · simp [hi]
  · simp [hi]

theorem diagonalMap_compact (a : ι → ℂ) (ha : ∃ C : ℝ, ∀ i, ‖a i‖ ≤ C)
    (hvan : ∀ ε : ℝ, 0 < ε → ∃ s : Finset ι, ∀ i, i ∉ s → ‖a i‖ ≤ ε) :
    IsCompactOperator (diagonalMap a ha) := by
  classical
  have hlim : Tendsto (fun s : Finset ι => basisApprox (sequenceBasis ι) (diagonalMap a ha) s)
      atTop (𝓝 (diagonalMap a ha)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨s, hs⟩ := hvan (ε/2) (by positivity)
    filter_upwards [eventually_ge_atTop s] with t ht
    obtain ⟨hb, he⟩ := diagonalMap_cut a ha t
    have hd : ∃ C : ℝ, ∀ i, ‖a i - (if i ∈ t then a i else 0 : ℂ)‖ ≤ C := by
      refine ⟨ε/2, fun i => ?_⟩
      by_cases hi : i ∈ t
      · simp only [ite_eq_left hi, sub_self, norm_zero]
        positivity
      · simpa [hi] using hs i (fun h => hi (ht h))
    have heq : diagonalMap a ha - diagonalMap (fun i => if i ∈ t then a i else 0) hb =
        diagonalMap (fun i => a i-(if i ∈ t then a i else 0)) hd := by
      ext x i
      simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, diagonalMap_apply]
      ring
    rw [dist_eq_norm, norm_sub_rev, ← he, heq]
    exact (diagonalMap_norm_le _ hd (C := ε/2) (by positivity) (by
      intro i
      by_cases hi : i ∈ t
      · simp only [ite_eq_left hi, sub_self, norm_zero]
        positivity
      · simpa [hi] using hs i (fun h => hi (ht h)))).trans_lt (by linarith)
  exact isCompactOperator_of_tendsto hlim
    (Eventually.of_forall (fun s => basisApprox_isCompactOperator _ _ s))

end

section
open Filter Topology
variable {ι : Type*}

theorem inversePower_bounded (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    ∃ C : ℝ, ∀ i, ‖(((s i^p)⁻¹ : ℝ) : ℂ)‖ ≤ C := by
  refine ⟨1, fun i => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity [hs i])]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (hs i))

def inversePower (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    SequenceHilbert ι →L[ℂ] SequenceHilbert ι :=
  diagonalMap (fun i => (((s i^p)⁻¹ : ℝ) : ℂ)) (inversePower_bounded s hs p)

@[simp] theorem inversePower_apply (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ)
    (x : SequenceHilbert ι) (i : ι) : inversePower s hs p x i = ((s i^p)⁻¹ : ℝ)*x i := rfl

theorem inversePower_positive (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    (inversePower s hs p).IsPositive := by
  exact diagonalMap_positive _ _ (fun i => inv_nonneg.mpr (pow_nonneg (by linarith [hs i]) _))

theorem inversePower_adjoint (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    (inversePower s hs p).adjoint = inversePower s hs p :=
  (inversePower_positive s hs p).isSelfAdjoint

theorem inversePower_norm_le (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    ‖inversePower s hs p‖ ≤ 1 := by
  apply diagonalMap_norm_le _ _ (by norm_num)
  intro i
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity [hs i])]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (hs i))

theorem inversePower_injective (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p : ℕ) :
    Function.Injective (inversePower s hs p) := by
  apply diagonalMap_injective
  intro i
  exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ (by linarith [hs i])))

theorem inversePower_mul (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (p q : ℕ) :
    inversePower s hs p * inversePower s hs q = inversePower s hs (p+q) := by
  ext x i
  simp only [mul_apply_eq_comp, inversePower_apply, pow_add, mul_inv,
    Complex.ofReal_mul, mul_assoc]

@[simp] theorem inversePower_zero (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) :
    inversePower s hs 0 = 1 := by
  ext x i
  simp

def gibbsFactor (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (k : ℝ)
    (B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) :
    SequenceHilbert ι →L[ℂ] SequenceHilbert ι :=
  k • (1 : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) +
    inversePower s hs 3 * B * inversePower s hs 3

theorem gibbsFactor_strictPositive (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    {k : ℝ} (hk : 0 < k) {B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι}
    (hB : B.IsPositive) : IsStrictlyPositive (gibbsFactor s hs k B) := by
  have hpos := hB.adjoint_conj (inversePower s hs 3)
  rw [inversePower_adjoint] at hpos
  have hb : 0 ≤ inversePower s hs 3 * B * inversePower s hs 3 :=
    ContinuousLinearMap.nonneg_iff_isPositive.mpr hpos
  have hsc : IsStrictlyPositive (k • (1 : SequenceHilbert ι →L[ℂ] SequenceHilbert ι)) := by
    apply IsStrictlyPositive.iff_of_unital.mpr
    constructor
    · apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
      have he : k • (1 : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) =
          diagonalMap (fun _ : ι => (k : ℂ)) ⟨|k|, fun _ => by simp⟩ := by
        ext x i
        simp
      rw [he]
      exact diagonalMap_positive _ _ (fun _ => hk.le)
    · change IsUnit (algebraMap ℝ (SequenceHilbert ι →L[ℂ] SequenceHilbert ι) k)
      exact (isUnit_iff_ne_zero.mpr hk.ne').map _
  exact hsc.add_nonneg hb

def gibbsInverse (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (k : ℝ)
    (B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) :
    SequenceHilbert ι →L[ℂ] SequenceHilbert ι :=
  inversePower s hs 4 * Ring.inverse (gibbsFactor s hs k B) * inversePower s hs 4

theorem gibbsInverse_positive (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    {k : ℝ} (hk : 0 < k) {B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι}
    (hB : B.IsPositive) : (gibbsInverse s hs k B).IsPositive := by
  have hA := gibbsFactor_strictPositive s hs hk hB
  have hi : (Ring.inverse (gibbsFactor s hs k B)).IsPositive := by
    let A := gibbsFactor s hs k B
    have hp : A.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp hA.nonneg
    apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
    intro x
    let y := Ring.inverse A x
    have hAy : A y = x := by
      exact congrArg (fun X : SequenceHilbert ι →L[ℂ] SequenceHilbert ι => X x)
        (Ring.mul_inverse_cancel A hA.isUnit)
    change ((inner ℂ y x).re : ℂ) = inner ℂ y x ∧ 0 ≤ (inner ℂ y x).re
    rw [← hAy]
    have hh := (ContinuousLinearMap.isPositive_iff_complex _).mp hp y
    have es : inner ℂ (A y) y = inner ℂ y (A y) := hp.isSymmetric y y
    change ((inner ℂ (A y) y).re : ℂ) = inner ℂ (A y) y ∧ 0 ≤ (inner ℂ (A y) y).re at hh
    rwa [es] at hh
  have h := hi.adjoint_conj (inversePower s hs 4)
  rw [inversePower_adjoint] at h
  exact h

theorem gibbsInverse_injective (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    {k : ℝ} (hk : 0 < k) {B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι}
    (hB : B.IsPositive) : Function.Injective (gibbsInverse s hs k B) := by
  have hA := (gibbsFactor_strictPositive s hs hk hB).isUnit
  have hinv : Function.Injective (⇑(Ring.inverse (gibbsFactor s hs k B))) := by
    apply Function.LeftInverse.injective (g := gibbsFactor s hs k B)
    intro x
    exact congrArg (fun T : SequenceHilbert ι →L[ℂ] SequenceHilbert ι => T x)
      (Ring.mul_inverse_cancel _ hA)
  exact (inversePower_injective s hs 4).comp (hinv.comp (inversePower_injective s hs 4))

theorem gibbsInverse_compact (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i) (k : ℝ)
    (B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι)
    (hcompact : IsCompactOperator (inversePower s hs 4)) :
    IsCompactOperator (gibbsInverse s hs k B) := by
  exact (hcompact.comp_clm (Ring.inverse (gibbsFactor s hs k B))).comp_clm (inversePower s hs 4)

end

section
open ContinuousLinearMap Module.End Submodule
universe v
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem exists_strictly_positive_eigenbasis {T : E →L[ℂ] E} (hc : IsCompactOperator T)
    (hp : T.IsPositive) (hi : Function.Injective T) :
    ∃ (J : Type v) (b : HilbertBasis J ℂ E) (p : J → ℝ),
      (∀ j, 0 < p j) ∧ ∀ j, T (b j) = (p j : ℂ) • b j := by
  obtain ⟨J, b, e, he⟩ := exists_eigenbasis hc hp.isSymmetric
  have hie (j : J) : inner ℂ (b j) (T (b j)) = e j := by
    rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
    simp
  have hr (j : J) : (e j).re ≥ 0 := by
    rw [← hie]
    exact hp.re_inner_nonneg_right _
  have hec (j : J) : ((e j).re : ℂ) = e j := by
    have h := hp.isSymmetric.conj_eigenvalue_eq_self
      (Module.End.hasEigenvalue_of_hasEigenvector
        ⟨Module.End.mem_eigenspace_iff.mpr (he j), b.orthonormal.ne_zero j⟩)
    apply Complex.ext
    · rfl
    · have := congrArg Complex.im h
      simp only [Complex.conj_im] at this
      simpa using (show (0 : ℝ) = (e j).im by linarith)
  refine ⟨J, b, fun j => (e j).re, fun j => lt_of_le_of_ne (hr j) ?_, ?_⟩
  · intro hz
    have hz' : e j = 0 := by
      change 0 = (e j).re at hz
      rw [← hec, ← hz]; simp
    have ht : T (b j) = T 0 := by simp [he, hz']
    exact b.orthonormal.ne_zero j (hi ht)
  · intro j
    rw [hec, he]

end

section
open Filter Topology
variable {ι : Type*}

theorem gibbsFactor_inner_lower (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    (k : ℝ) {B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι} (hB : B.IsPositive)
    (x : SequenceHilbert ι) :
    k*‖x‖^2 ≤ (inner ℂ x (gibbsFactor s hs k B x)).re := by
  have hp := hB.adjoint_conj (inversePower s hs 3)
  rw [inversePower_adjoint] at hp
  have hn := hp.re_inner_nonneg_right x
  have he : (inner ℂ x (k • x)).re = k*‖x‖^2 := by
    rw [inner_smul_right_eq_smul, Complex.smul_re]
    simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]
  change k*‖x‖^2 ≤ (inner ℂ x (k • x + inversePower s hs 3 (B (inversePower s hs 3 x)))).re
  rw [inner_add_right, Complex.add_re, he]
  exact le_add_of_nonneg_right hn

theorem gibbs_eigenvector_regular (s : ι → ℝ) (hs : ∀ i, 1 ≤ s i)
    {k u : ℝ} (hk : 0 < k) (hu : 0 < u)
    {B : SequenceHilbert ι →L[ℂ] SequenceHilbert ι} (hB : B.IsPositive)
    {ψ : SequenceHilbert ι} (hψ : ‖ψ‖ = 1)
    (he : gibbsInverse s hs k B ψ = ((u⁻¹ : ℝ) : ℂ) • ψ) :
    ∃ y z : SequenceHilbert ι,
      (∀ i, y i = (s i^4 : ℝ)*ψ i) ∧
      (∀ i, z i = (s i^7 : ℝ)*ψ i) ∧
      ‖y‖^2 ≤ u/k ∧
      ‖z‖ ≤ k⁻¹*(u+‖B‖*Real.sqrt (u/k)) := by
  let A := gibbsFactor s hs k B
  have hA : IsUnit A := (gibbsFactor_strictPositive s hs hk hB).isUnit
  let y := (u : ℂ) • Ring.inverse A (inversePower s hs 4 ψ)
  have h4 : inversePower s hs 4 y = ψ := by
    have hem : inversePower s hs 4 (Ring.inverse A (inversePower s hs 4 ψ)) =
        ((u⁻¹ : ℝ) : ℂ) • ψ := he
    change inversePower s hs 4 ((u : ℂ) • Ring.inverse A (inversePower s hs 4 ψ)) = ψ
    rw [(inversePower s hs 4).map_smul, hem, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hu.ne']
    simp
  have hy (i : ι) : y i = (s i^4 : ℝ)*ψ i := by
    have h := congrArg (fun x : SequenceHilbert ι => x i) h4
    simp only [inversePower_apply] at h
    have hn : (s i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hs i])
    push_cast at h ⊢
    field_simp at h ⊢
    exact h
  have hAy : A y = (u : ℂ) • inversePower s hs 4 ψ := by
    have hi := congrArg (fun X : SequenceHilbert ι →L[ℂ] SequenceHilbert ι => X (inversePower s hs 4 ψ))
      (Ring.mul_inverse_cancel A hA)
    simpa only [y, map_smul, mul_apply_eq_comp, one_apply_eq_self] using congrArg ((u : ℂ) • ·) hi
  have hybound : ‖y‖^2 ≤ u/k := by
    have hh := gibbsFactor_inner_lower s hs k hB y
    change k*‖y‖^2 ≤ (inner ℂ y (A y)).re at hh
    rw [hAy, inner_smul_right] at hh
    have hm : inner ℂ y (inversePower s hs 4 ψ) = inner ℂ ψ ψ := by
      calc
        _ = inner ℂ (inversePower s hs 4 y) ψ :=
          ((inversePower_positive s hs 4).isSymmetric y ψ).symm
        _ = _ := congrArg (fun v => inner ℂ v ψ) h4
    rw [hm, inner_self_eq_norm_sq_to_K, hψ] at hh
    norm_num at hh
    exact (le_div_iff₀ hk).mpr (by nlinarith)
  have hynorm : ‖y‖ ≤ Real.sqrt (u/k) :=
    (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr hybound
  let z := ((k⁻¹ : ℝ) : ℂ) • ((u : ℂ) • inversePower s hs 1 ψ - B (inversePower s hs 3 y))
  have hz (i : ι) : z i = (s i^7 : ℝ)*ψ i := by
    have heq := congrArg (fun x : SequenceHilbert ι => x i) hAy
    change k*(y i) + ((s i^3)⁻¹ : ℝ)*(B (inversePower s hs 3 y) i) =
      u*(((s i^4)⁻¹ : ℝ)*ψ i) at heq
    rw [hy i] at heq
    change ((k⁻¹ : ℝ) : ℂ)*((u : ℂ)*(((s i^1)⁻¹ : ℝ)*ψ i) - B (inversePower s hs 3 y) i) = _
    have hn : (s i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hs i])
    have hkn : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
    push_cast at heq ⊢
    field_simp at heq ⊢
    linear_combination -heq
  refine ⟨y, z, hy, hz, hybound, ?_⟩
  have h1 : ‖inversePower s hs 1 ψ‖ ≤ 1 := by
    calc
      _ ≤ ‖inversePower s hs 1‖*‖ψ‖ := (inversePower s hs 1).le_opNorm _
      _ ≤ 1 := by simpa only [hψ, mul_one] using inversePower_norm_le s hs 1
  have h3 : ‖inversePower s hs 3 y‖ ≤ Real.sqrt (u/k) := by
    calc
      _ ≤ ‖inversePower s hs 3‖*‖y‖ := (inversePower s hs 3).le_opNorm _
      _ ≤ ‖y‖ := by nlinarith [inversePower_norm_le s hs 3, norm_nonneg y]
      _ ≤ _ := hynorm
  calc
    ‖z‖ = k⁻¹*‖(u : ℂ) • inversePower s hs 1 ψ - B (inversePower s hs 3 y)‖ := by
      simp only [z, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk)]
    _ ≤ k⁻¹*(‖(u : ℂ) • inversePower s hs 1 ψ‖ + ‖B (inversePower s hs 3 y)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hk.le)
    _ ≤ k⁻¹*(u+‖B‖*Real.sqrt (u/k)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hk.le)
      apply add_le_add
      · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
        nlinarith
      · exact (B.le_opNorm _).trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))

@[simp] theorem sequenceBasis_inner (i : ι) (x : SequenceHilbert ι) :
    inner ℂ (sequenceBasis ι i) x = x i := by
  classical
  rw [sequenceBasis_apply, lp.inner_single_left]
  simp

theorem sequence_hasSum_norm_sq (x : SequenceHilbert ι) :
    HasSum (fun i => ‖x i‖^2) (‖x‖^2) := by
  simpa only [sequenceBasis_inner] using basis_hasSum_norm_sq (sequenceBasis ι) x

theorem real_exp_support (a b : ℝ) : Real.exp a*(1+b-a) ≤ Real.exp b := by
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (b-a)) (Real.exp_nonneg a)
  rw [← Real.exp_add] at h
  convert h using 1 <;> congr 1 <;> ring

theorem heat_weight_le_diagonal (s : ι → ℝ) (_hs : ∀ i, 1 ≤ s i)
    {k u : ℝ} (hk : 0 < k) {ψ y : SequenceHilbert ι}
    (hψ : ‖ψ‖ = 1) (hy : ∀ i, y i = (s i^4 : ℝ)*ψ i)
    (he : k*‖y‖^2 ≤ u) :
    Real.exp (-u) ≤ ∑' i, Real.exp (-k*s i^8)*‖ψ i‖^2 := by
  have hw : HasSum (fun i => ‖ψ i‖^2) 1 := by
    simpa only [hψ, one_pow] using sequence_hasSum_norm_sq ψ
  have hwy : HasSum (fun i => s i^8*‖ψ i‖^2) (‖y‖^2) := by
    convert sequence_hasSum_norm_sq y using 1
    funext i
    rw [hy i, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    ring
  have hh : Summable (fun i => Real.exp (-k*s i^8)*‖ψ i‖^2) := by
    apply Summable.of_nonneg_of_le (fun i => by positivity) _ hw.summable
    intro i
    have hex : Real.exp (-k*s i^8) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hk.le) (by positivity))
    nlinarith [sq_nonneg ‖ψ i‖, Real.exp_nonneg (-k*s i^8)]
  have hl : HasSum (fun i => Real.exp (-u)*((1+u)*‖ψ i‖^2-k*(s i^8*‖ψ i‖^2)))
      (Real.exp (-u)*((1+u)-k*‖y‖^2)) := by
    simpa only [mul_one] using ((hw.mul_left (1+u)).sub (hwy.mul_left k)).mul_left (Real.exp (-u))
  calc
    Real.exp (-u) ≤ Real.exp (-u)*((1+u)-k*‖y‖^2) := by
      nlinarith [Real.exp_pos (-u)]
    _ = ∑' i, Real.exp (-u)*((1+u)*‖ψ i‖^2-k*(s i^8*‖ψ i‖^2)) := hl.tsum_eq.symm
    _ ≤ _ := by
      apply hl.summable.tsum_le_tsum _ hh
      intro i
      have h := mul_le_mul_of_nonneg_right (real_exp_support (-u) (-k*s i^8)) (sq_nonneg ‖ψ i‖)
      convert h using 1; ring

theorem basis_coordinate_hasSum {κ : Type*} (b : HilbertBasis κ ℂ (SequenceHilbert ι)) (i : ι) :
    HasSum (fun j => ‖b j i‖^2) 1 := by
  have h := basis_hasSum_norm_sq b (sequenceBasis ι i)
  convert h using 1
  · funext j
    rw [← sequenceBasis_inner, norm_inner_symm]
  · simp only [(sequenceBasis ι).orthonormal.norm_eq_one, one_pow]

theorem heat_trace_bound {κ : Type*} (b : HilbertBasis κ ℂ (SequenceHilbert ι))
    (a : κ → ℝ) (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (hds : Summable d)
    (ha : ∀ j, 0 ≤ a j)
    (hw : ∀ j, a j ≤ ∑' i, d i*‖b j i‖^2) :
    Summable a ∧ ∑' j, a j ≤ ∑' i, d i := by
  have hrow (j : κ) : Summable (fun i => d i*‖b j i‖^2) := by
    apply Summable.of_nonneg_of_le (fun i => mul_nonneg (hd i) (sq_nonneg _)) _ hds
    intro i
    have hn : ‖b j i‖ ≤ 1 := by
      simpa only [b.orthonormal.norm_eq_one] using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) (b j) i
    exact mul_le_of_le_one_right (hd i) (by nlinarith [norm_nonneg (b j i)])
  have hfin (F : Finset κ) : ∑ j ∈ F, a j ≤ ∑' i, d i := by
    calc
      ∑ j ∈ F, a j ≤ ∑ j ∈ F, ∑' i, d i*‖b j i‖^2 := Finset.sum_le_sum (fun j _ => hw j)
      _ = ∑' i, ∑ j ∈ F, d i*‖b j i‖^2 := (Summable.tsum_finsetSum (fun j _ => hrow j)).symm
      _ ≤ ∑' i, d i := by
        apply Summable.tsum_le_tsum _ _ hds
        · intro i
          rw [← Finset.mul_sum]
          apply mul_le_of_le_one_right (hd i)
          exact (basis_coordinate_hasSum b i).summable.sum_le_tsum F (fun _ _ => sq_nonneg _) |>.trans_eq (basis_coordinate_hasSum b i).tsum_eq
        · exact summable_sum (fun j _ => hrow j)
  have hs := summable_of_sum_le ha hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

end

section
open Filter Topology

def numberWeight {n : ℕ} (i : Fin n → ℕ) : ℝ := 1+∑ j, (i j : ℝ)

def rootNumberWeight {n : ℕ} (i : Fin n → ℕ) : ℝ := Real.sqrt (numberWeight i)

theorem numberWeight_one_le {n : ℕ} (i : Fin n → ℕ) : 1 ≤ numberWeight i := by
  unfold numberWeight
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))

theorem rootNumberWeight_one_le {n : ℕ} (i : Fin n → ℕ) : 1 ≤ rootNumberWeight i := by
  exact (Real.le_sqrt (by norm_num) (by linarith [numberWeight_one_le i])).mpr (by
    simpa only [one_pow] using numberWeight_one_le i)

theorem rootNumberWeight_pow_four {n : ℕ} (i : Fin n → ℕ) :
    rootNumberWeight i^4 = numberWeight i^2 := by
  rw [show (4 : ℕ) = 2*2 from rfl, pow_mul, rootNumberWeight, Real.sq_sqrt (by linarith [numberWeight_one_le i])]

theorem rootNumberWeight_pow_eight {n : ℕ} (i : Fin n → ℕ) :
    rootNumberWeight i^8 = numberWeight i^4 := by
  rw [show (8 : ℕ) = 2*4 from rfl, pow_mul, rootNumberWeight, Real.sq_sqrt (by linarith [numberWeight_one_le i])]

theorem summable_exp_number (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun i : Fin n → ℕ => Real.exp (-t*(∑ j, (i j : ℝ)))) := by
  let w : ℕ → ℝ := fun m => Real.exp (-t*(m : ℝ))
  have hw : Summable w := by
    have hh : ‖Real.exp (-t)‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
      linarith
    apply (summable_geometric_of_norm_lt_one hh).congr
    intro m
    simpa only [w, mul_comm] using (Real.exp_nat_mul (-t) m).symm
  have hn : (∑' m, ENNReal.ofReal (w m)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => Real.exp_nonneg _) hw]
    exact ENNReal.ofReal_ne_top
  have he (i : Fin n → ℕ) :
      ENNReal.ofReal (Real.exp (-t*(∑ j, (i j : ℝ)))) = ∏ j, ENNReal.ofReal (w (i j)) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun j _ => Real.exp_nonneg _)]
    congr 1
    rw [← Real.exp_sum]
    congr 1
    exact Finset.mul_sum _ _ _
  have hf : (∑' i : Fin n → ℕ, ENNReal.ofReal (Real.exp (-t*(∑ j, (i j : ℝ))))) ≠ ⊤ := by
    simp_rw [he]
    rw [tsum_finite_product n (fun m => ENNReal.ofReal (w m))]
    exact ENNReal.pow_ne_top hn
  have hh := (ENNReal.hasSum_toReal hf).summable
  simpa only [ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hh

theorem summable_exp_number_aux (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Summable (fun i : Fin n → ℕ => Real.exp (-t*rootNumberWeight i^8)) := by
  apply Summable.of_nonneg_of_le (fun i => Real.exp_nonneg _) _ (summable_exp_number n ht)
  intro i
  apply Real.exp_le_exp.mpr
  rw [rootNumberWeight_pow_eight]
  have hw := numberWeight_one_le i
  have hh : numberWeight i ≤ numberWeight i^4 := le_self_pow₀ hw (by norm_num)
  have hsum : ∑ j, (i j : ℝ) ≤ numberWeight i^4 := by
    have hn : ∑ j, (i j : ℝ) = numberWeight i-1 := by simp [numberWeight]
    rw [hn]; linarith
  nlinarith

theorem inverseRootNumber_compact (n : ℕ) :
    IsCompactOperator (inversePower (rootNumberWeight (n := n)) rootNumberWeight_one_le 4) := by
  classical
  apply diagonalMap_compact
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_gt (ε⁻¹)
  let F : Finset (Fin n → ℕ) := Fintype.piFinset (fun _ => Finset.range (K+1))
  refine ⟨F, fun i hi => ?_⟩
  have hsum : (K+1 : ℝ) ≤ ∑ j, (i j : ℝ) := by
    simp only [F, Fintype.mem_piFinset, Finset.mem_range, not_forall] at hi
    obtain ⟨j, hj⟩ := hi
    have hh : K+1 ≤ i j := Nat.le_of_not_gt hj
    have hs := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (i j)) (Finset.mem_univ j)
    exact_mod_cast hh.trans hs
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity [rootNumberWeight_one_le i]),
    rootNumberWeight_pow_four]
  have hw := numberWeight_one_le i
  have hn : (K : ℝ) ≤ numberWeight i := by unfold numberWeight; linarith
  have hh : ε⁻¹ ≤ numberWeight i^2 := by
    nlinarith [sq_nonneg (numberWeight i-1)]
  exact (inv_le_comm₀ (by nlinarith : 0 < numberWeight i^2) hε).mpr hh

theorem gibbs_fock_spectral_regular (n : ℕ) {k : ℝ} (hk : 0 < k)
    {B : SequenceHilbert (Fin n → ℕ) →L[ℂ] SequenceHilbert (Fin n → ℕ)} (hB : B.IsPositive) :
    ∃ (J : Type) (b : HilbertBasis J ℂ (SequenceHilbert (Fin n → ℕ))) (u : J → ℝ),
      (∀ j, 0 < u j) ∧
      (∀ j, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (b j) = (((u j)⁻¹ : ℝ) : ℂ) • b j) ∧
      (∀ j, ∃ y z : SequenceHilbert (Fin n → ℕ),
        (∀ i, y i = (rootNumberWeight i^4 : ℝ)*b j i) ∧
        (∀ i, z i = (rootNumberWeight i^7 : ℝ)*b j i) ∧
        ‖y‖^2 ≤ u j/k ∧ ‖z‖ ≤ k⁻¹*(u j+‖B‖*Real.sqrt (u j/k))) ∧
      (∀ t : ℝ, 0 < t → Summable (fun j => Real.exp (-t*u j))) := by
  obtain ⟨J, b, e, hep, he⟩ := exists_strictly_positive_eigenbasis
    (gibbsInverse_compact rootNumberWeight rootNumberWeight_one_le k B (inverseRootNumber_compact n))
    (gibbsInverse_positive rootNumberWeight rootNumberWeight_one_le hk hB)
    (gibbsInverse_injective rootNumberWeight rootNumberWeight_one_le hk hB)
  let u : J → ℝ := fun j => (e j)⁻¹
  have hup (j : J) : 0 < u j := inv_pos.mpr (hep j)
  have hue (j : J) : gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (b j) =
      (((u j)⁻¹ : ℝ) : ℂ) • b j := by simpa only [u, inv_inv] using he j
  have hreg (j : J) := gibbs_eigenvector_regular rootNumberWeight rootNumberWeight_one_le hk
    (hup j) hB (b.orthonormal.norm_eq_one j) (hue j)
  refine ⟨J, b, u, hup, hue, hreg, ?_⟩
  intro t ht
  apply (heat_trace_bound b (fun j => Real.exp (-t*u j))
      (fun i => Real.exp (-(t*k)*rootNumberWeight i^8)) (fun _ => Real.exp_nonneg _)
      (summable_exp_number_aux n (mul_pos ht hk)) (fun _ => Real.exp_nonneg _) ?_).1
  intro j
  obtain ⟨y, z, hy, _, hnorm, _⟩ := hreg j
  have he' : (t*k)*‖y‖^2 ≤ t*u j := by
    have hh := (le_div_iff₀ hk).mp hnorm
    nlinarith
  simpa only [neg_mul] using heat_weight_le_diagonal rootNumberWeight rootNumberWeight_one_le (mul_pos ht hk)
    (b.orthonormal.norm_eq_one j) hy he'

theorem summable_polynomial_heat {J : Type*} (u : J → ℝ) (hu : ∀ j, 0 ≤ u j)
    (hs : Summable (fun j => Real.exp (-(1/2 : ℝ)*u j))) :
    Summable (fun j => Real.exp (-u j)*(1+u j^2)) := by
  have hscalar (x : ℝ) (hx : 0 ≤ x) :
      Real.exp (-x)*(1+x^2) ≤ 17*Real.exp (-(1/2 : ℝ)*x) := by
    have h := Real.add_one_le_exp (x/4)
    have he : x ≤ 4*Real.exp (x/4) := by linarith
    have he2 : x^2 ≤ 16*Real.exp (x/2) := by
      calc
        x^2 ≤ (4*Real.exp (x/4))^2 := pow_le_pow_left₀ hx he 2
        _ = 16*(Real.exp (x/4)*Real.exp (x/4)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 1; ring_nf
    have hm := mul_le_mul_of_nonneg_left he2 (Real.exp_nonneg (-x))
    have heq : Real.exp (-x)*(16*Real.exp (x/2)) = 16*Real.exp (-(1/2 : ℝ)*x) := by
      calc
        _ = 16*(Real.exp (-x)*Real.exp (x/2)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 1; ring_nf
    rw [heq] at hm
    have hle : Real.exp (-x) ≤ Real.exp (-(1/2 : ℝ)*x) := Real.exp_le_exp.mpr (by linarith)
    nlinarith
  apply Summable.of_nonneg_of_le (fun j => by positivity) _ (hs.mul_left 17)
  intro j
  exact hscalar (u j) (hu j)

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

def basisDiagonal (b : HilbertBasis ι ℂ E) (p : ι → ℝ)
    (hb : ∃ C : ℝ, ∀ i, ‖(p i : ℂ)‖ ≤ C) : E →L[ℂ] E :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((diagonalMap (fun i => (p i : ℂ)) hb).comp
      b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem basisDiagonal_positive (b : HilbertBasis ι ℂ E) (p : ι → ℝ)
    (hb : ∃ C : ℝ, ∀ i, ‖(p i : ℂ)‖ ≤ C) (hp : ∀ i, 0 ≤ p i) :
    (basisDiagonal b p hb).IsPositive := by
  apply (ContinuousLinearMap.isPositive_iff_complex _).mpr
  intro x
  change ((inner ℂ (b.repr.symm (diagonalMap _ hb (b.repr x))) x).re : ℂ) = inner ℂ (b.repr.symm (diagonalMap _ hb (b.repr x))) x ∧
    0 ≤ (inner ℂ (b.repr.symm (diagonalMap _ hb (b.repr x))) x).re
  rw [b.repr.symm.inner_map_eq_flip]
  simp only [LinearIsometryEquiv.symm_symm]
  exact (ContinuousLinearMap.isPositive_iff_complex _).mp (diagonalMap_positive p hb hp) (b.repr x)

theorem basisDiagonal_eigen (b : HilbertBasis ι ℂ E) (p : ι → ℝ)
    (hb : ∃ C : ℝ, ∀ i, ‖(p i : ℂ)‖ ≤ C) (i : ι) :
    basisDiagonal b p hb (b i) = (p i : ℂ) • b i := by
  classical
  change b.repr.symm (diagonalMap _ hb (b.repr (b i))) = _
  rw [b.repr_self, diagonalMap_single, mul_one]
  have he : (lp.single 2 i (p i : ℂ) : SequenceHilbert ι) = (p i : ℂ) • (lp.single 2 i (1 : ℂ) : SequenceHilbert ι) := by
    simpa only [smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : ι => ℂ) 2 i (p i : ℂ) (1 : ℂ))
  rw [he, map_smul, b.repr_symm_single]

theorem basisDiagonal_injective (b : HilbertBasis ι ℂ E) (p : ι → ℝ)
    (hb : ∃ C : ℝ, ∀ i, ‖(p i : ℂ)‖ ≤ C) (hp : ∀ i, p i ≠ 0) :
    Function.Injective (basisDiagonal b p hb) :=
  b.repr.symm.injective.comp ((diagonalMap_injective _ hb (fun i =>
    Complex.ofReal_ne_zero.mpr (hp i))).comp b.repr.injective)

theorem basisDiagonal_trace (b : HilbertBasis ι ℂ E) (p : ι → ℝ)
    (hb : ∃ C : ℝ, ∀ i, ‖(p i : ℂ)‖ ≤ C) :
    diagonalTrace b (basisDiagonal b p hb) = ∑' i, ENNReal.ofReal (p i) := by
  unfold diagonalTrace
  congr 1
  funext i
  rw [basisDiagonal_eigen, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  simp

theorem basisDiagonal_hasSum_trace (b : HilbertBasis ι ℂ E) (p : ι → ℝ)
    (hb : ∃ C : ℝ, ∀ i, ‖(p i : ℂ)‖ ≤ C) {z : ℝ} (hp : HasSum p z) :
    HasSum (fun i => (inner ℂ (b i) (basisDiagonal b p hb (b i))).re) z := by
  convert hp using 1
  funext i
  rw [basisDiagonal_eigen, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  simp

def heatPartition (u : ι → ℝ) : ℝ := ∑' i, Real.exp (-u i)

def gibbsWeight (u : ι → ℝ) (i : ι) : ℝ := Real.exp (-u i) / heatPartition u

theorem heatPartition_pos [Nonempty ι] (u : ι → ℝ) (hs : Summable (fun i => Real.exp (-u i))) :
    0 < heatPartition u := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact hs.tsum_pos (fun _ => Real.exp_nonneg _) i (Real.exp_pos _)

theorem gibbsWeight_pos [Nonempty ι] (u : ι → ℝ) (hs : Summable (fun i => Real.exp (-u i))) (i : ι) :
    0 < gibbsWeight u i := div_pos (Real.exp_pos _) (heatPartition_pos u hs)

theorem gibbsWeight_hasSum [Nonempty ι] (u : ι → ℝ) (hs : Summable (fun i => Real.exp (-u i))) :
    HasSum (gibbsWeight u) 1 := by
  have hh := hs.hasSum.div_const (heatPartition u)
  change HasSum (gibbsWeight u) (heatPartition u / heatPartition u) at hh
  rwa [div_self (heatPartition_pos u hs).ne'] at hh

theorem gibbsWeight_bounded [Nonempty ι] (u : ι → ℝ) (hs : Summable (fun i => Real.exp (-u i))) :
    ∃ C : ℝ, ∀ i, ‖(gibbsWeight u i : ℂ)‖ ≤ C := by
  refine ⟨1, fun i => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gibbsWeight_pos u hs i)]
  have hh := (gibbsWeight_hasSum u hs).summable.le_tsum i (fun j _ => (gibbsWeight_pos u hs j).le)
  rwa [(gibbsWeight_hasSum u hs).tsum_eq] at hh

def spectralGibbs [Nonempty ι] (b : HilbertBasis ι ℂ E) (u : ι → ℝ)
    (hs : Summable (fun i => Real.exp (-u i))) : E →L[ℂ] E :=
  basisDiagonal b (gibbsWeight u) (gibbsWeight_bounded u hs)

theorem spectralGibbs_positive [Nonempty ι] (b : HilbertBasis ι ℂ E) (u : ι → ℝ)
    (hs : Summable (fun i => Real.exp (-u i))) : (spectralGibbs b u hs).IsPositive :=
  basisDiagonal_positive b _ _ (fun i => (gibbsWeight_pos u hs i).le)

theorem spectralGibbs_injective [Nonempty ι] (b : HilbertBasis ι ℂ E) (u : ι → ℝ)
    (hs : Summable (fun i => Real.exp (-u i))) : Function.Injective (spectralGibbs b u hs) :=
  basisDiagonal_injective b _ _ (fun i => (gibbsWeight_pos u hs i).ne')

theorem spectralGibbs_trace_one [CompleteSpace E] [Nonempty ι] (b : HilbertBasis ι ℂ E) (u : ι → ℝ)
    (hs : Summable (fun i => Real.exp (-u i))) {κ : Type*} (c : HilbertBasis κ ℂ E) :
    HasSum (fun j => (inner ℂ (c j) (spectralGibbs b u hs (c j))).re) 1 := by
  exact hasSum_trace_basis b c (spectralGibbs_positive b u hs)
    (basisDiagonal_hasSum_trace b _ _ (gibbsWeight_hasSum u hs))

theorem spectralGibbs_eigen [Nonempty ι] (b : HilbertBasis ι ℂ E) (u : ι → ℝ)
    (hs : Summable (fun i => Real.exp (-u i))) (i : ι) :
    spectralGibbs b u hs (b i) = (gibbsWeight u i : ℂ) • b i :=
  basisDiagonal_eigen b _ _ i

theorem log_gibbsWeight [Nonempty ι] (u : ι → ℝ) (hs : Summable (fun i => Real.exp (-u i))) (i : ι) :
    -Real.log (gibbsWeight u i) = u i + Real.log (heatPartition u) := by
  rw [gibbsWeight, Real.log_div (Real.exp_ne_zero _) (heatPartition_pos u hs).ne', Real.log_exp]
  ring

end

section
variable {ι J : Type*}

theorem weighted_number_moment (b : HilbertBasis J ℂ (SequenceHilbert ι))
    (T : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (he : ∀ j, T (b j) = (p j : ℂ) • b j)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (ν : J → ℝ)
    (hrow : ∀ j, HasSum (fun i => w i*‖b j i‖^2) (ν j))
    (hs : Summable (fun j => p j*ν j)) :
    Summable (fun i => w i*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re) := by
  let f : J × ι → ℝ := fun a => p a.1*(w a.2*‖b a.1 a.2‖^2)
  have hf : Summable f := by
    apply (summable_prod_of_nonneg (fun a => mul_nonneg (hp a.1) (mul_nonneg (hw a.2) (sq_nonneg _)))).mpr
    refine ⟨fun j => ((hrow j).mul_left (p j)).summable, ?_⟩
    convert hs using 1
    funext j
    exact ((hrow j).mul_left (p j)).tsum_eq
  have hcol (i : ι) : HasSum (fun j => f (j,i))
      (w i*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re) := by
    have hh := (hasSum_quadratic_eigenbasis b T p he (sequenceBasis ι i)).mul_left (w i)
    have heq : (fun j => w i*(p j*‖inner ℂ (b j) (sequenceBasis ι i)‖^2)) =
        (fun j => f (j,i)) := by
      funext j
      rw [norm_inner_symm, sequenceBasis_inner]
      dsimp [f]
      ring
    rw [heq] at hh
    exact hh
  apply hf.prod_symm.prod.congr
  intro i
  exact (hcol i).tsum_eq

theorem gibbs_high_moment_summable (u : J → ℝ) (hu : ∀ j, 0 ≤ u j)
    {k b : ℝ} (hk : 0 < k) (hb : 0 ≤ b) (z : J → ℝ)
    (hz0 : ∀ j, 0 ≤ z j)
    (hz : ∀ j, z j ≤ k⁻¹*(u j+b*Real.sqrt (u j/k)))
    (hs : Summable (fun j => Real.exp (-(1/2 : ℝ)*u j))) :
    Summable (fun j => Real.exp (-u j)*z j^2) := by
  let D := k⁻¹*(1+b*(1+k⁻¹))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hbound (j : J) : z j ≤ D*(1+u j) := by
    have hr := Real.sqrt_nonneg (u j/k)
    have hr2 := Real.sq_sqrt (div_nonneg (hu j) hk.le)
    have hrle : Real.sqrt (u j/k) ≤ 1+u j/k := by nlinarith [sq_nonneg (Real.sqrt (u j/k)-1)]
    have hrle' : Real.sqrt (u j/k) ≤ (1+k⁻¹)*(1+u j) := by
      rw [div_eq_mul_inv] at hrle ⊢
      nlinarith [hu j, inv_nonneg.mpr hk.le, mul_nonneg (hu j) (inv_nonneg.mpr hk.le)]
    calc
      z j ≤ k⁻¹*(u j+b*Real.sqrt (u j/k)) := hz j
      _ ≤ k⁻¹*((1+u j)+b*((1+k⁻¹)*(1+u j))) :=
        mul_le_mul_of_nonneg_left (add_le_add (by linarith) (mul_le_mul_of_nonneg_left hrle' hb))
          (inv_nonneg.mpr hk.le)
      _ = D*(1+u j) := by dsimp [D]; ring
  have hsq (j : J) : z j^2 ≤ 2*D^2*(1+u j^2) := by
    have h := pow_le_pow_left₀ (hz0 j) (hbound j) 2
    rw [mul_pow] at h
    have hle : (1+u j)^2 ≤ 2*(1+u j^2) := by nlinarith [sq_nonneg (u j-1)]
    have hh := mul_le_mul_of_nonneg_left hle (sq_nonneg D)
    nlinarith
  apply Summable.of_nonneg_of_le (fun j => by positivity) _
    ((summable_polynomial_heat u hu hs).mul_left (2*D^2))
  intro j
  have hh := mul_le_mul_of_nonneg_left (hsq j) (Real.exp_nonneg (-u j))
  calc
    _ ≤ Real.exp (-u j)*(2*D^2*(1+u j^2)) := hh
    _ = _ := by ring

end

section

theorem exists_gibbs_seventh_moment (n : ℕ) {k : ℝ} (hk : 0 < k)
    {B : SequenceHilbert (Fin n → ℕ) →L[ℂ] SequenceHilbert (Fin n → ℕ)} (hB : B.IsPositive) :
    ∃ (J : Type) (b : HilbertBasis J ℂ (SequenceHilbert (Fin n → ℕ)))
      (u : J → ℝ) (ω : SequenceHilbert (Fin n → ℕ) →L[ℂ] SequenceHilbert (Fin n → ℕ)),
      (∀ j, 0 < u j) ∧
      (∀ j, gibbsInverse rootNumberWeight rootNumberWeight_one_le k B (b j) =
        (((u j)⁻¹ : ℝ) : ℂ) • b j) ∧
      (∀ j, ω (b j) = (gibbsWeight u j : ℂ) • b j) ∧
      ω.IsPositive ∧ Function.Injective ω ∧
      HasSum (fun i => (inner ℂ (sequenceBasis _ i) (ω (sequenceBasis _ i))).re) 1 ∧
      Summable (fun i => numberWeight i^7 * (inner ℂ (sequenceBasis _ i) (ω (sequenceBasis _ i))).re) := by
  classical
  obtain ⟨J, b, u, hu, he, hreg, hheat⟩ := gibbs_fock_spectral_regular n hk hB
  have hJ : Nonempty J := by
    by_contra h
    have : IsEmpty J := not_nonempty_iff.mp h
    have hh := (basis_hasSum_norm_sq b (sequenceBasis (Fin n → ℕ) (fun _ => 0))).tsum_eq
    simp only [tsum_empty, (sequenceBasis (Fin n → ℕ)).orthonormal.norm_eq_one, one_pow] at hh
    exact zero_ne_one hh
  let := hJ
  have ht : Summable (fun j => Real.exp (-u j)) := by simpa using hheat 1 (by norm_num)
  let ω := spectralGibbs b u ht
  choose y z hy hz hys hzs using hreg
  have hn : Summable (fun j => Real.exp (-u j)*‖z j‖^2) :=
    gibbs_high_moment_summable u (fun j => (hu j).le) hk (norm_nonneg B)
      (fun j => ‖z j‖) (fun j => norm_nonneg _) hzs (hheat (1/2) (by norm_num))
  have hw : Summable (fun j => gibbsWeight u j*‖z j‖^2) := by
    apply (hn.div_const (heatPartition u)).congr
    intro j
    dsimp [gibbsWeight]
    ring
  refine ⟨J, b, u, ω, hu, he, spectralGibbs_eigen b u ht, spectralGibbs_positive b u ht,
    spectralGibbs_injective b u ht, spectralGibbs_trace_one b u ht (sequenceBasis _), ?_⟩
  apply weighted_number_moment b ω (gibbsWeight u) (fun j => (gibbsWeight_pos u ht j).le)
    (spectralGibbs_eigen b u ht) (fun i => numberWeight i^7)
    (fun i => pow_nonneg (by linarith [numberWeight_one_le i]) _) (fun j => ‖z j‖^2) _ hw
  intro j
  have heq : (fun i => ‖z j i‖^2) = (fun i => numberWeight i^7*‖b j i‖^2) := by
    funext i
    rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity [rootNumberWeight_one_le i]), mul_pow]
    congr 1
    rw [← pow_mul, show (7*2 : ℕ) = 2*7 from rfl, pow_mul, rootNumberWeight,
      Real.sq_sqrt (by linarith [numberWeight_one_le i])]
  rw [← heq]
  exact sequence_hasSum_norm_sq (z j)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

theorem polar_eigenbasis (b : HilbertBasis J ℂ E) (M : E →L[ℂ] E)
    (hi : Function.Injective M.adjoint) (u : J → ℝ) (hu : ∀ j, 0 < u j)
    (he : ∀ j, M.adjoint (M (b j)) = (((u j)⁻¹ : ℝ) : ℂ) • b j) :
    ∃ c : HilbertBasis J ℂ E, ∀ j, c j = (Real.sqrt (u j) : ℂ) • M (b j) := by
  classical
  let v : J → E := fun j => (Real.sqrt (u j) : ℂ) • M (b j)
  have hv : Orthonormal ℂ v := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [v, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    rw [← ContinuousLinearMap.adjoint_inner_right, he, inner_smul_right]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
      have hs := Real.sq_sqrt (hu i).le
      calc
        _ = ((Real.sqrt (u i)^2*(u i)⁻¹ : ℝ) : ℂ) := by push_cast; ring
        _ = 1 := by rw [hs, mul_inv_cancel₀ (hu i).ne']; norm_num
    · rw [ite_eq_right hij, b.orthonormal.inner_eq_zero hij]
      simp
  have hc : (Submodule.span ℂ (Set.range v))ᗮ = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    apply hi
    rw [map_zero]
    apply b.repr.injective
    apply lp.ext
    funext j
    rw [map_zero]
    rw [b.repr_apply_apply]
    change inner ℂ (b j) (M.adjoint x) = 0
    rw [ContinuousLinearMap.adjoint_inner_right]
    have hh := (Submodule.mem_orthogonal _ x).mp hx (v j) (Submodule.subset_span ⟨j, rfl⟩)
    change inner ℂ ((Real.sqrt (u j) : ℂ) • M (b j)) x = 0 at hh
    rw [inner_smul_left, Complex.conj_ofReal] at hh
    exact (mul_eq_zero.mp hh).resolve_left (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hu j)).ne')
  exact ⟨HilbertBasis.mkOfOrthogonalEqBot hv hc, fun j => by
    rw [HilbertBasis.coe_mkOfOrthogonalEqBot]⟩

theorem inverse_factor_form_parseval (b : HilbertBasis J ℂ E)
    (A X : E →L[ℂ] E) (hA : IsStrictlyPositive A) (hX : X.IsSymmetric)
    (hiX : Function.Injective X) (u : J → ℝ) (hu : ∀ j, 0 < u j)
    (he : ∀ j, (X * Ring.inverse A * X) (b j) = (((u j)⁻¹ : ℝ) : ℂ) • b j)
    (y : E) :
    HasSum (fun j => u j*‖inner ℂ (b j) (X y)‖^2) (inner ℂ y (A y)).re := by
  let S := CFC.sqrt A
  have hSpos : S.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg A)
  have hSu : IsUnit S := (CFC.isUnit_sqrt_iff A hA.nonneg).mpr hA.isUnit
  have hSq : S*S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  let R := Ring.inverse S
  have hRS : R*S = 1 := Ring.inverse_mul_cancel S hSu
  have hSR : S*R = 1 := Ring.mul_inverse_cancel S hSu
  have hRa : R.adjoint = R := hSpos.isSelfAdjoint.ringInverse
  have hXa : X.adjoint = X := hX.isSelfAdjoint
  have hRR : R*R = Ring.inverse A := by
    apply hA.isUnit.mul_left_cancel
    rw [Ring.mul_inverse_cancel A hA.isUnit, ← hSq]
    calc
      S*S*(R*R) = S*(S*R)*R := by noncomm_ring
      _ = 1 := by rw [hSR, mul_one, hSR]
  let M := R*X
  have hMa : M.adjoint = X*R := by
    change star (R*X) = X*R
    rw [star_mul]
    change X.adjoint*R.adjoint = X*R
    rw [hRa, hXa]
  have hiR : Function.Injective R := by
    intro x y h
    have hh := congrArg S h
    simpa only [← mul_apply_eq_comp, hSR, ContinuousLinearMap.one_def, ContinuousLinearMap.id_apply] using hh
  have hiM : Function.Injective M.adjoint := by
    rw [hMa]
    exact hiX.comp hiR
  have hMM : M.adjoint*M = X*Ring.inverse A*X := by
    rw [hMa]
    dsimp [M]
    calc
      X*R*(R*X) = X*(R*R)*X := by noncomm_ring
      _ = _ := by rw [hRR]
  obtain ⟨c, hc⟩ := polar_eigenbasis b M hiM u hu (fun j => by
    simpa only [← mul_apply_eq_comp, hMM] using he j)
  have hcoeff (j : J) : inner ℂ (c j) (S y) =
      (Real.sqrt (u j) : ℂ)*inner ℂ (b j) (X y) := by
    rw [hc, inner_smul_left, Complex.conj_ofReal, ← ContinuousLinearMap.adjoint_inner_right, hMa]
    congr 1
    rw [← mul_apply_eq_comp, mul_assoc, hRS, mul_one]
  have hsum := basis_hasSum_norm_sq c (S y)
  have heq : (fun j => ‖inner ℂ (c j) (S y)‖^2) =
      (fun j => u j*‖inner ℂ (b j) (X y)‖^2) := by
    funext j
    rw [hcoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, Real.sq_sqrt (hu j).le]
  rwa [heq, ← sqrt_inner_eq (ContinuousLinearMap.nonneg_iff_isPositive.mp hA.nonneg)] at hsum

end

open scoped BigOperators ComplexConjugate
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def logarithmSandwich (A X : E →L[ℂ] E) (c : ℝ) : E →L[ℂ] E :=
  A + (c : ℂ) • (X * X)

theorem logarithmSandwich_parseval (b : HilbertBasis J ℂ E)
    (A X : E →L[ℂ] E) (hA : IsStrictlyPositive A) (hX : X.IsSymmetric)
    (hiX : Function.Injective X) (u : J → ℝ) (hu : ∀ j, 0 < u j)
    (he : ∀ j, (X * Ring.inverse A * X) (b j) = (((u j)⁻¹ : ℝ) : ℂ) • b j)
    (c : ℝ) (y : E) :
    HasSum (fun j => (u j+c)*‖inner ℂ (b j) (X y)‖^2)
      (inner ℂ y (logarithmSandwich A X c y)).re := by
  have hh := (inverse_factor_form_parseval b A X hA hX hiX u hu he y).add
    ((basis_hasSum_norm_sq b (X y)).mul_left c)
  have hn : (inner ℂ y ((X*X) y)).re = ‖X y‖^2 := by
    have hx := hX y (X y)
    change inner ℂ (X y) (X y) = inner ℂ y (X (X y)) at hx
    rw [mul_apply_eq_comp, ← hx]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (X y)
  convert! hh using 1
  · ext j
    ring
  · simp only [logarithmSandwich, add_apply,
      smul_apply, inner_add_right, inner_smul_right,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hn]

theorem gibbs_logarithmSandwich_parseval [Nonempty J] (b : HilbertBasis J ℂ E)
    (A X : E →L[ℂ] E) (hA : IsStrictlyPositive A) (hX : X.IsSymmetric)
    (hiX : Function.Injective X) (u : J → ℝ) (hu : ∀ j, 0 < u j)
    (he : ∀ j, (X * Ring.inverse A * X) (b j) = (((u j)⁻¹ : ℝ) : ℂ) • b j)
    (hs : Summable (fun j => Real.exp (-u j))) (y : E) :
    HasSum (fun j => -Real.log (gibbsWeight u j)*‖inner ℂ (b j) (X y)‖^2)
      (inner ℂ y (logarithmSandwich A X (Real.log (heatPartition u)) y)).re := by
  convert! logarithmSandwich_parseval b A X hA hX hiX u hu he
    (Real.log (heatPartition u)) y using 1
  ext j
  rw [log_gibbsWeight u hs j]

omit [CompleteSpace E] in

theorem inverse_factor_eigen_preimage (b : HilbertBasis J ℂ E)
    (A X : E →L[ℂ] E) (hA : IsStrictlyPositive A) (hiX : Function.Injective X)
    (u : J → ℝ) (hu : ∀ j, 0 < u j)
    (he : ∀ j, (X * Ring.inverse A * X) (b j) = (((u j)⁻¹ : ℝ) : ℂ) • b j)
    (j : J) (v : E) (t : ℂ) (hv : X v = t • b j) :
    A v = (u j : ℂ) • X (t • b j) := by
  have hi : Ring.inverse A (X (t • b j)) = (((u j)⁻¹ : ℝ) : ℂ) • v := by
    apply hiX
    calc
      X (Ring.inverse A (X (t • b j))) = t • ((X*Ring.inverse A*X) (b j)) := by
        simp only [mul_apply_eq_comp, map_smul]
      _ = t • ((((u j)⁻¹ : ℝ) : ℂ) • b j) := by rw [he]
      _ = X ((((u j)⁻¹ : ℝ) : ℂ) • v) := by
        simp only [map_smul, hv, smul_smul]
        congr 1
        ring
  have hAi (z : E) : A (Ring.inverse A z) = z := by
    change (A*Ring.inverse A) z = z
    rw [Ring.mul_inverse_cancel A hA.isUnit]
    rfl
  have hh : X (t • b j) = (((u j)⁻¹ : ℝ) : ℂ) • A v := by
    calc
      _ = A (Ring.inverse A (X (t • b j))) := (hAi _).symm
      _ = _ := by rw [hi, map_smul]
  rw [hh, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (hu j).ne', Complex.ofReal_one, one_smul]

omit [CompleteSpace E] in
theorem logarithmSandwich_eigen_preimage (b : HilbertBasis J ℂ E)
    (A X : E →L[ℂ] E) (hA : IsStrictlyPositive A) (hiX : Function.Injective X)
    (u : J → ℝ) (hu : ∀ j, 0 < u j)
    (he : ∀ j, (X * Ring.inverse A * X) (b j) = (((u j)⁻¹ : ℝ) : ℂ) • b j)
    (c : ℝ) (j : J) (v : E) (t : ℂ) (hv : X v = t • b j) :
    logarithmSandwich A X c v = ((u j+c : ℝ) : ℂ) • X (t • b j) := by
  simp only [logarithmSandwich, add_apply,
    smul_apply, mul_apply_eq_comp]
  rw [inverse_factor_eigen_preimage b A X hA hiX u hu he j v t hv, hv,
    ← add_smul, ← Complex.ofReal_add]

end QuantumTrace

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate

namespace QuantumTrace
variable {ι J : Type*}

theorem weighted_spectral_vectors (b : HilbertBasis J ℂ (SequenceHilbert ι))
    (T : SequenceHilbert ι →L[ℂ] SequenceHilbert ι) (p : J → ℝ)
    (hp : ∀ j, 0 ≤ p j) (he : ∀ j, T (b j) = (p j : ℂ) • b j)
    (w : ι → ℝ)
    (hm : Summable (fun i => w i^2*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re)) :
    ∃ y : J → SequenceHilbert ι,
      (∀ j i, y j i = (w i : ℂ)*((Real.sqrt (p j) : ℂ)*b j i)) ∧
      Summable (fun j => ‖y j‖^2) ∧
      (∑' j, ‖y j‖^2) = ∑' i, w i^2*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re := by
  let f : ι × J → ℝ := fun a => w a.1^2*(p a.2*‖b a.2 a.1‖^2)
  have hf0 (a : ι × J) : 0 ≤ f a := mul_nonneg (sq_nonneg _) (mul_nonneg (hp _) (sq_nonneg _))
  have hcol (i : ι) : HasSum (fun j => f (i,j))
      (w i^2*(inner ℂ (sequenceBasis ι i) (T (sequenceBasis ι i))).re) := by
    have hh := (hasSum_quadratic_eigenbasis b T p he (sequenceBasis ι i)).mul_left (w i^2)
    simpa only [f, norm_inner_symm, sequenceBasis_inner] using hh
  have hf : Summable f := by
    apply (summable_prod_of_nonneg hf0).mpr
    refine ⟨fun i => (hcol i).summable, ?_⟩
    simpa only [(hcol _).tsum_eq] using hm
  have hnorm (j : J) (i : ι) : ‖(w i : ℂ)*((Real.sqrt (p j) : ℂ)*b j i)‖^2 = f (i,j) := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (hp j), f]
  have hmem (j : J) : Memℓp (fun i => (w i : ℂ)*((Real.sqrt (p j) : ℂ)*b j i)) 2 := by
    apply memℓp_gen
    have hh : Summable (fun i => f (i,j)) := hf.prod_symm.prod_factor j
    convert! hh using 1
    funext i
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, hnorm]
  let y : J → SequenceHilbert ι := fun j => ⟨_, hmem j⟩
  have hy (j : J) : HasSum (fun i => f (i,j)) (‖y j‖^2) := by
    have hh := sequence_hasSum_norm_sq (y j)
    simpa only [y, hnorm] using hh
  refine ⟨y, fun _ _ => rfl, ?_, ?_⟩
  · have hh : Summable (fun j => ∑' i, f (i,j)) := hf.prod_symm.prod
    simpa only [(hy _).tsum_eq] using hh
  · calc
      _ = ∑' j, ∑' i, f (i,j) := tsum_congr (fun j => (hy j).tsum_eq.symm)
      _ = ∑' i, ∑' j, f (i,j) := Summable.tsum_comm (f := fun i j => f (i,j)) hf
      _ = _ := tsum_congr (fun i => (hcol i).tsum_eq)

end QuantumTrace

end

end OAI
