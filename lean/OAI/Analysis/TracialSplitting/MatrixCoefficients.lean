import OAI.Analysis.TracialSplitting.TraceNormalization

namespace OAI

universe uA uJ uK uN


section

noncomputable section

open scoped InnerProductSpace ComplexOrder

namespace NuclearTrace

section ChangeBasis

variable {A : Type uA} {K : Type uK} [CStarAlgebra A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (α : A →⋆ₐ[ℂ] (K →L[ℂ] K))

variable {N : Type uN} {J : Type uJ} [Fintype N] [Fintype J]

lemma coefficientMap_change_vectors (k : N → K) (a : N → A)
    (e : J → K) (c : J → N → ℂ) (hk : ∀ i, k i = ∑ u, c u i • e u) (x : A) :
    coefficientMap α k a x = coefficientMap α e (fun u => ∑ i, c u i • a i) x := by
  classical
  simp only [coefficientMap,LinearMap.coe_mk,AddHom.coe_mk,hk,map_sum,map_smul,
    inner_sum,sum_inner,inner_smul_left,inner_smul_right,star_sum,star_smul,
    Finset.mul_sum,Finset.sum_mul,Finset.smul_sum,Finset.sum_smul,
    smul_mul_assoc,mul_smul_comm,smul_smul]
  conv_lhs =>
    arg 2
    ext i
    arg 2
    ext j
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext u
    arg 2
    ext i
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext u
    rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext u
    arg 2
    ext v
    rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  change c v j * (star (c u i) * _) = _
  ring

lemma coefficientMap_orthonormal (k : N → K) (a : N → A) :
    ∃ (n : ℕ) (e : Fin n → K) (b : Fin n → A), Orthonormal ℂ e ∧
      coefficientMap α k a = coefficientMap α e b := by
  classical
  let S : Submodule ℂ K := Submodule.span ℂ (Set.range k)
  let : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range k)
  let basis := stdOrthonormalBasis ℂ S
  let ki (i : N) : S := ⟨k i, Submodule.subset_span (Set.mem_range_self i)⟩
  let e (u : Fin (Module.finrank ℂ S)) : K := basis u
  let c (u : Fin (Module.finrank ℂ S)) (i : N) : ℂ := basis.repr (ki i) u
  have hk (i : N) : k i = ∑ u, c u i • e u := by
    have h := congrArg (fun z : S => (z : K)) (basis.sum_repr (ki i))
    simpa only [Submodule.coe_sum,Submodule.coe_smul] using h.symm
  refine ⟨_,e,(fun u => ∑ i, c u i • a i),?_,?_⟩
  · exact S.subtypeₗᵢ.orthonormal_comp_iff.mpr basis.orthonormal
  · exact LinearMap.ext (fun x => coefficientMap_change_vectors α k a e c hk x)

end ChangeBasis

section Compression

variable {A : Type uA} {K : Type uK} {N : Type uN} [CStarAlgebra A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [Fintype N] [DecidableEq N]

def operatorMatrix : (EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N) ≃⋆ₐ[ℂ]
    CStarMatrix N N ℂ :=
  Matrix.toEuclideanCLM.symm.trans CStarMatrix.ofMatrixStarAlgEquiv

lemma operatorMatrix_apply (T : EuclideanSpace ℂ N →L[ℂ] EuclideanSpace ℂ N)
    (i j : N) : operatorMatrix T i j =
      ⟪EuclideanSpace.basisFun N ℂ i,T (EuclideanSpace.basisFun N ℂ j)⟫_ℂ := by
  change (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun N ℂ) T.toLinearMap) i j = _
  simp [LinearMap.toMatrixOrthonormal,LinearMap.toMatrix_apply,
    OrthonormalBasis.repr_apply_apply]

def orthonormalLinear (e : N → K) : EuclideanSpace ℂ N →ₗ[ℂ] K :=
  (EuclideanSpace.basisFun N ℂ).toBasis.constr ℂ e

omit [CompleteSpace K] [DecidableEq N] in
@[simp] lemma orthonormalLinear_basis (e : N → K) (i : N) :
    orthonormalLinear e (EuclideanSpace.basisFun N ℂ i) = e i := by
  exact (EuclideanSpace.basisFun N ℂ).toBasis.constr_basis ℂ e i

omit [CompleteSpace K] [DecidableEq N] in
lemma orthonormalLinear_orthonormal (e : N → K) (he : Orthonormal ℂ e) :
    Orthonormal ℂ (orthonormalLinear e ∘ (EuclideanSpace.basisFun N ℂ).toBasis) := by
  convert he using 1
  ext i
  exact orthonormalLinear_basis e i

def orthonormalInclusion (e : N → K) (he : Orthonormal ℂ e) :
    EuclideanSpace ℂ N →ₗᵢ[ℂ] K :=
  (orthonormalLinear e).isometryOfOrthonormal (v := (EuclideanSpace.basisFun N ℂ).toBasis)
    (EuclideanSpace.basisFun N ℂ).orthonormal (orthonormalLinear_orthonormal e he)

omit [CompleteSpace K] [DecidableEq N] in
@[simp] lemma orthonormalInclusion_basis (e : N → K) (he : Orthonormal ℂ e) (i : N) :
    orthonormalInclusion e he (EuclideanSpace.basisFun N ℂ i) = e i := by
  exact orthonormalLinear_basis e i

def compressionMatrix (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (e : N → K)
    (he : Orthonormal ℂ e) : A →ₗ[ℂ] CStarMatrix N N ℂ where
  toFun x := operatorMatrix (((orthonormalInclusion e he).toContinuousLinearMap.adjoint.comp
    (α x)).comp (orthonormalInclusion e he).toContinuousLinearMap)
  map_add' x y := by simp [ContinuousLinearMap.comp_add,ContinuousLinearMap.add_comp]
  map_smul' c x := by simp [ContinuousLinearMap.smul_comp]

lemma compressionMatrix_apply (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (e : N → K)
    (he : Orthonormal ℂ e) (x : A) (i j : N) :
    compressionMatrix α e he x i j = ⟪e i,α x (e j)⟫_ℂ := by
  change operatorMatrix _ i j = _
  rw [operatorMatrix_apply]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    LinearIsometry.coe_toContinuousLinearMap,orthonormalInclusion_basis]

lemma compressionMatrix_one (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (e : N → K)
    (he : Orthonormal ℂ e) : compressionMatrix α e he 1 = 1 := by
  ext i j
  rw [compressionMatrix_apply,map_one]
  exact orthonormal_iff_ite.mp he i j

lemma compressionMatrix_norm (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (e : N → K)
    (he : Orthonormal ℂ e) (x : A) : ‖compressionMatrix α e he x‖ ≤ ‖x‖ := by
  let V := (orthonormalInclusion e he).toContinuousLinearMap
  have hV : ‖V‖ ≤ 1 := (orthonormalInclusion e he).norm_toContinuousLinearMap_le
  change ‖operatorMatrix ((V.adjoint.comp (α x)).comp V)‖ ≤ _
  apply (NonUnitalStarAlgHom.norm_apply_le
    ((operatorMatrix (N := N)).toStarAlgHom) _).trans
  calc
    ‖(V.adjoint.comp (α x)).comp V‖ ≤ ‖V.adjoint‖ * ‖α x‖ * ‖V‖ := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖x‖ * 1 := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      gcongr
      exact NonUnitalStarAlgHom.norm_apply_le α x
    _ = ‖x‖ := by ring

lemma coefficientMap_factorization (α : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (e : N → K) (he : Orthonormal ℂ e) (a : N → A) (x : A) :
    coefficientMap α e a x =
      ∑ i, ∑ j, (compressionMatrix α e he x i j) • (star (a i)*a j) := by
  simp only [coefficientMap,LinearMap.coe_mk,AddHom.coe_mk,compressionMatrix_apply]

lemma coefficientMap_one (α : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (e : N → K) (he : Orthonormal ℂ e) (a : N → A) :
    coefficientMap α e a 1 = ∑ i, star (a i)*a i := by
  rw [coefficientMap_factorization α e he a 1,compressionMatrix_one]
  simp [CStarMatrix.one_apply]

end Compression

section Choi

variable {A : Type uA} {N : Type uN} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [Fintype N] [DecidableEq N]

lemma coefficient_choi_nonneg (a : N → A) :
    0 ≤ CStarMatrix.ofMatrix (fun i j : N => star (a i)*a j) := by
  classical
  by_cases hN : Nonempty N
  · let k : N := Classical.choice hN
    let R : CStarMatrix N N A := CStarMatrix.ofMatrix (fun i j => if i = k then a j else 0)
    have hr : star R*R = CStarMatrix.ofMatrix (fun i j : N => star (a i)*a j) := by
      ext i j
      rw [CStarMatrix.mul_apply]
      change (∑ l : N, star (if l = k then a i else 0) *
        (if l = k then a j else 0)) = star (a i)*a j
      simp
    rw [← hr]
    exact star_mul_self_nonneg R
  · have : IsEmpty N := not_nonempty_iff.mp hN
    have he : CStarMatrix.ofMatrix (fun i j : N => star (a i)*a j) = 0 := by
      ext i; exact isEmptyElim i
    rw [he]

end Choi

section FiniteSystems

variable {A : Type} [CStarAlgebra A]

structure FiniteCoefficientSystem (A : Type) [CStarAlgebra A] where
  Index : Type
  [finiteIndex : Fintype Index]
  [decidableIndex : DecidableEq Index]
  input : A →ₗ[ℂ] CStarMatrix Index Index ℂ
  input_one : input 1 = 1
  input_norm : ∀ x : A, ‖input x‖ ≤ ‖x‖
  coefficient : Index → A

attribute [instance] FiniteCoefficientSystem.finiteIndex FiniteCoefficientSystem.decidableIndex

section Matrices

variable {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

def blockDiagHom : (CStarMatrix I I ℂ × CStarMatrix J J ℂ) →⋆ₐ[ℂ]
    CStarMatrix (I ⊕ J) (I ⊕ J) ℂ where
  toFun T := CStarMatrix.ofMatrix (Matrix.fromBlocks
    (CStarMatrix.ofMatrix.symm T.1) 0 0 (CStarMatrix.ofMatrix.symm T.2))
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_one' := by
    ext i j; cases i <;> cases j <;> simp [CStarMatrix.one_apply,Matrix.fromBlocks]
  map_add' S T := by
    ext i j; cases i <;> cases j <;> simp [CStarMatrix.add_apply,Matrix.fromBlocks]
  map_mul' S T := by
    ext i j
    cases i <;> cases j <;>
      simp [CStarMatrix.mul_apply,Fintype.sum_sum_type,Matrix.fromBlocks]
  commutes' c := by
    ext i j
    cases i <;> cases j <;> simp [Algebra.algebraMap_eq_smul_one,CStarMatrix.smul_apply,
      CStarMatrix.one_apply,Matrix.fromBlocks]
  map_star' T := by
    ext i j; cases i <;> cases j <;> simp [CStarMatrix.star_apply,Matrix.fromBlocks]

end Matrices

section Synthesis

variable {I : Type} [Fintype I]

def matrixSynthesis (a : I → A) : CStarMatrix I I ℂ →ₗ[ℂ] A where
  toFun T := ∑ i, ∑ j, T i j • (star (a i)*a j)
  map_add' S T := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' c T := by simp [smul_smul,Finset.smul_sum]

lemma matrixSynthesis_one [DecidableEq I] (a : I → A) :
    matrixSynthesis a 1 = ∑ i, star (a i)*a i := by
  change (∑ i, ∑ j, (1 : CStarMatrix I I ℂ) i j • (star (a i)*a j)) = _
  simp [CStarMatrix.one_apply]

lemma matrixSynthesis_smul (a : I → A) {c : ℝ} (hc : 0 ≤ c) (T : CStarMatrix I I ℂ) :
    matrixSynthesis (fun i => Real.sqrt c • a i) T = c • matrixSynthesis a T := by
  have he (i j : I) : star (Real.sqrt c • a i)*(Real.sqrt c • a j) = c • (star (a i)*a j) := by
    rw [star_smul,star_trivial,smul_mul_smul_comm,Real.mul_self_sqrt hc]
  change (∑ i, ∑ j, T i j • (star (Real.sqrt c • a i)*(Real.sqrt c • a j))) =
    c • (∑ i, ∑ j, T i j • (star (a i)*a j))
  simp only [he,Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => smul_comm (T i j) c (star (a i)*a j)))

end Synthesis

namespace FiniteCoefficientSystem

def output (F : FiniteCoefficientSystem A) : A →ₗ[ℂ] A :=
  (matrixSynthesis F.coefficient).comp F.input

def zero : FiniteCoefficientSystem A where
  Index := Empty
  finiteIndex := inferInstance
  decidableIndex := inferInstance
  input := 0
  input_one := by ext i; exact isEmptyElim i
  input_norm := by intro x; simp
  coefficient := Empty.elim

@[simp] lemma zero_output (x : A) : (zero : FiniteCoefficientSystem A).output x = 0 := by
  simp [output,zero,matrixSynthesis]

def scale (F : FiniteCoefficientSystem A) (c : ℝ) : FiniteCoefficientSystem A :=
  { F with coefficient := fun i => Real.sqrt c • F.coefficient i }

lemma scale_output (F : FiniteCoefficientSystem A) {c : ℝ} (hc : 0 ≤ c) (x : A) :
    (F.scale c).output x = c • F.output x := matrixSynthesis_smul F.coefficient hc (F.input x)

open scoped Classical in

def add (F G : FiniteCoefficientSystem A) : FiniteCoefficientSystem A where
  Index := F.Index ⊕ G.Index
  finiteIndex := inferInstance
  decidableIndex := inferInstance
  input := blockDiagHom.toLinearMap.comp (F.input.prod G.input)
  input_one := by
    change blockDiagHom (F.input 1,G.input 1) = 1
    rw [F.input_one,G.input_one]
    exact map_one blockDiagHom
  input_norm x := by
    change ‖blockDiagHom (F.input x,G.input x)‖ ≤ ‖x‖
    exact (NonUnitalStarAlgHom.norm_apply_le
      (blockDiagHom (I := F.Index) (J := G.Index)) (F.input x,G.input x)).trans
      (max_le (F.input_norm x) (G.input_norm x))
  coefficient := Sum.elim F.coefficient G.coefficient

lemma add_output (F G : FiniteCoefficientSystem A) (x : A) :
    (F.add G).output x = F.output x + G.output x := by
  classical
  change (∑ i, ∑ j, blockDiagHom (F.input x,G.input x) i j •
    (star (Sum.elim F.coefficient G.coefficient i)*Sum.elim F.coefficient G.coefficient j)) =
    (∑ i, ∑ j, F.input x i j • (star (F.coefficient i)*F.coefficient j)) +
    (∑ i, ∑ j, G.input x i j • (star (G.coefficient i)*G.coefficient j))
  simp [blockDiagHom,Fintype.sum_sum_type,Matrix.fromBlocks]

end FiniteCoefficientSystem

end FiniteSystems

section HullRepresentation

variable {A K : Type} [CStarAlgebra A]

variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def finiteSystemCone : ConvexCone ℝ (selfAdjoint A →ₗ[ℝ] selfAdjoint A) where
  carrier := {L | ∃ F : FiniteCoefficientSystem A, ∀ x : selfAdjoint A, (L x : A) = F.output x}
  smul_mem' := by
    intro c hc L hL
    obtain ⟨F,hF⟩ := hL
    refine ⟨F.scale c,fun x => ?_⟩
    change c • (L x : A) = (F.scale c).output x
    rw [hF,F.scale_output hc.le]
  add_mem' := by
    intro L hL M hM
    obtain ⟨F,hF⟩ := hL
    obtain ⟨G,hG⟩ := hM
    refine ⟨F.add G,fun x => ?_⟩
    change (L x : A) + (M x : A) = (F.add G).output x
    rw [hF,hG,F.add_output]

theorem coefficientCone_finite_system (α : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    (L : selfAdjoint A →ₗ[ℝ] selfAdjoint A) (hL : L ∈ coefficientCone α) :
    ∃ F : FiniteCoefficientSystem A, ∀ x : selfAdjoint A, (L x : A) = F.output x := by
  apply (ConvexCone.hull_min (C := finiteSystemCone) ?_) hL
  rintro M ⟨n,k,a,rfl⟩
  obtain ⟨m,e,b,he,hmap⟩ := coefficientMap_orthonormal α k a
  let F : FiniteCoefficientSystem A := {
    Index := Fin m
    finiteIndex := inferInstance
    decidableIndex := inferInstance
    input := compressionMatrix α e he
    input_one := compressionMatrix_one α e he
    input_norm := compressionMatrix_norm α e he
    coefficient := b }
  refine ⟨F,fun x => ?_⟩
  change coefficientMap α k a (x : A) = matrixSynthesis b (compressionMatrix α e he (x : A))
  rw [hmap,coefficientMap_factorization α e he b]
  rfl

end HullRepresentation

end NuclearTrace

end

end

end OAI
