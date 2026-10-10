import OAI.Algebra.Determinantal.Gradients

namespace OAI

namespace PermanentBorder.Selector
open MvPolynomial Polynomial Matrix
open GradientAlgebra AdjugateAlgebra Conductor

lemma fixedAffinePencil_eq_pencil {K : Type*} [Field K] {k : ℕ}
    (θ : Fin (k+1) → K) (A : Matrix (Fin (k+1)) (Fin (k+1)) K) :
    fixedAffinePencil θ A = pencilMatrix (pencilBase θ A) := by
  ext i j
  simp only [fixedAffinePencil, pencilMatrix, pencilBase, Matrix.add_apply,
    Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, Matrix.diagonal_apply,
    smul_eq_mul, map_add, map_mul]
  split_ifs <;> simp
  ring

theorem gradient_forces_normalization_defect {K : Type*}
    [Field K] [Infinite K] [CharP K 2] {k q : ℕ} (hq : 3*q ≤ k)
    (θ : Fin (k+1) → K) (hθ : Function.Injective θ)
    (A : Matrix (Fin (k+1)) (Fin (k+1)) K)
    (hcrit : ∀ ij : Fin (k+1) × Fin (k+1), MvPolynomial.eval
      (fun ab : Fin (k+1) × Fin (k+1) => A ab.1 ab.2)
      (pderiv ij (diagonalCoefficient
        (Matrix.of fun a b => (MvPolynomial.X (a,b) :
          MvPolynomial (Fin (k+1) × Fin (k+1)) K)) (fun i => MvPolynomial.C (θ i)) q)) = 0) :
    let T := -(pencilBase θ A)
    let Q := FractionRing K[X]
    let R := integralClosure K[X] (AdjoinRoot (T.charpoly.map (algebraMap K[X] Q)))
    ((q+2).choose 2 : ℕ∞) ≤ Module.length K (R ⧸ LinearMap.range
      (normalizationInclusion (Q := Q) T.charpoly T.charpoly_monic).toLinearMap) := by
  apply critical_normalization_defect θ hθ A q hq
  intro i j
  have h := hcrit (j,i)
  rw [diagonalCoefficient_eq_affineSelector, gradient_affineSelector,
    fixedAffinePencil_eq_pencil] at h
  exact h

end PermanentBorder.Selector

namespace PermanentBorder.CentralizerDimension

open Matrix MvPolynomial

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

def centralizer (A : Matrix ι ι K) : Submodule K (Matrix ι ι K) where
  carrier := {B | A * B = B * A}
  zero_mem' := by simp
  add_mem' := by
    intro B C hB hC
    dsimp at hB hC ⊢
    simp only [mul_add, add_mul, hB, hC]
  smul_mem' := by
    intro c B hB
    dsimp at hB ⊢
    simp only [Matrix.mul_smul, Matrix.smul_mul, hB]

@[simp] theorem mem_centralizer (A B : Matrix ι ι K) :
    B ∈ centralizer A ↔ A * B = B * A := Iff.rfl

def centralizerOne (A : Matrix ι ι K) : centralizer A :=
  ⟨1, by simp⟩

noncomputable def centralizerBasis (A : Matrix ι ι K) :
    Module.Basis (Fin (Module.finrank K (centralizer A))) K (centralizer A) :=
  Module.finBasis K (centralizer A)

noncomputable def coordinateMatrix (A : Matrix ι ι K) :
    Matrix ι ι (MvPolynomial (Fin (Module.finrank K (centralizer A))) K) :=
  fun i j => ∑ b, C ((centralizerBasis A b).val i j) * X b

noncomputable def determinantPolynomial (A : Matrix ι ι K) :
    MvPolynomial (Fin (Module.finrank K (centralizer A))) K :=
  (coordinateMatrix A).det

noncomputable def singularIdeal (A : Matrix ι ι K) :
    Ideal (MvPolynomial (Fin (Module.finrank K (centralizer A))) K) :=
  Ideal.span {determinantPolynomial A}

theorem eval_coordinateMatrix (A : Matrix ι ι K) (B : centralizer A) :
    (coordinateMatrix A).map (eval (fun b => (centralizerBasis A).repr B b)) = B.val := by
  classical
  ext i j
  have h := congrArg (fun W : centralizer A => W.val i j)
    ((centralizerBasis A).sum_repr B)
  simp only [coordinateMatrix, Matrix.map_apply, map_sum, map_mul, eval_C, eval_X]
  simpa only [Submodule.coe_sum, Submodule.coe_smul, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, mul_comm] using h

theorem eval_determinantPolynomial (A : Matrix ι ι K) (B : centralizer A) :
    eval (fun b => (centralizerBasis A).repr B b) (determinantPolynomial A) =
      B.val.det := by
  rw [determinantPolynomial, RingHom.map_det]
  change ((coordinateMatrix A).map (eval (fun b => (centralizerBasis A).repr B b))).det = _
  rw [eval_coordinateMatrix]

theorem determinantPolynomial_ne_zero (A : Matrix ι ι K) :
    determinantPolynomial A ≠ 0 := by
  intro h
  have he := eval_determinantPolynomial A (centralizerOne A)
  simp [h, centralizerOne] at he

theorem singular_centralizer_dimension (A : Matrix ι ι K) :
    ringKrullDim (MvPolynomial (Fin (Module.finrank K (centralizer A))) K ⧸
      singularIdeal A) + 1 ≤ (Module.finrank K (centralizer A) : WithBot ℕ∞) := by
  calc
    _ ≤ ringKrullDim (MvPolynomial (Fin (Module.finrank K (centralizer A))) K) :=
      ringKrullDim_quotient_succ_le_of_nonZeroDivisor
        (mem_nonZeroDivisors_iff_ne_zero.mpr (determinantPolynomial_ne_zero A))
    _ = _ := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      simp

theorem nilpotent_centralizer_vanish [Nonempty ι] (A : Matrix ι ι K)
    (B : centralizer A) (hB : IsNilpotent B.val) :
    eval (fun b => (centralizerBasis A).repr B b) (determinantPolynomial A) = 0 := by
  rw [eval_determinantPolynomial]
  obtain ⟨e, he⟩ := hB
  have hd := congrArg Matrix.det he
  rw [Matrix.det_pow, Matrix.det_zero] at hd
  exact (show IsNilpotent B.val.det from ⟨e, hd⟩).eq_zero

noncomputable def nilpotencyEquation (A : Matrix ι ι K) (d : ℕ) :
    MvPolynomial (Fin (Module.finrank K (centralizer A))) K :=
  ((coordinateMatrix A).charpoly - Polynomial.X ^ Fintype.card ι).coeff d

noncomputable def nilpotentIdeal (A : Matrix ι ι K) :
    Ideal (MvPolynomial (Fin (Module.finrank K (centralizer A))) K) :=
  Ideal.span (Set.range (nilpotencyEquation A))

theorem eval_nilpotencyEquation (A : Matrix ι ι K) (B : centralizer A) (d : ℕ) :
    eval (fun b => (centralizerBasis A).repr B b) (nilpotencyEquation A d) =
      (B.val.charpoly - Polynomial.X ^ Fintype.card ι).coeff d := by
  rw [nilpotencyEquation, ← Polynomial.coeff_map]
  congr 1
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    ← Matrix.charpoly_map, eval_coordinateMatrix]

theorem nilpotentIdeal_vanishing_iff (A : Matrix ι ι K) (B : centralizer A) :
    (∀ p ∈ nilpotentIdeal A,
      eval (fun b => (centralizerBasis A).repr B b) p = 0) ↔ IsNilpotent B.val := by
  constructor
  · intro h
    have heq : B.val.charpoly = Polynomial.X ^ Fintype.card ι := by
      apply sub_eq_zero.mp
      ext d
      have hd := h _ (Ideal.subset_span (Set.mem_range_self d))
      simpa only [eval_nilpotencyEquation, Polynomial.coeff_zero] using hd
    refine ⟨Fintype.card ι, ?_⟩
    have hc := Matrix.aeval_self_charpoly B.val
    rwa [heq, Polynomial.aeval_X_pow] at hc
  · intro h
    have heq : B.val.charpoly = Polynomial.X ^ Fintype.card ι :=
      sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h).eq_zero
    have hi : nilpotentIdeal A ≤ RingHom.ker
        (eval (fun b => (centralizerBasis A).repr B b)) := by
      rw [nilpotentIdeal, Ideal.span_le]
      rintro _ ⟨d, rfl⟩
      change eval (fun b => (centralizerBasis A).repr B b) (nilpotencyEquation A d) = 0
      rw [eval_nilpotencyEquation, heq, sub_self, Polynomial.coeff_zero]
    exact fun p hp => hi hp

theorem singularIdeal_le_nilpotentIdeal [Nonempty ι] (A : Matrix ι ι K) :
    singularIdeal A ≤ nilpotentIdeal A := by
  rw [singularIdeal, Ideal.span_singleton_le_iff_mem]
  have h0 : (coordinateMatrix A).charpoly.coeff 0 ∈ nilpotentIdeal A := by
    have heq : nilpotencyEquation A 0 = (coordinateMatrix A).charpoly.coeff 0 := by
      simp [nilpotencyEquation, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        Ne.symm (Fintype.card_ne_zero : Fintype.card ι ≠ 0)]
    rw [← heq]
    exact Ideal.subset_span (Set.mem_range_self 0)
  rw [determinantPolynomial, Matrix.det_eq_sign_charpoly_coeff]
  exact (nilpotentIdeal A).mul_mem_left _ h0

theorem nilpotent_centralizer_dimension [Nonempty ι] (A : Matrix ι ι K) :
    ringKrullDim (MvPolynomial (Fin (Module.finrank K (centralizer A))) K ⧸
      nilpotentIdeal A) + 1 ≤ (Module.finrank K (centralizer A) : WithBot ℕ∞) := by
  calc
    _ ≤ ringKrullDim (MvPolynomial (Fin (Module.finrank K (centralizer A))) K ⧸
        singularIdeal A) + 1 := by
      exact add_le_add (ringKrullDim_le_of_surjective
        (Ideal.Quotient.factor (singularIdeal_le_nilpotentIdeal A))
        (Ideal.Quotient.factor_surjective (singularIdeal_le_nilpotentIdeal A))) le_rfl
    _ ≤ _ := singular_centralizer_dimension A

end PermanentBorder.CentralizerDimension

namespace PermanentBorder.MatrixFieldExtension
open Matrix
variable {K L ι : Type*} [Field K] [Field L] [Fintype ι] [DecidableEq ι]

theorem rank_map (φ : K →+* L) (M : Matrix ι ι K) :
    (M.map φ).rank = M.rank := by
  classical
  obtain ⟨U, V, d, h⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal M
  let P := (U.map Matrix.TransvectionStruct.toMatrix).prod
  let Q := (V.map Matrix.TransvectionStruct.toMatrix).prod
  have hP : P.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod U
  have hQ : Q.det = 1 := Matrix.TransvectionStruct.det_toMatrix_prod V
  have hP' : (P.map φ).det = 1 := by
    change (φ.mapMatrix P).det = 1
    rw [← φ.map_det, hP, map_one]
  have hQ' : (Q.map φ).det = 1 := by
    change (φ.mapMatrix Q).det = 1
    rw [← φ.map_det, hQ, map_one]
  have h' : P.map φ * M.map φ * Q.map φ = diagonal (φ ∘ d) := by
    simpa only [Matrix.map_mul, Matrix.diagonal_map (map_zero φ), Function.comp_def] using
      congrArg (fun X : Matrix ι ι K => X.map φ) h
  calc
    (M.map φ).rank = (P.map φ * M.map φ * Q.map φ).rank := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (hQ' ▸ isUnit_one),
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ (hP' ▸ isUnit_one)]
    _ = (diagonal (φ ∘ d)).rank := congrArg Matrix.rank h'
    _ = (diagonal d).rank := by
      simp only [Matrix.rank_diagonal, Function.comp_apply, map_ne_zero]
    _ = (P * M * Q).rank := congrArg Matrix.rank h.symm
    _ = M.rank := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (hQ ▸ isUnit_one),
        Matrix.rank_mul_eq_right_of_isUnit_det _ _ (hP ▸ isUnit_one)]

theorem finrank_ker_map (φ : K →+* L) (M : Matrix ι ι K) :
    Module.finrank L (LinearMap.ker (M.map φ).mulVecLin) =
      Module.finrank K (LinearMap.ker M.mulVecLin) := by
  have h := M.mulVecLin.finrank_range_add_finrank_ker
  have h' := (M.map φ).mulVecLin.finrank_range_add_finrank_ker
  change M.rank + _ = _ at h
  change (M.map φ).rank + _ = _ at h'
  rw [rank_map] at h'
  simp only [Module.finrank_fintype_fun_eq_card] at h h'
  omega

variable [Algebra K L]

def mapKernel (M : Matrix ι ι K) (v : LinearMap.ker M.mulVecLin) :
    LinearMap.ker (M.map (algebraMap K L)).mulVecLin :=
  ⟨algebraMap K L ∘ v.val, by
    change (M.map (algebraMap K L)) *ᵥ (algebraMap K L ∘ v.val) = 0
    ext i
    rw [← RingHom.map_mulVec]
    have hv : M *ᵥ v.val = 0 := v.property
    simp only [hv, Pi.zero_apply, map_zero]⟩

omit [DecidableEq ι] in
theorem mapKernel_linearIndependent {κ : Type*} (M : Matrix ι ι K)
    (b : Module.Basis κ K (LinearMap.ker M.mulVecLin)) :
    LinearIndependent L (fun i => mapKernel (L := L) M (b i)) := by
  have hb : LinearIndependent K (fun i => (b i).val) :=
    b.linearIndependent.map' (LinearMap.ker M.mulVecLin).subtype (Submodule.ker_subtype _)
  have hm : LinearIndependent L (fun i => algebraMap K L ∘ (b i).val) :=
    (linearIndependent_algebraMap_comp_iff (R := K) (S := L)).mpr hb
  exact hm.of_comp (LinearMap.ker (M.map (algebraMap K L)).mulVecLin).subtype

noncomputable def kernelBasisMap {κ : Type*} [Fintype κ] (M : Matrix ι ι K)
    (b : Module.Basis κ K (LinearMap.ker M.mulVecLin)) :
    Module.Basis κ L (LinearMap.ker (M.map (algebraMap K L)).mulVecLin) :=
  basisOfLinearIndependentOfCardEqFinrank' (fun i => mapKernel (L := L) M (b i))
    (mapKernel_linearIndependent M b)
    (by rw [finrank_ker_map, Module.finrank_eq_card_basis b])

@[simp] theorem kernelBasisMap_apply {κ : Type*} [Fintype κ] (M : Matrix ι ι K)
    (b : Module.Basis κ K (LinearMap.ker M.mulVecLin)) (i : κ) :
    kernelBasisMap (L := L) M b i = mapKernel M (b i) := by
  simp only [kernelBasisMap, coe_basisOfLinearIndependentOfCardEqFinrank']

end PermanentBorder.MatrixFieldExtension

namespace PermanentBorder.CentralizerBaseChange
open Matrix CentralizerDimension MatrixFieldExtension
variable {K L ι : Type*} [Field K] [Field L]
  [Fintype ι] [DecidableEq ι]

def equationMatrix (A : Matrix ι ι K) : Matrix (ι × ι) (ι × ι) K :=
  fun i j => (if i.2 = j.2 then A i.1 j.1 else 0) -
    (if i.1 = j.1 then A j.2 i.2 else 0)

theorem equationMatrix_mulVec (A B : Matrix ι ι K) :
    equationMatrix A *ᵥ Function.uncurry B = Function.uncurry (A * B - B * A) := by
  funext ij
  rcases ij with ⟨i,j⟩
  change (∑ a : ι × ι, ((if j = a.2 then A i a.1 else 0) -
    (if i = a.1 then A a.2 j else 0)) * B a.1 a.2) =
    (∑ a, A i a * B a j) - ∑ a, B i a * A a j
  simp only [Fintype.sum_prod_type, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_comm]

omit [Fintype ι] in
@[simp] theorem equationMatrix_map (A : Matrix ι ι K) (φ : K →+* L) :
    equationMatrix (A.map φ) = (equationMatrix A).map φ := by
  ext i j
  simp only [equationMatrix, Matrix.map_apply, map_sub, apply_ite φ, map_zero]

def centralizerKernelEquiv (A : Matrix ι ι K) :
    centralizer A ≃ₗ[K] LinearMap.ker (equationMatrix A).mulVecLin where
  toFun B := ⟨Function.uncurry B.val, by
    change equationMatrix A *ᵥ Function.uncurry B.val = 0
    rw [equationMatrix_mulVec, sub_eq_zero.mpr B.property]
    rfl⟩
  invFun v := ⟨(fun i j => v.val (i,j)), by
    apply sub_eq_zero.mp
    have h := equationMatrix_mulVec A (show Matrix ι ι K from fun i j => v.val (i,j))
    ext i j
    exact (congrFun h (i,j)).symm.trans (congrFun v.property (i,j))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable [Algebra K L]

theorem finrank_centralizer_map (A : Matrix ι ι K) :
    Module.finrank L (centralizer (A.map (algebraMap K L))) =
      Module.finrank K (centralizer A) := by
  calc
    _ = Module.finrank L (LinearMap.ker (equationMatrix (A.map (algebraMap K L))).mulVecLin) :=
      (centralizerKernelEquiv _).finrank_eq
    _ = Module.finrank L (LinearMap.ker ((equationMatrix A).map (algebraMap K L)).mulVecLin) := by
      rw [equationMatrix_map]
    _ = Module.finrank K (LinearMap.ker (equationMatrix A).mulVecLin) :=
      finrank_ker_map _ _
    _ = _ := (centralizerKernelEquiv _).finrank_eq.symm

def flatten (F : Type*) [Field F] (ι : Type*) :
    Matrix ι ι F ≃ₗ[F] (ι × ι → F) where
  toFun := Function.uncurry
  invFun := Function.curry
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def mapCentralizer (A : Matrix ι ι K) (B : centralizer A) :
    centralizer (A.map (algebraMap K L)) :=
  ⟨B.val.map (algebraMap K L), by
    change A.map _ * B.val.map _ = B.val.map _ * A.map _
    rw [← Matrix.map_mul, ← Matrix.map_mul, B.property]⟩

theorem mapCentralizer_linearIndependent {κ : Type*}
    (A : Matrix ι ι K) (b : Module.Basis κ K (centralizer A)) :
    LinearIndependent L (fun i => mapCentralizer (L := L) A (b i)) := by
  have hb : LinearIndependent K (fun i => Function.uncurry (b i).val) :=
    (b.linearIndependent.map' (centralizer A).subtype (Submodule.ker_subtype _)).map'
      (flatten K ι).toLinearMap (LinearEquiv.ker _)
  have hm : LinearIndependent L (fun i => algebraMap K L ∘ Function.uncurry (b i).val) :=
    (linearIndependent_algebraMap_comp_iff (R := K) (S := L)).mpr hb
  exact hm.of_comp ((flatten L ι).toLinearMap.comp (centralizer (A.map (algebraMap K L))).subtype)

noncomputable def centralizerBasisMap {κ : Type*} [Fintype κ]
    (A : Matrix ι ι K) (b : Module.Basis κ K (centralizer A)) :
    Module.Basis κ L (centralizer (A.map (algebraMap K L))) :=
  basisOfLinearIndependentOfCardEqFinrank' (fun i => mapCentralizer (L := L) A (b i))
    (mapCentralizer_linearIndependent A b)
    (by rw [finrank_centralizer_map, Module.finrank_eq_card_basis b])

@[simp] theorem centralizerBasisMap_apply {κ : Type*} [Fintype κ]
    (A : Matrix ι ι K) (b : Module.Basis κ K (centralizer A)) (i : κ) :
    centralizerBasisMap (L := L) A b i = mapCentralizer A (b i) := by
  simp only [centralizerBasisMap, coe_basisOfLinearIndependentOfCardEqFinrank']

end PermanentBorder.CentralizerBaseChange

namespace PermanentBorder.CoordinateGauge
open Module Submodule
variable {K ι : Type*} [Field K] [Fintype ι]

theorem exists_coordinate_gauge (S : Submodule K (ι → K)) :
    ∃ a : Fin (Module.finrank K S) → ι, Function.Injective a ∧
      Function.Bijective (fun x : S => fun j => x.val (a j)) := by
  classical
  let q (i : ι) : Module.Dual K S := (LinearMap.proj i).comp S.subtype
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K q
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let r : S →ₗ[K] (κ → K) := LinearMap.pi fun j => q (a j)
  have hri : Function.Injective r := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hz : ∀ j, q (a j) x = 0 := congrFun (show r x = 0 from hx)
    have hs : ∀ g ∈ Submodule.span K (Set.range (q ∘ a)), g x = 0 := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem z hz' => obtain ⟨j, rfl⟩ := hz'; exact hz j
      | zero => rfl
      | add y z _ _ hy hz => simp only [LinearMap.add_apply, hy, hz, add_zero]
      | smul c y _ hy => simp only [LinearMap.smul_apply, hy, smul_zero]
    have hcoord (i : ι) : q i x = 0 := by
      apply hs
      rw [hspan]
      exact Submodule.subset_span (Set.mem_range_self i)
    change x = 0
    apply Subtype.ext
    funext i
    exact hcoord i
  have hc : Fintype.card κ = Module.finrank K S := by
    apply Nat.le_antisymm
    · simpa only [Subspace.dual_finrank_eq] using hli.fintype_card_le_finrank
    · simpa only [Module.finrank_fintype_fun_eq_card] using
        (LinearMap.finrank_le_finrank_of_injective hri)
  have hrs : Function.Surjective r :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa only [Module.finrank_fintype_fun_eq_card] using hc.symm)).mp hri
  let e := Fintype.equivFinOfCardEq hc
  refine ⟨a ∘ e.symm, ha.comp e.symm.injective, ?_, ?_⟩
  · intro x y h
    apply hri
    funext j
    have he := congrFun h (e j)
    change x.val (a j) = y.val (a j)
    simpa only [Function.comp_apply, e.symm_apply_apply] using he
  · intro v
    obtain ⟨x, hx⟩ := hrs (v ∘ e)
    refine ⟨x, ?_⟩
    funext j
    have he := congrFun hx (e.symm j)
    simpa only [r, LinearMap.pi_apply, q, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.proj_apply, Function.comp_apply, e.apply_symm_apply] using he

end PermanentBorder.CoordinateGauge

end OAI
