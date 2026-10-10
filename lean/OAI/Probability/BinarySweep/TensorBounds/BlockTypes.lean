import Mathlib
import OAI.Probability.BinarySweep.Representations.IsotypicProjectionMoment
import OAI.Probability.BinarySweep.TensorBounds.SignedBlocks
import OAI.Probability.BinarySweep.FiniteLaws.PiCentrality

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation

variable {I A : Type*} [Fintype I] [LinearOrder I]
  [Fintype A] [DecidableEq A] {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

lemma submatrix_sum_eq {U X Y : Type*} [Fintype U]
    (M : U → Matrix X X ℂ) (f : Y → X) :
    (∑u, M u).submatrix f f=∑u, (M u).submatrix f f := by
  ext x y
  simp [Matrix.submatrix,Matrix.sum_apply]

def blockProjection (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :
    Matrix (Fin N → A) (Fin N → A) ℂ :=
  (piTensorMatrices (fun i => isotypicProjection p (ρ i))).submatrix (blockWords e) (blockWords e)

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma blockProjection_psd (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :
    (blockProjection e p ρ).PosSemidef :=
  (piTensorMatrices_psd _ (fun i => isotypicProjection_psd p (ρ i))).submatrix _

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma blockProjection_idempotent (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) :
    blockProjection e p ρ*blockProjection e p ρ=blockProjection e p ρ := by
  unfold blockProjection
  rw [Matrix.submatrix_mul_equiv,piTensorMatrices_mul]
  have hh : (fun i => isotypicProjection p (ρ i)*isotypicProjection p (ρ i)) =
      (fun i => isotypicProjection p (ρ i)) := by
    funext i
    exact projectionMatrix_idempotent (hilbertSubspace (isotypicSpan (ρ i) (tensorRep p (n i))))
  rw [hh]

omit [Fintype A] [DecidableEq A] in
lemma block_tensor_density (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (r : I → Matrix A A ℂ) :
    (piTensorMatrices (fun i => matrixTensorPower (n i) (r i))).submatrix
      (blockWords e) (blockWords e) = tensorMatrices (fun t => r (ofLex (e.symm t)).1) := by
  ext x y
  change (∏i, ∏a : Fin (n i), r i (x (e (toLex ⟨i,a⟩))) (y (e (toLex ⟨i,a⟩)))) =
    ∏t, r (ofLex (e.symm t)).1 (x t) (y t)
  calc
    _ = ∏t : Σ i, Fin (n i), r t.1 (x (e (toLex t))) (y (e (toLex t))) := (Fintype.prod_sigma _).symm
    _ = _ := by
      have hh := (toLex.trans e.toEquiv).prod_comp (fun t => r (ofLex (e.symm t)).1 (x t) (y t))
      change (∏t : Σ i, Fin (n i), r (ofLex (e.symm (e (toLex t)))).1 (x (e (toLex t))) (y (e (toLex t)))) = _ at hh
      simpa only [OrderIso.symm_apply_apply, ofLex_toLex] using hh

lemma block_density_domination [Nonempty A] (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    [∀i, (ρ i).IsIrreducible] :
    (((∏i, (Module.finrank ℂ (V i):ℂ)*(n i+1:ℂ)^(2*(Fintype.card A)^2))) •
      (∑u : ∀i, LocalDensityIndex p (n i),
        tensorMatrices (fun t => localDensity p (n (ofLex (e.symm t)).1) (u (ofLex (e.symm t)).1))) -
      blockProjection e p ρ).PosSemidef := by
  have h := piTensor_density_domination (fun i => isotypicProjection p (ρ i))
    (fun i u => matrixTensorPower (n i) (localDensity p (n i) u))
    (fun i => (Module.finrank ℂ (V i):ℂ)*(n i+1:ℂ)^(2*(Fintype.card A)^2))
    (fun i => isotypicProjection_psd p (ρ i))
    (fun i => local_type_density_domination p (n i) (ρ i))
  have hh := h.submatrix (blockWords (A:=A) e)
  simpa only [Matrix.submatrix_sub,Matrix.submatrix_smul,Pi.sub_apply,Pi.smul_apply,submatrix_sum_eq,
    block_tensor_density,blockProjection] using hh

omit [∀i, FiniteDimensional ℂ (V i)] in
lemma blockProjection_central (e : (Σₗ i, Fin (n i)) ≃o Fin N)
    (p : A → Bool) (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    (M : Matrix (Fin N → A) (Fin N → A) ℂ)
    (hc : ∀g : ∀i, Equiv.Perm (Fin (n i)),
      M*actionMatrix p (blockPerm e g)=actionMatrix p (blockPerm e g)*M) :
    M*blockProjection e p ρ=blockProjection e p ρ*M := by
  let E := Matrix.reindexAlgEquiv ℂ ℂ (blockWords (A:=A) e)
  have he (g : ∀i, Equiv.Perm (Fin (n i))) :
      E (actionMatrix p (blockPerm e g))=piTensorMatrices (fun i => actionMatrix p (g i)) := by
    change E (LinearMap.toMatrix' (act p (blockPerm e g)))=_
    rw [actionMatrix_blocks]
    ext x y
    change (piTensorMatrices (fun i => actionMatrix p (g i))) (blockWords e ((blockWords e).symm x)) (blockWords e ((blockWords e).symm y)) = _
    simp
  have hP : E (blockProjection e p ρ)=piTensorMatrices (fun i => isotypicProjection p (ρ i)) := by
    ext x y
    change (piTensorMatrices (fun i => isotypicProjection p (ρ i))) (blockWords e ((blockWords e).symm x)) (blockWords e ((blockWords e).symm y)) = _
    simp
  have hsingle (i : I) (g : Equiv.Perm (Fin (n i))) :
      piTensorMatrices (fun j => actionMatrix p (Pi.mulSingle (M:=fun j => Equiv.Perm (Fin (n j))) i g j)) =
        siteMatrix i (actionMatrix p g) := by
    have hs := siteMatrix_eq_mask (i:=i) (P:=fun j => actionMatrix p (Pi.mulSingle (M:=fun j => Equiv.Perm (Fin (n j))) i g j))
    simp only [Pi.mulSingle_eq_same] at hs
    rw [hs]
    congr 1
    funext j
    by_cases hji : j=i
    · subst j; simp
    · simp [Pi.mulSingle_eq_of_ne hji,actionMatrix_one]
  apply E.injective
  simp only [map_mul,hP]
  apply piTensor_centrality (fun i g => actionMatrix p g) (fun i => isotypicProjection p (ρ i))
    (fun i => typeProjection_central p (ρ i))
  intro i g
  have hh := congrArg E (hc (Pi.mulSingle (M:=fun j => Equiv.Perm (Fin (n j))) i g))
  simpa only [map_mul,he,hsingle] using hh

end BinaryCoordinateSweeps.Signed

end

open scoped BigOperators Classical ComplexOrder
open Matrix

namespace BinaryCoordinateSweeps
open Density TraceHolder Irrep Representation

lemma piTensorMatrices_pow {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀i, Fintype (A i)] [∀i, DecidableEq (A i)]
    (M : ∀i, Matrix (A i) (A i) ℂ) (q : ℕ) :
    (piTensorMatrices M)^q=piTensorMatrices (fun i => M i^q) := by
  induction q with
  | zero => simp only [pow_zero,piTensorMatrices_one]
  | succ q ih => rw [pow_succ,ih,piTensorMatrices_mul]; simp only [pow_succ]

lemma gram_trace_real {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (q : ℕ) : ((matrixMoment q M:ℝ):ℂ)=((star M*M)^q).trace := by
  have hh := ((Matrix.posSemidef_conjTranspose_mul_self M).pow q).trace_nonneg
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im, Matrix.star_eq_conjTranspose] using (Complex.nonneg_iff.mp hh).2

lemma tensor_matrixMoment {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀i, Fintype (A i)] [∀i, DecidableEq (A i)]
    (M : ∀i, Matrix (A i) (A i) ℂ) (q : ℕ) :
    matrixMoment q (piTensorMatrices M)=∏i, matrixMoment q (M i) := by
  unfold matrixMoment
  rw [Matrix.star_eq_conjTranspose,piTensorMatrices_star,piTensorMatrices_mul,
    piTensorMatrices_pow,piTensorMatrices_trace]
  have he (i : I) : (((M i).conjTranspose*M i)^q).trace=
      ((matrixMoment q (M i):ℝ):ℂ) := (gram_trace_real (M i) q).symm
  simp_rw [he]
  rw [← Complex.ofReal_prod,Complex.ofReal_re]
  rfl

lemma matrixMoment_reindex {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (e : I ≃ J) (M : Matrix J J ℂ) (q : ℕ) :
    matrixMoment q (M.submatrix e e)=matrixMoment q M := by
  have hp (B : Matrix J J ℂ) : (B.submatrix e e)^q=(B^q).submatrix e e := by
    induction q with
    | zero => simp only [pow_zero,Matrix.submatrix_one_equiv]
    | succ q ih => rw [pow_succ,ih,Matrix.submatrix_mul_equiv,← pow_succ]
  unfold matrixMoment
  rw [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv,hp]
  congr 1
  exact e.sum_comp (fun i => ((M.conjTranspose*M)^q) i i)

namespace Signed
variable {I A : Type*} [Fintype I] [LinearOrder I]
  [Fintype A] [DecidableEq A] {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

def blockAverage (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool)
    (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) : Matrix (Fin N → A) (Fin N → A) ℂ :=
  ∑g : ∀i, Equiv.Perm (Fin (n i)), (∏i, w i (g i)) • actionMatrix p (blockPerm e g)

lemma blockAverage_tensor (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool)
    (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) :
    blockAverage e p w=(piTensorMatrices (fun i => signedAverage p (w i))).submatrix
      (blockWords e) (blockWords e) := by
  unfold blockAverage signedAverage
  rw [piTensorMatrices_sum,submatrix_sum_eq]
  apply Finset.sum_congr rfl
  intro g _
  rw [piTensorMatrices_smul,Matrix.submatrix_smul]
  congr 1
  exact actionMatrix_blocks e g p

lemma block_projected_moment (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    [∀i, (ρ i).IsIrreducible] (hρ : ∀i g v, ‖ρ i g v‖=‖v‖)
    (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) {q : ℕ} (hq : 0 < q) :
    matrixMoment q (blockProjection e p ρ*blockAverage e p w)=
      ∏i, (Module.finrank ℂ (IntertwiningMap (ρ i) (hilbertTensorRep p (n i))):ℝ)*
        evenMoment q (groupAverage (ρ i) (w i)) := by
  rw [blockAverage_tensor,blockProjection,Matrix.submatrix_mul_equiv,
    piTensorMatrices_mul,matrixMoment_reindex,tensor_matrixMoment]
  apply Finset.prod_congr rfl
  intro i _
  exact local_projected_moment p (ρ i) (hρ i) (w i) hq

theorem block_projected_moment_le (e : (Σₗ i, Fin (n i)) ≃o Fin N) (p : A → Bool)
    (ρ : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i))
    [∀i, (ρ i).IsIrreducible] (hρ : ∀i g v, ‖ρ i g v‖=‖v‖)
    (w : ∀i, Equiv.Perm (Fin (n i)) → ℂ) {q : ℕ} (hq : 0 < q) :
    matrixMoment q (blockProjection e p ρ*blockAverage e p w) ≤
      ∏i, (n i+1:ℝ)^((Fintype.card A)^2)*evenMoment q (groupAverage (ρ i) (w i)) := by
  rw [blockAverage_tensor,blockProjection,Matrix.submatrix_mul_equiv,
    piTensorMatrices_mul,matrixMoment_reindex,tensor_matrixMoment]
  apply Finset.prod_le_prod₀
  · intro i _; exact matrixMoment_nonneg _ _
  · intro i _; exact local_projected_moment_le p (ρ i) (hρ i) (w i) hq

end Signed
end BinaryCoordinateSweeps

end

end OAI
