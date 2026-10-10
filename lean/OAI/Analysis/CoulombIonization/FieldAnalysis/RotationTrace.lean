import Mathlib
import OAI.Analysis.CoulombIonization.Variational.ConfigurationCoordinates

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_RotationTrace_scope

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

lemma sum_norm_sq_basis_eq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {ι κ ν : Type} [Fintype ι] [Fintype κ] [Fintype ν]
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℝ E)
    (d : OrthonormalBasis ν ℝ F) (L : E →L[ℝ] F) :
    (∑ i, ‖L (b i)‖^2) = ∑ j, ‖L (c j)‖^2 := by
  have he {α : Type} [Fintype α] (a : OrthonormalBasis α ℝ E) :
      (∑ i, ‖L (a i)‖^2) = ∑ j, ‖L.adjoint (d j)‖^2 := by
    calc
      _ = ∑ i, ∑ j, ⟪d j,L (a i)⟫^2 := by
        apply Finset.sum_congr rfl
        intro i _
        exact (d.sum_sq_inner_right _).symm
      _ = ∑ j, ∑ i, ⟪L.adjoint (d j),a i⟫^2 := by
        rw [Finset.sum_comm]
        simp_rw [ContinuousLinearMap.adjoint_inner_left]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        exact a.sum_sq_inner_left _
  exact (he b).trans (he c).symm

lemma sum_norm_sq_basis_isometry
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {ι ν : Type} [Fintype ι] [Fintype ν]
    (b : OrthonormalBasis ι ℝ E) (d : OrthonormalBasis ν ℝ F)
    (R : E ≃ₗᵢ[ℝ] E) (L : E →L[ℝ] F) :
    (∑ i, ‖L (R (b i))‖^2) = ∑ i, ‖L (b i)‖^2 :=
  sum_norm_sq_basis_eq (b.map R) b d L

end Work_RotationTrace_scope

open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff

open CoulombAtom
variable {N : ℕ}

def particleRotation (R : Space ≃ₗᵢ[ℝ] Space) : Configuration N ≃L[ℝ] Configuration N :=
  ContinuousLinearEquiv.piCongrRight (fun _ => R.toContinuousLinearEquiv)

def flatRotation (R : Space ≃ₗᵢ[ℝ] Space) :
    ((Fin N × Fin 3) → ℝ) ≃L[ℝ] ((Fin N × Fin 3) → ℝ) :=
  ((configurationCoordinates N).symm.trans (particleRotation R)).trans (configurationCoordinates N)

@[simp] lemma flatRotation_apply (R : Space ≃ₗᵢ[ℝ] Space)
    (x : (Fin N × Fin 3) → ℝ) (q : Fin N × Fin 3) :
    flatRotation R x q = R (WithLp.toLp 2 (fun a => x (q.1,a))) q.2 := rfl

lemma particleRotation_preserving (R : Space ≃ₗᵢ[ℝ] Space) :
    MeasurePreserving (particleRotation (N := N) R) :=
  measurePreserving_pi (fun _ : Fin N => (volume : Measure Space))
    (fun _ => volume) (fun _ => R.measurePreserving)

lemma flatRotation_preserving (R : Space ≃ₗᵢ[ℝ] Space) :
    MeasurePreserving (flatRotation (N := N) R) :=
  (configurationCoordinates_preserving N).comp
    ((particleRotation_preserving R).comp (configurationCoordinates_symm_preserving N))

lemma flatRotation_anti {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (ha : FlatAntisymmetric f) (R : Space ≃ₗᵢ[ℝ] Space) :
    FlatAntisymmetric (fun s x => f s (flatRotation R x)) := by
  intro i j hij s x
  convert ha i j hij s (flatRotation R x) using 1
  congr 1

def flatInsertion (i : Fin N) : Space →L[ℝ] ((Fin N × Fin 3) → ℝ) :=
  (configurationCoordinates N).toContinuousLinearMap.comp (ContinuousLinearMap.single ℝ (fun _ : Fin N => Space) i)

lemma flatInsertion_apply (i : Fin N) (v : Space) (q : Fin N × Fin 3) :
    flatInsertion i v q = if q.1=i then v q.2 else 0 := by
  change ((Pi.single i v : Configuration N) q.1) q.2 = _
  by_cases h : q.1=i <;> simp [h]

lemma flatInsertion_basis (i : Fin N) (a : Fin 3) :
    flatInsertion i ((EuclideanSpace.basisFun (Fin 3) ℝ) a) = Pi.single (i,a) 1 := by
  ext q
  rcases q with ⟨j,c⟩
  simp only [flatInsertion_apply,EuclideanSpace.basisFun_apply]
  by_cases hi : j=i
  · subst j
    simp [Pi.single_apply]
  · simp [hi,Prod.mk.injEq]

lemma flatRotation_insertion (R : Space ≃ₗᵢ[ℝ] Space) (i : Fin N) (v : Space) :
    flatRotation R (flatInsertion i v) = flatInsertion i (R v) := by
  ext q
  rw [flatRotation_apply,flatInsertion_apply]
  by_cases h : q.1=i
  · simp only [flatInsertion_apply,h,ite_true]
  · simp only [flatInsertion_apply,h,ite_false]
    change R 0 q.2 = _
    simp

lemma flatRotation_trace (R : Space ≃ₗᵢ[ℝ] Space)
    (L : ((Fin N × Fin 3) → ℝ) →L[ℝ] ℂ) :
    (∑ q, ‖L (flatRotation R (Pi.single q 1))‖^2) = ∑ q, ‖L (Pi.single q 1)‖^2 := by
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [←flatInsertion_basis,flatRotation_insertion]
  exact sum_norm_sq_basis_isometry (EuclideanSpace.basisFun (Fin 3) ℝ)
    Complex.orthonormalBasisOneI R (L.comp (flatInsertion i))

lemma memLp_fderiv_apply {f : ((Fin N × Fin 3) → ℝ) → ℂ}
    (hg : ∀ q, MemLp (fun x => fderiv ℝ f x (Pi.single q 1)) 2)
    (v : (Fin N × Fin 3) → ℝ) : MemLp (fun x => fderiv ℝ f x v) 2 := by
  classical
  have hv : v = ∑ q, v q • Pi.single q (1:ℝ) := by
    ext q
    simp [Pi.single_apply]
  have he : (fun x => fderiv ℝ f x v) = fun x => ∑ q, v q • fderiv ℝ f x (Pi.single q 1) := by
    funext x
    conv_lhs => rw [hv]
    simp only [map_sum,map_smul]
  rw [he]
  exact memLp_finsetSum _ (fun q _ => (hg q).const_smul (v q))

lemma flatRotation_fderiv {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (R : Space ≃ₗᵢ[ℝ] Space) (x v : (Fin N × Fin 3) → ℝ) :
    fderiv ℝ (fun y => f (flatRotation R y)) x v =
      fderiv ℝ f (flatRotation R x) (flatRotation R v) := by
  have hh := (hf.differentiable (by simp) (flatRotation R x)).hasFDerivAt.comp x
    (flatRotation R).hasFDerivAt
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe]
    using congrArg (fun L : ((Fin N × Fin 3) → ℝ) →L[ℝ] ℂ => L v) hh.fderiv

lemma flatRotation_gradient_memLp {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hg : ∀ q, MemLp (fun x => fderiv ℝ f x (Pi.single q 1)) 2)
    (R : Space ≃ₗᵢ[ℝ] Space) (q : Fin N × Fin 3) :
    MemLp (fun x => fderiv ℝ (fun y => f (flatRotation R y)) x (Pi.single q 1)) 2 := by
  simp_rw [flatRotation_fderiv hf]
  exact (memLp_fderiv_apply hg _).comp_measurePreserving (flatRotation_preserving R)

lemma flatRotation_kinetic {f : ((Fin N × Fin 3) → ℝ) → ℂ} (hf : ContDiff ℝ 1 f)
    (hg : ∀ q, MemLp (fun x => fderiv ℝ f x (Pi.single q 1)) 2)
    (R : Space ≃ₗᵢ[ℝ] Space) :
    (∑ q, ∫ x, ‖fderiv ℝ (fun y => f (flatRotation R y)) x (Pi.single q 1)‖^2) =
       ∑ q, ∫ x, ‖fderiv ℝ f x (Pi.single q 1)‖^2 := by
  rw [←integral_finsetSum _ (fun q _ => (flatRotation_gradient_memLp hf hg R q).norm.integrable_sq),
    ←integral_finsetSum _ (fun q _ => (hg q).norm.integrable_sq)]
  simp_rw [flatRotation_fderiv hf,flatRotation_trace]
  exact (flatRotation_preserving (N := N) R).integral_comp (flatRotation (N := N) R).toHomeomorph.measurableEmbedding (fun x => ∑ q, ‖fderiv ℝ f x (Pi.single q 1)‖^2)

end CoulombNeumann

end

end OAI
