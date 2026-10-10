import OAI.NumberTheory.Ostmann.Supply.LocalKernelCoordinates
import OAI.NumberTheory.Ostmann.Supply.TensorOperators

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
open TensorOperators
variable {p : ℕ} [NeZero p]

def scalarOnly (S T : Finset (ZMod p)) : LocalCoordinates T →L[ℂ] LocalCoordinates S :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ ℂ (centeredSpace S)).symm.toContinuousLinearMap.comp
    ((WithLp.fstL 2 ℂ ℂ (centeredSpace T)).prod 0)

omit [NeZero p] in
@[simp] theorem scalarOnly_fst (S T : Finset (ZMod p)) (x : LocalCoordinates T) :
    (scalarOnly S T x).fst = x.fst := rfl

omit [NeZero p] in
@[simp] theorem scalarOnly_snd (S T : Finset (ZMod p)) (x : LocalCoordinates T) :
    (scalarOnly S T x).snd = 0 := rfl

theorem localBlock_constant_eq_scalarOnly (S T : Finset (ZMod p))
    (hS : S.Nonempty) (hT : T.Nonempty) :
    localBlock S T (convolutionOperator (fun _ : ZMod p => (1:ℂ))) = scalarOnly S T := by
  apply ContinuousLinearMap.ext
  intro x
  apply (WithLp.equiv 2 (ℂ × centeredSpace S)).injective
  apply Prod.ext
  · exact localBlock_one_fst S T hS hT x
  · exact localBlock_one_snd S T hT x

theorem eval_four_single {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a b c d : E) (u v : ℂ) :
    BivariateTruncation.eval (Finsupp.single (0,0) a + Finsupp.single (1,0) b +
      Finsupp.single (0,1) c + Finsupp.single (1,1) d) u v =
      a+u•b+v•c+(u*v)•d := by
  change evalLinearMap u v _ = _
  rw [map_add,map_add,map_add]
  simp only [evalLinearMap_apply,TensorOperators.eval_single,pow_zero,pow_one,
    mul_one,one_mul,one_smul]

theorem collect_scalar_pencil {E : Type*} [AddCommGroup E] [Module ℂ E]
    (a b c : E) (t u v : ℂ) :
    a+u•(t•b)+v•(t•b)+(u*v)•c = a+((u+v)*t)•b+(u*v)•c := by
  module

def localKernelPolynomial (S : Finset (ZMod p)) (t : ℝ) :
    (ℕ×ℕ) →₀ (LocalCoordinates Sᶜ →L[ℂ] LocalCoordinates S) :=
  Finsupp.single (0,0) (localBlock S Sᶜ (convolutionOperator (fun _ : ZMod p => (1:ℂ)))) +
  Finsupp.single (1,0) ((t:ℂ) • localBlock S Sᶜ (spectralProjection (largeSpectrum S))) +
  Finsupp.single (0,1) ((t:ℂ) • localBlock S Sᶜ (spectralProjection (largeSpectrum S))) +
  Finsupp.single (1,1) (localBlock S Sᶜ (squaredLocalKernelOperator S t))

theorem eval_localKernelPolynomial (S : Finset (ZMod p)) (t : ℝ) (u v : ℂ) :
    @BivariateTruncation.eval (LocalCoordinates Sᶜ →L[ℂ] LocalCoordinates S)
      (by
        exact ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ)
          (E := LocalCoordinates Sᶜ) (F := LocalCoordinates S) (σ₁₂ := RingHom.id ℂ))
      (by infer_instance) (localKernelPolynomial S t) u v = localKernelBlock S t u v := by
  let : NormedAddCommGroup (LocalCoordinates Sᶜ →L[ℂ] LocalCoordinates S) := by
    exact ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ)
      (E := LocalCoordinates Sᶜ) (F := LocalCoordinates S) (σ₁₂ := RingHom.id ℂ)
  rw [localKernelPolynomial,eval_four_single]
  rw [localKernelBlock,localKernelOperator_decomposition,localBlock_add,localBlock_add,
    localBlock_smul,localBlock_smul]
  apply ContinuousLinearMap.ext
  intro x
  simp only [add_apply,smul_apply]
  exact collect_scalar_pencil _ _ _ (t:ℂ) u v

theorem localKernelPolynomial_zero (S : Finset (ZMod p)) (t : ℝ)
    (hS : S.Nonempty) (hT : Sᶜ.Nonempty) :
    localKernelPolynomial S t (0,0) = scalarOnly S Sᶜ := by
  simp [localKernelPolynomial,localBlock_constant_eq_scalarOnly S Sᶜ hS hT]

end Ostmann.Supply

end

end OAI
