import OAI.Analysis.Nuclearity.QuotientCommutingBound
import OAI.Analysis.Nuclearity.DenseUnitalCompletion
import OAI.Analysis.Nuclearity.UnitalFaithfulRepresentation
import OAI.Analysis.Nuclearity.MinimalTensorKernelFaithful
import OAI.Analysis.JiangSu.CStarAlgebras.CStarNormCompletion

namespace OAI

/-! Tensor-norm nuclearity of a separable quotient of the nuclear source.
The completion is made unital using the image of its algebraic unit; no
unital representation of the quotient in a nonunital algebra is assumed. -/
noncomputable section
open Filter TopologicalSpace
open scoped TensorProduct ComplexOrder
namespace WeakPureInfiniteness

universe u v
variable {A : Type u} {Q B : Type v} [CStarAlgebra A] [CStarAlgebra Q] [CStarAlgebra B]
  [PartialOrder A] [StarOrderedRing A] [PartialOrder Q] [StarOrderedRing Q]
  [PartialOrder B] [StarOrderedRing B] [SeparableSpace Q]

private def algebraicLeft : Q →⋆ₐ[ℂ] Q ⊗[ℂ] B where
  __ := (Algebra.TensorProduct.includeLeft : Q →ₐ[ℂ] Q ⊗[ℂ] B)
  map_star' a := by simp

private def algebraicRight : B →⋆ₐ[ℂ] Q ⊗[ℂ] B where
  __ := (Algebra.TensorProduct.includeRight : B →ₐ[ℂ] Q ⊗[ℂ] B)
  map_star' b := by simp

omit [PartialOrder Q] [StarOrderedRing Q] [PartialOrder B] [StarOrderedRing B]
  [SeparableSpace Q] in
private lemma algebraic_legs (a : Q) (b : B) :
    algebraicLeft a * algebraicRight b = a ⊗ₜ[ℂ] b := by
  change (a ⊗ₜ[ℂ] 1) * (1 ⊗ₜ[ℂ] b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

omit [PartialOrder Q] [StarOrderedRing Q] [PartialOrder B] [StarOrderedRing B]
  [SeparableSpace Q] in
private lemma algebraic_legs_commute (a : Q) (b : B) :
    Commute (algebraicLeft a) (algebraicRight b) := by
  change (a ⊗ₜ[ℂ] 1) * (1 ⊗ₜ[ℂ] b) = (1 ⊗ₜ[ℂ] b) * (a ⊗ₜ[ℂ] 1)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

lemma quotient_dense_tensor_norm {E : Type*} [NonUnitalCStarAlgebra E]
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q)
    (f : Q ⊗[ℂ] B →⋆ₙₐ[ℂ] E) (hf : Function.Injective f) (hd : DenseRange f)
    (z : Q ⊗[ℂ] B) : ‖f z‖ = ‖minimalAlgebraicLinear z‖ := by
  let _ : CStarAlgebra E := denseUnitalCStarAlgebra f hd
  let _ : PartialOrder E := CStarAlgebra.spectralOrder E
  let _ : StarOrderedRing E := CStarAlgebra.spectralOrderedRing E
  let g := denseUnitalHom f hd
  let ι := universalGNSUnitalRepresentation E
  let π := ι.comp (g.comp (algebraicLeft (Q := Q) (B := B)))
  let η := ι.comp (g.comp (algebraicRight (Q := Q) (B := B)))
  have hc (a : Q) (b : B) : Commute (π a) (η b) :=
    (algebraic_legs_commute a b).map (ι.comp g)
  let θ := nuclearQuotientCommutingRepresentation ω hω hA q hq π η hc
  have he (a : Q) (b : B) : θ (minimalElementary a b) = ι (f (a ⊗ₜ[ℂ] b)) := by
    rw [nuclearQuotientCommutingRepresentation_elementary]
    change ι (g (algebraicLeft a)) * ι (g (algebraicRight b)) = _
    rw [← map_mul, ← map_mul, algebraic_legs]
    rfl
  have hθ : Function.Injective θ := by
    apply minimalTensor_injective_of_elementary_kernel θ
    intro a b hz
    rw [he] at hz
    have hz' : f (a ⊗ₜ[ℂ] b) = 0 :=
      (universalGNSUnitalRepresentation_injective E) (hz.trans (map_zero ι).symm)
    have hz'' : a ⊗ₜ[ℂ] b = 0 := hf (hz'.trans (map_zero f).symm)
    rw [← minimalAlgebraicLinear_tmul, hz'', map_zero]
  have heval : θ (minimalAlgebraicLinear z) = ι (f z) := by
    induction z using TensorProduct.inductionOn with
    | tmul a b => exact he a b
    | add x y hx hy => simp only [map_add, hx, hy]
  have hn := NonUnitalStarAlgHom.norm_map θ hθ (minimalAlgebraicLinear z)
  rw [heval] at hn
  have hi : ‖ι (f z)‖ = ‖f z‖ := by
    exact NonUnitalStarAlgHom.norm_map ι.toNonUnitalStarAlgHom
      (universalGNSUnitalRepresentation_injective E) (f z)
  exact hi.symm.trans hn

lemma quotient_norm_value
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q)
    (p : Pureness.CStarAlgebraNorm (Q ⊗[ℂ] B)) (z : Q ⊗[ℂ] B) :
    p.toAlgebraNorm z = ‖minimalAlgebraicLinear z‖ := by
  let _ : NonUnitalCStarAlgebra p.Completion := p.completionCStarAlgebra
  have hd : DenseRange p.completionMap := by
    let _ := p.normedRing
    let _ := p.normedAlgebra
    let _ := p.cstarRing
    exact UniformSpace.Completion.denseRange_coe
  have h := quotient_dense_tensor_norm ω hω hA q hq p.completionMap
    p.completionMap_injective hd z
  rwa [p.completionMap_norm] at h

omit [PartialOrder B] [StarOrderedRing B] in
 theorem nuclear_quotient_tensorNorm
    (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ atTop)
    (hA : Nuclear A) (q : A →⋆ₐ[ℂ] Q) (hq : Function.Surjective q) :
    Pureness.IsNuclear.{v,v} Q := by
  intro B _
  let _ : PartialOrder B := CStarAlgebra.spectralOrder B
  let _ : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  constructor
  intro p r
  have he (z : Q ⊗[ℂ] B) : p.toAlgebraNorm z = r.toAlgebraNorm z :=
    (quotient_norm_value ω hω hA q hq p z).trans (quotient_norm_value ω hω hA q hq r z).symm
  exact Pureness.CStarAlgebraNorm.eq_of_mutual_bound p r
    ⟨1, fun z => by rw [one_mul, he z]⟩
    ⟨1, fun z => by rw [one_mul, he z]⟩

end WeakPureInfiniteness

end

end OAI
