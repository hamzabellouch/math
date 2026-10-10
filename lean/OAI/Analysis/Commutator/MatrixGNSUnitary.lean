import Mathlib
import OAI.Analysis.Commutator.GNSVectorUnitary
import OAI.Analysis.Commutator.MatrixVectorTrace

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

local instance matrixGNSUnitaryDecidableEq : DecidableEq ι := Classical.decEq ι

variable (τ : A →ₚ[ℂ] ℂ)

omit [Fintype ι] in
lemma dense_algebraArray : DenseRange (algebraArray (ι:=ι) τ) := by
  have hd₁ : DenseRange (fun a : ι → A =>
      WithLp.toLp 2 (fun i => TracialGNS.algebraVector τ (a i))) := by
    let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => τ.GNS)).symm
    exact e.surjective.denseRange.comp
      (DenseRange.piMap (fun _ : ι => TracialGNS.algebraVector_dense τ)) e.continuous
  have hd₂ : DenseRange (fun a : ι → ι → A =>
      WithLp.toLp 2 (fun i => WithLp.toLp 2
        (fun j => TracialGNS.algebraVector τ (a i j)))) := by
    let e := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => PiLp 2 (fun _ : ι => τ.GNS))).symm
    exact e.surjective.denseRange.comp (DenseRange.piMap (fun _ : ι => hd₁)) e.continuous
  apply hd₂.mono
  rintro y ⟨a,rfl⟩
  exact ⟨CStarMatrix.ofMatrix a,rfl⟩

lemma dense_vacuumOrbit [Nonempty ι] :
    DenseRange (fun X : CStarMatrix ι ι A => representation (ι:=ι) τ X (vacuum (ι:=ι) τ)) := by
  have hs : Function.Surjective (fun v : ArraySpace (ι:=ι) τ => scale ι • v) := by
    intro v
    exact ⟨(scale ι)⁻¹ • v,by simp only [smul_smul,mul_inv_cancel₀ (scale_ne_zero (ι:=ι)),one_smul]⟩
  have hd := hs.denseRange.comp (dense_algebraArray (ι:=ι) τ)
    (continuous_const_smul (scale ι))
  apply hd.mono
  rintro y ⟨X,rfl⟩
  exact ⟨X,representation_vacuum τ X⟩

noncomputable def unitary [Nonempty ι] :=
  VectorGNS.equivalence (A:=CStarMatrix ι ι A) (H:=ArraySpace (ι:=ι) τ)
    (trace (ι:=ι) τ) (representation (ι:=ι) τ) (vacuum (ι:=ι) τ)
    (trace_vector (ι:=ι) τ) (dense_vacuumOrbit (ι:=ι) τ)

lemma unitary_algebraVector [Nonempty ι] (X : CStarMatrix ι ι A) :
    unitary (ι:=ι) τ (TracialGNS.algebraVector (trace (ι:=ι) τ) X)=scale ι • algebraArray τ X := by
  rw [unitary,VectorGNS.equivalence_algebraVector,representation_vacuum]

lemma unitary_intertwines [Nonempty ι] (X : CStarMatrix ι ι A)
    (v : (trace (ι:=ι) τ).GNS) :
    unitary (ι:=ι) τ ((trace (ι:=ι) τ).gnsStarAlgHom X v)=
      representation τ X (unitary (ι:=ι) τ v) :=
  VectorGNS.equivalence_intertwines _ _ _ _ _ _ _

lemma unitary_conjugates [Nonempty ι] (X : CStarMatrix ι ι A) :
    (unitary (ι:=ι) τ).conjStarAlgEquiv ((trace (ι:=ι) τ).gnsStarAlgHom X)=representation τ X :=
  VectorGNS.equivalence_conjugates _ _ _ _ _ _

end Kadison.MatrixGNS

end

end
end

end OAI
