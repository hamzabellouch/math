import Mathlib
import OAI.Analysis.Commutator.OperatorAmplification
import OAI.Analysis.Commutator.TracialConjugation
import OAI.Analysis.Commutator.TracialSequenceTrace

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

open ContinuousLinearMap

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Fintype ι]

local instance matrixVectorTraceDecidableEq : DecidableEq ι := Classical.decEq ι

variable (τ : A →ₚ[ℂ] ℂ)

abbrev ArraySpace := PiLp 2 (fun _ : ι => PiLp 2 (fun _ : ι => τ.GNS))

def representation : CStarMatrix ι ι A →⋆ₐ[ℂ] (ArraySpace (ι:=ι) τ →L[ℂ] ArraySpace (ι:=ι) τ) :=
  CyclicColumns.matrixRepresentation ((OperatorAmplification.diagonal ι).comp τ.gnsStarAlgHom)

@[simp] lemma representation_apply (X : CStarMatrix ι ι A) (v : ArraySpace (ι:=ι) τ) (i j : ι) :
    representation τ X v i j=∑ k, τ.gnsStarAlgHom (X i k) (v k j) := by
  simp [representation,CyclicColumns.matrixRepresentation,CyclicColumns.matrixAction_apply]

def algebraArray (X : CStarMatrix ι ι A) : ArraySpace (ι:=ι) τ :=
  WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun j => TracialGNS.algebraVector τ (X i j)))

omit [Fintype ι] in
@[simp] lemma algebraArray_apply (X : CStarMatrix ι ι A) (i j : ι) :
    algebraArray τ X i j=TracialGNS.algebraVector τ (X i j) := rfl

lemma representation_oneArray (X : CStarMatrix ι ι A) :
    representation τ X (algebraArray τ 1)=algebraArray τ X := by
  ext i j
  simp only [representation_apply,algebraArray_apply,CStarMatrix.one_apply]
  classical
  simp [apply_ite,TracialGNS.algebraVector,map_zero]

def scale (ι : Type*) [Fintype ι] : ℂ := ((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ)

lemma scale_ne_zero [Nonempty ι] : scale ι≠0 := by
  simp only [scale,ne_eq,Complex.ofReal_eq_zero,inv_eq_zero]
  exact Real.sqrt_ne_zero'.mpr (by exact_mod_cast (Fintype.card_pos (α:=ι)))

def vacuum : ArraySpace (ι:=ι) τ := scale ι • algebraArray τ 1

lemma representation_vacuum (X : CStarMatrix ι ι A) :
    representation τ X (vacuum (ι:=ι) τ)=scale ι • algebraArray τ X := by
  rw [vacuum,map_smul,representation_oneArray]

def trace : CStarMatrix ι ι A →ₚ[ℂ] ℂ where
  toLinearMap := (VectorFunctional.functional (vacuum (ι:=ι) τ)).toLinearMap.comp
    (representation τ).toLinearMap
  monotone' := by
    have hmono : Monotone (representation (ι:=ι) τ) := by
      intro first second hle
      exact (NonUnitalStarRingHom.ofClass (representation τ)).map_le_map_of_map_star hle
    exact (VectorFunctional.functional (vacuum (ι:=ι) τ)).monotone.comp hmono

lemma trace_vector (X : CStarMatrix ι ι A) :
    trace (ι:=ι) τ X=inner ℂ (vacuum τ) (representation τ X (vacuum τ)) := rfl

lemma diagonal_inner (X : CStarMatrix ι ι A) :
    inner ℂ (algebraArray τ (1:CStarMatrix ι ι A)) (algebraArray τ X)=∑ i,τ (X i i) := by
  simp only [PiLp.inner_apply,algebraArray_apply,TracialGNS.inner_algebraVector,CStarMatrix.one_apply]
  simp [apply_ite]

lemma trace_apply (X : CStarMatrix ι ι A) :
    trace (ι:=ι) τ X=(Fintype.card ι : ℂ)⁻¹ * ∑ i,τ (X i i) := by
  rw [trace_vector,representation_vacuum,vacuum,inner_smul_left,inner_smul_right,diagonal_inner]
  have hs : starRingEnd ℂ (scale ι)*scale ι=(Fintype.card ι : ℂ)⁻¹ := by
    change star (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ) *
      (((Real.sqrt (Fintype.card ι : ℝ))⁻¹ : ℝ) : ℂ)=_
    rw [Complex.star_def,Complex.conj_ofReal,←Complex.ofReal_mul,←mul_inv_rev,
      Real.mul_self_sqrt (Nat.cast_nonneg _),Complex.ofReal_inv,Complex.ofReal_natCast]
  rw [←mul_assoc,hs]

lemma trace_one [Nonempty ι] (h1 : τ 1=1) : trace (ι:=ι) τ 1=1 := by
  rw [trace_apply]
  simp only [CStarMatrix.one_apply,ite_true,h1,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)

lemma trace_mul (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (X Y : CStarMatrix ι ι A) :
    trace (ι:=ι) τ (X*Y)=trace (ι:=ι) τ (Y*X) := by
  simp only [trace_apply,CStarMatrix.mul_apply,map_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact hτ _ _

end Kadison.MatrixGNS

end

end
end

end OAI
