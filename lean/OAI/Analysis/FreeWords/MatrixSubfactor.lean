import Mathlib
import OAI.Analysis.FreeWords.MatrixUnitHom
import OAI.Analysis.FreeWords.ProjectionPartition
import OAI.Analysis.FreeWords.UnitaryExtension

namespace OAI

noncomputable section

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport KKFreeLiftFrontier

open scoped ComplexOrder

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance matrixSubfactorPartialOrder (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance matrixSubfactorPreorder (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance matrixSubfactorLE (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance matrixSubfactorStarOrderedRing (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

end

end KKProjectionSupport

namespace KKProjectionSupport

noncomputable section

open scoped BigOperators

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Ring A] [Algebra ℂ A]

variable [StarRing A] [StarModule ℂ A]

end

end KKProjectionSupport

namespace KKProjectionSupport

open KKTraceTransfer KKUltraTrace KKFactorSupport KKFreeLiftFrontier

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance matrixSubfactorSystemPartialOrder (M : VonNeumannAlgebra H) :
    PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance matrixSubfactorSystemPreorder (M : VonNeumannAlgebra H) :
    Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance matrixSubfactorSystemLE (M : VonNeumannAlgebra H) :
    LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance matrixSubfactorSystemStarOrderedRing (M : VonNeumannAlgebra H) :
    StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem partial_matrix_system {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M) (hF : IsFactor M)
    (p : ι → ConcreteAlgebra M) (hp : ∀ i, IsStarProjection (p i))
    (horth : ∀ i j, i≠j → p i*p j=0) (h1 : ∑ i, p i=1)
    (i₀ : ι) (hτ : ∀ i, τ.map (p i)=τ.map (p i₀)) :
    ∃ e : ι → ι → ConcreteAlgebra M,
      (∀ i j k l, e i j*e k l=if j=k then e i l else 0) ∧
      (∑ i, e i i)=1 ∧ (∀ i j, star (e i j)=e j i) ∧
      (∀ i j, τ.map (e i j)=if i=j then τ.map (p i₀) else 0) := by
  choose v hv using fun i => projection_equivalent_of_trace M τ hF (p i₀) (p i)
    (hp i₀) (hp i) (hτ i).symm
  have hvpartial (i : ι) : Partial (v i) := partial_of_initial_projection (by rw [(hv i).1]; exact hp i₀)
  have hvp (i : ι) : v i*p i₀=v i := by rw [← (hv i).1,← mul_assoc]; exact hvpartial i
  have hpv (i : ι) : p i*v i=v i := by rw [← (hv i).2]; exact hvpartial i
  have hsvp (i : ι) : star (v i)*p i=star (v i) := by
    simpa only [star_mul,(hp i).isSelfAdjoint.star_eq] using congrArg star (hpv i)
  have hprod (i j : ι) : star (v i)*v j=if i=j then p i₀ else 0 := by
    by_cases hij : i=j
    · subst j; simpa only [ite_true] using (hv i).1
    · rw [ite_eq_right hij]
      calc
        star (v i)*v j = (star (v i)*p i)*(p j*v j) := by rw [hsvp,hpv]
        _ = star (v i)*(p i*p j)*v j := by simp only [mul_assoc]
        _ = 0 := by rw [horth i j hij,mul_zero,zero_mul]
  let e (i j : ι) := v i*star (v j)
  refine ⟨e,?_,?_,?_,?_⟩
  · intro i j k l
    change (v i*star (v j))*(v k*star (v l))=if j=k then v i*star (v l) else 0
    calc
      (v i*star (v j))*(v k*star (v l)) = (v i*(star (v j)*v k))*star (v l) := by simp only [mul_assoc]
      _ = if j=k then v i*star (v l) else 0 := by rw [hprod]; split_ifs <;> simp only [hvp,mul_zero,zero_mul]
  · simpa only [e,funext (fun i => (hv i).2)] using h1
  · intro i j; simp only [e,star_mul,star_star]
  · intro i j
    change τ.map (v i*star (v j))=if i=j then τ.map (p i₀) else 0
    rw [τ.tracial,hprod]
    by_cases hij : i=j
    · subst j; simp
    · simp only [ite_eq_right hij,ite_eq_right (Ne.symm hij),map_zero]

theorem exists_matrix_subfactor (M : VonNeumannAlgebra H) (τ : FaithfulNormalTrace M)
    (hF : IsFactor M) (hD : IsDiffuse M) (n : ℕ) (hn : 0 < n) :
    ∃ ρ : Matrix (Fin n) (Fin n) ℂ →⋆ₐ[ℂ] ConcreteAlgebra M,
      Function.Injective ρ ∧ ∀ x, τ.map (ρ x) = (n : ℂ)⁻¹ * Matrix.trace x := by
  classical
  let i₀ : Fin n := ⟨0,hn⟩
  let : Nonempty (Fin n) := ⟨i₀⟩
  let : Nontrivial (ConcreteAlgebra M) := ⟨⟨0,1,fun h => by
    have ht := congrArg τ.map h
    rw [map_zero,τ.normalized] at ht
    exact zero_ne_one ht⟩⟩
  have hn0 : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have htr : τ.map (1 : ConcreteAlgebra M)=(n:ℂ)*(((n:ℝ)⁻¹:ℝ):ℂ) := by
    rw [τ.normalized,Complex.ofReal_inv,Complex.ofReal_natCast,mul_inv_cancel₀ hn0]
  obtain ⟨p,hp,hp1,horth,h1,hτp⟩ := projection_partition M τ hD n 1 (IsStarProjection.one _)
    (n:ℝ)⁻¹ (inv_nonneg.mpr (Nat.cast_nonneg n)) htr
  obtain ⟨e,hm,he1,hes,het⟩ := partial_matrix_system M τ hF p hp horth h1 i₀
    (fun i => (hτp i).trans (hτp i₀).symm)
  let ρ := matrixUnitHom e hm he1 hes
  refine ⟨ρ,ρ.toAlgHom.toRingHom.injective,?_⟩
  intro x
  change τ.map (∑ i, ∑ j, x i j • e i j)=(n:ℂ)⁻¹*Matrix.trace x
  simp only [map_sum,map_smul,het,smul_eq_mul,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,
    ite_true,smul_eq_mul,hτp,Complex.ofReal_inv,Complex.ofReal_natCast]
  rw [Matrix.trace,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

end

end KKProjectionSupport
end

end OAI
