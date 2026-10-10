import Mathlib

namespace OAI

noncomputable section


namespace KaplanskyConsequences
open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
namespace Regular
variable {ι : Type*} {H : Type*} [NormedAddCommGroup H]

abbrev HilbertSum (ι H : Type*) [NormedAddCommGroup H] := lp (fun _ : ι => H) 2

lemma reindex_mem (e : ι ≃ ι) (x : HilbertSum ι H) :
    Memℓp (fun i => x (e i)) 2 := by
  apply memℓp_gen
  exact e.summable_iff.2 ((memℓp_gen_iff (by norm_num)).1 (lp.memℓp x))

variable [InnerProductSpace ℂ H]

def reindex (e : ι ≃ ι) : HilbertSum ι H ≃ₗᵢ[ℂ] HilbertSum ι H where
  toFun x := ⟨fun i => x (e.symm i), reindex_mem e.symm x⟩
  invFun x := ⟨fun i => x (e i), reindex_mem e x⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; rfl
  map_smul' r x := by ext; rfl
  norm_map' x := by
    rw [lp.norm_eq_tsum_rpow (by norm_num),lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.symm.tsum_eq (fun i => ‖x i‖ ^ (2 : ℝ≥0∞).toReal)

@[simp] lemma reindex_apply (e : ι ≃ ι) (x : HilbertSum ι H) (i : ι) :
    reindex e x i = x (e.symm i) := rfl

variable {G : Type*} [Group G]

def left (g : G) : HilbertSum G H →L[ℂ] HilbertSum G H :=
  (reindex (Equiv.mulLeft g)).toLinearIsometry.toContinuousLinearMap

@[simp] lemma left_apply (g h : G) (x : HilbertSum G H) : left g x h = x (g⁻¹*h) := rfl

lemma left_one : left (H := H) (1 : G) = 1 := by ext x h; simp
lemma left_mul (g h : G) : left (H := H) (g*h) = left g * left h := by
  ext x k
  simp [mul_assoc]

variable [CompleteSpace H]

lemma left_star (g : G) : star (left (H := H) g) = left g⁻¹ := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  change inner ℂ (left g⁻¹ x) y = inner ℂ x (left g y)
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  simpa [left_apply,mul_assoc] using
    (Equiv.mulLeft g).tsum_eq (fun i => inner ℂ (x i) (y (g⁻¹*i)))

def Algebra (G : Type*) [Group G] : StarSubalgebra ℂ (HilbertSum G ℂ →L[ℂ] HilbertSum G ℂ) :=
  (StarAlgebra.adjoin ℂ (Set.range (left (H := ℂ) (G := G)))).topologicalClosure

instance : IsClosed (Algebra G : Set (HilbertSum G ℂ →L[ℂ] HilbertSum G ℂ)) :=
  StarSubalgebra.isClosed_topologicalClosure _

instance : CStarAlgebra (Algebra G) := inferInstance

def generator (g : G) : Algebra G :=
  ⟨left g,StarSubalgebra.le_topologicalClosure _
    (StarAlgebra.subset_adjoin ℂ _ ⟨g,rfl⟩)⟩

end Regular
end KaplanskyConsequences


namespace KaplanskyConsequences.Regular
abbrev F2 := FreeGroup (Fin 2)


open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
variable {G H : Type*} [Group G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

def diagonal (T : H →L[ℂ] H) : HilbertSum G H →L[ℂ] HilbertSum G H :=
  lp.mapCLM 2 (fun _ => T) (norm_nonneg T) (fun _ => le_rfl)

end KaplanskyConsequences.Regular


namespace Kaplansky

section

section
open scoped ComplexOrder IsMulCommutative


variable {A : Type*} [CStarAlgebra A]

structure OneQuasitrace (A : Type*) [CStarAlgebra A] where
  toFun : A → ℂ
  square_nonneg : ∀ x, 0  ≤  toFun (star x * x)
  square_swap : ∀ x, toFun (star x * x) = toFun (x * star x)
  real_imag : ∀ h k, IsSelfAdjoint h → IsSelfAdjoint k →
    toFun (h + Complex.I • k) = toFun h + Complex.I * toFun k
  abelian_linear : ∀ S : NonUnitalStarSubalgebra ℂ A,
    IsClosed (S : Set A) → (∀ x y : S, x * y = y * x) →
    ∃ f : S →ₗ[ℂ] ℂ, ∀ x : S, f x = toFun x

instance : CoeFun (OneQuasitrace A) (fun _ => A → ℂ) := ⟨OneQuasitrace.toFun⟩

def OneQuasitrace.Normalized (τ : OneQuasitrace A) : Prop := τ 1 = 1

end


open scoped ComplexOrder CStarAlgebra
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

def ProperlyInfinite (A : Type*) [CStarAlgebra A] : Prop :=
  ∃ s t : A, star s*s = 1 ∧ star t*t = 1 ∧ star s*t = 0

end


attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

def upperLeft (a : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  CStarMatrix.ofMatrix fun i j => if i = 0 ∧ j = 0 then a else 0

def OneQuasitrace.IsTwo (τ : OneQuasitrace A) : Prop :=
  ∃ σ : OneQuasitrace (CStarMatrix (Fin 2) (Fin 2) A), ∀ a, σ (upperLeft a) = τ a

end Kaplansky


namespace KaplanskyConsequences

section
open scoped ComplexOrder
open Metric Topology
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

structure ClosedStarIdeal (A : Type*) [CStarAlgebra A] extends NonUnitalStarSubalgebra ℂ A where
  mul_mem_left : ∀ (a b : A), b ∈ toNonUnitalStarSubalgebra → a * b ∈ toNonUnitalStarSubalgebra
  mul_mem_right : ∀ (a b : A), a ∈ toNonUnitalStarSubalgebra → a * b ∈ toNonUnitalStarSubalgebra
  closed : IsClosed (toNonUnitalStarSubalgebra : Set A)

end


open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

def StablyFinite (A : Type*) [CStarAlgebra A] : Prop :=
  ∀ n : ℕ, 0 < n → ∀ v : CStarMatrix (Fin n) (Fin n) A,
    star v * v = 1 → v * star v = 1

structure TracialState (A : Type*) [CStarAlgebra A] where
  functional : A →ₚ[ℂ] ℂ
  normalized : functional 1 = 1
  tracial : ∀ a b, functional (a * b) = functional (b * a)

def TraceFreeStablyFinite : Prop :=
  ∃ (A : Type) (inst : CStarAlgebra A),
    letI := inst
    Nontrivial A ∧ TopologicalSpace.SeparableSpace A ∧ StablyFinite A ∧
      IsEmpty (TracialState A)

end KaplanskyConsequences

namespace KaplanskyConsequences.Regular
open scoped ComplexOrder InnerProductSpace BigOperators ENNReal
attribute [local instance] Classical.propDecidable
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
variable {G H : Type*} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def tensorAlgebra (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    StarSubalgebra ℂ (HilbertSum G H →L[ℂ] HilbertSum G H) :=
  (StarAlgebra.adjoin ℂ (Set.range (fun a => diagonal (G:=G) (ρ a)) ∪ Set.range (left (G:=G) (H:=H)))).topologicalClosure

instance (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) :
    IsClosed (tensorAlgebra (G:=G) ρ : Set (HilbertSum G H →L[ℂ] HilbertSum G H)) :=
  StarSubalgebra.isClosed_topologicalClosure _
instance (ρ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) : CStarAlgebra (tensorAlgebra (G:=G) ρ) := inferInstance

end KaplanskyConsequences.Regular

namespace KaplanskyConsequences

section

section
open Kaplansky Regular

def ReducedQuasitraceLoss : Prop :=
  ∃ (B : Type) (instB : CStarAlgebra B),
    letI := instB
    Nontrivial B ∧ TopologicalSpace.SeparableSpace B ∧
      (∃ τ : OneQuasitrace B, τ.Normalized ∧ τ.IsTwo) ∧
      ∃ (H : Type) (instH : NormedAddCommGroup H) (innerH : InnerProductSpace ℂ H),
        letI := instH
        letI := innerH
        ∃ (completeH : CompleteSpace H),
          letI := completeH
          ∃ ρ : B →⋆ₐ[ℂ] (H →L[ℂ] H), Function.Injective ρ ∧
            ProperlyInfinite (tensorAlgebra (G:=F2) ρ) ∧
            ¬ ∃ τ : OneQuasitrace (tensorAlgebra (G:=F2) ρ), τ.Normalized ∧ τ.IsTwo
end

open Kaplansky Regular

def CStarSimple (A : Type*) [CStarAlgebra A] : Prop :=
  ∀ I : ClosedStarIdeal A,
    (∀ a : A, a ∈ I.toNonUnitalStarSubalgebra → a = 0) ∨
    (∀ a : A, a ∈ I.toNonUnitalStarSubalgebra)

def SimpleStableTensorCounterexample : Prop :=
  CStarSimple (Algebra F2) ∧ StablyFinite (Algebra F2) ∧
  ∃ (M : Type) (instM : CStarAlgebra M),
    letI := instM
    Nontrivial M ∧ CStarSimple M ∧ StablyFinite M ∧
      ∃ (H : Type) (instH : NormedAddCommGroup H) (innerH : InnerProductSpace ℂ H),
        letI := instH
        letI := innerH
        ∃ (completeH : CompleteSpace H),
          letI := completeH
          ∃ ρ : M →⋆ₐ[ℂ] (H →L[ℂ] H), Function.Injective ρ ∧
            ProperlyInfinite (tensorAlgebra (G:=F2) ρ)
end


def StableFinitenessBundle : Prop :=
  SimpleStableTensorCounterexample ∧ ReducedQuasitraceLoss ∧ TraceFreeStablyFinite

theorem stable_finiteness_bundle : StableFinitenessBundle := by
  sorry

end KaplanskyConsequences

end

end OAI
