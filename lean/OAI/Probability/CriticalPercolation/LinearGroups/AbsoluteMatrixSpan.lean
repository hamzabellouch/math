import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.FieldSpanTransfer
import OAI.Probability.CriticalPercolation.LinearGroups.FullSpanAlternative

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {K L T G n : Type*} [Field K] [Field L] [Field T] [Group G]
variable [Fintype n] [DecidableEq n]

def matrixRepresentation (ρ : G →* GL n K) : G →* ((n → K) ≃ₗ[K] (n → K)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)

@[simp] lemma matrixRepresentation_apply (ρ : G →* GL n K) (g : G) (v : n → K) :
    matrixRepresentation ρ g v=(ρ g).val.mulVec v := rfl

def matrixFlatten : Matrix n n K ≃ₗ[K] (n × n → K) where
  toFun M p := M p.1 p.2
  invFun f i j := f (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def FullMatrixSpan (ρ : G →* GL n K) : Prop :=
  Submodule.span K (Set.range (fun g (p : n×n) => ρ g p.1 p.2))=⊤

def StrongFullMatrixSpan (ρ : G →* GL n K) : Prop :=
  ∀ H : Subgroup G, H.FiniteIndex → FullMatrixSpan (ρ.comp H.subtype)

lemma span_equiv_top {K V W J : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (e : V ≃ₗ[K] W) (v : J → V)
    (hv : Submodule.span K (Set.range v)=⊤) :
    Submodule.span K (Set.range (fun j => e (v j)))=⊤ := by
  rw [show Set.range (fun j => e (v j))=e '' Set.range v from (Set.range_comp _ _)]
  change Submodule.span K (e.toLinearMap '' Set.range v)=⊤
  rw [←Submodule.map_span e.toLinearMap,hv,Submodule.map_top]
  exact e.range

lemma FullMatrixSpan.fullSpan (ρ : G →* GL n K) (hρ : FullMatrixSpan ρ) :
    FullSpan (matrixRepresentation ρ) := by
  let e := (matrixFlatten (K:=K) (n:=n)).symm.trans Matrix.toLin'
  exact span_equiv_top e (fun g (p:n×n) => ρ g p.1 p.2) hρ

lemma StrongFullMatrixSpan.strongFullSpan (ρ : G →* GL n K) (hρ : StrongFullMatrixSpan ρ) :
    StrongFullSpan (matrixRepresentation ρ) := by
  intro H hH
  exact FullMatrixSpan.fullSpan (ρ.comp H.subtype) (hρ H hH)

lemma FullMatrixSpan.transfer (f : K →+* T) (e : L →+* T)
    (ρ : G →* GL n K) (τ : G →* GL n L)
    (hm : ∀ g i j, f (ρ g i j)=e (τ g i j)) (hρ : FullMatrixSpan ρ) : FullMatrixSpan τ :=
  pi_span_transfer f e (fun g (p:n×n) => ρ g p.1 p.2)
    (fun g (p:n×n) => τ g p.1 p.2) (fun g p => hm g p.1 p.2) hρ

lemma StrongFullMatrixSpan.transfer (f : K →+* T) (e : L →+* T)
    (ρ : G →* GL n K) (τ : G →* GL n L)
    (hm : ∀ g i j, f (ρ g i j)=e (τ g i j)) (hρ : StrongFullMatrixSpan ρ) :
    StrongFullMatrixSpan τ := by
  intro H hH
  exact FullMatrixSpan.transfer f e (ρ.comp H.subtype) (τ.comp H.subtype)
    (fun g i j => hm g i j) (hρ H hH)

end CriticalPercolation.LinearGrowth
end
end

end OAI
