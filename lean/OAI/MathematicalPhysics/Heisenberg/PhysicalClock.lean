import OAI.MathematicalPhysics.Heisenberg.SpectralTransfer

namespace OAI

section
noncomputable section
open scoped Classical BigOperators Matrix Matrix.Norms.Operator
namespace Heisenberg.SlotTensor
open TensorMatrix SpinSlots
variable {X : Type} [Fintype X] [DecidableEq X]

abbrev SiteEdges (R : X → X → Prop) := {e : X×X // R e.1 e.2}
abbrev ClockEdges (R : X → X → Prop) (ℓ : ℕ) := {e : (X×Fin ℓ)×(X×Fin ℓ) // R e.1.1 e.2.1}

def clockEdgeEquiv (R : X → X → Prop) (ℓ : ℕ) : ClockEdges R ℓ ≃ SiteEdges R × (Fin ℓ×Fin ℓ) where
  toFun e:=⟨⟨(e.val.1.1,e.val.2.1),e.property⟩,(e.val.1.2,e.val.2.2)⟩
  invFun e:=⟨((e.1.val.1,e.2.1),(e.1.val.2,e.2.2)),e.1.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

def clockGenerator (R : X → X → Prop) (ℓ : ℕ) : Matrix ((X×Fin ℓ) → Bool) ((X×Fin ℓ) → Bool) ℝ :=
  ∑ e : ClockEdges R ℓ,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap e.val.1 e.val.2)-1)

def spinGenerator (R : X → X → Prop) (ℓ : ℕ) : Matrix (X → Level ℓ) (X → Level ℓ) ℝ :=
  ∑ e : SiteEdges R,(spinBond ℓ e.val.1 e.val.2-((ℓ:ℝ)^2/4) • 1)

lemma sum_clock_pair (ℓ : ℕ) (x y : X) :
    (∑ a : Fin ℓ,∑ b : Fin ℓ,(1/2:ℝ) • (SlotColor.matrix (Equiv.swap (x,a) (y,b))-1))=
      slotBond ℓ x y-((ℓ:ℝ)^2/4) • 1 := by
  simp only [smul_sub,Finset.sum_sub_distrib,←Finset.smul_sum,slotBond]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
  rw [←Nat.cast_smul_eq_nsmul ℝ,←Nat.cast_smul_eq_nsmul ℝ,smul_smul,smul_smul]
  module

lemma generator_intertwines (R : X → X → Prop) (hR : ∀ x y,R x y → x≠y) (ℓ : ℕ) :
    Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) (clockGenerator R ℓ)*tensor (fun _ : X=>basis ℓ)=
      tensor (fun _ : X=>basis ℓ)*spinGenerator R ℓ := by
  let r:=Matrix.reindexAlgEquiv ℝ ℝ (configEquiv (X:=X) ℓ)
  have hr (A : Matrix ((X×Fin ℓ) → Bool) ((X×Fin ℓ) → Bool) ℝ) :
      r A=Matrix.reindex (configEquiv ℓ) (configEquiv ℓ) A:=rfl
  rw [←hr]
  have he : clockGenerator R ℓ=∑ e : SiteEdges R,∑ a : Fin ℓ,∑ b : Fin ℓ,
      (1/2:ℝ) • (SlotColor.matrix (Equiv.swap (e.val.1,a) (e.val.2,b))-1) := by
    rw [clockGenerator,←(clockEdgeEquiv R ℓ).symm.sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type]
    rfl
  rw [he]
  simp only [sum_clock_pair,map_sum,map_sub,map_smul,map_one,Matrix.sum_mul,Matrix.sub_mul,
    Matrix.smul_mul,Matrix.one_mul,spinGenerator,Matrix.mul_sum,Matrix.mul_sub,
    Matrix.mul_smul,Matrix.mul_one]
  apply Finset.sum_congr rfl
  intro e _
  rw [hr,bond_intertwines ℓ (hR _ _ e.property)]

end Heisenberg.SlotTensor
end
end

end OAI
