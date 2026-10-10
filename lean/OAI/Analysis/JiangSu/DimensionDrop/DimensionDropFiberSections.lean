import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.DimensionDropTensorCoefficients

namespace OAI

section

noncomputable section
namespace JiangSuConstruction
open Pureness ConcreteMatrixUnits
open scoped TensorProduct CStarAlgebra ComplexOrder Kronecker

variable {p q : ℕ} {B : Type*} [CStarAlgebra B]
variable {ι : Type*} [Fintype ι]

lemma endpoints_ne : leftEndpoint≠rightEndpoint := by
  intro h
  have := congrArg Subtype.val h
  norm_num [leftEndpoint,rightEndpoint] at this

def fiberSection (t : Interval) (g : C(Interval,ℝ))
    (h0 : t≠leftEndpoint → g leftEndpoint=0)
    (h1 : t≠rightEndpoint → g rightEndpoint=0) :
    DimensionDrop p q →ₗ[ℂ] DimensionDrop p q where
  toFun f := ⟨scalarMatrix g (f.val t),by
    constructor
    · change scalarMatrix g (f.val t) leftEndpoint∈(leftAmplification p q).range
      rw [scalarMatrix_apply_complex]
      by_cases ht : t=leftEndpoint
      · rw [ht]
        exact (leftAmplification p q).range.smul_mem f.property.1 _
      · simp [h0 ht]
    · change scalarMatrix g (f.val t) rightEndpoint∈(rightAmplification p q).range
      rw [scalarMatrix_apply_complex]
      by_cases ht : t=rightEndpoint
      · rw [ht]
        exact (rightAmplification p q).range.smul_mem f.property.2 _
      · simp [h1 ht]⟩
  map_add' f h := by
    apply Subtype.ext; apply ContinuousMap.ext; intro x
    change g x • (f.val t+h.val t)=g x • f.val t+g x • h.val t
    rw [smul_add]
  map_smul' z f := by
    apply Subtype.ext; apply ContinuousMap.ext; intro x
    change g x • (z • f.val t)=z • (g x • f.val t)
    rw [smul_comm]

def fiberBound (p q : ℕ) : ℝ := (p*q:ℝ)^2+(p:ℝ)^2+(q:ℝ)^2
lemma fiberBound_nonneg (p q : ℕ) : 0≤fiberBound p q := by unfold fiberBound; positivity

lemma fiberSection_tensor_bound [NeZero p] [NeZero q]
    (r s : CStarAlgebraNorm (DimensionDrop p q ⊗[ℂ] B))
    (f : ι → DimensionDrop p q) (b : ι → B) (t : Interval)
    (g : C(Interval,ℝ)) (h0 h1) (hg : ∀ x,|g x|≤1) :
    s.toAlgebraNorm (∑ l,fiberSection t g h0 h1 (f l) ⊗ₜ[ℂ] b l) ≤
      fiberBound p q*r.toAlgebraNorm (∑ l,f l ⊗ₜ[ℂ] b l) := by
  classical
  let z := ∑ l,f l ⊗ₜ[ℂ] b l
  have hC : 0≤r.toAlgebraNorm z := apply_nonneg _ _
  by_cases ht0 : t=leftEndpoint
  · subst t
    have hex (l : ι) : ∃ x : Mat p,(leftAmplification p q) x=(f l).val leftEndpoint :=
      (f l).property.1
    choose x hx using hex
    have hh0 : g leftEndpoint≠0 → ∀ y : Mat p,
        (leftAmplification p q) y∈(leftAmplification p q).range := fun _ y => ⟨y,rfl⟩
    have hh1 : g rightEndpoint≠0 → ∀ y : Mat p,
        (leftAmplification p q) y∈(rightAmplification p q).range := by
      intro hn
      exact False.elim (hn (h1 endpoints_ne))
    have he (l : ι) : fiberSection leftEndpoint g h0 h1 (f l)=
        cutoffAmplification g (leftAmplification p q) hh0 hh1 (x l) := by
      apply Subtype.ext; apply ContinuousMap.ext; intro u
      change g u • (f l).val leftEndpoint=g u • (leftAmplification p q) (x l)
      rw [hx]
    have hc (i j : Fin p) : ‖∑ l,x l i j • b l‖≤r.toAlgebraNorm z := by
      have he' (l : ι) : x l i j=(f l).val leftEndpoint (i,0) (j,0) := by
        rw [←hx]
        change x l i j = x l i j * (1 : Matrix (Fin q) (Fin q) ℂ) 0 0
        simp
      simpa only [he'] using tensor_coefficient_le r f b leftEndpoint (i,0) (j,0)
    simp only [he]
    apply (tensor_cutoff_bound s g (leftAmplification p q) hh0 hh1 hg x b hC hc).trans
    simp only [Fintype.card_fin]
    apply mul_le_mul_of_nonneg_right _ hC
    unfold fiberBound
    nlinarith [sq_nonneg (p*q:ℝ),sq_nonneg (q:ℝ)]
  by_cases ht1 : t=rightEndpoint
  · subst t
    have hex (l : ι) : ∃ x : Mat q,(rightAmplification p q) x=(f l).val rightEndpoint :=
      (f l).property.2
    choose x hx using hex
    have hh0 : g leftEndpoint≠0 → ∀ y : Mat q,
        (rightAmplification p q) y∈(leftAmplification p q).range := by
      intro hn
      exact False.elim (hn (h0 endpoints_ne.symm))
    have hh1 : g rightEndpoint≠0 → ∀ y : Mat q,
        (rightAmplification p q) y∈(rightAmplification p q).range := fun _ y => ⟨y,rfl⟩
    have he (l : ι) : fiberSection rightEndpoint g h0 h1 (f l)=
        cutoffAmplification g (rightAmplification p q) hh0 hh1 (x l) := by
      apply Subtype.ext; apply ContinuousMap.ext; intro u
      change g u • (f l).val rightEndpoint=g u • (rightAmplification p q) (x l)
      rw [hx]
    have hc (i j : Fin q) : ‖∑ l,x l i j • b l‖≤r.toAlgebraNorm z := by
      have he' (l : ι) : x l i j=(f l).val rightEndpoint (0,i) (0,j) := by
        rw [←hx]
        change x l i j = (1 : Matrix (Fin p) (Fin p) ℂ) 0 0 * x l i j
        simp
      simpa only [he'] using tensor_coefficient_le r f b rightEndpoint (0,i) (0,j)
    simp only [he]
    apply (tensor_cutoff_bound s g (rightAmplification p q) hh0 hh1 hg x b hC hc).trans
    simp only [Fintype.card_fin]
    apply mul_le_mul_of_nonneg_right _ hC
    unfold fiberBound
    nlinarith [sq_nonneg (p*q:ℝ),sq_nonneg (p:ℝ)]
  · have hh0 : g leftEndpoint≠0 → ∀ y : TensorMat p q,
        y∈(leftAmplification p q).range := by
      intro hn; exact False.elim (hn (h0 ht0))
    have hh1 : g rightEndpoint≠0 → ∀ y : TensorMat p q,
        y∈(rightAmplification p q).range := by
      intro hn; exact False.elim (hn (h1 ht1))
    have he (l : ι) : fiberSection t g h0 h1 (f l)=
        cutoffAmplification g (StarAlgHom.id ℂ _) hh0 hh1 ((f l).val t) := rfl
    simp only [he]
    apply (tensor_cutoff_bound s g (StarAlgHom.id ℂ _) hh0 hh1 hg (fun l => (f l).val t)
      b hC (fun i j => tensor_coefficient_le r f b t i j)).trans
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    apply mul_le_mul_of_nonneg_right _ hC
    unfold fiberBound
    nlinarith [sq_nonneg (p:ℝ),sq_nonneg (q:ℝ)]

end JiangSuConstruction

end
end

end OAI
