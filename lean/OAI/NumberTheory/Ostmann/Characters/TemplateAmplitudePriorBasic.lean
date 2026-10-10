import OAI.NumberTheory.Ostmann.Characters.TemplateConstituentInput
import OAI.NumberTheory.Ostmann.Characters.WordSelection

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open Construction

def assemblePriorSample {A H Y I Ω : Type*} (e : A ⊕ (H ⊕ Y) ≃ I)
    (w : A → Ω) (h : H → Ω) (y : Y → Ω) : I → Ω :=
  fun i => Sum.elim w (Sum.elim h y) (e.symm i)

def priorSampleEquiv {A H Y I Ω : Type*} (e : A ⊕ (H ⊕ Y) ≃ I) :
    (Y → Ω) × ((A → Ω) × (H → Ω)) ≃ (I → Ω) where
  toFun x := assemblePriorSample e x.2.1 x.2.2 x.1
  invFun f := (fun y => f (e (.inr (.inr y))),
    (fun a => f (e (.inl a)),fun h => f (e (.inr (.inl h)))))
  left_inv x := by
    rcases x with ⟨y,w,h⟩
    simp only [assemblePriorSample,Equiv.symm_apply_apply,Sum.elim_inl,Sum.elim_inr]
  right_inv f := by
    funext i
    obtain ⟨a,rfl⟩ := e.surjective i
    rcases a with a | (h | y) <;> simp [assemblePriorSample]

theorem productPrior_assembled_mass {A H Y I Ω : Type*}
    [Fintype A] [Fintype H] [Fintype Y] [Fintype I] [Fintype Ω]
    [DecidableEq A] [DecidableEq H] [DecidableEq Y] [DecidableEq I]
    (e : A ⊕ (H ⊕ Y) ≃ I) (μ : I → FinitePrior Ω)
    (w : A → Ω) (h : H → Ω) (y : Y → Ω) :
    (productPrior μ).mass (assemblePriorSample e w h y) =
      (productPrior (fun i : Y => μ (e (.inr (.inr i))))).mass y *
      (productPrior (fun i : A => μ (e (.inl i)))).mass w *
      (productPrior (fun i : H => μ (e (.inr (.inl i))))).mass h := by
  change (∏ i, (μ i).mass (assemblePriorSample e w h y i)) = _
  rw [← e.prod_comp]
  simp only [assemblePriorSample,Equiv.symm_apply_apply,Fintype.prod_sum_type,
    Sum.elim_inl,Sum.elim_inr,productPrior]
  ring

theorem productPrior_split_cmean {A H Y I Ω : Type*}
    [Fintype A] [Fintype H] [Fintype Y] [Fintype I] [Fintype Ω]
    [DecidableEq A] [DecidableEq H] [DecidableEq Y] [DecidableEq I]
    (e : A ⊕ (H ⊕ Y) ≃ I) (μ : I → FinitePrior Ω) (F : (I → Ω) → ℂ) :
    (productPrior μ).cmean F =
      (productPrior (fun i : Y => μ (e (.inr (.inr i))))).cmean (fun y =>
        (productPrior (fun i : A => μ (e (.inl i)))).cmean (fun w =>
          (productPrior (fun i : H => μ (e (.inr (.inl i))))).cmean (fun h =>
            F (assemblePriorSample e w h y)))) := by
  classical
  unfold FinitePrior.cmean
  rw [← (priorSampleEquiv (Ω:=Ω) e).sum_comp (fun x => ((productPrior μ).mass x:ℂ)*F x)]
  simp only [Fintype.sum_prod_type,priorSampleEquiv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro w hw
  apply Finset.sum_congr rfl
  intro h hh
  change ((productPrior μ).mass (assemblePriorSample e w h y):ℂ)*F (assemblePriorSample e w h y) = _
  rw [productPrior_assembled_mass]
  simp only [Complex.ofReal_mul]
  ring

end Ostmann.Characters.Template

end

end OAI
