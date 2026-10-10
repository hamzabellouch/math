import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryConjugate

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem otherProduct_reindex (e : ι ≃ κ) (p : κ → ℕ) (i : ι) (hp : p (e i)≠0) :
    Construction.otherProduct (fun j => p (e j)) i=Construction.otherProduct p (e i) := by
  apply mul_right_cancel₀ hp
  rw [Construction.otherProduct,Finset.prod_erase_mul _ _ (Finset.mem_univ i),
    Construction.otherProduct,Finset.prod_erase_mul _ _ (Finset.mem_univ (e i))]
  exact e.prod_comp p

theorem crtFrequency_reindex (e : ι ≃ κ) (p : κ → ℕ) [∀ i, NeZero (p i)]
    (s : ℤ) (i : ι) :
    Construction.crtFrequency (fun j => p (e j)) s i=Construction.crtFrequency p s (e i) := by
  unfold Construction.crtFrequency
  rw [otherProduct_reindex e p i (NeZero.ne _)]

omit [DecidableEq ι] [DecidableEq κ] in
theorem primeGraphPhase_reindex [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (B : κ → κ → ℤ) (p : κ → ℕ)
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) (ν : κ → ℂ) :
    primeGraphPhase (fun i h => B (e i) (e h)) (fun i => p (e i)) (fun i => χ (e i))
      (fun i => ν (e i)) = primeGraphPhase B p χ ν := by
  unfold primeGraphPhase
  rw [←e.prod_comp (fun i => ν i*∏ h,χ i (p h)^B i h)]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  exact e.prod_comp (fun h => χ (e i) (p h)^B (e i) h)

theorem crtPhase_product_reindex (e : ι ≃ κ) (p : κ → ℕ) [∀ i, NeZero (p i)]
    (a : ∀ i, ZMod (p i)) (s : ℤ) :
    (∏ i, ZMod.stdAddChar (-(a (e i)*Construction.crtFrequency (fun j => p (e j)) s i))) =
      ∏ i, ZMod.stdAddChar (-(a i*Construction.crtFrequency p s i)) := by
  simp_rw [crtFrequency_reindex e p s]
  exact e.prod_comp (fun i => ZMod.stdAddChar (-(a i*Construction.crtFrequency p s i)))

theorem next_history_graphPhase_reindex (k j : ℕ) (hj : j<k) (width : Role → ℕ)
    (p : UnaryOutputIndex k j width → ℕ) [∀ i, Fact (p i).Prime]
    (χ : ∀ i, MulChar (ZMod (p i)) ℂ) (s : ℤ) (t : HistoryReconstruction.Tree (j+1)) :
    let e := nextConstituentEquiv (schedule k j) j width
    primeGraphPhase (constituentGraph k (j+1) width) (fun i => p (e i)) (fun i => χ (e i))
      (fun i => actualHistoryUnary k width (χ (e i)) (j+1) s t i) =
    primeGraphPhase
      (transferGraph (collapsedConstituentGraph (schedule k j) j width (pivotSlot k j hj)
        (graph k j) (intraGraph k j))) p χ
      (fun i => actualHistoryUnary k width (χ i) (j+1) s t (e.symm i)) := by
  dsimp only
  have hg : constituentGraph k (j+1) width = fun i h =>
      transferGraph (collapsedConstituentGraph (schedule k j) j width (pivotSlot k j hj)
        (graph k j) (intraGraph k j))
        (nextConstituentEquiv (schedule k j) j width i)
        (nextConstituentEquiv (schedule k j) j width h) := by
    funext i h
    exact constituentGraph_succ k j hj width i h
  rw [hg]
  simpa only [Equiv.symm_apply_apply] using
    primeGraphPhase_reindex (nextConstituentEquiv (schedule k j) j width) _ p χ
      (fun i => actualHistoryUnary k width (χ i) (j+1) s t
        ((nextConstituentEquiv (schedule k j) j width).symm i))

end Ostmann.Characters.Template

end

end OAI
