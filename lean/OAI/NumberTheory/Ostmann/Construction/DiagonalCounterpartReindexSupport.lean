import OAI.NumberTheory.Ostmann.Construction.DiagonalRegrouping
import OAI.NumberTheory.Ostmann.Construction.SourceAssignmentSupport
import OAI.NumberTheory.Ostmann.Construction.SourceFrequencyBoundsFamily

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

theorem remainingPrior_mass_ne_zero_iff (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (x : RemainingSample sources T giant) :
    (remainingPrior sources T giant).mass x≠0 ↔
      giant.law.mass x.1≠0 ∧ (assignmentPrior sources T).mass x.2≠0 :=
  mul_ne_zero_iff

theorem remainingValues_gt_of_mass_ne_zero (sources : SourceFamily) (T : List SourceSlot)
    (giant : PrimeSource) (N : ℕ) (hg : giant.AboveFrequency N)
    (hs : ∀i : Fin T.length,(sources T[i].origin).AboveFrequency N)
    (x : RemainingSample sources T giant) (hx : (remainingPrior sources T giant).mass x≠0) :
    ∀q∈remainingValues sources T giant x,N<q := by
  obtain ⟨hq,hx⟩ := (remainingPrior_mass_ne_zero_iff sources T giant x).mp hx
  intro q hq'
  rcases List.mem_cons.mp hq' with rfl | hq'
  · exact hg x.1 hq
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hq'
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact hs i (x.2 i) (assignmentPrior_component_mass_ne_zero sources T x.2 hx i)

theorem refinedRowDiagonal_congr_on_weighted_support {α κ τ : Type*} [Fintype α]
    [DecidableEq κ] [DecidableEq τ] (w : α→ℝ) (f : α→ℂ)
    (tag₁ : α→κ) (tag₂ : α→τ)
    (he : ∀x y,(w x:ℂ)*f x≠0→(w y:ℂ)*f y≠0→(tag₁ y=tag₁ x ↔ tag₂ y=tag₂ x)) :
    refinedRowDiagonal w tag₁ f=refinedRowDiagonal w tag₂ f := by
  unfold refinedRowDiagonal diagonalComplex
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hfx : (w x:ℂ)*f x=0
  · simp [hfx]
  by_cases hfy : (w y:ℂ)*f y=0
  · simp [hfy]
  simp only [he x y hfx hfy]

theorem remainingDiagonal_eq_product_diagonal_of_positive_mass (d : Decomposition) (P : Finset ℕ)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (giant : PrimeSource)
    (X G : ℝ) (bins : List ℕ→State→ℝ) (outside : List ℕ) (l p : ℕ)
    (u : SourceAssignment sources (Template.extracted (l+1) (Template.current seed l)))
    (hg : giant.AboveFrequency (V l))
    (hs : ∀i : Fin (Template.remainder (l+1) (Template.current seed l)).length,
      (sources (Template.remainder (l+1) (Template.current seed l))[i].origin).AboveFrequency (V l)) :
    remainingDiagonal d P sources seed V giant X G bins outside l p u =
      (refinedRowDiagonal (remainingTermMass sources seed V giant l)
        (remainingTermProductTag sources seed V giant l)
        (remainingTermValue d P sources seed V giant X G bins outside l p u)).re := by
  unfold remainingDiagonal
  apply congrArg Complex.re
  apply refinedRowDiagonal_congr_on_weighted_support
  intro x y hx hy
  obtain ⟨hmx,hfx⟩ := mul_ne_zero_iff.mp hx
  obtain ⟨hmy,hfy⟩ := mul_ne_zero_iff.mp hy
  have hmx' : (remainingPrior sources _ giant).mass x.1≠0 := by exact_mod_cast hmx
  have hmy' : (remainingPrior sources _ giant).mass y.1≠0 := by exact_mod_cast hmy
  have hxlarge := remainingValues_gt_of_mass_ne_zero sources _ giant (V l) hg hs x.1 hmx'
  have hylarge := remainingValues_gt_of_mass_ne_zero sources _ giant (V l) hg hs y.1 hmy'
  have hfx' := (remainingIntegrand_root_support d P sources seed V giant X G bins outside l p u x.1 x.2 hfx).2.2.2.2
  have hfy' := (remainingIntegrand_root_support d P sources seed V giant X G bins outside l p u y.1 y.2 hfy).2.2.2.2
  simpa only [remainingTermExactTag,remainingTermProductTag,Prod.mk.injEq,remainingState] using
    remainingExactTag_eq_iff sources _ giant y.1 x.1 hfy'.1 hfx'.1
      (fun q hq => hfy'.2.trans_lt (hylarge q hq))
      (fun q hq => hfx'.2.trans_lt (hxlarge q hq))

end Ostmann.Construction

end

end OAI
