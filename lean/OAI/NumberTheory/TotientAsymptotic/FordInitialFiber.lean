import OAI.NumberTheory.TotientAsymptotic.FordInitialConditions
import OAI.NumberTheory.TotientAsymptotic.FordInitialRecovery
import OAI.NumberTheory.TotientAsymptotic.InitialPrimeCount

namespace OAI

/-! Counting the original tuples above one first-cutoff state. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

theorem ford_initial_fiber_count : ∃ C : ℝ,0 < C ∧
    ∀ (b D r : ℕ) (y S : ℝ) (Y U : ℕ → ℝ),Real.exp 2 ≤ y → 1 ≤ B y → 2 ≤ Y 1 →
    ∀ _hp : FordComparisonParameters b y S D r Y U,
    ∀ T : Finset (ShiftedPair b),(∀ t ∈ T,FordComparisonConditions b y S D r Y U t) →
    ∀ s ∈ T.image (fun t => fordFactorState t (Y 1)),
    ((T.filter (fun t => fordFactorState t (Y 1)=s)).card:ℝ) ≤
      (C*(y/(D*r*factorProduct s:ℕ))*(B y)^2/(Real.log y/(6*B y))^3)*
        (Real.log y/Real.log (Y 1)) := by
  classical
  obtain ⟨C,hC,hbound⟩ := initial_rough_count
  refine ⟨C,hC,?_⟩
  intro b D r y S Y U hy hBy hU hp T hT s hs
  let j : Fin b := ⟨0,by have := hp.1; omega⟩
  let Q := T.filter (fun t => fordFactorState t (Y 1)=s)
  let E := Q.image (fun t => fordInitialFactor hp.1 t Y)
  obtain ⟨t₀,ht₀,he₀⟩ := Finset.mem_image.mp hs
  have ha : 0 < s.left j := by
    have he := congrArg (fun q : ShiftedPair b => q.left j) he₀
    rw [← he]
    exact partBelow_pos _ _
  have hb : 0 < s.right j := by
    have he := congrArg (fun q : ShiftedPair b => q.right j) he₀
    rw [← he]
    exact partBelow_pos _ _
  have hpS : 0 < factorProduct s := by
    rw [← he₀]
    exact Finset.prod_pos (fun j _ => partBelow_pos _ _)
  have hd : 0 < D*r*factorProduct s := by
    have hD : 0 < D := by rcases hp with ⟨_,_,_,_,_,_,_,hD,_,_,_,_⟩; omega
    have hr : 0 < r := by rcases hp with ⟨_,_,_,_,_,_,_,_,_,_,hr,_⟩; omega
    positivity
  have hE : ∀ n ∈ E,InitialRoughConditions (s.left j) (s.right j)
      (D*r*factorProduct s) y (Y 1) n := by
    intro n hn
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨ht,he⟩ := Finset.mem_filter.mp ht
    have hh := ford_initial_conditions ((Real.exp_pos 2).le.trans hy) hBy hp (hT t ht)
    change InitialRoughConditions ((fordFactorState t (Y 1)).left j)
      ((fordFactorState t (Y 1)).right j) (D*r*factorProduct (fordFactorState t (Y 1)))
      y (Y 1) (fordInitialFactor hp.1 t Y) at hh
    rwa [he] at hh
  have hinj : Set.InjOn (fun t => fordInitialFactor hp.1 t Y) (↑Q : Set (ShiftedPair b)) := by
    intro t ht v hv he
    obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
    obtain ⟨hv,hsv⟩ := Finset.mem_filter.mp hv
    exact ford_initial_recover hp (hT t ht) (hT v hv) (hst.trans hsv.symm) he
  have hcard : E.card=Q.card := Finset.card_image_of_injOn hinj
  have hh := hbound (s.left j) (s.right j) (D*r*factorProduct s) y (Y 1)
    ha hb hd hy hBy hU (ford_cutoff_le_y hp hp.1) E hE
  rwa [hcard] at hh

end TotientAsymptotic

end

end OAI
