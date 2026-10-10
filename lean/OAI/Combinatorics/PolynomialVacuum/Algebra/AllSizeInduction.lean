import OAI.Combinatorics.PolynomialVacuum.Algebra.AllSizeConstruction

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

theorem interpolateState_all_degrees {n : ℕ} (hn : 2≤n)
    (ψ : State n) (χ : State (n+1)) (hψ : VacuumRegular ψ) (hχ : VacuumRegular χ) :
    (∀ s i, (interpolateState ψ χ s).degreeOf i≤n+1) ∧
    (∀ s i, s i=Spin.plus → (interpolateState ψ χ s).degreeOf i≤n) := by
  have hs := interpolateState_spectator_degrees hn ψ χ hψ.exchange hψ.degree hψ.plus
    (fun s i => (hχ.degree s i).trans (by omega))
    (fun s i h => (hχ.plus s i h).trans (by omega))
  constructor
  · intro s i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (interpolateState_last_degrees ψ χ s).1
    · exact (hs s j).1
  · intro s i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (interpolateState_last_degrees ψ χ s).2
    · exact (hs s j).2

 

theorem polynomialVacuum_at_step (n : ℕ)
    (hψ : VacuumAt polynomialVacuum (n+2))
    (hχ : VacuumAt polynomialVacuum (n+3)) : VacuumAt polynomialVacuum (n+4) := by
  let ψ := polynomialVacuum (n+2)
  let χ := polynomialVacuum (n+3)
  let Ψ := interpolateState ψ χ
  have hdef : polynomialVacuum (n+4)=Ψ := by rw [polynomialVacuum]
  have hfirst : FirstCupReduction (liftState Ψ) (liftState ψ) (n+2) :=
    interpolateState_firstCup ψ χ (liftState (polynomialVacuum n)) (liftState (polynomialVacuum (n+1)))
      hψ.regular.exchange (hψ.nodes n rfl) (hψ.firstCup n rfl) (hψ.lastZero (n+1) rfl)
      (hχ.firstCup (n+1) rfl) (fun s => hψ.regular.degree s _)
      (fun s hs => by have:=hψ.regular.plus s _ hs; simpa using this)
  have hnodes : NaturalCupNodes (liftState Ψ) (liftState ψ) (n+2) :=
    lift_interpolate_cupNodes ψ χ hψ.regular.exchange
  have hcup : ∀ i≤n+2, CupAt (liftState Ψ) (liftState ψ) (n+2) i :=
    interpolateState_all_cups ψ χ hψ.regular.exchange hχ.regular.exchange hfirst
  have hdg := interpolateState_all_degrees (by omega : 2≤n+2) ψ χ hψ.regular hχ.regular
  have hd : ∀ s i, (Ψ s).degreeOf i≤n+3 := hdg.1
  have hp : ∀ s i, s i=Spin.plus → (Ψ s).degreeOf i≤n+2 := hdg.2
  have hz : MinusZero Ψ := interpolateState_minusZero ψ χ hψ.regular.exchange hψ.regular.minus hχ.regular.minus
  have hex : LowerExchange (liftState Ψ) (n+4) :=
    fullExchange_of_cups (by omega : 2≤n+2) Ψ ψ
      (interpolateState_first_exchanges ψ χ hψ.regular.exchange hχ.regular.exchange)
      hψ.regular.exchange hnodes hcup hd hp hz
  have hcy : NaturalCyclic (n+3) (liftState Ψ) :=
    cyclicity_of_cups Ψ ψ hex hcup (hψ.cyclic (n+1) rfl) hd hp hz
  have hhom : ∀ s, (Ψ s).IsHomogeneous ((n+4).choose 2) :=
    homogeneity_of_cups Ψ ψ hex hcup hψ.regular.homogeneous hd hp hz
  have hcharge : ChargeZero Ψ := chargeZero_of_cups Ψ ψ hex hcup hψ.regular.charge hd hp hz
  constructor
  · rw [hdef]
    exact ⟨hcharge,hhom,(fun s i => (hd s i).trans (by omega)),
      (fun s i hs => (hp s i hs).trans (by omega)),hz,hex⟩
  · intro k hk
    have he : k=n+3 := by omega
    subst k
    rw [show n+3+1=n+4 by omega,hdef]
    exact hcy
  · intro k hk
    have he : k=n+2 := by omega
    subst k
    rw [show n+2+2=n+4 by omega,hdef]
    exact hnodes
  · intro k hk
    have he : k=n+2 := by omega
    subst k
    rw [show n+2+2=n+4 by omega,hdef]
    exact hfirst
  · intro k hk
    have he : k=n+2 := by omega
    subst k
    rw [show n+2+2=n+4 by omega,hdef]
    exact hcup
  · intro k hk
    have he : k=n+3 := by omega
    subst k
    rw [show n+3+1=n+4 by omega,hdef]
    exact interpolateState_lastZero ψ χ

theorem polynomialVacuum_at (N : ℕ) : VacuumAt polynomialVacuum N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    rcases N with _|_|_|_|n
    · exact polynomialVacuum_at_zero
    · exact polynomialVacuum_at_one
    · exact polynomialVacuum_at_two
    · exact polynomialVacuum_at_three
    · exact polynomialVacuum_at_step n (ih (n+2) (by omega)) (ih (n+3) (by omega))

end PolynomialVacuumAlgebra

end OAI
