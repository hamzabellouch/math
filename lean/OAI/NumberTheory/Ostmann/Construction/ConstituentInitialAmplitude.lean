import OAI.NumberTheory.Ostmann.Construction.ConstituentPrimeGuardedAmplitude
import OAI.NumberTheory.Ostmann.Construction.ScheduledInitialPhase

namespace OAI

/-! # The actual guarded amplitude at depth zero in original prime coordinates -/

namespace Ostmann
open scoped BigOperators Classical

theorem initial_constituent_word_prod {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (x : (Σ i, Fin (size i)) → ℕ) (a : CopyScheduleAtoms role 0) :
    ((scheduleConstituentWord role size 0 a).map (fun i => x i.val)).prod =
      ∏ k, x ⟨a.val, k⟩ := by
  rw [scheduleConstituentWord_prod]
  rfl

theorem initial_constituent_pairwise {I : Type*} (role : I → CopyScheduleRole)
    (size : I → ℕ) (x : (Σ i, Fin (size i)) → ℕ) :
    Pairwise (fun i j : SurvivingConstituent role size 0 => (x i.val).Coprime (x j.val)) ↔
      Pairwise (fun i j => (x i).Coprime (x j)) := by
  constructor
  · intro h i j hij
    exact h (show (⟨i, trivial⟩ : SurvivingConstituent role size 0) ≠ ⟨j, trivial⟩ from
      fun he => hij (congrArg Subtype.val he))
  · intro h i j hij
    exact h (fun he => hij (Subtype.ext he))

noncomputable def sampledTuplePhase {I : Type*} [Fintype I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (center : ∀ p : ℕ, ZMod p) (v : ℤ) (x : I → P) : ℂ := by
  letI : ∀ i, NeZero (x i : ℕ) := fun i => ⟨(hP _ (x i).property).ne_zero⟩
  exact tupleGraphPhase (fun i => (x i : ℕ)) (fun i => χ i (x i))
    (fun i => center (x i)) v

theorem scheduledSamplePhase_zero {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : I → ℕ → ℂ) (pivot : ℕ → I) (v : ℤ)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (x : I → P)
    (hκ : ∀ i (p : P), κ i p =
      @primitiveGaussPhase p.val ⟨(hP p p.property).ne_zero⟩ (χ i p))
    (center : ∀ p : ℕ, ZMod p) :
    scheduledSamplePhase role χ κ pivot 0 v P hP (fun i => x i.val) center =
      sampledTuplePhase P hP χ center v x := by
  let : ∀ i, Fact (x i : ℕ).Prime := fun i => ⟨hP _ (x i).property⟩
  exact (tupleGraphPhase_eq_scheduled role χ κ pivot (fun i => (x i : ℕ)) center
    (fun i => hκ i (x i)) v).symm

/-- This is the original independent prime law, with the full initial range,
unit and prime support kept inside the integrand. -/
theorem constituentPrimeGuardedAmplitude_zero {I D : Type*} [Fintype I] [Fintype D]
    (role : I → CopyScheduleRole) (size : I → ℕ)
    (χ : (Σ i, Fin (size i)) → ∀ p : ℕ, DirichletCharacter ℂ p)
    (κ : (Σ i, Fin (size i)) → ℕ → ℂ) (pivot : ℕ → (Σ i, Fin (size i)))
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (Q : (Σ i, Fin (size i)) → Finset ℕ)
    (hκ : ∀ i (p : P), κ i p =
      @primitiveGaussPhase p.val ⟨(hP p p.property).ne_zero⟩ (χ i p))
    (childBound pivotBound : ℕ → ℕ) (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (hist : D → ℤ)
    (center : ∀ p : ℕ, ZMod p) :
    constituentPrimeGuardedAmplitude role size χ κ pivot 0 P hP Q
      childBound pivotBound ranges leaf hist center =
    ∑ x : (Σ i, Fin (size i)) → P,
      ((∏ i, primeSubsetPrior P (Q i) (x i) : ℝ) : ℂ) *
      ∑ d, fullAtomTransferWeight role childBound pivotBound ranges leaf 0
        (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)) (hist d) *
        (if Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) then
          sampledTuplePhase P hP χ center (hist d) x else 0) := by
  let ρ := fun i : Σ j, Fin (size j) => role i.1
  let e : ((Σ i, Fin (size i)) → P) ≃ (SurvivingConstituent role size 0 → P) :=
    Equiv.arrowCongr (initialSurvivorEquiv ρ) (Equiv.refl P)
  unfold constituentPrimeGuardedAmplitude
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  have hprior : (∏ i : SurvivingConstituent role size 0,
      scheduledRolePrior ρ (fun j => primeSubsetPrior P (Q j)) 0 i (e x i)) =
      ∏ i, primeSubsetPrior P (Q i) (x i) :=
    (initialSurvivorEquiv ρ).prod_comp (fun i : SurvivingConstituent role size 0 =>
      primeSubsetPrior P (Q i.val) (x i.val)) |>.symm
  apply congrArg₂ (fun a b : ℂ => a * b)
  · exact congrArg (fun r : ℝ => (r : ℂ)) hprior
  apply Finset.sum_congr rfl
  intro d _
  have hword : (fun v => ((scheduleConstituentWord role size 0 v).map
      (fun i => (e x i : ℕ))).prod) = (fun a => ∏ k, (x ⟨a.val, k⟩ : ℕ)) := by
    funext a
    exact initial_constituent_word_prod role size (fun i => (x i : ℕ)) a
  rw [hword]
  congr 1
  have hpair := initial_constituent_pairwise role size (fun i => (x i : ℕ))
  change (if Pairwise (fun i j : SurvivingConstituent role size 0 =>
      (x i.val : ℕ).Coprime (x j.val : ℕ)) then _ else 0) = _
  rw [hpair]
  split_ifs
  · exact scheduledSamplePhase_zero ρ χ κ pivot (hist d) P hP x hκ center
  · rfl

end Ostmann

end OAI
