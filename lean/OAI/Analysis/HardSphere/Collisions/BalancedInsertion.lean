import Mathlib
import OAI.Analysis.HardSphere.Geometry.DeficiencyPenalty

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter PeriodicCutoff TightCutoff
open scoped ComplexConjugate

lemma exists_balanced_insertion (S : Type) [Fintype S] [Nonempty S] [DecidableEq S] (m : ℕ) :
    ∃ site : ℕ → S, ∀ z, insertionCount site (m*Fintype.card S) z=m := by
  classical
  let T := m*Fintype.card S
  let e : Fin T ≃ Fin m × S := Fintype.equivOfCardEq (by simp [T])
  let site : ℕ → S := fun i ↦ if h : i<T then (e ⟨i,h⟩).2 else Classical.choice ‹Nonempty S›
  refine ⟨site,?_⟩
  intro z
  let A := (Finset.range T).filter (fun i ↦ site i=z)
  have hl (i : A) : i.val<T := Finset.mem_range.mp (Finset.mem_filter.mp i.property).1
  have hz (i : A) : (e ⟨i.val,hl i⟩).2=z := by
    have h := (Finset.mem_filter.mp i.property).2
    simpa only [site,dite_eq_left (hl i)] using h
  let f : A → Fin m := fun i ↦ (e ⟨i.val,hl i⟩).1
  let g : Fin m → A := fun j ↦ ⟨(e.symm (j,z)).val,by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr (e.symm (j,z)).isLt,?_⟩
    simp only [site,dite_eq_left (e.symm (j,z)).isLt,e.apply_symm_apply]⟩
  have hg (j : Fin m) : f (g j)=j := by
    change (e (e.symm (j,z))).1=j
    rw [e.apply_symm_apply]
  have hf (i : A) : g (f i)=i := by
    apply Subtype.ext
    change (e.symm ((e ⟨i.val,hl i⟩).1,z)).val=i.val
    rw [←hz i]
    simp only [Prod.mk.eta,e.symm_apply_apply]
  let q : A ≃ Fin m := ⟨f,g,hf,hg⟩
  have hc := Fintype.card_congr q
  simpa only [Fintype.card_coe,Fintype.card_fin,insertionCount,A,T] using hc

lemma deficiency_penalty_cells : ∃ C : ℝ, 0<C ∧
    ∀ (S : Type) [Fintype S] [Nonempty S] [DecidableEq S]
      (n : ℕ) (L : Length) (r : ℝ), 0<r → 0<n →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (w : S → SmoothMultiplier 1 L),
    (∀ z X, conj ((w z).toFun X)=(w z).toFun X) →
    (∀ z, (∫ y : Torus L, ‖(w z).orbital y‖^2)=1) →
    (∀ z v : S, z≠v → ∀ x : Torus L, (w v).orbital x≠0 →
      ¬ ∃ y∈tsupport (w z).orbital, torusDistance L y x ≤ 2*r) →
    ∀ (k m : ℕ) (B E : ℝ),
    (∀ z, (w z).orbitalBound ≤ B) → (∀ z, (w z).orbitalEnergy ≤ E) →
    C*B*(k+m)*r^3 ≤ 1/4 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
    (∀ᵐ Y ∂volume, u.1 Y≠0 → ∀ z, (closeLabels r (w z) Y).card ≤ k) →
    m*Fintype.card S*(energy g/(n:ℝ)-C*(E+B*(k+m)*r))*‖u.1‖^2 ≤
      energy u-energy g*‖u.1‖^2 := by
  obtain ⟨C,hC,hdef⟩ := deficiency_penalty
  refine ⟨C,hC,?_⟩
  intro S _ _ _ n L r hr hn g hg w hw hwN hsep k m B E hB hE hs u hu hk
  obtain ⟨site,hsite⟩ := exists_balanced_insertion S m
  simpa only [Nat.cast_mul] using hdef S n L r hr hn g hg w hw hwN hsep (m*Fintype.card S) k m site B E hB hE
    (fun z ↦ le_of_eq (hsite z)) hs u hu hk

end HardSphere

end

end OAI
