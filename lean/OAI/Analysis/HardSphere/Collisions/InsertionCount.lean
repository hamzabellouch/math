import Mathlib
import OAI.Analysis.HardSphere.Collisions.LocalInsertion

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
open scoped Classical

lemma closeLabels_cons {n : ℕ} {L : Length} (r : ℝ) (w : SmoothMultiplier 1 L)
    (x : Torus L) (Y : Configuration n L) :
    (closeLabels r w (Fin.cons x Y)).card=(closeLabels r w Y).card+
      (if ∃ y∈tsupport w.orbital, torusDistance L y x ≤ 2*r then 1 else 0) := by
  classical
  simp only [closeLabels,Finset.card_filter]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]
  exact Nat.add_comm _ _

lemma closeLabels_insert_le {S : Type*} [DecidableEq S] {n : ℕ} {L : Length} (r : ℝ)
    (w : S → SmoothMultiplier 1 L)
    (hsep : ∀ z v : S, z≠v → ∀ x : Torus L, (w v).orbital x≠0 →
      ¬ ∃ y∈tsupport (w z).orbital, torusDistance L y x ≤ 2*r)
    (v z : S) (X : Configuration (n+1) L) (hx : (w v).orbital (X 0)≠0) :
    (closeLabels r (w z) X).card ≤ (closeLabels r (w z) (Fin.tail X)).card+(if v=z then 1 else 0) := by
  classical
  have he : Fin.cons (X 0) (Fin.tail X)=X := by funext i; cases i using Fin.cases <;> rfl
  rw [←he,closeLabels_cons]
  simp only [Fin.tail_cons]
  by_cases hvz : v=z
  · subst v
    simp only [ite_true]
    split_ifs <;> omega
  · have hzv : z≠v := Ne.symm hvz
    rw [ite_eq_right hvz,ite_eq_right (hsep z v hzv (X 0) hx)]

noncomputable def insertionCount {S : Type*} [DecidableEq S] (site : ℕ → S) (t : ℕ) (z : S) : ℕ :=
  ((Finset.range t).filter (fun i ↦ site i=z)).card

lemma insertionCount_zero {S : Type*} [DecidableEq S] (site : ℕ → S) (z : S) :
    insertionCount site 0 z=0 := by simp [insertionCount]

lemma insertionCount_succ {S : Type*} [DecidableEq S] (site : ℕ → S) (t : ℕ) (z : S) :
    insertionCount site (t+1) z=insertionCount site t z+(if site t=z then 1 else 0) := by
  simp only [insertionCount,Finset.card_filter,Finset.sum_range_succ]

lemma insertionCount_mono {S : Type*} [DecidableEq S] (site : ℕ → S) {t T : ℕ} (ht : t ≤ T) (z : S) :
    insertionCount site t z ≤ insertionCount site T z := by
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,hiz⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le ht),hiz⟩

lemma local_insertion_iterated : ∃ C : ℝ, 0<C ∧
    ∀ (S : Type) [DecidableEq S] (n : ℕ) (L : Length) (r : ℝ), 0<r →
    ∀ (w : S → SmoothMultiplier 1 L),
    (∀ z X, conj ((w z).toFun X)=(w z).toFun X) →
    (∀ z, (∫ y : Torus L, ‖(w z).orbital y‖^2)=1) →
    (∀ z v : S, z≠v → ∀ x : Torus L, (w v).orbital x≠0 →
      ¬ ∃ y∈tsupport (w z).orbital, torusDistance L y x ≤ 2*r) →
    ∀ (T k m : ℕ) (site : ℕ → S) (B E : ℝ),
    (∀ z, (w z).orbitalBound ≤ B) → (∀ z, (w z).orbitalEnergy ≤ E) →
    (∀ z, insertionCount site T z ≤ m) → C*B*(k+m)*r^3 ≤ 1/4 →
    ∀ u : Jet n L, u∈dirichletDomain n L r →
    (∀ᵐ Y ∂volume, u.1 Y≠0 → ∀ z, (closeLabels r (w z) Y).card ≤ k) →
    ∃ v : Jet (n+T) L, v∈dirichletDomain (n+T) L r ∧ ‖v.1‖=‖u.1‖ ∧
      energy v ≤ energy u+T*(C*(E+B*(k+m)*r))*‖u.1‖^2 := by
  obtain ⟨C,hC,hins⟩ := local_insertion_supported
  refine ⟨C,hC,?_⟩
  intro S _ n L r hr w hw hn hsep T k m site B E hB hE hct hs u hu hk
  have hrec (t : ℕ) (ht : t ≤ T) : ∃ v : Jet (n+t) L,
      v∈dirichletDomain (n+t) L r ∧ ‖v.1‖=‖u.1‖ ∧
      energy v ≤ energy u+t*(C*(E+B*(k+m)*r))*‖u.1‖^2 ∧
      (∀ᵐ X ∂volume, v.1 X≠0 → ∀ z,
        (closeLabels r (w z) X).card ≤ k+insertionCount site t z) := by
    induction t with
    | zero =>
      refine ⟨u,hu,rfl,?_,?_⟩
      · simp only [Nat.cast_zero,zero_mul,add_zero,le_refl]
      · simpa only [insertionCount_zero,Nat.add_zero] using hk
    | succ t ih =>
      obtain ⟨v,hv,hvn,hve,hvk⟩ := ih (Nat.le_trans (Nat.le_succ t) ht)
      have hmass : C*(w (site t)).orbitalBound*(k+m:ℕ)*r^3 ≤ 1/4 := by
        apply le_trans _ hs
        simp only [Nat.cast_add]
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_left (hB _) hC.le
      have hbudget : ∀ᵐ X ∂volume, v.1 X≠0 → (closeLabels r (w (site t)) X).card ≤ k+m := by
        filter_upwards [hvk] with X hX
        intro hne
        exact (hX hne (site t)).trans (Nat.add_le_add_left
          ((insertionCount_mono site (Nat.le_trans (Nat.le_succ t) ht) _).trans (hct _)) k)
      obtain ⟨v',hv',hvn',hve',hvs⟩ := hins (n+t) L r hr (w (site t)) (hw _) (hn _) (k+m) hmass v hv hbudget
      refine ⟨v',hv',hvn'.trans hvn,?_,?_⟩
      · have hbound : C*((w (site t)).orbitalEnergy+(w (site t)).orbitalBound*(k+m:ℕ)*r) ≤
            C*(E+B*(k+m)*r) := by
          apply mul_le_mul_of_nonneg_left _ hC.le
          apply add_le_add (hE _)
          rw [Nat.cast_add]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB _) (by positivity)) hr.le
        rw [hvn] at hve'
        have he := hve'.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right hbound (sq_nonneg _)))
        rw [Nat.cast_add,Nat.cast_one]
        nlinarith
      · filter_upwards [hvs,(configurationTail_quasiPreserving (n+t) L).ae hvk] with X hX hOld
        intro hne z
        obtain ⟨hOldne,hOrb⟩ := hX hne
        have hh := closeLabels_insert_le r w hsep (site t) z X hOrb
        have hh' := hOld hOldne z
        rw [insertionCount_succ]
        omega
  obtain ⟨v,hv,hvn,hve,_⟩ := hrec T le_rfl
  exact ⟨v,hv,hvn,hve⟩

end HardSphere

end

end OAI
