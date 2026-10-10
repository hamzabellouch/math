import Mathlib
import OAI.Probability.ThreeStateClauses.Basic
import OAI.Probability.ThreeStateClauses.PosteriorLaw
import OAI.Probability.ThreeStateClauses.Products

namespace OAI

/-! Regular Law. -/

open scoped BigOperators ENNReal NNReal Topology
open Filter
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace ThreeState.TreeClauses.Tree
open ThreeState.TreeClauses.Experiment

def RegularObservation (b : ℕ) : ℕ → Type
  | 0 => Spin
  | n+1 => Fin b → RegularObservation b n

instance regularObservationFintype (b ℓ : ℕ) : Fintype (RegularObservation b ℓ) := by
  induction ℓ with
  | zero => exact inferInstanceAs (Fintype Spin)
  | succ ℓ ih => letI := ih; exact inferInstanceAs (Fintype (Fin b → RegularObservation b ℓ))

instance regularObservationMeasurable (b : ℕ) : (ℓ : ℕ) → MeasurableSpace (RegularObservation b ℓ)
  | 0 => inferInstanceAs (MeasurableSpace Spin)
  | ℓ+1 => letI := regularObservationMeasurable b ℓ
           inferInstanceAs (MeasurableSpace (Fin b → RegularObservation b ℓ))
instance regularObservationSingleton (b : ℕ) : (ℓ : ℕ) → MeasurableSingletonClass (RegularObservation b ℓ)
  | 0 => inferInstanceAs (MeasurableSingletonClass Spin)
  | ℓ+1 => letI := regularObservationSingleton b ℓ
           inferInstanceAs (MeasurableSingletonClass (Fin b → RegularObservation b ℓ))

instance observationCountable (ℓ : ℕ) : Countable (Observation ℓ) := by
  induction ℓ with
  | zero => exact inferInstanceAs (Countable Spin)
  | succ ℓ ih => let := ih; exact inferInstanceAs (Countable (Multiset (Observation ℓ)))

instance observationMeasurable (ℓ : ℕ) : MeasurableSpace (Observation ℓ) := ⊤
instance observationSingleton (ℓ : ℕ) : MeasurableSingletonClass (Observation ℓ) :=
  ⟨fun _ ↦ MeasurableSpace.measurableSet_top⟩

def regularLaw (b : ℕ) (lam : ℝ) (hlam : Admissible lam) :
    (ℓ : ℕ) → Spin → PMF (RegularObservation b ℓ)
  | 0, i => PMF.pure i
  | ℓ+1, i => productPMF (fun _ : Fin b ↦ (channel lam hlam i).bind (regularLaw b lam hlam ℓ))

def forgetRegular (b : ℕ) : (ℓ : ℕ) → RegularObservation b ℓ → Observation ℓ
  | 0, i => i
  | ℓ+1, v => (List.ofFn (fun j ↦ forgetRegular b ℓ (v j)) : Multiset (Observation ℓ))

lemma productPMF_list {α : Type} (p : PMF α) (n : ℕ) :
    (productPMF (fun _ : Fin n ↦ p)).map List.ofFn = iidList p n := by
  induction n with
  | zero =>
    have h : productPMF (fun _ : Fin 0 ↦ p) = PMF.pure (fun i : Fin 0 ↦ i.elim0) := by
      apply PMF.ext
      intro v
      simp [PMF.pure_apply, Subsingleton.elim v (fun i : Fin 0 ↦ i.elim0)]
    rw [h, PMF.pure_map]
    rfl
  | succ n ih =>
    rw [productPMF_cons, PMF.map_bind]
    change (p.bind (fun a ↦ _)) = p.bind (fun a ↦ _)
    congr 1
    funext a
    rw [PMF.map_comp]
    have he : (List.ofFn ∘ Fin.cons (n := n) (α := fun _ ↦ α) a : (Fin n → α) → List α) = List.cons a ∘ List.ofFn := by
      funext v; exact List.ofFn_cons a v
    rw [he, ← PMF.map_comp, ih]

lemma regularLaw_forget (b : ℕ) (lam : ℝ) (hlam : Admissible lam) (ℓ : ℕ) (i : Spin) :
    (regularLaw b lam hlam ℓ i).map (forgetRegular b ℓ) =
      observationLaw lam hlam (PMF.pure b) ℓ i := by
  induction ℓ generalizing i with
  | zero => exact PMF.map_id _
  | succ ℓ ih =>
    simp only [observationLaw, PMF.pure_bind]
    change (productPMF (fun _ : Fin b ↦ (channel lam hlam i).bind (regularLaw b lam hlam ℓ))).map
      ((fun xs : List (Observation ℓ) ↦ (xs : Multiset (Observation ℓ))) ∘
        List.ofFn ∘ (fun v j ↦ forgetRegular b ℓ (v j))) = _
    rw [← PMF.map_comp, ← PMF.map_comp, productPMF_map]
    simp_rw [PMF.map_bind, ih]
    rw [productPMF_list]
    exact (PMF.map_id _).symm

def regularExpansion (b : ℕ) (lam : ℝ) (hlam : Admissible lam) :
    (ℓ : ℕ) → RegularObservation b ℓ → PMF (RegularObservation b (ℓ+1))
  | 0, i => productPMF (fun _ : Fin b ↦ channel lam hlam i)
  | ℓ+1, v => productPMF (fun j : Fin b ↦ regularExpansion b lam hlam ℓ (v j))

lemma regularLaw_degrades (b : ℕ) (lam : ℝ) (hlam : Admissible lam) (ℓ : ℕ) (i : Spin) :
    (regularLaw b lam hlam ℓ i).bind (regularExpansion b lam hlam ℓ) =
      regularLaw b lam hlam (ℓ+1) i := by
  induction ℓ generalizing i with
  | zero =>
    change (PMF.pure i).bind (fun j ↦ productPMF (fun _ : Fin b ↦ channel lam hlam j)) =
      productPMF (fun _ : Fin b ↦ (channel lam hlam i).bind PMF.pure)
    rw [PMF.pure_bind, PMF.bind_pure]
  | succ ℓ ih =>
    change (productPMF (fun _ : Fin b ↦ (channel lam hlam i).bind (regularLaw b lam hlam ℓ))).bind
      (fun v ↦ productPMF (fun j ↦ regularExpansion b lam hlam ℓ (v j))) = _
    rw [productPMF_bind]
    simp only [PMF.bind_bind]
    simp_rw [ih]
    rfl

end ThreeState.TreeClauses.Tree

end

end OAI
