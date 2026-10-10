import Mathlib
import OAI.Probability.Ballisticity.Estimates.IndependentRandomTestBound
import OAI.Probability.Ballisticity.Estimates.FinitePolicyPMF

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def futureRows {d : ℕ} (S : ℕ → Set (Lattice d)) (i : ℕ) : Set (Lattice d) :=
  ⋃ j ∈ Set.Ici i, S j

lemma futureRows_mono {d : ℕ} (S : ℕ → Set (Lattice d)) {i j : ℕ}
    (h : i ≤ j) : futureRows S j ⊆ futureRows S i := by
  intro x hx
  obtain ⟨k,hk,hx⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨k,h.trans hk,hx⟩

lemma rows_subset_futureRows {d : ℕ} (S : ℕ → Set (Lattice d)) (i : ℕ) :
    S i ⊆ futureRows S i := by
  intro x hx
  exact Set.mem_iUnion₂.mpr ⟨i,(show i ≤ i from le_rfl),hx⟩

lemma finitePolicyPMF_local {d : ℕ} {G : Type*} [Add G]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (i : ℕ) (x : G) (n : ℕ) (w : List G) :
    @Measurable _ _ (rowSigma (futureRows S i)) _ (fun ω => finitePolicyPMF Q ω i x n w) := by
  induction n generalizing i x w with
  | zero => exact measurable_const
  | succ n ih =>
    cases w with
    | nil =>
      simp only [finitePolicyPMF_nil_succ]
      exact measurable_const
    | cons u w =>
      simp only [finitePolicyPMF_cons]
      exact ((hQ i x u).mono (rowSigma_mono (rows_subset_futureRows S i)) le_rfl).mul
        ((ih (i+1) (x+u) w).mono (rowSigma_mono (futureRows_mono S (by omega))) le_rfl)

lemma disjoint_rows_future {d : ℕ} (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (i : ℕ) :
    Disjoint (S i) (futureRows S (i+1)) := by
  simp only [futureRows,Set.disjoint_iUnion_right]
  intro j hj
  change i+1 ≤ j at hj
  exact hS (by omega)

lemma finitePolicyPMF_annealed {d : ℕ} {G : Type*} [Add G]
    (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (Q : ℕ → Environment d → G → PMF G) (S : ℕ → Set (Lattice d))
    (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (hQ : ∀ i x u, @Measurable _ _ (rowSigma (S i)) _ (fun ω => Q i ω x u))
    (p : PMF G) (havg : ∀ i x u, (∫⁻ ω, Q i ω x u ∂environmentLaw ν) = p u)
    (i : ℕ) (x : G) (n : ℕ) (w : List G) :
    (∫⁻ ω, finitePolicyPMF Q ω i x n w ∂environmentLaw ν) =
      finitePolicyPMF (fun _ (_ : Unit) _ => p) () i x n w := by
  induction n generalizing i x w with
  | zero => simp [finitePolicyPMF]
  | succ n ih =>
    cases w with
    | nil => simp only [finitePolicyPMF_nil_succ,lintegral_zero]
    | cons u w =>
      simp only [finitePolicyPMF_cons]
      have hp := finitePolicyPMF_local Q S hQ (i+1) (x+u) n w
      have hind := indepFun_of_disjoint_rows ν (disjoint_rows_future S hS i)
        (fun ω => Q i ω x u) (fun ω => finitePolicyPMF Q ω (i+1) (x+u) n w)
        (hQ i x u) hp
      rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
        ((hQ i x u).mono (rowSigma_le _) le_rfl).aemeasurable
        (hp.mono (rowSigma_le _) le_rfl).aemeasurable hind,havg,ih]

end DirectionalTransience

end

end

end OAI
