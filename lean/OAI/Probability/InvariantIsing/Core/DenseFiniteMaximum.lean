import OAI.Probability.InvariantIsing.Core.FiniteGaussianMaximum
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.DenseEmbedding

namespace OAI

/-! Increasing finite maxima exhaust a continuous function on a dense sequence. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

def prefixMaximum (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i : Fin (n+1) => f i)

lemma le_prefixMaximum (f : ℕ → ℝ) {i n : ℕ} (h : i ≤ n) : f i ≤ prefixMaximum f n := by
  exact Finset.le_sup' (fun j : Fin (n+1) => f j) (Finset.mem_univ ⟨i,by omega⟩)

lemma prefixMaximum_le (f : ℕ → ℝ) {n : ℕ} {b : ℝ} (h : ∀ i ≤ n, f i ≤ b) :
    prefixMaximum f n ≤ b := by
  apply Finset.sup'_le
  intro i _
  exact h i (by omega)

lemma prefixMaximum_monotone (f : ℕ → ℝ) : Monotone (prefixMaximum f) := by
  intro n m hnm
  exact prefixMaximum_le f (fun i hi => le_prefixMaximum f (hi.trans hnm))

lemma prefixMaximum_bddAbove {f : ℕ → ℝ} (hf : BddAbove (range f)) :
    BddAbove (range (prefixMaximum f)) := by
  obtain ⟨b,hb⟩ := hf
  exact ⟨b,fun _ ⟨n,hn⟩ => hn ▸ prefixMaximum_le f (fun i _ => hb (mem_range_self i))⟩

lemma prefixMaximum_tendsto {f : ℕ → ℝ} (hf : BddAbove (range f)) :
    Tendsto (prefixMaximum f) atTop (𝓝 (⨆ i, f i)) := by
  have hb := prefixMaximum_bddAbove hf
  have he : (⨆ n, prefixMaximum f n) = ⨆ i, f i := by
    apply le_antisymm
    · exact ciSup_le (fun n => prefixMaximum_le f (fun i _ => le_ciSup hf i))
    · exact ciSup_le (fun i => (le_prefixMaximum f (le_refl i)).trans (le_ciSup hb i))
  rw [← he]
  exact tendsto_atTop_ciSup (prefixMaximum_monotone f) hb

theorem dense_prefixMaximum_tendsto {S : Type*} [TopologicalSpace S] [Nonempty S]
    (s : ℕ → S) (hs : DenseRange s) (f : S → ℝ) (hf : Continuous f)
    (hb : BddAbove (range f)) :
    Tendsto (prefixMaximum (f ∘ s)) atTop (𝓝 (⨆ x, f x)) := by
  have hbs : BddAbove (range (f ∘ s)) := hb.mono (range_comp_subset_range _ _)
  have he : (⨆ i, f (s i)) = ⨆ x, f x := by
    apply le_antisymm
    · exact ciSup_le (fun i => le_ciSup hb (s i))
    · apply ciSup_le
      exact isClosed_property hs (isClosed_le hf continuous_const)
        (fun i => le_ciSup hbs i)
  simpa only [Function.comp_def,he] using prefixMaximum_tendsto hbs

end InvariantIsing

end

end OAI
