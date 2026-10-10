import OAI.Probability.InvariantIsing.Core.DenseFiniteMaximum

namespace OAI

/-! Decreasing finite minima exhaust continuous functions on a dense sequence. -/
noncomputable section
open Filter Set
open scoped Topology
namespace InvariantIsing

def prefixMinimum (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i : Fin (n+1) => f i)

lemma prefixMinimum_le (f : ℕ → ℝ) {i n : ℕ} (h : i ≤ n) : prefixMinimum f n ≤ f i :=
  Finset.inf'_le (fun j : Fin (n+1) => f j) (Finset.mem_univ (⟨i,by omega⟩ : Fin (n+1)))

lemma le_prefixMinimum (f : ℕ → ℝ) {n : ℕ} {b : ℝ} (h : ∀ i ≤ n, b ≤ f i) :
    b ≤ prefixMinimum f n := by
  apply Finset.le_inf'
  intro i _
  exact h i (by omega)

lemma prefixMinimum_antitone (f : ℕ → ℝ) : Antitone (prefixMinimum f) := by
  intro n m hnm
  exact le_prefixMinimum f (fun i hi => prefixMinimum_le f (hi.trans hnm))

lemma prefixMinimum_bddBelow {f : ℕ → ℝ} (hf : BddBelow (range f)) :
    BddBelow (range (prefixMinimum f)) := by
  obtain ⟨b,hb⟩ := hf
  exact ⟨b,fun _ ⟨n,hn⟩ => hn ▸ le_prefixMinimum f (fun i _ => hb (mem_range_self i))⟩

lemma prefixMinimum_tendsto {f : ℕ → ℝ} (hf : BddBelow (range f)) :
    Tendsto (prefixMinimum f) atTop (𝓝 (⨅ i, f i)) := by
  have hb := prefixMinimum_bddBelow hf
  have he : (⨅ n, prefixMinimum f n) = ⨅ i, f i := by
    apply le_antisymm
    · exact le_ciInf (fun i => (ciInf_le hb i).trans (prefixMinimum_le f (le_refl i)))
    · exact le_ciInf (fun n => le_prefixMinimum f (fun i _ => ciInf_le hf i))
  rw [← he]
  exact tendsto_atTop_ciInf (prefixMinimum_antitone f) hb

theorem dense_prefixMinimum_tendsto {S : Type*} [TopologicalSpace S] [Nonempty S]
    (s : ℕ → S) (hs : DenseRange s) (f : S → ℝ) (hf : Continuous f)
    (hb : BddBelow (range f)) :
    Tendsto (prefixMinimum (f ∘ s)) atTop (𝓝 (⨅ x, f x)) := by
  have hbs : BddBelow (range (f ∘ s)) := hb.mono (range_comp_subset_range _ _)
  have he : (⨅ i, f (s i)) = ⨅ x, f x := by
    apply le_antisymm
    · apply le_ciInf
      exact isClosed_property hs (isClosed_le continuous_const hf)
        (fun i => ciInf_le hbs i)
    · exact le_ciInf (fun i => ciInf_le hb (s i))
  simpa only [Function.comp_def,he] using prefixMinimum_tendsto hbs

end InvariantIsing

end

end OAI
