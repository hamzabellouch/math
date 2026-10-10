import OAI.Probability.InvariantIsing.Spectral.SpectralPartitionCounts

namespace OAI

/-! Counts on arbitrary finite spectral labels and their deterministic relabeling. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology Classical BigOperators

namespace InvariantIsing

def spectralLabelCount {ι : Type*} {N : ℕ}
    (g : Fin N → ι) (a : ι) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => g i=a)).card

lemma spectral_label_counts_partition {ι : Type*} [Fintype ι]
    (N : ℕ → ℕ) (hN : ∀ k, 0 < N k) (eig : (k : ℕ) → Fin (N k) → ℝ)
    (ν : ProbabilityMeasure ℝ)
    (hweak : Tendsto (fun k => empiricalSpectralLaw (hN k) (eig k)) atTop (𝓝 ν))
    (S : ι → Set ℝ) (hS : ∀ a, MeasurableSet (S a))
    (hboundary : ∀ a, (ν : Measure ℝ) (frontier (S a))=0)
    (g : (k : ℕ) → Fin (N k) → ι)
    (hg : ∀ k a i, g k i=a ↔ eig k i∈S a) :
    Tendsto (fun k a => (spectralLabelCount (g k) a : ℝ)/N k) atTop
      (𝓝 (fun a => (ν : Measure ℝ).real (S a))) := by
  apply tendsto_pi_nhds.mpr
  intro a
  have hh := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak (hboundary a)
  have hr := (ENNReal.tendsto_toReal (measure_ne_top (ν : Measure ℝ) (S a))).comp hh
  apply hr.congr
  intro k
  change (empiricalSpectralLaw (hN k) (eig k) : Measure ℝ).real (S a)=_
  rw [empiricalSpectralLaw_mass (hN k) (eig k) (S a) (hS a)]
  congr 2
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,hg]

lemma spectralLabelCount_relabel {ι κ : Type*} [Fintype ι] [DecidableEq κ]
    {N : ℕ} (g : Fin N → ι) (f : ι → κ) (b : κ) :
    spectralLabelCount (f ∘ g) b =
      ∑ a : {a : ι // f a=b}, spectralLabelCount g a := by
  have hh := Finset.sum_card_fiberwise_eq_card_filter Finset.univ
    (Finset.univ.filter (fun a => f a=b)) g
  rw [← Finset.sum_subtype (Finset.univ.filter (fun a => f a=b)) (by simp)
    (fun a => spectralLabelCount g a)]
  simpa only [spectralLabelCount, Finset.mem_filter,Finset.mem_univ,true_and,
    Function.comp_apply] using hh.symm

lemma spectral_label_counts_relabel {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N : ℕ → ℕ) (g : (k : ℕ) → Fin (N k) → ι) (w : ι → ℝ)
    (hlim : Tendsto (fun k a => (spectralLabelCount (g k) a : ℝ)/N k) atTop (𝓝 w))
    (f : ι → κ) :
    Tendsto (fun k b => (spectralLabelCount (f ∘ g k) b : ℝ)/N k) atTop
      (𝓝 (fun b => ∑ a : {a : ι // f a=b}, w a)) := by
  apply tendsto_pi_nhds.mpr
  intro b
  have hh := tendsto_finsetSum (Finset.univ : Finset {a : ι // f a=b}) (fun a _ =>
    (tendsto_pi_nhds.mp hlim) (a : ι))
  convert hh using 1
  funext k
  rw [spectralLabelCount_relabel, Nat.cast_sum, Finset.sum_div]

end InvariantIsing

end

end OAI
