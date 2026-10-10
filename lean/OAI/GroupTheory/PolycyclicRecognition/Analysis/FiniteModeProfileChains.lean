import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfileChainConcentration
import Mathlib.Order.Filter.Finite

namespace OAI

/-! # Finite generator choices in the independent profile chains -/

noncomputable section
namespace PolycyclicRecognition

open Filter MeasureTheory Set TopologicalSpace
open scoped Topology

/-- Along a further increasing subsequence a finite generator index is
constant. This leaves an already converging profile law unchanged. -/
theorem exists_constant_mode_subsequence {I : Type*} [Finite I] (mode : ℕ → I) :
    ∃ i : I, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, mode (φ n) = i := by
  have he : ∃ i : I, ∃ᶠ n in atTop, mode n = i := by
    by_contra h
    push Not at h
    have hall : ∀ᶠ n in atTop, ∀ i, mode n ≠ i := eventually_all.mpr h
    obtain ⟨n, hn⟩ := hall.exists
    exact hn (mode n) rfl
  obtain ⟨i, hi⟩ := he
  obtain ⟨φ, hφ, hconst⟩ := extraction_of_frequently_atTop hi
  exact ⟨i, φ, hφ, hconst⟩

/-- The selected word may use a different finite generator at every
scale. It suffices to verify each actual fixed-generator subsequence. -/
theorem independent_profile_chain_concentration_finite_modes
    {V W I : Type*} [TopologicalSpace V] [NormedAddCommGroup W] [Finite I]
    (S : Set C(V, W)) [CompactSpace S] [MetrizableSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (Z : Set V) [CompactSpace Z] (n : ℕ)
    {A K : ℕ → Type*} [∀ m, MeasurableSpace (A m)] [∀ m, MeasurableSpace (K m)]
    [∀ m, Nonempty (K m)]
    (μ : ∀ m, ProbabilityMeasure (A m)) (ν : ∀ m, ProbabilityMeasure (K m))
    (profile : ∀ m, A m × K m → Fin (n + 1) → S)
    (hp : ∀ m, Measurable (profile m))
    (mode : ∀ m, K m → Fin n → I)
    (hedge : ∀ k : ∀ m, K m, ∀ edge : Fin n, ∀ i : I,
      ∀ ι : ℕ → ℕ, StrictMono ι → (∀ m, mode (ι m) (k (ι m)) edge = i) →
      ∀ limitLaw : ProbabilityMeasure (S × S),
      Tendsto (fun m => ProbabilityMeasure.map
        (ProbabilityMeasure.map (μ (ι m)) (fun a => profile (ι m) (a, k (ι m))))
        (fun f => (f edge.castSucc, f edge.succ))) atTop (𝓝 limitLaw) →
      ∀ f ∈ (limitLaw : Measure (S × S)).support, ∀ z ∈ Z, f.1.val z = f.2.val z)
    (j : Fin (n + 1)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun m => (μ m : Measure (A m)).prod (ν m : Measure (K m))
      {p | η ≤ dist ((profile m p j).val.restrict Z)
        ((profile m p 0).val.restrict Z)}) atTop (𝓝 0) := by
  apply independent_profile_chain_concentration S Z n μ ν profile hp ?_ j hη
  intro k edge ι hι limitLaw hlim
  obtain ⟨i, φ, hφ, hconst⟩ := exists_constant_mode_subsequence
    (fun m => mode (ι m) (k (ι m)) edge)
  exact hedge k edge i (ι ∘ φ) (hι.comp hφ) hconst limitLaw
    (hlim.comp hφ.tendsto_atTop)

end PolycyclicRecognition

end

end OAI
