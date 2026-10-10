import OAI.Analysis.CircleDomains.Sobolev.AdmissibleWeakLimit
import OAI.Analysis.CircleDomains.Sobolev.HilbertWeakSubsequence
import Mathlib.MeasureTheory.Measure.SeparableMeasure

namespace OAI

/-! Uniformly bounded L² densities with eventual pointwise admissibility
bound the modulus of the whole family. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma measureFamilyModulus_le_of_bounded_L2_sequence
    {A Z : Type*} [MeasurableSpace Z] (σ : Measure Z) [IsSeparable σ]
    (K : A → FiniteMeasure Z) (f : ℕ → Z → ℝ)
    (hf : ∀ n, MemLp (f n) 2 σ) (hfm : ∀ n, Measurable (f n))
    (hf0 : ∀ n z, 0 ≤ f n z) {C : ℝ}
    (hnorm : ∀ n, ‖(hf n).toLp (f n)‖ ≤ C)
    (ha : ∀ a, ∀ᶠ n in atTop, 1 ≤ ∫⁻ z, ENNReal.ofReal (f n z) ∂(K a : Measure Z)) :
    measureFamilyModulus A Z σ K ≤ ENNReal.ofReal (C^2) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : TopologicalSpace.SeparableSpace (Lp ℝ 2 σ) := inferInstance
  obtain ⟨v,hv,ρ,hρ,hw⟩ := exists_hilbert_weak_subsequence
    (fun n => (hf n).toLp (f n)) C hnorm
  let S : ℕ → Set A := fun n => {a | ∀ k, n ≤ k →
    1 ≤ ∫⁻ z, ENNReal.ofReal (f k z) ∂(K a : Measure Z)}
  have hcover (a : A) : ∀ᶠ n in atTop, a ∈ S n := by
    obtain ⟨N,hN⟩ := eventually_atTop.mp (ha a)
    exact eventually_atTop.mpr ⟨N,fun n hn k hk => hN k (hn.trans hk)⟩
  have hu (n : ℕ) : ∀ᶠ k in atTop,
      (hf (ρ k)).toLp (f (ρ k)) ∈ admissibleL2Classes σ (fun a : S n => K a.val) := by
    filter_upwards [hρ.tendsto_atTop.eventually (eventually_ge_atTop n)] with k hk
    exact ⟨f (ρ k),hf (ρ k),hfm (ρ k),hf0 (ρ k),
      fun a => a.property (ρ k) hk,rfl⟩
  exact (measureFamilyModulus_le_weak_limit σ K S hcover
    (fun k => (hf (ρ k)).toLp (f (ρ k))) v hu hw).trans
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg v) hv 2))

end CircleDomainRigidity

end

end OAI
