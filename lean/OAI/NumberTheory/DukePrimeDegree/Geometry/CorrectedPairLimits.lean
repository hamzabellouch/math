import OAI.NumberTheory.DukePrimeDegree.Dynamics.CorrectedGenericPairs
import OAI.NumberTheory.DukePrimeDegree.Dynamics.GenericMeanOscillation

namespace OAI

/-!
# Compactly corrected generic pairs approach the same point

The common correcting parameters lie in one compact stabilizer patch.
After a subsequence, both corrected starting points approach the same
quotient point.  Their actual invariant means can consequently be
compared using a fixed finite continuous approximation.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_common_corrected_pair_limit {n : ℕ}
    (H : Subgroup (G n)) (K : Set H) (hK : IsCompact K)
    (u : ℕ → H) (hu : ∀ k, u k ∈ K)
    (a b : ℕ → G n) (ha : Tendsto a atTop (𝓝 1)) (hb : Tendsto b atTop (𝓝 1))
    (x : X n) :
    ∃ u₀ ∈ K, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => rightAction x (u (φ k) : G n))
        atTop (𝓝 (rightAction x (u₀ : G n))) ∧
      Tendsto (fun k => rightAction x (a (φ k) * b (φ k) * (u (φ k) : G n)))
        atTop (𝓝 (rightAction x (u₀ : G n))) ∧
      Tendsto (fun k => (u (φ k) : G n)⁻¹ *
        (a (φ k) * b (φ k)) * (u (φ k) : G n)) atTop (𝓝 1) := by
  let : SecondCountableTopology H :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨u₀, hu₀, φ, hφ, hlim⟩ := hK.tendsto_subseq hu
  have hulim : Tendsto (fun k => (u (φ k) : G n)) atTop (𝓝 (u₀ : G n)) :=
    continuous_subtype_val.continuousAt.tendsto.comp hlim
  have hablim : Tendsto (fun k => a (φ k) * b (φ k)) atTop (𝓝 (1 : G n)) := by
    simpa only [one_mul, Function.comp_def] using
      (ha.comp hφ.tendsto_atTop).mul (hb.comp hφ.tendsto_atTop)
  have hfulllim : Tendsto (fun k => a (φ k) * b (φ k) * (u (φ k) : G n))
      atTop (𝓝 (u₀ : G n)) := by
    simpa only [one_mul] using hablim.mul hulim
  have hact : Continuous (fun g : G n => rightAction x g) := by
    exact (continuous_rightAction_uncurry n).comp (continuous_const.prodMk continuous_id)
  refine ⟨u₀, hu₀, φ, hφ, hact.continuousAt.tendsto.comp hulim,
    hact.continuousAt.tendsto.comp hfulllim, ?_⟩
  simpa only [mul_one, inv_mul_cancel] using (hulim.inv.mul hablim).mul hulim

/-- The comparison does not identify the invariant mean with a global
constant; it uses the genuine value at each corrected generic point. -/
theorem exists_corrected_mean_comparison_subsequence {n : ℕ}
    (H : Subgroup (G n)) (K : Set H) (hK : IsCompact K)
    (u : ℕ → H) (hu : ∀ k, u k ∈ K)
    (a b : ℕ → G n) (ha : Tendsto a atTop (𝓝 1)) (hb : Tendsto b atTop (𝓝 1))
    (x : X n) (q F : X n → ℝ) (hF : Continuous F)
    (E : Set (X n)) (ε η : ℝ) (hη : 0 < η)
    (happrox : ∀ y ∈ E, |q y - F y| ≤ ε)
    (hgood : ∀ k, rightAction x (u k : G n) ∈ E ∧
      rightAction x (a k * b k * (u k : G n)) ∈ E) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᶠ k in atTop,
        |q (rightAction x (u (φ k) : G n)) -
          q (rightAction x (a (φ k) * b (φ k) * (u (φ k) : G n)))| ≤ 2 * ε + η := by
  obtain ⟨u₀, _hu₀, φ, hφ, hfirst, hsecond, _hrelative⟩ :=
    exists_common_corrected_pair_limit H K hK u hu a b ha hb x
  refine ⟨φ, hφ, ?_⟩
  exact eventually_invariant_means_close q F E ε η hη happrox
    _ _ (rightAction x (u₀ : G n)) hF.continuousAt hfirst hsecond
    (Eventually.of_forall fun k => hgood (φ k))

end DukePrimeDegree

end

end OAI
