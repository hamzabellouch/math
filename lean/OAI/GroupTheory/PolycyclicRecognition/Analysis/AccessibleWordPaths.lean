import OAI.GroupTheory.PolycyclicRecognition.Analysis.SuccessfulSamplePaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.RescaledWordEndpoints

namespace OAI

/-! # Actual paths to compact successful polynomial images -/

noncomputable section

namespace PolycyclicRecognition

open Module Set Metric

/-- The successful parameter witnesses give paths to every point of the
actual rescaled exponential image. No inverse to the polynomial endpoint map
is chosen and no extra good-sheet hypothesis is introduced. -/
theorem accessible_word_paths
    {L N G I : Type*} [LieRing L] [LieAlgebra ℝ L] [Group N] [Group G]
    [PseudoMetricSpace G] [IsTopologicalGroup G] {n m c : ℕ}
    (basis : Basis (Fin n) ℝ L) (Exp : L → N) (hzero : Exp 0 = 1)
    (a : DynkinCoefficients c 2)
    (hm : ∀ u v, Exp (finiteDynkinPolynomial a ![u, v]) = Exp u * Exp v)
    (X : I → L) (s : I → ℝ) (r : ℝ) (letters : Fin m → I)
    (ι : N →* G) (hinj : Function.Injective ι) (x d₀ : G)
    (A : Set N) (S : Set G) (n₀ : N) (hn₀ : n₀ ∈ A)
    (sample : ℕ → ℝ → N) (hsub : ∀ j u v, sample j u * (sample j v)⁻¹ = sample j (u - v))
    (hsample : ∀ j : Fin m, ∀ u, sample j.val u =
      Exp (u • (Real.exp (r * s (letters j)) • X (letters j))))
    (d : Fin m → ℝ → G) (hd : ∀ i, Continuous (d i)) (hd₀ : ∀ i, d i 0 = 1)
    (hf : ∀ i : Fin m, Continuous (fun t => ι (sample i.val t)))
    (hf₀ : ∀ i : Fin m, ι (sample i.val 0) = 1)
    {speed error ρ : ℝ} (hspeed : 0 ≤ speed) (herror : 0 ≤ error)
    (hbase : ∀ n ∈ A, x * ι n * d₀ ∈ S)
    (hstep : ∀ n ∈ A, ∀ i : Fin m, ∀ b : ℝ, |b| ≤ 2 * ρ → n * sample i.val b ∈ A →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b) speed error ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b t ∈ S)
    (C : Set (Fin n → ℝ))
    (hC : ∀ y ∈ C, ∃ t ∈ closedBall (0 : Fin (m + m) → ℝ) ρ,
      SwitchSuccessful (fun _ => A) 0 m n₀ (sampledSwitchParameters sample m t) ∧
      differenceAmplitudeWordEndpoint a letters
        (basisBracket basis, fun i => basis.equivFun (Real.exp (r * s i) • X i)) t = y) :
    ∀ y ∈ C, ∃ γ : Path (x * ι n₀ * d₀)
      (x * ι (n₀ * Exp (basis.equivFun.symm y)) * d₀),
      PathMetricBound γ (speed * 2 ^ m) (error * 2 ^ m) ∧ ∀ u, γ u ∈ S := by
  intro y hy
  obtain ⟨t, ht, hs, he⟩ := hC y hy
  obtain ⟨γ, hγ, hS⟩ := successful_sample_path ι x d₀ A S m sample hsub d hd hd₀ hf hf₀
    r hspeed herror hbase hstep hinj n₀ hn₀ t (by simpa using ht) hs
  have hend : switchEndpoint m n₀ (sampledSwitchParameters sample m t) =
      n₀ * Exp (basis.equivFun.symm y) := by
    rw [sampled_rescaled_endpoint_eq basis Exp hzero a hm X s r letters sample hsub hsample, he]
  refine ⟨γ.cast rfl (by rw [hend]), ?_, hS⟩
  exact hγ

end PolycyclicRecognition

end

end OAI
