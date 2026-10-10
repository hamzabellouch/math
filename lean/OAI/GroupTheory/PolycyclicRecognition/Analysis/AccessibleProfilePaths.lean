import OAI.GroupTheory.PolycyclicRecognition.Analysis.AccessibleWordPaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SupportVisitImage
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CenteredProfilePaths

namespace OAI

/-! # Successful endpoint paths with their actual relative profile bounds -/

noncomputable section

namespace PolycyclicRecognition

open Module Set Metric
open scoped NNReal

/-- Successful parameters supply paths to every retained polynomial endpoint.
The two good-sheet leg estimates and the short switch estimate control the
whole image; subtracting the actual starting image costs its profile error. -/
theorem accessible_word_profile_paths
    {L N G I W : Type*} [LieRing L] [LieAlgebra ℝ L] [Group N] [Group G]
    [PseudoMetricSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n m c : ℕ}
    (basis : Basis (Fin n) ℝ L) (Exp : L → N) (hzero : Exp 0 = 1)
    (a : DynkinCoefficients c 2)
    (hm : ∀ u v, Exp (finiteDynkinPolynomial a ![u, v]) = Exp u * Exp v)
    (X : I → L) (s : I → ℝ) (r : ℝ) (letters : Fin m → I)
    (ι : N →* G) (hinj : Function.Injective ι) (x d₀ : G)
    (A : Set N) (n₀ : N) (hn₀ : n₀ ∈ A)
    (sample : ℕ → ℝ → N) (hsub : ∀ j u v, sample j u * (sample j v)⁻¹ = sample j (u - v))
    (hsample : ∀ j : Fin m, ∀ u, sample j.val u =
      Exp (u • (Real.exp (r * s (letters j)) • X (letters j))))
    (d : Fin m → ℝ → G) (hd : ∀ i, Continuous (d i)) (hd₀ : ∀ i, d i 0 = 1)
    (hf : ∀ i : Fin m, Continuous (fun t => ι (sample i.val t)))
    (hf₀ : ∀ i : Fin m, ι (sample i.val 0) = 1)
    (J : G → W) {K : ℝ≥0} (hJ : LipschitzWith K J)
    (center w₀ : W) (E : Set W)
    {speed error ρ B B₀ δ : ℝ} (hspeed : 0 ≤ speed) (herror : 0 ≤ error) (hδ : 0 ≤ δ)
    (hbase : ∀ n ∈ A, ∃ w ∈ E, ‖J (x * ι n * d₀) - center - r • w‖ ≤ B)
    (hstart : ‖J (x * ι n₀ * d₀) - center - r • w₀‖ ≤ B₀)
    (hleg : ∀ n ∈ A, ∀ i : Fin m, ∀ t : unitInterval,
      ∃ w ∈ E, ‖J ((x * ι n * d₀) * d i (r * t)) - center - r • w‖ ≤ B)
    (hmetric : ∀ n ∈ A, ∀ i : Fin m, ∀ b : ℝ, |b| ≤ 2 * ρ → n * sample i.val b ∈ A →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b) speed error)
    (hswitch : ∀ n ∈ A, ∀ i : Fin m, ∀ b : ℝ, |b| ≤ 2 * ρ → ∀ t : unitInterval,
      dist ((x * ι n) * ι (sample i.val ((t : ℝ) * b)) * (d₀ * d i r))
        ((x * ι n * d₀) * d i r) ≤ δ)
    (C : Set (Fin n → ℝ))
    (hC : ∀ y ∈ C, ∃ t ∈ closedBall (0 : Fin (m + m) → ℝ) ρ,
      SwitchSuccessful (fun _ => A) 0 m n₀ (sampledSwitchParameters sample m t) ∧
      differenceAmplitudeWordEndpoint a letters
        (basisBracket basis, fun i => basis.equivFun (Real.exp (r * s i) • X i)) t = y) :
    ∀ y ∈ C, ∃ γ : Path (x * ι n₀ * d₀)
      (x * ι (n₀ * Exp (basis.equivFun.symm y)) * d₀),
      PathMetricBound γ (speed * 2 ^ m) (error * 2 ^ m) ∧
      ∀ u, ∃ w ∈ (fun z => z - w₀) '' E,
        ‖J (γ u) - J (x * ι n₀ * d₀) - r • w‖ ≤ B + K * δ + B₀ := by
  let S := {g : G | ∃ w ∈ E, ‖J g - center - r • w‖ ≤ B + K * δ}
  have hnonneg : 0 ≤ (K : ℝ) * δ := mul_nonneg K.coe_nonneg hδ
  have hbase' : ∀ n ∈ A, x * ι n * d₀ ∈ S := by
    intro n hn
    obtain ⟨w, hw, hh⟩ := hbase n hn
    exact ⟨w, hw, hh.trans (le_add_of_nonneg_right hnonneg)⟩
  have hstep : ∀ n ∈ A, ∀ i : Fin m, ∀ b : ℝ, |b| ≤ 2 * ρ → n * sample i.val b ∈ A →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b) speed error ∧
      ∀ t, supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample i.val t)) (hf i) (hf₀ i) (x * ι n) d₀ r b t ∈ S := by
    intro n hn i b hb hn'
    refine ⟨hmetric n hn i b hb hn', ?_⟩
    apply supportVisitPath_image_bound (d i) (hd i) (hd₀ i)
      (fun t => ι (sample i.val t)) (hf i) (hf₀ i) J hJ
      (x * ι n) d₀ r b center E hδ (hleg n hn i) ?_ (hswitch n hn i b hb)
    simpa only [map_mul, mul_assoc] using hleg (n * sample i.val b) hn' i
  intro y hy
  obtain ⟨γ, hγ, hγS⟩ := accessible_word_paths basis Exp hzero a hm X s r letters
    ι hinj x d₀ A S n₀ hn₀ sample hsub hsample d hd hd₀ hf hf₀
    hspeed herror hbase' hstep C hC y hy
  exact ⟨γ, hγ, centered_path_height_bound γ J center w₀ E r (B + K * δ) B₀ hstart hγS⟩

end PolycyclicRecognition

end

end OAI
