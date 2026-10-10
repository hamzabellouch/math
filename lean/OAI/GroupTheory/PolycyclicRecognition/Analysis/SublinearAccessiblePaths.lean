import OAI.GroupTheory.PolycyclicRecognition.Analysis.AccessibleProfilePaths
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SegmentProfileLegs

namespace OAI

/-! # Sublinear profile errors on the complete accessible endpoint paths -/

noncomputable section

namespace PolycyclicRecognition

open Module Set Metric Filter
open scoped Topology NNReal

/-- The vanishing good-profile errors on all support legs give exactly the
relative height estimate required by the accessible-volume comparison.
Only successful endpoints are used; the submersive endpoint map is unchanged. -/
theorem sublinear_accessible_word_paths
    {L N G I W : Type*} [LieRing L] [LieAlgebra ℝ L] [Group N] [Group G]
    [PseudoMetricSpace G] [IsTopologicalGroup G]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {n m c : ℕ}
    (basis : ℝ → Basis (Fin n) ℝ L) (Exp : L → N) (hzero : Exp 0 = 1)
    (a : DynkinCoefficients c 2)
    (hm : ∀ u v, Exp (finiteDynkinPolynomial a ![u, v]) = Exp u * Exp v)
    (X : I → L) (s : I → ℝ) (letters : Fin m → I)
    (ι : N →* G) (hinj : Function.Injective ι) (x d₀ : ℝ → G)
    (A : ℝ → Set N) (n₀ : ℝ → N) (hn₀ : ∀ r, n₀ r ∈ A r)
    (sample : ℝ → ℕ → ℝ → N)
    (hsub : ∀ r j u v, sample r j u * (sample r j v)⁻¹ = sample r j (u - v))
    (hsample : ∀ r, ∀ j : Fin m, ∀ u, sample r j.val u =
      Exp (u • (Real.exp (r * s (letters j)) • X (letters j))))
    (d : Fin m → ℝ → G) (hd : ∀ i, Continuous (d i)) (hd₀ : ∀ i, d i 0 = 1)
    (hf : ∀ r, ∀ i : Fin m, Continuous (fun t => ι (sample r i.val t)))
    (hf₀ : ∀ r, ∀ i : Fin m, ι (sample r i.val 0) = 1)
    (J : ℝ → G → W) {K : ℝ≥0} (hJ : ∀ r, LipschitzWith K (J r))
    (center : ℝ → W) (w₀ : W) (E : Set W)
    (ζ : ℝ → ℝ) (hζ : Tendsto ζ atTop (𝓝 0))
    {speed switchError ρ : ℝ} (hspeed : 0 ≤ speed) (hswitchError : 0 ≤ switchError)
    (hbase : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r,
      ∃ w ∈ E, ‖J r (x r * ι u * d₀ r) - center r - r • w‖ ≤ r * (ζ r + η))
    (hstart : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop,
      ‖J r (x r * ι (n₀ r) * d₀ r) - center r - r • w₀‖ ≤ r * (ζ r + η))
    (hleg : ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m,
      ∀ t : unitInterval, ∃ w ∈ E,
        ‖J r ((x r * ι u * d₀ r) * d i (r * t)) - center r - r • w‖ ≤ r * (ζ r + η))
    (hmetric : ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m, ∀ b : ℝ,
      |b| ≤ 2 * ρ → u * sample r i.val b ∈ A r →
      PathMetricBound (supportVisitPath (d i) (hd i) (hd₀ i)
        (fun t => ι (sample r i.val t)) (hf r i) (hf₀ r i) (x r * ι u) (d₀ r) r b)
        (speed * r) (speed * (1 + Real.log (2 + r))))
    (hswitch : ∀ᶠ r in atTop, ∀ u ∈ A r, ∀ i : Fin m, ∀ b : ℝ,
      |b| ≤ 2 * ρ → ∀ t : unitInterval,
      dist ((x r * ι u) * ι (sample r i.val ((t : ℝ) * b)) * (d₀ r * d i r))
        ((x r * ι u * d₀ r) * d i r) ≤ switchError * (1 + Real.log (2 + r)))
    (C : ℝ → Set (Fin n → ℝ))
    (hC : ∀ᶠ r in atTop, ∀ y ∈ C r, ∃ t ∈ closedBall (0 : Fin (m + m) → ℝ) ρ,
      SwitchSuccessful (fun _ => A r) 0 m (n₀ r) (sampledSwitchParameters (sample r) m t) ∧
      differenceAmplitudeWordEndpoint a letters
        (basisBracket (basis r), fun i => (basis r).equivFun (Real.exp (r * s i) • X i)) t = y) :
    ∀ η : ℝ, 0 < η → ∀ᶠ r in atTop, ∀ y ∈ C r,
      ∃ γ : Path (x r * ι (n₀ r) * d₀ r)
        (x r * ι (n₀ r * Exp ((basis r).equivFun.symm y)) * d₀ r),
        PathMetricBound γ ((speed * 2 ^ m) * r)
          ((speed * 2 ^ m) * (1 + Real.log (2 + r))) ∧
        ∀ u, ∃ w ∈ (fun z => z - w₀) '' E,
          ‖J r (γ u) - J r (x r * ι (n₀ r) * d₀ r) - r • w‖ ≤
            η * r + K * switchError * (1 + Real.log (2 + r)) := by
  intro η hη
  have hη4 : 0 < η / 4 := by positivity
  filter_upwards [hbase (η / 4) hη4, hstart (η / 4) hη4, hleg (η / 4) hη4,
    hmetric, hswitch, hC, hζ.eventually (gt_mem_nhds hη4),
    eventually_ge_atTop (0 : ℝ)] with r hb hst hl hmtr hsw hCr hz hr y hy
  have hlog : 0 ≤ 1 + Real.log (2 + r) := by
    have hh := Real.log_nonneg (show 1 ≤ 2 + r by linarith)
    linarith
  obtain ⟨γ, hγ, hheight⟩ := accessible_word_profile_paths (basis r) Exp hzero a hm
    X s r letters ι hinj (x r) (d₀ r) (A r) (n₀ r) (hn₀ r)
    (sample r) (hsub r) (hsample r) d hd hd₀ (hf r) (hf₀ r) (J r) (hJ r)
    (center r) w₀ E (mul_nonneg hspeed hr) (mul_nonneg hspeed hlog)
    (mul_nonneg hswitchError hlog) hb hst hl hmtr hsw (C r) hCr y hy
  refine ⟨γ, ?_, ?_⟩
  · convert hγ using 1 <;> ring
  · intro u
    obtain ⟨w, hw, hh⟩ := hheight u
    refine ⟨w, hw, hh.trans ?_⟩
    nlinarith

end PolycyclicRecognition

end

end OAI
