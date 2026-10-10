import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformCompactProbeBridge
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSampledBridge

namespace OAI

/-! # Uniform contact-bridge constants before the source choices -/

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra Filter Set
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

/-- The constants precede the section, the scale and the subexponential
radius. Only the eventual threshold depends on those choices. The estimate
uses the original center, sampled root and actual neighboring-letter rate. -/
theorem exists_uniform_sampled_contact_bridge
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (S : H → MulAut F.N.carrier)
    (hS : ∀ h v, S h (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (letter : Fin M.letterCount) (h₀ : H) (hq : 0 < M.weight letter h₀)
    {c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ {d : ℕ} (σ : (Fin d → ℝ) →ₗ[ℝ] cartanRootIdeal H)
        {Z : Set (Fin d → ℝ)}, IsCompact Z →
      ∀ (scale R : ℕ → ℝ), Tendsto scale atTop atTop →
        (∀ n, 0 ≤ scale n) → (∀ n, 0 ≤ R n) →
        HasSubexponentialUpperBoundSeq scale R →
      ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, ∀ δ : ℝ, 0 ≤ δ → c * δ ≤ 1 →
        ∀ (u i sample : F.N.carrier) (x : G) (t : ℝ) (z : Fin d → ℝ),
        |t| ≤ R j * Real.exp ((M.weight letter h₀ + B * δ) * scale j) → z ∈ Z →
        let h := (scale j * (1 - c * δ)) • h₀
        let k := (S h).symm (F.ExpN (F.N.equiv (t • M.letter letter)))
        dist (x * F.inclusionN (sample * coneProbeSecond (S h) u i k) *
            F.inclusionD (F.ExpD (F.D.equiv h)))
          (x * F.inclusionN
            (sample * coneProbeFirst (S h) u i (F.ExpN (F.N.equiv (σ z)))) *
            F.inclusionD (F.ExpD (F.D.equiv h))) ≤
          (C * δ + D * ε) * scale j := by
  let a : ℝ := 1 + B / M.weight letter h₀
  have ha : 0 < a := by dsimp [a]; positivity
  have haq : a * M.weight letter h₀ = M.weight letter h₀ + B := by
    dsimp [a]
    field_simp
  obtain ⟨C, D, hC, hD, hb⟩ := exists_uniform_compact_source_probe_bridge_bound T M F
    hExpG realize haarN haarD dynkinN b₀ letter hq.le (div_nonneg hc ha.le)
  refine ⟨C * a, D, mul_nonneg hC ha.le, hD, ?_⟩
  intro d σ Z hZ scale R hs hscale0 hR0 hR ε hε
  let b := ‖(finBasis ℝ H).equivFun h₀‖
  let RH := fun n => (b + 1) * (1 + scale n) ^ 1
  have hb0 : 0 ≤ b := norm_nonneg _
  have hRH0 : ∀ n, 0 ≤ RH n := fun n =>
    mul_nonneg (by linarith) (pow_nonneg (by linarith [hscale0 n]) _)
  have hRH : HasSubexponentialUpperBoundSeq scale RH :=
    (subexponential_upper_polynomial (by linarith : 0 < b + 1) 1).along_sequence hs
  filter_upwards [hb σ hZ scale RH R hs hscale0 hRH0 hR0 hRH hR ε hε] with j hj
  intro δ hδ hδc u i sample x t z ht hz
  let h := (scale j * (1 - c * δ)) • h₀
  have hfac : 0 ≤ 1 - c * δ := sub_nonneg.mpr hδc
  have hh : ‖(finBasis ℝ H).equivFun h‖ ≤ RH j := by
    simp only [h, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hscale0 j) hfac)]
    change scale j * (1 - c * δ) * b ≤ (b + 1) * (1 + scale j) ^ 1
    have hmul := mul_nonneg hc hδ
    have h₁ := mul_le_mul_of_nonneg_left (show 1 - c * δ ≤ 1 by linarith) (hscale0 j)
    have h₂ := mul_le_mul_of_nonneg_right h₁ hb0
    nlinarith [hscale0 j]
  have hid : (c / a) * (a * δ) = c * δ := by field_simp
  have hw : M.weight letter h =
      (1 - (c / a) * (a * δ)) * (M.weight letter h₀) * scale j := by
    rw [hid]
    simp only [h, map_smul, smul_eq_mul]
    ring
  have ht' : |t| ≤ R j * Real.exp ((1 + a * δ) * (M.weight letter h₀) * scale j) := by
    refine ht.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hR0 j))
    apply mul_le_mul_of_nonneg_right _ (hscale0 j)
    nlinarith
  have he := hj (a * δ) (mul_nonneg ha.le hδ) h (S h) u i
    (x * F.inclusionN sample) t z hh (hS h) hw ht' hz
  dsimp only at he ⊢
  rw [show (C * a) * δ + D * ε = C * (a * δ) + D * ε by ring,
    sampled_coneProbe_dist]
  simpa only [MulEquiv.apply_symm_apply, mul_assoc] using he

end PolycyclicRecognition

end

end OAI
