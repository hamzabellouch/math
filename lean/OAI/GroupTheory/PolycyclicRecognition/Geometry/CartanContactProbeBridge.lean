import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCompactProbeBridge
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequenceVolumeComparison

namespace OAI

/-! # The bridge at the prescribed inward contact pivot -/

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

/-- The scalar action is constructed, and the pivot is explicitly
`r (1-cδ) h₀`. Its logarithm has a uniform linear bound for `cδ ≤ 1`.
Only the cited exponential, Dynkin and representation inputs remain. -/
theorem exists_contact_pivot_probe_bridge
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {d : ℕ} (σ : (Fin d → ℝ) →ₗ[ℝ] cartanRootIdeal H)
    {Z : Set (Fin d → ℝ)} (hZ : IsCompact Z)
    (letter : Fin M.letterCount) (h₀ : H) (hq : 0 ≤ M.weight letter h₀)
    {c : ℝ} (hc : 0 ≤ c)
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ S : H → MulAut F.N.carrier,
      (∀ h v, S h (F.ExpN (F.N.equiv v)) =
        F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v))) ∧
      ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in atTop, ∀ δ : ℝ, 0 ≤ δ → c * δ ≤ 1 →
          ∀ (n i : F.N.carrier) (x : G) (t : ℝ) (z : Fin d → ℝ),
          |t| ≤ R j * Real.exp ((1 + δ) * (M.weight letter h₀) * scale j) → z ∈ Z →
          let h := (scale j * (1 - c * δ)) • h₀
          dist (x * (F.inclusionN (coneProbeFirst (S h) n i (F.ExpN (F.N.equiv (σ z)))) *
                F.inclusionD (F.ExpD (F.D.equiv h))))
            (x * (F.inclusionN (n * S h i * F.ExpN (F.N.equiv (t • M.letter letter))) *
                F.inclusionD (F.ExpD (F.D.equiv h)))) ≤
            (C * δ + D * ε) * scale j := by
  obtain ⟨⟨chart, hchart⟩, _⟩ := haarN.2 F.ExpN F.isExpN
    (F.N.tangent_nilpotent (cartanRootIdeal_nilpotent H T))
  have hbij : Function.Bijective F.ExpN := funext hchart ▸ chart.bijective
  let S : H → MulAut F.N.carrier := fun h =>
    integrateNilpotentLieEquiv F.N.equiv F.ExpN hbij dynkinN F.isExpN M.bound_zero
      (cartanIdealWeightDilation T H h)
  have hS (h : H) (v : cartanRootIdeal H) : S h (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)) :=
    integrateNilpotentLieEquiv_apply_exp F.N.equiv F.ExpN hbij dynkinN F.isExpN
      M.bound_zero (cartanIdealWeightDilation T H h) v
  let B := ‖(finBasis ℝ H).equivFun h₀‖
  let RH := fun n => (B + 1) * (1 + scale n) ^ 1
  have hB : 0 ≤ B := norm_nonneg _
  have hRH0 : ∀ n, 0 ≤ RH n := fun n =>
    mul_nonneg (by linarith) (pow_nonneg (by linarith [hscale0 n]) _)
  have hRH : HasSubexponentialUpperBoundSeq scale RH :=
    (subexponential_upper_polynomial (by linarith : 0 < B + 1) 1).along_sequence hs
  obtain ⟨C, D, hC, hD, hb⟩ := exists_compact_source_probe_bridge_bound T M F
    hExpG realize haarN haarD dynkinN b₀ σ hZ letter hq hc scale RH R hs
    hscale0 hRH0 hR0 hRH hR
  refine ⟨S, hS, C, D, hC, hD, ?_⟩
  intro ε hε
  filter_upwards [hb ε hε] with j hj
  intro δ hδ hδc n i x t z ht hz
  let h := (scale j * (1 - c * δ)) • h₀
  have hfac : 0 ≤ 1 - c * δ := sub_nonneg.mpr hδc
  have hh : ‖(finBasis ℝ H).equivFun h‖ ≤ RH j := by
    simp only [h, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hscale0 j) hfac)]
    change scale j * (1 - c * δ) * B ≤ (B + 1) * (1 + scale j) ^ 1
    have hmul := mul_nonneg hc hδ
    have h₁ := mul_le_mul_of_nonneg_left (show 1 - c * δ ≤ 1 by linarith) (hscale0 j)
    have h₂ := mul_le_mul_of_nonneg_right h₁ hB
    nlinarith [hscale0 j]
  have hweight : M.weight letter h = (1 - c * δ) * (M.weight letter h₀) * scale j := by
    simp only [h, map_smul, smul_eq_mul]
    ring
  exact hj δ hδ h (S h) n i x t z hh (hS h) hweight ht hz

end PolycyclicRecognition

end

end OAI
