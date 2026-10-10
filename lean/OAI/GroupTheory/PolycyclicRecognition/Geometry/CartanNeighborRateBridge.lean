import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSampledBridge

namespace OAI

/-! # Contact bridges at the original neighboring-letter rate -/

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

/-- The original neighboring-sheet amplitude has exponent `q + B * δ`.
At a positive contact support this gives the same small bridge as the
normalized exponent, after a proved change of the enlargement parameter. -/
theorem exists_sampled_contact_bridge_at_neighbor_rate
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (S : H → MulAut F.N.carrier)
    (hS : ∀ h v, S h (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {d : ℕ} (σ : (Fin d → ℝ) →ₗ[ℝ] cartanRootIdeal H)
    {Z : Set (Fin d → ℝ)} (hZ : IsCompact Z)
    (letter : Fin M.letterCount) (h₀ : H) (hq : 0 < M.weight letter h₀)
    {c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B)
    (scale R : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale0 : ∀ n, 0 ≤ scale n) (hR0 : ∀ n, 0 ≤ R n)
    (hR : HasSubexponentialUpperBoundSeq scale R) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ ε : ℝ, 0 < ε →
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
  obtain ⟨C, D, hC, hD, hb⟩ := exists_sampled_contact_pivot_bridge T M F
    hExpG realize haarN haarD dynkinN S hS b₀ σ hZ letter h₀ hq.le
    (div_nonneg hc ha.le) scale R hs hscale0 hR0 hR
  refine ⟨C * a, D, mul_nonneg hC ha.le, hD, ?_⟩
  intro ε hε
  filter_upwards [hb ε hε] with j hj
  intro δ hδ hδc u i sample x t z ht hz
  have hid : (c / a) * (a * δ) = c * δ := by
    field_simp
  have ht' : |t| ≤ R j * Real.exp ((1 + a * δ) * (M.weight letter h₀) * scale j) := by
    refine ht.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hR0 j))
    apply mul_le_mul_of_nonneg_right _ (hscale0 j)
    nlinarith
  have he := hj (a * δ) (mul_nonneg ha.le hδ) (by rw [hid]; exact hδc)
    u i sample x t z ht' hz
  dsimp only at he ⊢
  rw [hid] at he
  convert he using 1
  ring

end PolycyclicRecognition

end

end OAI
