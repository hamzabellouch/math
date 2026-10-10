import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ContinuousCutoffStableOrbit
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ContinuousCoordinateSequence
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffContinuousLinearization
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffEndpointContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphStepDecay

namespace OAI

/-! # The global stable graph retains its localized physical coordinates -/

open Set Filter Topology
open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

def HasContinuousCoordinateStableOrbits {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp)
    (κ : Radius → FourierL2 →L[ℝ] F) : Prop :=
  ∀ ν : ℝ, 0 < ν → ∃ ρ : ℝ, 0 < ρ ∧ ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 0 < K ∧
    ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ,
    ∃ ζ : Radius → F →L[ℝ] FourierL2,
      let π := fun L => K • κ L
      ContinuousOn ζ {L : Radius | L₀ ≤ L.1} ∧
      Continuous (fun q : Radius × FourierL2 => π q.1 q.2) ∧
      (∀ L : Radius, L₀ ≤ L.1 → (∀ v, π L (ζ L v) = v) ∧ ‖ζ L‖ ≤ 1 ∧ ‖π L‖ ≤ C) ∧
      ∃ G : CutoffStableParameter ρ L₀ π → FourierL2, Continuous G ∧
        ∀ p, ‖G p‖ ≤ 2 * ρ ∧ ‖G p‖ ≤ 4 * (‖p.1.2‖ + 2 * η) ∧ stableFrameProjection (ζ p.1.1) (π p.1.1) (G p) = p.1.2 ∧
          ‖π p.1.1 (G p)‖ ≤ ν * (‖p.1.2‖ + 2 * η) + 2 * η ∧
          ∃ u : ℝ → FourierL2, ∃ hu : ContinuousOn u (Ici 0),
            u 0 = sampledCutoffProfileOrbit a k p.1.1.1 ha1 hk p.1.1.2 χ hχ Qp hQp 0 + G p ∧
            (∀ (S : ℝ) (hS : 0 < S), expandingSlabRestriction u hu S =
              expandingPicard a b k p.1.1.1 S ha hk p.1.1.2 hS.le
                (expandingNonlinearReaction a k p.1.1.1 S ha ha1 hk p.1.1.2 m) (u 0)
                (expandingSlabRestriction u hu S)) ∧
            Tendsto (fun s => ‖u s - sampledCutoffProfileOrbit a k p.1.1.1 ha1 hk p.1.1.2 χ hχ Qp hQp s‖)
              atTop (𝓝 0)

attribute [local irreducible] HasContinuousCoordinateStableOrbits
  HasContinuousTorusCoordinateData cutoffProfileEndpoint expandingPicard
  sampledCutoffProfileOrbit expandingNonlinearReaction

theorem exists_continuous_coordinateStable_orbits {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 hk χ hχ Qp hQp L‖ ≤ Q)
    (T : ℝ≥0) (hT : 0 < (T : ℝ))
    (hratio : 2 * Real.exp (-(2 + a) * T / 2) ≤ 1)
    (κ : Radius → FourierL2 →L[ℝ] F)
    (hlinear : HasContinuousTorusCoordinateData (F := F) T
      (cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T) κ)
    (hnonlinear : HasContinuousCutoffNonlinearSteps a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T) :
    HasContinuousCoordinateStableOrbits (F := F) a b k ha ha1 hk m χ hχ Qp hQp κ := by
  classical
  unfold HasContinuousCoordinateStableOrbits
  intro ν hν
  obtain ⟨δ, Lnl, B, hδ, _, hB, V, h, hcV, hch, hsol, hV, hend, hzero, hlip⟩ := hnonlinear
  obtain ⟨K, hK, C, hC, ρ, hρ, hρδ, hfamily⟩ :=
    exists_continuous_coordinateStable_sequence a δ B ha hδ hB.le T hratio
      (cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T)
      (continuous_cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T) κ hlinear ν hν
  refine ⟨ρ, hρ, C, hC, K, hK, ?_⟩
  intro η hη
  obtain ⟨Lg, ζ, π, hκ, hζc, hπc, hbound, hπζ, hseq⟩ := hfamily η hη
  let L₀ := max Lg Lnl
  let ζ₀ := fun L => ζ L 0
  let π₀ := fun L => K • κ L
  have hpizero (L : Radius) : π L 0 = π₀ L :=
    (hκ L 0).trans (by rw [expandingDiscreteRadius_zero])
  let P := CutoffStableParameter ρ L₀ π₀
  let l : P → Radius := fun p => p.1.1
  let w : P → FourierL2 := fun p => p.1.2
  have hlc : Continuous l := continuous_fst.comp continuous_subtype_val
  have hwc : Continuous w := continuous_snd.comp continuous_subtype_val
  have hl (p : P) : Lg ≤ (l p).1 := (le_max_left _ _).trans p.2.1
  let ln := fun n (p : P) => expandingDiscreteRadius (l p) T n
  have hln (n : ℕ) (p : P) : Lnl ≤ (ln n p).1 :=
    ((le_max_right _ _).trans p.2.1).trans (expandingDiscreteRadius_ge (l p) T n)
  let r := fun n (p : P) => (⟨(ln n p).1, (ln n p).2, hln n p⟩ : {R : ℝ // 1 ≤ R ∧ Lnl ≤ R})
  have hrc (n : ℕ) : Continuous (r n) :=
    (continuous_subtype_val.comp ((continuous_expandingDiscreteRadius T n).comp hlc)).subtype_mk _
  let H := fun p n v => h (r n p, v)
  have hHc (n : ℕ) : Continuous (fun q : P × {v : FourierL2 // ‖v‖ ≤ δ} => H q.1 n q.2) :=
    hch.comp (((hrc n).comp continuous_fst).prodMk continuous_snd)
  obtain ⟨z, hzc, hz0, hzstep, hzn, hsharp, hflat⟩ := hseq P l hlc hl H hHc
    (fun p n d hd hdδ v u hv hu => hlip d hd hdδ (r n p) v u hv hu)
    (fun p n v hv => hzero (r n p, v) hv)
    w hwc (fun p => p.2.2.1) (fun p => by
      rw [hpizero]
      exact p.2.2.2)
  refine ⟨L₀, ζ₀, ?_, ?_, ?_, (fun p => z p 0), hzc 0, ?_⟩
  · apply (hζc 0).mono
    intro L hL
    exact (le_max_left Lg Lnl).trans hL
  · have he : (fun p : Radius × FourierL2 => π₀ p.1 p.2) =
        (fun p : Radius × FourierL2 => π p.1 0 p.2) := by
      funext p
      rw [hpizero]
    rw [he]
    exact hπc 0
  · intro L hL
    have hLg : Lg ≤ L.1 := (le_max_left _ _).trans hL
    simpa only [hpizero] using
      (show (∀ v, π L 0 (ζ L 0 v) = v) ∧ ‖ζ L 0‖ ≤ 1 ∧ ‖π L 0‖ ≤ C from
        ⟨hπζ L hLg 0, (hbound L hLg 0).1, (hbound L hLg 0).2⟩)
  · intro p
    refine ⟨by simpa using hzn p 0, by simpa using hsharp p 0, ?_, ?_, ?_⟩
    · simpa only [hpizero] using hz0 p
    · simpa only [hpizero] using hflat p
    · have hzδ (n : ℕ) : ‖z p n‖ ≤ δ := (hzn p n).trans ((mul_le_of_le_one_right
        (by positivity : 0 ≤ 2 * ρ) (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num))).trans hρδ)
      let Z := fun n => (⟨z p n, hzδ n⟩ : {f : FourierL2 // ‖f‖ ≤ δ})
      let W := fun n => V (r n p, Z n)
      have hWM (n : ℕ) : W n ⟨T, T.2, le_rfl⟩ = z p (n + 1) := by
        calc
          _ = cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T (ln n p) (z p n) +
              H p n (Z n) := hend (r n p, Z n)
          _ = cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T (ln n p) (z p n) +
              cutoffRemainderExtension δ (H p) n (z p n) := by
            rw [cutoffRemainderExtension, dite_eq_left (hzδ n)]
          _ = _ := (hzstep p n).symm
      have hWbound (n : ℕ) : ‖W n‖ ≤ B * (‖z p n‖ +
          (expandingRadius (l p).1 ((n : ℝ) * T)) ^ (-2 - a)) := hV (r n p, Z n)
      have hr : Real.exp (-(2 + a) * T / 2) ≤ 1 / 2 := by linarith
      have hWgeo := cutoffStep_path_geometric_bound a (l p).1 T B (2 * ρ)
        (lt_of_lt_of_le zero_lt_one (l p).2) hB.le hr (z p) W (hzn p) hWbound
      exact exists_cutoffGlobal_orbit_of_steps a b k (l p).1 T ha ha1 hk (l p).2 hT m χ hχ Qp hQp
        (z p) W hWM (fun n => hsol (r n p, Z n))
        (B * (2 * ρ + (l p).1 ^ (-2 - a))) (1 / 2) (by norm_num) (by norm_num) hWgeo

end DefocusingNLS

end OAI
