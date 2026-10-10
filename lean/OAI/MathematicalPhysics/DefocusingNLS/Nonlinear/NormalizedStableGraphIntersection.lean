import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FlatStableGraphIntersection

namespace OAI

/-! # Selecting parameters using unnormalized coordinates of the flat graph -/

open Set Metric
namespace DefocusingNLS
local notation "Params" => ProfileSymmetryParameters
local notation "Radius" => {L : ℝ // 1 ≤ L}

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem stableFrameProjection_normalize (K : ℝ)
    (ζ : V →L[ℝ] FourierL2) (κ : FourierL2 →L[ℝ] V) :
    stableFrameProjection (K • ζ) κ = stableFrameProjection ζ (K • κ) := by
  ext f
  simp only [stableFrameProjection, sub_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply,
    smul_apply, map_smul]

theorem normalized_flatStableGraph_intersection
    (C : Params ≃L[ℝ] V) (r ρ L₀ ε ν η W K : ℝ)
    (hr : 0 ≤ r) (hν : 0 ≤ ν) (hK : 0 < K) (hW : W ≤ ρ / 4)
    (κ : Radius → FourierL2 →L[ℝ] V) (ζ : Radius → V →L[ℝ] FourierL2)
    (hκc : Continuous (fun q : Radius × FourierL2 => κ q.1 q.2))
    (hζc : ContinuousOn ζ {L : Radius | L₀ ≤ L.1})
    (hinv : ∀ L : Radius, L₀ ≤ L.1 → ∀ v, (K • κ L) (ζ L v) = v)
    (G : CutoffStableParameter ρ L₀ (fun L => K • κ L) → FourierL2)
    (hGc : Continuous G)
    (hGstable : ∀ q, stableFrameProjection (ζ q.1.1) (K • κ q.1.1) (G q) = q.1.2)
    (hGflat : ∀ q, ‖(K • κ q.1.1) (G q)‖ ≤ ν * (‖q.1.2‖ + 2 * η) + 2 * η)
    (L : closedBall (0 : Params) r → Radius) (hLc : Continuous L)
    (hL : ∀ p, L₀ ≤ (L p).1)
    (f : closedBall (0 : Params) r → FourierL2) (hfc : Continuous f)
    (hwbound : ∀ p, ‖stableFrameProjection (ζ (L p)) (K • κ (L p)) (f p)‖ ≤ W)
    (herror : ∀ p, ‖κ (L p) (f p) - C p.1‖ ≤ ε)
    (hsmall : ‖C.symm.toContinuousLinearMap‖ *
      (ε + (ν * (W + 2 * η) + 2 * η) / K) ≤ r) :
    ∃ p, ∃ q : CutoffStableParameter ρ L₀ (fun L => K • κ L),
      q.1.1 = L p ∧ G q = f p := by
  let w := fun p => stableFrameProjection (ζ (L p)) (K • κ (L p)) (f p)
  have hzc : Continuous (fun p => ζ (L p)) := hζc.comp_continuous hLc hL
  have hpc : Continuous (fun p => (K • κ (L p)) (f p)) :=
    continuous_const.smul (hκc.comp (hLc.prodMk hfc))
  have hwc : Continuous w := hfc.sub (hzc.clm_apply hpc)
  let Q := fun p : closedBall (0 : Params) r =>
    (⟨(L p, w p), hL p, (hwbound p).trans hW,
      stableFrameProjection_coordinate _ _ (hinv (L p) (hL p)) (f p)⟩ :
        CutoffStableParameter ρ L₀ (fun L => K • κ L))
  have hQc : Continuous Q := (hLc.prodMk hwc).subtype_mk _
  have hgb (p : closedBall (0 : Params) r) :
      ‖κ (L p) (G (Q p))‖ ≤ (ν * (W + 2 * η) + 2 * η) / K := by
    apply (le_div_iff₀ hK).mpr
    have hn := hGflat (Q p)
    simp only [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hK] at hn
    apply (show ‖κ (L p) (G (Q p))‖ * K = K * ‖κ (L p) (G (Q p))‖ by ring).le.trans
    exact hn.trans (add_le_add (mul_le_mul_of_nonneg_left
      (add_le_add (hwbound p) le_rfl) hν) le_rfl)
  have hgs (p : closedBall (0 : Params) r) :
      stableFrameProjection (K • ζ (L p)) (κ (L p)) (G (Q p)) =
        stableFrameProjection (K • ζ (L p)) (κ (L p)) (f p) := by
    simp only [stableFrameProjection_normalize]
    exact hGstable (Q p)
  obtain ⟨p, hp⟩ := physical_parameter_zero_of_coordinate_bound C r ε
    ((ν * (W + 2 * η) + 2 * η) / K) hr f (fun p => G (Q p))
    (fun p => κ (L p)) (fun p => K • ζ (L p)) hfc (hGc.comp hQc)
    (hκc.comp ((hLc.comp continuous_fst).prodMk continuous_snd)) herror hgb hgs hsmall
  exact ⟨p, Q p, rfl, hp.symm⟩

end DefocusingNLS

end OAI
