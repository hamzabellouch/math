import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalStartingChartBounds
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalModulationBudget
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.NormalizedStableGraphIntersection
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.NormalizedFrameLowerBound
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalCutoffOrbit

namespace OAI

/-! # An open physical family from the actual flat stable graph and symmetry frame -/

open Set Metric Filter Topology
open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}
local notation "Params" => ProfileSymmetryParameters

attribute [local irreducible] physicalStartingPerturbation physicalStartingOperator
  physicalReferenceData modulatedCutoffProfile sampledPhysicalFrame
  expandingCoordinates expandingPicard expandingNonlinearReaction
  sampledCutoffProfileOrbit

theorem physical_cutoff_orbit_open_of_frame
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (hS : HasCartesianSymbol (-2 * a) Q)
    (F : Params →L[ℝ] HomogeneousY a k)
    (hphys : ∀ p y, homogeneousPhysicalCLM a k ha ha1 hk (F p) y =
      (p.1 : ℂ) * (Complex.I * Q y) +
      (p.2.2 : ℂ) * (((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y) +
      cartesianDerivative p.2.1 Q y)
    (π : HomogeneousY a k →L[ℝ] V)
    (C : Params ≃L[ℝ] V)
    (hC : ∀ p, C p = π (F (physicalModulationParameterEquiv b p)))
    (hgraph : HasContinuousCoordinateStableOrbits a b k ha ha1 hk m χ hχ Q hQ
      (expandingCoordinates a k ha ha1 hk χ π)) :
    ∃ U : Set FourierL2, U.Nonempty ∧ IsOpen U ∧
      ∀ f ∈ U, HasPhysicalCutoffOrbit a b k ha ha1 hk m χ hχ Q hQ f := by
  let : Nontrivial V := C.toEquiv.symm.nontrivial
  obtain ⟨Jloc, hJloc, hloc⟩ := exists_homogeneousLocalization_bound a k ha ha1 hk χ
  let B := max 1 (‖π‖ * Jloc)
  have hB : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  let κ := expandingCoordinates a k ha ha1 hk χ π
  have hκ (L : Radius) : ‖κ L‖ ≤ B :=
    (expandingCoordinates_norm_le a k Jloc ha ha1 hk hJloc χ π hloc L).trans (le_max_right _ _)
  obtain ⟨A, hA, hnorm⟩ := physicalStartingPerturbation_modulation_bound a k ha ha1 hk
    χ hχ hχzero Q hQ hS
  have hF := physicalFrame_smooth a b k ha ha1 hk Q hQ F hphys
  obtain ⟨E₀, hE₀, hcoord⟩ := physicalStartingPerturbation_modulation_coordinates a b k ha ha1 hk
    χ hχ hχzero hχone Q hQ hS F hphys hF π B hκ
  let D := ‖sobolevToExpanding a k ha hk‖
  let H := ‖C.symm.toContinuousLinearMap‖
  let M := ‖(physicalModulationParameterEquiv b).toContinuousLinearMap‖
  obtain ⟨ν, hν, hbudget⟩ := exists_physical_modulation_budget A B D E₀ H M
    hA hB (norm_nonneg _) hE₀ (norm_nonneg _) (norm_nonneg _)
  obtain ⟨ρ, hρ, Cg, _, K, hK, hg⟩ := hgraph ν hν
  obtain ⟨r, ε, η, J, δ, hr, hrhalf, hrlog, hε, hη, hJ, hδ, hDδ, hW, hsmall⟩ :=
    hbudget ρ K hρ hK
  obtain ⟨L₀, ζ, hζc, hπc, hinv, G, hGc, hG⟩ := hg η hη
  obtain ⟨Lerr, herror⟩ := hcoord ε hε
  let Lbig := max J (max L₀ (max Lerr 2))
  have hJbig : J ≤ Lbig := le_max_left _ _
  have hL₀big : L₀ ≤ Lbig := (le_max_left _ _).trans (le_max_right _ _)
  have hLerrbig : Lerr ≤ Lbig := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have h2big : 2 ≤ Lbig := hJ.trans hJbig
  let R : Radius := ⟨2 * Lbig, by linarith⟩
  have hR : 2 ≤ R.1 := by change 2 ≤ 2 * Lbig; linarith
  let f₀ := physicalReferenceData a k ha ha1 hk χ hχ Q hQ R
  refine ⟨ball f₀ δ, ⟨f₀, mem_ball_self hδ⟩, isOpen_ball, ?_⟩
  intro f hf
  have hdist : ‖f - f₀‖ ≤ δ := (mem_ball_iff_norm.mp hf).le
  let L := fun p : closedBall (0 : Params) r => physicalModulationRadius R p.1
  have hLc : Continuous L := (continuous_physicalModulationRadius R).comp continuous_subtype_val
  have hpbound (p : closedBall (0 : Params) r) : ‖p.1‖ ≤ r := by
    simpa only [mem_closedBall, dist_zero_right] using p.2
  have hLp (p : closedBall (0 : Params) r) : Lbig ≤ (L p).1 := by
    have h := (physicalModulationRadius_bounds R hR p.1 ((hpbound p).trans hrlog)).2.1
    change 2 * Lbig ≤ 2 * (L p).1 at h
    linarith
  have hLR (p : closedBall (0 : Params) r) : R.1 = expandingRadius (L p).1 p.1.2.2 :=
    physicalModulationRadius_cancel R hR p.1 ((hpbound p).trans hrlog)
  let P := fun p : closedBall (0 : Params) r =>
    physicalStartingPerturbation a k ha ha1 hk χ hχ Q hQ (L p) p.1.1
      (euclideanToTorus ((1 / (L p).1) • p.1.2.1)) f
  have hPc : Continuous P := (continuous_physicalModulation_perturbation a k ha ha1 hk
    χ hχ Q hQ R f).comp continuous_subtype_val
  have hPn (p : closedBall (0 : Params) r) : ‖P p‖ ≤ (A + 1) * r := by
    have h := hnorm (L p) R (h2big.trans (hLp p)) p.1
      ((hpbound p).trans hrhalf) ((hpbound p).trans hrlog) (hLR p) f
    apply h.trans
    change A * ‖p.1‖ + D * ‖f - f₀‖ ≤ _
    have hd := mul_le_mul_of_nonneg_left hdist (norm_nonneg (sobolevToExpanding a k ha hk))
    have hp := mul_le_mul_of_nonneg_left (hpbound p) hA
    nlinarith
  have hw (p : closedBall (0 : Params) r) :
      ‖stableFrameProjection (ζ (L p)) (K • κ (L p)) (P p)‖ ≤ 2 * K * B * (A + 1) * r := by
    have hi := hinv (L p) (hL₀big.trans (hLp p))
    exact (normalized_stable_projection_bound K B hK.le (κ (L p)) (hκ (L p))
      (ζ (L p)) hi.2.1 hi.1 (P p)).trans
      ((mul_le_mul_of_nonneg_left (hPn p) (by positivity)).trans_eq (by ring))
  let err := E₀ * (r ^ 2 + r / J) + ε * M * r + B * D * δ
  have herr (p : closedBall (0 : Params) r) : ‖κ (L p) (P p) - C p.1‖ ≤ err := by
    have h := herror (L p) R (hLerrbig.trans (hLp p)) (h2big.trans (hLp p)) p.1
      ((hpbound p).trans hrhalf) ((hpbound p).trans hrlog) (hLR p) f
    rw [← hC] at h
    apply h.trans
    have hsq : ‖p.1‖ ^ 2 ≤ r ^ 2 := by nlinarith [norm_nonneg p.1, hpbound p]
    have hdiv : ‖p.1‖ / (L p).1 ≤ r / J :=
      (div_le_div_of_nonneg_right (hpbound p) (by linarith [(L p).2])).trans
        (div_le_div_of_nonneg_left hr.le (by linarith : 0 < J) (hJbig.trans (hLp p)))
    exact add_le_add (add_le_add
      (mul_le_mul_of_nonneg_left (add_le_add hsq hdiv) hE₀)
      (mul_le_mul_of_nonneg_left (hpbound p) (by positivity)))
      (mul_le_mul_of_nonneg_left hdist (by positivity))
  have hκc : Continuous (fun q : Radius × FourierL2 => κ q.1 q.2) := by
    have hc : Continuous (fun q : Radius × FourierL2 => K⁻¹ • (K • κ q.1) q.2) :=
      continuous_const.smul hπc
    simpa only [smul_apply, smul_smul, inv_mul_cancel₀ hK.ne', one_smul] using hc
  obtain ⟨p, q, hqp, hqf⟩ := normalized_flatStableGraph_intersection C r ρ L₀ err ν η
    (2 * K * B * (A + 1) * r) K hr.le hν.le hK hW κ ζ hκc hζc
    (fun L hL => (hinv L hL).1) G hGc (fun q => (hG q).2.2.1)
    (fun q => (hG q).2.2.2.1) L hLc (fun p => hL₀big.trans (hLp p)) P hPc hw herr hsmall
  obtain ⟨u, hu, hu0, hsol, hdecay⟩ := (hG q).2.2.2.2
  refine ⟨q.1.1, p.1.1, euclideanToTorus ((1 / (L p).1) • p.1.2.1), u, hu, ?_, hsol, hdecay⟩
  rw [hu0, hqf]
  have hqzero : sampledCutoffProfileOrbit a k q.1.1.1 ha1 hk q.1.1.2 χ hχ Q hQ 0 =
      sampledCutoffProfileAtRadius a k ha1 hk χ hχ Q hQ q.1.1 := by
    unfold sampledCutoffProfileOrbit
    congr 1
    apply Subtype.ext
    simp [expandingRadius]
  rw [hqzero, hqp]
  unfold P physicalStartingPerturbation
  abel

end DefocusingNLS

end OAI
