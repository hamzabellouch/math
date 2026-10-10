import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffProfileCoordinateLimit
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalFrame
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FiniteOperatorConvergence
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCoordinateMap

namespace OAI

/-! # Sampling the actual smooth physical frame and its finite coordinates -/

open Filter Topology
open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}
local notation "Params" => ProfileSymmetryParameters

noncomputable def physicalFrameCutoff (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (F : Params →L[ℝ] HomogeneousY a k)
    (hF : ∀ p, ContDiff ℝ ∞ (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y))
    (L : Radius) : Params →ₗ[ℝ] 𝓢(E, ℂ) where
  toFun p := cutoffProfileSchwartz L.1 (by linarith [L.2]) χ hχ
    (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y) (hF p)
  map_add' p q := by
    ext y
    simp only [cutoffProfileSchwartz_apply, map_add, add_apply,
      ZeroAtInftyContinuousMap.add_apply, mul_add]
  map_smul' c p := by
    ext y
    simp only [cutoffProfileSchwartz_apply, map_smul, RingHom.id_apply,
      ContinuousLinearMap.map_smul_of_tower, ZeroAtInftyContinuousMap.smul_apply,
      smul_apply, Complex.real_smul]
    ring

noncomputable def sampledPhysicalFrame (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (F : Params →L[ℝ] HomogeneousY a k)
    (hF : ∀ p, ContDiff ℝ ∞ (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y))
    (L : Radius) : Params →L[ℝ] FourierL2 :=
  (((physicalSchwartzTorusSamplingCLM a k L.1 ha1 hk L.2).restrictScalars ℝ).toLinearMap.comp
    (physicalFrameCutoff a k ha ha1 hk χ hχ F hF L)).toContinuousLinearMap

@[simp] theorem sampledPhysicalFrame_apply (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (F : Params →L[ℝ] HomogeneousY a k)
    (hF : ∀ p, ContDiff ℝ ∞ (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y))
    (L : Radius) (p : Params) :
    sampledPhysicalFrame a k ha ha1 hk χ hχ F hF L p =
      physicalSchwartzTorusSamplingCLM a k L.1 ha1 hk L.2
        (cutoffProfileSchwartz L.1 (by linarith [L.2]) χ hχ
          (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y) (hF p)) := rfl

attribute [local irreducible] sampledPhysicalFrame physicalFrameCutoff

theorem sampledPhysicalFrame_coordinate_limit {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (F : Params →L[ℝ] HomogeneousY a k)
    (hF : ∀ p, ContDiff ℝ ∞ (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y))
    (hb : ∀ p, ∃ B : ℝ, 0 ≤ B ∧ ∀ L : Radius,
      ‖sampledPhysicalFrame a k ha ha1 hk χ hχ F hF L p‖ ≤ B)
    (π : HomogeneousY a k →L[ℝ] V)
    (L : ℕ → Radius) (hLinf : Tendsto (fun n => (L n).1) atTop atTop) :
    Tendsto (fun n => (expandingCoordinates a k ha ha1 hk χ π (L n)).comp
      (sampledPhysicalFrame a k ha ha1 hk χ hχ F hF (L n))) atTop (𝓝 (π.comp F)) := by
  apply tendsto_finite_domain_operator_of_basis (Module.finBasis ℝ Params)
  intro i
  let p := (Module.finBasis ℝ Params) i
  obtain ⟨B, hB, hbound⟩ := hb p
  simpa only [ContinuousLinearMap.comp_apply, expandingCoordinates_apply, sampledPhysicalFrame_apply] using
    cutoffProfile_finite_coordinate_limit a k ha ha1 hk χ hχ hχzero hχone
    (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y) (hF p) (F p)
    (fun _ => rfl) B hB (fun R hR => by simpa only [sampledPhysicalFrame_apply] using hbound ⟨R, hR⟩) L hLinf π

theorem sampledPhysicalFrame_coordinate_approximation {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (hχone : ∀ y : E, ‖y‖ ≤ 1 / 2 → χ y = 1)
    (F : Params →L[ℝ] HomogeneousY a k)
    (hF : ∀ p, ContDiff ℝ ∞ (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y))
    (hb : ∀ p, ∃ B : ℝ, 0 ≤ B ∧ ∀ L : Radius,
      ‖sampledPhysicalFrame a k ha ha1 hk χ hχ F hF L p‖ ≤ B)
    (π : HomogeneousY a k →L[ℝ] V) (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : Radius, L₀ ≤ L.1 →
      ‖(expandingCoordinates a k ha ha1 hk χ π L).comp
        (sampledPhysicalFrame a k ha ha1 hk χ hχ F hF L) - π.comp F‖ < ε := by
  by_contra! h
  choose L hL hbad using fun n : ℕ => h (n : ℝ)
  have hi : Tendsto (fun n => (L n).1) atTop atTop :=
    tendsto_atTop_mono hL tendsto_natCast_atTop_atTop
  have ht := tendsto_iff_norm_sub_tendsto_zero.mp
    (sampledPhysicalFrame_coordinate_limit a k ha ha1 hk χ hχ hχzero hχone F hF hb π L hi)
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hbad n)) hn

end DefocusingNLS

end OAI
