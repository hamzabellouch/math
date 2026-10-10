import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileInitial
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousWeakNorm
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLocalizationPhysical

namespace OAI

/-! # A slab-independent norm bound for the initial homogeneous limit -/

open Set Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingProfile_weak_initial_norm (a b k T Q M C : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hT : 0 ≤ T)
    (m : ℕ) (hQ : 0 ≤ Q) (hC : 0 ≤ C) (χ : 𝓢(E, ℂ))
    (hCb : ∀ (L : ℝ) (hL : 1 ≤ L) (f : FourierL2),
      ‖homogeneousLocalizationCLM a k L ha ha1 hk hL χ f‖ ≤ C * ‖f‖)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n)
    (q : ℕ → C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ n t, ‖q n t‖ ≤ Q)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M) (v : HomogeneousY a k)
    (hv : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (homogeneousLocalizationCLM a k (L n) ha ha1 hk (hL n) χ
        (expandingProfileTrajectory a b k (L n) T ha ha1 hk (hL n) hT m Q hQ (q n)
          (hq n) (f n) ⟨0, le_rfl, hT⟩))) atTop (𝓝 (ℓ v))) :
    ‖v‖ ≤ C * M := by
  apply homogeneousY_norm_le_of_weak_limit a k (C * M) ha ha1 hk
    (fun n => homogeneousLocalizationCLM a k (L n) ha ha1 hk (hL n) χ (f n)) v
  · intro n
    exact (hCb (L n) (hL n) (f n)).trans (mul_le_mul_of_nonneg_left (hf n) hC)
  · intro ℓ
    simpa only [expandingProfileTrajectory_initial] using hv ℓ

end DefocusingNLS

end OAI
