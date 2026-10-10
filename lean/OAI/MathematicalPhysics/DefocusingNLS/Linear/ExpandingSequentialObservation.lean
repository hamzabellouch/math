import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingFilteredLimit
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! # A local observation threshold from the expanding-domain sequence criterion -/

open Filter Topology

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

/-- A functional vanishing on all bounded, locally null sequences has a uniform
smallness threshold on a sufficiently large physical ball. -/
theorem exists_expanding_observation_threshold (a k : ℝ)
    (F : Radius → FourierL2 → ℝ)
    (hseq : ∀ (L : ℕ → Radius), Tendsto (fun n => (L n).1) atTop atTop →
      ∀ (f : ℕ → FourierL2), (∀ n, ‖f n‖ ≤ 1) →
      (∀ R ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
        ‖expandingTorusFunction a k (L n).1 (f n)
          (euclideanToTorus ((L n).1⁻¹ • y))‖ < ε) →
      Tendsto (fun n => F (L n) (f n)) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∀ (L : Radius), (n : ℝ) ≤ L.1 → ∀ f : FourierL2,
      ‖f‖ ≤ 1 →
      (∀ y : E, ‖y‖ ≤ (n : ℝ) →
        ‖expandingTorusFunction a k L.1 f (euclideanToTorus (L.1⁻¹ • y))‖ ≤
          1 / ((n : ℝ) + 1)) → F L f ≤ ε := by
  classical
  by_contra hn
  push Not at hn
  choose L hL f hf hlocal hbad using hn
  have hLinf : Tendsto (fun n => (L n).1) atTop atTop :=
    tendsto_atTop_mono hL tendsto_natCast_atTop_atTop
  have hnull : ∀ R δ : ℝ, 0 < δ → ∀ᶠ n in atTop, ∀ y : E, ‖y‖ ≤ R →
      ‖expandingTorusFunction a k (L n).1 (f n)
        (euclideanToTorus ((L n).1⁻¹ • y))‖ < δ := by
    intro R δ hδ
    have hr : ∀ᶠ n : ℕ in atTop, R ≤ (n : ℝ) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R)
    have hd : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < δ :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hδ)
    filter_upwards [hr, hd] with n hRn hdn
    intro y hy
    exact (hlocal n y (hy.trans hRn)).trans_lt hdn
  have ht := hseq L hLinf f hf hnull
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hε)).exists
  exact (hbad n).not_gt hn

end DefocusingNLS

end OAI
