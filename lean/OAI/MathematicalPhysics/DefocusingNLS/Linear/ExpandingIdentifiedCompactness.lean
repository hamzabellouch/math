import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileCompactness
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeakLimitPath
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingWeakInitialBound
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileLimitEquation

namespace OAI

/-! # Every bounded sequence of actual trajectories has an identified local limit -/

open Set Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] expandingProfileTrajectory expandingSpacetimePath

theorem expandingProfile_exists_identified_limit (a b k T Q M C₀ : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 10 < k) (hT : 0 ≤ T)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀) (m : ℕ)
    (χ : 𝓢(E, ℂ)) (ρ : ℝ) (hρ : 0 < ρ) (hχ : ∀ y : E, ‖y‖ ≤ ρ → χ y = 1)
    (hCb : ∀ (L : ℝ) (hL : 1 ≤ L) (f : FourierL2),
      ‖homogeneousLocalizationCLM a k L ha ha1 (by linarith) hL χ f‖ ≤ C₀ * ‖f‖)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (hLinf : Tendsto L atTop atTop)
    (q : ℕ → C(Icc (0 : ℝ) T, FourierL2)) (hq : ∀ n t, ‖q n t‖ ≤ Q)
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M) (Q₀ : HomogeneousY a k)
    (hqp : ∀ (s : Icc (0 : ℝ) T) (y : E),
      Tendsto (fun n => expandingPhysicalContinuous a k (expandingRadius (L n) s)
        ha ha1 (by linarith) ((hL n).trans (expandingRadius_ge (L n) s (hL n) s.2.1)) (q n s) y)
        atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 (by linarith) Q₀ y))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v : C(Icc (0 : ℝ) T × E, ℂ),
      ∃ u₀ : HomogeneousY a k, ‖u₀‖ ≤ C₀ * M ∧
        Tendsto (fun n => expandingProfilePhysicalPath a b k (L (φ n)) T
          ha ha1 (by linarith) (hL (φ n)) hT m Q hQ (q (φ n)) (hq (φ n)) (f (φ n)))
          atTop (𝓝 v) ∧
        (∀ t y, v (t, y) = homogeneousPhysicalCLM a k ha ha1 (by linarith)
          (homogeneousLinearizedTrajectory a b k T ha ha1 (by linarith) hT m Q₀ u₀ t) y) ∧
        (∀ (t : Icc (0 : ℝ) T) (ℓ : HomogeneousY a k →L[ℝ] ℂ),
          Tendsto (fun n => ℓ (homogeneousLocalizationCLM a k (expandingRadius (L (φ n)) t)
            ha ha1 (by linarith) ((hL (φ n)).trans (expandingRadius_ge (L (φ n)) t (hL (φ n)) t.2.1)) χ
            (expandingProfileTrajectory a b k (L (φ n)) T ha ha1 (by linarith) (hL (φ n)) hT
              m Q hQ (q (φ n)) (hq (φ n)) (f (φ n)) t))) atTop
            (𝓝 (ℓ (homogeneousLinearizedTrajectory a b k T ha ha1 (by linarith) hT m Q₀ u₀ t)))) := by
  have hk8 : 8 < k := by linarith
  have hc := exists_expandingProfile_localUniform_limit a b (k - 2) Q M T ha ha1
    (by linarith) hQ hM hT m L hL q hq f hf
  simp only [sub_add_cancel] at hc
  obtain ⟨v, φ, hφ, hv⟩ := hc
  let S := fun n => expandingProfileTrajectory a b k (L (φ n)) T ha ha1 hk8 (hL (φ n)) hT
    m Q hQ (q (φ n)) (hq (φ n)) (f (φ n))
  obtain ⟨K, hK, hKb⟩ := exists_expandingProfileTrajectory_bound a b k ha ha1 hk8 m Q hQ
  let A := (K + 1) * Real.exp ((K + 1) * T) * M
  have hSb (n : ℕ) (t : Icc (0 : ℝ) T) : ‖S n t‖ ≤ A :=
    ((ContinuousMap.norm_coe_le_norm (S n) t).trans
      (hKb (L (φ n)) T (hL (φ n)) hT (q (φ n)) (hq (φ n)) (f (φ n)))).trans
      (mul_le_mul_of_nonneg_left (hf (φ n)) (by positivity))
  obtain ⟨C, _hC, w, hw, hphysical, _hweakcont, _hsm, hweak⟩ :=
    expandingLimit_exists_weaklyContinuous_path a k A T ha ha1 hk8 hT
      (fun n => L (φ n)) (fun n => hL (φ n)) (hLinf.comp hφ.tendsto_atTop)
      χ ρ hρ hχ S hSb v hv
  have hvc (y : E) : Continuous (fun t => homogeneousPhysicalCLM a k ha ha1 hk8 (w t) y) :=
    (v.continuous.comp (continuous_id.prodMk continuous_const)).congr (fun t => (hphysical t y).symm)
  have hvp (t : Icc (0 : ℝ) T) (y : E) :
      Tendsto (fun n => expandingPhysicalContinuous a k (expandingRadius (L (φ n)) t)
        ha ha1 hk8 ((hL (φ n)).trans (expandingRadius_ge (L (φ n)) t (hL (φ n)) t.2.1))
        (S n t) y) atTop (𝓝 (homogeneousPhysicalCLM a k ha ha1 hk8 (w t) y)) := by
    have h := ((continuous_eval_const (t, y)).tendsto v).comp hv
    change Tendsto (fun n => expandingProfilePhysicalPath a b k (L (φ n)) T
      ha ha1 hk8 (hL (φ n)) hT m Q hQ (q (φ n)) (hq (φ n)) (f (φ n)) (t, y))
      atTop (𝓝 (v (t, y))) at h
    simp only [expandingPhysicalContinuous_apply, S]
    simpa only [Function.comp_apply, expandingProfilePhysicalPath, expandingSpacetimePath_apply,
      ← hphysical t y] using h
  have hid := expandingProfile_limit_identification a b k T Q M (C * A) ha ha1 hk8 hT m hQ
    (fun n => L (φ n)) (fun n => hL (φ n)) (fun n => q (φ n)) (fun n => hq (φ n))
    (fun n => f (φ n)) (fun n => hf (φ n)) Q₀ w hw hvc
    (fun t y => (hqp t y).comp hφ.tendsto_atTop) hvp
  have hinit : ‖w ⟨0, le_rfl, hT⟩‖ ≤ C₀ * M := by
    apply expandingProfile_weak_initial_norm a b k T Q M C₀ ha ha1 hk8 hT m hQ hC₀ χ hCb
      (fun n => L (φ n)) (fun n => hL (φ n)) (fun n => q (φ n)) (fun n => hq (φ n))
      (fun n => f (φ n)) (fun n => hf (φ n))
    intro ℓ
    simpa only [expandingRadius, zero_div, Real.exp_zero, mul_one] using hweak ⟨0, le_rfl, hT⟩ ℓ
  refine ⟨φ, hφ, v, w ⟨0, le_rfl, hT⟩, hinit, hv, ?_, ?_⟩
  · intro t y
    exact (hphysical t y).symm.trans (congrArg (fun z => homogeneousPhysicalCLM a k ha ha1 hk8 z y)
      (congrFun hid t))
  · intro t ℓ
    simpa only [congrFun hid t] using hweak t ℓ

end DefocusingNLS

end OAI
