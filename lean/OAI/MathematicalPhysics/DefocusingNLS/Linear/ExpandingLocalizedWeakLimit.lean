import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousLocalizationPhysical
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousWeakSubsequence
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousWeakObservation

namespace OAI

/-! # Weak limits of bounded data on expanding tori

The actual localization has a uniform Y bound.  Its weak subsequences
therefore converge strongly under every compact physical observation.
-/

open Filter Topology Set
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousLocalObservation_of_weakLimit (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (S : Set E) [CompactSpace S]
    (u : ℕ → HomogeneousY a k) (v : HomogeneousY a k) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
      Tendsto (fun n => ℓ (u n)) atTop (𝓝 (ℓ v))) :
    Tendsto (fun n => homogeneousLocalObservation a k ha ha1 hk S (u n))
      atTop (𝓝 (homogeneousLocalObservation a k ha ha1 hk S v)) := by
  have hbound (n : ℕ) : ‖u n - v‖ ≤ M + ‖v‖ := by
    linarith [norm_sub_le (u n) v, hu n]
  have hw (ℓ : HomogeneousY a k →L[ℝ] ℂ) :
      Tendsto (fun n => ℓ (u n - v)) atTop (𝓝 0) := by
    simpa only [map_sub, sub_self] using (hweak ℓ).sub_const (ℓ v)
  have h := tendsto_homogeneousLocalObservation_of_weakNull a k (M + ‖v‖)
    ha ha1 hk S (fun n => u n - v) hbound hw
  have hn := h.norm
  simp only [map_sub, norm_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

theorem exists_expandingLocalized_weakLimit (a k M : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : ℕ → ℝ) (hL : ∀ n, 1 ≤ L n) (χ : 𝓢(E, ℂ))
    (f : ℕ → FourierL2) (hf : ∀ n, ‖f n‖ ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ v : HomogeneousY a k, ‖v‖ ≤ C * M ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ ℓ : HomogeneousY a k →L[ℝ] ℂ,
        Tendsto (fun n => ℓ (homogeneousLocalizationCLM a k (L (φ n))
          ha ha1 hk (hL (φ n)) χ (f (φ n)))) atTop (𝓝 (ℓ v))) ∧
      (∀ (S : Set E) (_ : CompactSpace S),
        Tendsto (fun n => homogeneousLocalObservation a k ha ha1 hk S
          (homogeneousLocalizationCLM a k (L (φ n)) ha ha1 hk (hL (φ n)) χ (f (φ n))))
          atTop (𝓝 (homogeneousLocalObservation a k ha ha1 hk S v))) := by
  obtain ⟨C, hC, hb⟩ := exists_homogeneousLocalization_bound a k ha ha1 hk χ
  let w := fun n => homogeneousLocalizationCLM a k (L n) ha ha1 hk (hL n) χ (f n)
  have hw (n : ℕ) : ‖w n‖ ≤ C * M :=
    (hb (L n) (hL n) (f n)).trans (mul_le_mul_of_nonneg_left (hf n) hC)
  obtain ⟨v, hv, φ, hφ, hweak⟩ := homogeneousY_weak_subsequence a k (C * M) ha1 hk w hw
  refine ⟨C, hC, v, hv, φ, hφ, hweak, ?_⟩
  intro S hS
  exact homogeneousLocalObservation_of_weakLimit a k (C * M) ha ha1 hk S
    (fun n => w (φ n)) v (fun n => hw (φ n)) hweak

end DefocusingNLS

end OAI
