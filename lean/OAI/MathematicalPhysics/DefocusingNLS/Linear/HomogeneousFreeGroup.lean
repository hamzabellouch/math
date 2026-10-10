import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeOperator

namespace OAI

/-! # Group law for the exact whole-space free evolution -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

@[simp] theorem homogeneousFreeAmplitude_zero (a b : ℝ) :
    homogeneousFreeAmplitude a b 0 = 1 := by
  simp [homogeneousFreeAmplitude]

@[simp] theorem homogeneousFreePhase_zero (ξ : E) : homogeneousFreePhase 0 ξ = 1 := by
  simp [homogeneousFreePhase]

theorem homogeneousFreeAmplitude_add (a b s t : ℝ) :
    homogeneousFreeAmplitude a b (s + t) =
      homogeneousFreeAmplitude a b s * homogeneousFreeAmplitude a b t := by
  unfold homogeneousFreeAmplitude
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem homogeneousFreePhase_add (s t : ℝ) (ξ : E) :
    homogeneousFreePhase (s + t) ξ = homogeneousFreePhase s ξ *
      homogeneousFreePhase t (Real.exp (s / 2) • ξ) := by
  unfold homogeneousFreePhase
  rw [← Complex.exp_add, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    mul_pow, ← Real.exp_nat_mul]
  have he : (2 : ℝ) * (s / 2) = s := by ring
  simp only [Nat.cast_ofNat]
  rw [he, Real.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem homogeneousFreeFourier_zero (a b : ℝ) (ψ : 𝓢(E, ℂ)) :
    homogeneousFreeFourier a b 0 ψ = ψ := by
  ext ξ
  simp

theorem homogeneousFreeFourier_add (a b s t : ℝ) (ψ : 𝓢(E, ℂ)) :
    homogeneousFreeFourier a b (s + t) ψ =
      homogeneousFreeFourier a b s (homogeneousFreeFourier a b t ψ) := by
  ext ξ
  simp only [homogeneousFreeFourier_apply, homogeneousFreeAmplitude_add,
    homogeneousFreePhase_add]
  have he : Real.exp ((s + t) / 2) = Real.exp (t / 2) * Real.exp (s / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, mul_smul]
  ring

@[simp] theorem homogeneousFreeOperator_zero (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    homogeneousFreeOperator a b k 0 ha ha1 hk f = f := by
  have h := (homogeneousFrequencyEmbedding_dense a k ha ha1 hk).equalizer
    (homogeneousFreeOperator a b k 0 ha ha1 hk).continuous continuous_id (by
      funext ψ
      simp only [Function.comp_apply, homogeneousFreeOperator_on_Schwartz,
        homogeneousFreeFourier_zero, id_eq])
  exact congr_fun h f

theorem homogeneousFreeOperator_add (a b k s t : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    homogeneousFreeOperator a b k (s + t) ha ha1 hk f =
      homogeneousFreeOperator a b k s ha ha1 hk
        (homogeneousFreeOperator a b k t ha ha1 hk f) := by
  have h := (homogeneousFrequencyEmbedding_dense a k ha ha1 hk).equalizer
    (homogeneousFreeOperator a b k (s + t) ha ha1 hk).continuous
    ((homogeneousFreeOperator a b k s ha ha1 hk).continuous.comp
      (homogeneousFreeOperator a b k t ha ha1 hk).continuous) (by
      funext ψ
      simp only [Function.comp_apply, homogeneousFreeOperator_on_Schwartz,
        homogeneousFreeFourier_add])
  exact congr_fun h f

@[simp] theorem homogeneousFreeOperator_neg_cancel (a b k s : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (f : HomogeneousY a k) :
    homogeneousFreeOperator a b k (-s) ha ha1 hk
      (homogeneousFreeOperator a b k s ha ha1 hk f) = f := by
  rw [← homogeneousFreeOperator_add]
  simp

end DefocusingNLS

end OAI
