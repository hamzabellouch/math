import Mathlib
import OAI.Analysis.WeakInfiniteness.ContinuousDeletion
import OAI.Analysis.WeakInfiniteness.LocalFamily

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace
open Filter Topology
open Complex selfAdjoint
open scoped ComplexOrder

namespace WeakPureInfiniteness

noncomputable section

open scoped CStarAlgebra Topology

def spectralTent (t r x : ℝ) : ℝ := max (1-|x-t|/r) 0

lemma spectralTent_continuous (t r : ℝ) : Continuous (spectralTent t r) := by
  unfold spectralTent; fun_prop

lemma spectralTent_nonneg (t r x : ℝ) : 0 ≤ spectralTent t r x := le_max_right _ _

lemma spectralTent_center (t r : ℝ) : spectralTent t r t=1 := by
  simp [spectralTent]

lemma spectralTent_zero {t r x : ℝ} (hr : 0 < r) (hx : r ≤ |x-t|) :
    spectralTent t r x=0 := by
  apply max_eq_right
  have : 1 ≤ |x-t|/r := (le_div_iff₀ hr).mpr (by simpa using hx)
  linarith

def spectralPlateau (t r x : ℝ) : ℝ := min 1 (max 0 (2-|x-t|/r))

lemma spectralPlateau_continuous (t r : ℝ) : Continuous (spectralPlateau t r) := by
  unfold spectralPlateau; fun_prop

lemma spectralPlateau_one {t r x : ℝ} (hr : 0 < r) (hx : |x-t| ≤ r) :
    spectralPlateau t r x=1 := by
  apply min_eq_left
  have : |x-t|/r ≤ 1 := (div_le_iff₀ hr).mpr (by simpa using hx)
  exact (by linarith : 1 ≤ 2-|x-t|/r).trans (le_max_right _ _)

lemma spectralPlateau_zero {t r x : ℝ} (hr : 0 < r) (hx : 2*r ≤ |x-t|) :
    spectralPlateau t r x=0 := by
  unfold spectralPlateau
  have : 2 ≤ |x-t|/r := (le_div_iff₀ hr).mpr (by linarith)
  rw [max_eq_left (by linarith)]
  exact min_eq_right zero_le_one

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma continuouslySupported_cfc (U : A) (f : C(ℝ,ℝ)) (S : Set ℝ)
    (hf : ∀ x,f x ≠ 0 → x ∈ S) : ContinuouslySupported U (cfc f U) S := by
  intro g hg
  constructor
  · rw [← cfc_mul f g U f.continuous.continuousOn g.continuous.continuousOn]
    calc
      cfc (fun x => f x*g x) U=cfc (0 : ℝ → ℝ) U := by
        apply cfc_congr
        intro x _
        change f x*g x=0
        by_cases hx : f x=0
        · rw [hx,zero_mul]
        · rw [hg x (hf x hx),mul_zero]
      _ = 0 := cfc_zero ℝ U
  · rw [← cfc_mul g f U g.continuous.continuousOn f.continuous.continuousOn]
    calc
      cfc (fun x => g x*f x) U=cfc (0 : ℝ → ℝ) U := by
        apply cfc_congr
        intro x _
        change g x*f x=0
        by_cases hx : f x=0
        · rw [hx,mul_zero]
        · rw [hg x (hf x hx),zero_mul]
      _ = 0 := cfc_zero ℝ U

lemma continuouslySupported_hereditary (U u : A) (hu : IsSelfAdjoint u) (S : Set ℝ)
    (hs : ContinuouslySupported U u S) {v : A} (hv : v ∈ hereditarySubalgebra u hu) :
    ContinuouslySupported U v S := by
  intro g hg
  constructor
  · exact mul_zero_of_mem_hereditary_left hu (hs g hg).1 hv
  · have hright := mul_zero_of_mem_hereditary_left hu (hs g hg).1
      (star_mem (s := hereditarySubalgebra u hu) hv)
    have he := congrArg star hright
    simpa only [star_mul,star_star,(cfc_predicate g U).star_eq,star_zero] using he

lemma cfc_nonzero_of_spectral_value (π : A →⋆ₐ[ℂ] B) {U : A} (hU : IsSelfAdjoint U)
    (f : C(ℝ,ℝ)) {t : ℝ} (ht : t ∈ spectrum ℝ (π U)) (hf : f t ≠ 0) :
    π (cfc f U) ≠ 0 := by
  rw [π.map_cfc f U f.continuous.continuousOn (by fun_prop) hU (hU.map π)]
  intro hz
  have he := norm_apply_le_norm_cfc f (π U) ht f.continuous.continuousOn (hU.map π)
  rw [hz,norm_zero] at he
  exact (not_le_of_gt (norm_pos_iff.mpr hf)) he

lemma cfc_mem_of_zero (D : NonUnitalStarSubalgebra ℂ A) [IsClosed (D : Set A)]
    {U : A} (hU : U ∈ D) (f : C(ℝ,ℝ)) (hf : f 0=0) : cfc f U ∈ D := by
  rw [← cfcₙ_eq_cfc (f := (f : ℝ → ℝ)) (a := U) f.continuous.continuousOn hf]
  exact cfcₙ_mem f hU

lemma exists_nonzero_spectral_value {U : B} (hU : IsSelfAdjoint U) (hn : U ≠ 0) :
    ∃ t ∈ spectrum ℝ U,t ≠ 0 := by
  by_contra! h
  apply hn
  calc
    U=cfc (fun x : ℝ => x) U := (cfc_id' ℝ U hU).symm
    _ = cfc (0 : ℝ → ℝ) U := cfc_congr (fun x hx => h x hx)
    _ = 0 := cfc_zero ℝ U

end

end WeakPureInfiniteness
end

end OAI
