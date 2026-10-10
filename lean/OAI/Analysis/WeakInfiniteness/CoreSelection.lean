import Mathlib
import OAI.Analysis.WeakInfiniteness.Plateau

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

universe u v

variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma exists_supported_positive_core (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    {u : A} (hu : 0 ≤ u) (hn : π u ≠ 0) :
    ∃ p ∈ hereditarySubalgebra u hu.isSelfAdjoint,
      ∃ h ∈ hereditarySubalgebra u hu.isSelfAdjoint,
      0 ≤ p ∧ ‖p‖ ≤ 1 ∧ 0 ≤ h ∧ p*h=h ∧ π h ≠ 0 := by
  let α := ‖π u‖
  have hα : 0 < α := norm_pos_iff.mpr hn
  let p := cfcₙ (spectralRamp (α/8)) (positiveCut (α/2) u)
  let h := positiveCut (7*α/8) u
  have huD := self_mem_hereditary u hu
  have hmidD : positiveCut (α/2) u ∈ hereditarySubalgebra u hu.isSelfAdjoint := cfcₙ_mem _ huD
  have hpD : p ∈ hereditarySubalgebra u hu.isSelfAdjoint := cfcₙ_mem _ hmidD
  have hhD : h ∈ hereditarySubalgebra u hu.isSelfAdjoint := cfcₙ_mem _ huD
  have hp : 0 ≤ p := cfcₙ_nonneg (fun s _ => spectralRamp_nonneg (α/8) s)
  have hpn : ‖p‖ ≤ 1 := by
    apply norm_cfcₙ_le
    intro s _
    rw [Real.norm_eq_abs,abs_of_nonneg (spectralRamp_nonneg (α/8) s)]
    exact spectralRamp_le_one _ _
  refine ⟨p,hpD,h,hhD,hp,hpn,positiveCut_nonneg _ _,
    spectralRamp_positiveCut_plateau u hu.isSelfAdjoint hα,?_⟩
  have he : π h=positiveCut (7*α/8) (π u) :=
    π.map_cfcₙ (fun s : ℝ => max (s-7*α/8) 0) u (by fun_prop)
      (max_eq_right (by linarith)) (by fun_prop) hu.isSelfAdjoint (map_nonneg π hu).isSelfAdjoint
  rw [he]
  exact positiveCut_ne_zero_of_lt_norm (map_nonneg π hu) (by positivity) (by dsimp [α]; linarith)

lemma positiveCut_eq_zero_of_norm_le {B : Type*} [CStarAlgebra B]
    (b : B) {α : ℝ} (hα : 0 ≤ α) (hbn : ‖b‖ ≤ α) : positiveCut α b=0 := by
  obtain hB | hB := subsingleton_or_nontrivial B
  · exact Subsingleton.elim _ _
  let : Nontrivial B := hB
  change cfcₙ (fun s : ℝ => max (s-α) 0) b=0
  calc
    cfcₙ (fun s : ℝ => max (s-α) 0) b=cfcₙ (0 : ℝ → ℝ) b := by
      apply cfcₙ_congr
      intro s hs
      change max (s-α) 0=0
      apply max_eq_right
      rcases mem_quasispectrum_iff.mp hs with rfl | hs
      · linarith
      · have := spectrum.norm_le_norm_of_mem hs
        have := Real.le_norm_self s
        linarith
    _ = 0 := cfcₙ_zero ℝ b

lemma norm_lt_of_positiveCut_image_ne_zero
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) {c : A} (hc : 0 ≤ c) {α : ℝ} (hα : 0 ≤ α)
    (hn : π (positiveCut α c) ≠ 0) : α < ‖π c‖ := by
  have he : π (positiveCut α c)=positiveCut α (π c) :=
    π.map_cfcₙ (fun s : ℝ => max (s-α) 0) c (by fun_prop)
      (max_eq_right (by linarith)) (by fun_prop) hc.isSelfAdjoint (map_nonneg π hc).isSelfAdjoint
  rw [he] at hn
  exact lt_of_not_ge (fun h => hn (positiveCut_eq_zero_of_norm_le _ hα h))

end

end WeakPureInfiniteness
end

end OAI
