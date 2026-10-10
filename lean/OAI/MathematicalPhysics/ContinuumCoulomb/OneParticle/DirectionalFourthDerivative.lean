import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombKernelHomogeneity
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace OAI

/-! Fourth derivatives along the affine coordinate lines used by cubature. -/

noncomputable section
namespace ContinuumCoulomb

/-- Local smoothness suffices; the function may be singular away from the line point. -/
theorem fourthDeriv_affine_line (f : Position → ℝ) (b v : Position) (t : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) :
    iteratedDeriv 4 (fun s : ℝ => f (b+s • v)) t =
      iteratedFDeriv ℝ 4 f (b+t • v) (fun _ => v) := by
  let L : ℝ →L[ℝ] Position := (ContinuousLinearMap.id ℝ ℝ).smulRight v
  let g : Position → ℝ := fun z => f (b+z)
  have hg : ContDiffAt ℝ 4 g (L t) :=
    hf.comp (L t) (contDiffAt_const.add contDiffAt_id)
  obtain ⟨U,hU,ht,hgU⟩ := hg.contDiffOn' le_rfl (by norm_num)
  have hgU : ContDiffOn ℝ 4 g U := by simpa using hgU
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have hgt : ContDiffAt ℝ 4 (g ∘ L) t := hg.comp t L.contDiff.contDiffAt
  have h := L.iteratedFDerivWithin_comp_right hgU hU.uniqueDiffOn hpre.uniqueDiffOn ht
    (i := 4) le_rfl
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn hgt ht,
    iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn hg ht] at h
  change iteratedFDeriv ℝ 4 (g ∘ L) t (fun _ => 1) = _
  rw [h]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hL (s : ℝ) : L s = s • v := rfl
  simp only [hL,one_smul]
  change iteratedFDeriv ℝ 4 (fun z => f (b+z)) (t • v) (fun _ => v) = _
  rw [iteratedFDeriv_comp_add_left]

theorem fourthDeriv_affine_line_bound (f : Position → ℝ) (b v : Position) (t : ℝ)
    (hf : ContDiffAt ℝ 4 f (b+t • v)) :
    |iteratedDeriv 4 (fun s : ℝ => f (b+s • v)) t| ≤
      ‖iteratedFDeriv ℝ 4 f (b+t • v)‖*‖v‖^4 := by
  rw [fourthDeriv_affine_line f b v t hf,← Real.norm_eq_abs]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    (iteratedFDeriv ℝ 4 f (b+t • v)).le_opNorm (fun _ => v)

end ContinuumCoulomb

end

end OAI
