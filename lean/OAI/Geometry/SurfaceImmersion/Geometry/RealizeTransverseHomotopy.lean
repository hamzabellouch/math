import OAI.Geometry.SurfaceImmersion.Whitney.SupportedExactCollar
import OAI.Geometry.SurfaceImmersion.Correction.PrescribedTransverseModel

namespace OAI

/-! Realization of a transverse-vector homotopy by an actual supported
smooth surface change, retaining the whole original singular set. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem realize_transverse_homotopy {f : Base → W} {V : ℝ × ℝ → W}
    (hf : ContDiff ℝ ∞ f) (hV : ContDiff ℝ ∞ V)
    (hV0 : ∀ t, V (0,t) = axisTransverse f t)
    {a b : ℝ} (hab : a ≤ b)
    (hI : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc a b,
      Function.Injective (homotopyCollarJet (axisValue f) V s t 0 0))
    (hstation : ∀ t ∉ Ioo a b, ∀ s ∈ Icc (0:ℝ) 1,
      V (s,t) = axisTransverse f t)
    {U : Set Base} (hU : IsOpen U)
    (haxis : ∀ t ∈ Icc a b, crosscapAxis t ∈ U) :
    ∃ (F : Base → W) (K : Set Base), ContDiff ℝ ∞ F ∧ IsCompact K ∧ K ⊆ U ∧
      (∀ x, Function.Injective (fderiv ℝ F x) ↔ Function.Injective (fderiv ℝ f x)) ∧
      (∀ x ∉ K, F =ᶠ[𝓝 x] f) ∧
      (∀ t, F =ᶠ[𝓝 (crosscapAxis t)] prescribedTransverseModel f (fun t => V (1,t))) ∧
      ∀ t, F (crosscapAxis t) = f (crosscapAxis t) ∧
        fderiv ℝ F (crosscapAxis t) = fderiv ℝ f (crosscapAxis t) +
          (ContinuousLinearMap.proj 0).smulRight (V (1,t)-axisTransverse f t) := by
  let b' : ℝ → W := fun t => V (1,t)
  have hb' : ContDiff ℝ ∞ b' := hV.comp (contDiff_const.prodMk contDiff_id)
  let g := prescribedTransverseModel f b'
  have hg : ContDiff ℝ ∞ g := prescribedTransverseModel_smooth hf hb'
  have hgc : ∀ t, f (crosscapAxis t) = g (crosscapAxis t) := fun t =>
    (prescribedTransverseModel_axis f b' t).symm
  have hgb : ∀ t, V (1,t) = axisTransverse g t := fun t =>
    (prescribedTransverseModel_transverse hf hb' t).symm
  have hgs : ∀ x : Base, x 1 ∉ Ioo a b → g x = f x ∧
      ∀ s ∈ Icc (0:ℝ) 1, V (s,x 1) = axisTransverse f (x 1) := by
    intro x hx
    exact ⟨prescribedTransverseModel_eq (hstation (x 1) hx 1 ⟨zero_le_one,le_rfl⟩),
      hstation (x 1) hx⟩
  obtain ⟨F,K,hF,hK,hKU,hreg,hout,hinner⟩ :=
    supported_exact_collar hf hg hV hgc hV0 hgb hab hI hgs hU haxis
  refine ⟨F,K,hF,hK,hKU,hreg,hout,hinner,?_⟩
  intro t
  constructor
  · exact (hinner t).self_of_nhds.trans (prescribedTransverseModel_axis f b' t)
  · rw [(hinner t).fderiv_eq]
    exact prescribedTransverseModel_first_jet hf hb' t

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
