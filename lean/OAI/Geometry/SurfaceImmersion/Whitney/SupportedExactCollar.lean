import OAI.Geometry.SurfaceImmersion.Whitney.CompactExactCollar
import OAI.Geometry.SurfaceImmersion.Whitney.AxisCollarJet
import OAI.Geometry.SurfaceImmersion.Geometry.CompactAxisRectangle

namespace OAI

/-! Exact boundary-germ replacement inside any prescribed neighborhood,
with the entire old singular set preserved. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem supported_exact_collar {f g : Base → W} {V : ℝ × ℝ → W}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hV : ContDiff ℝ ∞ V)
    (hc : ∀ t, f (crosscapAxis t) = g (crosscapAxis t))
    (hV0 : ∀ t, V (0,t) = axisTransverse f t)
    (hV1 : ∀ t, V (1,t) = axisTransverse g t)
    {a b : ℝ} (hab : a ≤ b)
    (hI : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc a b,
      Function.Injective (homotopyCollarJet (axisValue f) V s t 0 0))
    (hstation : ∀ x : Base, x 1 ∉ Ioo a b → g x = f x ∧
      ∀ s ∈ Icc (0:ℝ) 1, V (s,x 1) = axisTransverse f (x 1))
    {U : Set Base} (hU : IsOpen U)
    (haxis : ∀ t ∈ Icc a b, crosscapAxis t ∈ U) :
    ∃ (F : Base → W) (K : Set Base), ContDiff ℝ ∞ F ∧ IsCompact K ∧ K ⊆ U ∧
      (∀ x, Function.Injective (fderiv ℝ F x) ↔ Function.Injective (fderiv ℝ f x)) ∧
      (∀ x ∉ K, F =ᶠ[𝓝 x] f) ∧
      ∀ t, F =ᶠ[𝓝 (crosscapAxis t)] g := by
  let O : Set Base := U ∩ {x | Function.Injective (fderiv ℝ f x)}
  have hO : IsOpen O := hU.inter (ContinuousLinearMap.isOpen_injective.preimage
    (hf.continuous_fderiv (by simp)))
  have haO : ∀ t ∈ Icc a b, (![0,t] : Base) ∈ O := by
    intro t ht
    refine ⟨?_,?_⟩
    · simpa only [crosscapAxis_apply] using haxis t ht
    · change Function.Injective (fderiv ℝ f ![0,t])
      have hi := hI 0 ⟨le_rfl,zero_le_one⟩ t ht
      rw [axis_collar_jet hf hV0] at hi
      simpa only [crosscapAxis_apply] using hi
  obtain ⟨R,hR,hrect⟩ := compact_axis_rectangle hab hO haO
  obtain ⟨r,F,K,hr,hrR,hF,hK,hKs,hout,hreg,hinner⟩ :=
    compact_exact_collar hf hg hV hc hV0 hV1 hR hI hstation
  have hKO : K ⊆ O := by
    intro x hx
    obtain ⟨hu,ht⟩ := hKs hx
    have huR : |x 0| ≤ R := hu.trans (by linarith)
    have hh := hrect (x 0) (abs_le.mp huR) (x 1)
      ⟨by linarith [ht.1],by linarith [ht.2]⟩
    convert hh using 1
    ext i
    fin_cases i <;> rfl
  refine ⟨F,K,hF,hK,fun x hx => (hKO hx).1,?_,hout,hinner⟩
  intro x
  by_cases hx : x ∈ K
  · have ht := hKs hx
    have hu : |x 0| < r := ht.1.trans_lt (half_lt_self hr)
    have hFI := hreg (x 0) hu (x 1) ht.2
    have hxeq : (![x 0,x 1] : Base) = x := by
      ext i
      fin_cases i <;> rfl
    have hFI' : Function.Injective (fderiv ℝ F x) := by simpa only [hxeq] using hFI
    exact iff_of_true hFI' (hKO hx).2
  · rw [(hout x hx).fderiv_eq]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
