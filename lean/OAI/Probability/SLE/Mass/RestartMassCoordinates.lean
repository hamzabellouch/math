import OAI.Probability.SLE.Mass.ConformalMassTransport
import OAI.Probability.SLE.Geometry.RestartConformalRadius

namespace OAI

/-! The actual centered inverse Loewner map and its mass weight.
These are defined only on interior points; no boundary extension is used. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory Classical
open scoped NNReal ENNReal Topology CompactlySupported

namespace SLEExactGauge

def IsCapacityTwoWitness.restartHomeomorph
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) :
    upperHalfPlane ≃ₜ survivingDomain γ T := by
  rcases hw with ⟨hc,_,_,hG,hF,hGM,hFM,hFG,hGF,_,_,_,_⟩
  have hshift (z : upperHalfPlane) : (z:ℂ)+(U T:ℂ) ∈ upperHalfPlane := by
    simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,add_zero]
      using z.property
  have hback (z : survivingDomain γ T) : G T z-(U T:ℂ) ∈ upperHalfPlane := by
    simpa only [upperHalfPlane,mem_ofPred_eq,Complex.sub_im,Complex.ofReal_im,sub_zero]
      using hGM T z.property
  refine {
    toFun := fun z => ⟨F T ((z:ℂ)+(U T:ℂ)),hFM T (hshift z)⟩
    invFun := fun z => ⟨G T z-(U T:ℂ),hback z⟩
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · intro z
    apply Subtype.ext
    exact (congrArg (fun v : ℂ => v-(U T:ℂ)) (hGF T _ (hshift z))).trans
      (add_sub_cancel_right _ _)
  · intro z
    apply Subtype.ext
    change F T ((G T z-(U T:ℂ))+(U T:ℂ)) = z
    rw [sub_add_cancel,hFG T _ z.property]
  · exact ((hF T).continuousOn.comp_continuous
      (continuous_subtype_val.add continuous_const) hshift).subtype_mk _
  · exact (((hG T).continuousOn.comp_continuous continuous_subtype_val
      (fun z => z.property)).sub continuous_const).subtype_mk _

@[simp] lemma IsCapacityTwoWitness.restartHomeomorph_apply
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (z : upperHalfPlane) :
    ((hw.restartHomeomorph T z : survivingDomain γ T):ℂ) = F T ((z:ℂ)+(U T:ℂ)) := by
  rcases hw with ⟨hc,h0,hi,hG,hF,hGM,hFM,hFG,hGF,hG0,hode,hn,ht⟩
  rfl

def IsCapacityTwoWitness.restartMassWeight
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (κ : ℝ) (hκ : 0 < κ) :
    C(upperHalfPlane, ℝ≥0) where
  toFun z := ⟨‖deriv (F T) ((z:ℂ)+(U T:ℂ))‖ ^ (1+κ/8),Real.rpow_nonneg (norm_nonneg _) _⟩
  continuous_toFun := by
    have hshift (z : upperHalfPlane) : (z:ℂ)+(U T:ℂ) ∈ upperHalfPlane := by
      simpa only [upperHalfPlane,mem_ofPred_eq,Complex.add_im,Complex.ofReal_im,add_zero]
        using z.property
    have hd := (hw.2.2.2.2.1 T).deriv isOpen_upperHalfPlane
    have hc := hd.continuousOn.comp_continuous
      (continuous_subtype_val.add continuous_const) hshift
    exact ((Real.continuous_rpow_const (by linarith : 0 ≤ 1+κ/8)).comp hc.norm).subtype_mk _

def IsCapacityTwoWitness.restartMass
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (κ : ℝ) (hκ : 0 < κ)
    (μ : Measure upperHalfPlane) : Measure (survivingDomain γ T) :=
  Multipoint.conformalMass (hw.restartHomeomorph T) (hw.restartMassWeight T κ hκ) μ

lemma IsCapacityTwoWitness.restartMass_integral
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (T : ℝ≥0) (κ : ℝ) (hκ : 0 < κ)
    (μ : Measure upperHalfPlane) (f : C_c(survivingDomain γ T, ℝ)) :
    (∫ z, f z ∂hw.restartMass T κ hκ μ) =
      ∫ z : upperHalfPlane, ‖deriv (F T) ((z:ℂ)+(U T:ℂ))‖ ^ (1+κ/8) *
        f (hw.restartHomeomorph T z) ∂μ :=
  Multipoint.conformalMass_integral (hw.restartHomeomorph T)
    (hw.restartMassWeight T κ hκ) μ f

end SLEExactGauge

end

end OAI
