import OAI.Geometry.SurfaceImmersion.Primitive.LeadingProfileIdentification
import OAI.Geometry.SurfaceImmersion.Geometry.JetVariations

namespace OAI

/-! C3 closeness controls the finite data used by the leading-profile map,
with no loss in the fast phase parameter. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates SurfaceVelocityFamily.Loop

lemma lowJet_sub_variation {F G : Base → Space}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    (fun p => lowJet G p-lowJet F p) = variationLowJet (fun x => G x-F x) := by
  funext p
  have he := lowJet_affine hF (hG.sub hF) 1 p
  have hf : (fun q => F q+(1 : ℝ) • (G q-F q)) = G := by
    funext q
    simp only [one_smul]
    abel
  rw [hf,one_smul] at he
  rw [he]
  abel

lemma lowDerivative_sub_variation {F G : Base → Space}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (i : Fin 2) (p : Base) :
    lowDerivative G i p-lowDerivative F i p =
      fderiv ℝ (variationLowJet (fun x => G x-F x)) p (coordinateVector i) := by
  rw [← lowJet_derivative hG,← lowJet_derivative hF]
  have he := congrArg (fun L : Base →L[ℝ] LowJet => L (coordinateVector i))
    (fderiv_fun_sub ((lowJet_smooth hG).differentiable (by simp) p)
      ((lowJet_smooth hF).differentiable (by simp) p))
  have hh : (fderiv ℝ (fun q => lowJet G q-lowJet F q) p) (coordinateVector i) =
      (fderiv ℝ (lowJet G) p) (coordinateVector i)-
        (fderiv ℝ (lowJet F) p) (coordinateVector i) := he
  rw [lowJet_sub_variation hF hG] at hh
  exact hh.symm

lemma leadingInput_sub_bound {F G : Base → Space} {U : Set Base}
    (hU : IsOpen U) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    {C : ℝ} (hC : 0 ≤ C) (hb : WeightedBound U 1 3 C (fun x => G x-F x))
    {p : Base} (hp : p ∈ U) (t : ℝ) :
    ‖(((lowJet G p,t),lowDerivative G 1 p) : LeadingProfileInput)-
      ((lowJet F p,t),lowDerivative F 1 p)‖ ≤ C := by
  have hv : WeightedBound U 1 1 C (variationLowJet (fun x => G x-F x)) := by
    simpa using weighted_variationLowJet hU (hG.sub hF) zero_lt_one le_rfl hC 1 hb
  have hlow : ‖lowJet G p-lowJet F p‖ ≤ C := by
    rw [show lowJet G p-lowJet F p = variationLowJet (fun x => G x-F x) p from
      congrFun (lowJet_sub_variation hF hG) p]
    exact hv.norm_le hp
  have hd := hv.directional hU zero_lt_one (variationLowJet_smooth (hG.sub hF)).contDiffOn
    (coordinateVector 1)
  have hder : ‖lowDerivative G 1 p-lowDerivative F 1 p‖ ≤ C := by
    rw [lowDerivative_sub_variation hF hG]
    apply (hd.norm_le hp).trans
    simpa only [div_one] using mul_le_of_le_one_left hC (norm_coordinateVector_le 1)
  simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero] using
    (max_le (max_le hlow hC) hder)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
