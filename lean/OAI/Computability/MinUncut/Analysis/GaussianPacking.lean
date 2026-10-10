import Mathlib
import OAI.Computability.MinUncut.Estimates.LiftedVectors

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace MinUncut.GaussianBudget
variable {X C : Type*} [Fintype X] [Fintype C]

abbrev productLaw (X C : Type*) [Fintype X] [Fintype C] :=
  (Measure.pi (fun _ : X => gaussianReal 0 1)).prod
    ((Measure.pi (fun _ : X => gaussianReal 0 1)).prod (Measure.pi (fun _ : C => gaussianReal 0 1)))

def packEquiv : ((X → ℝ) × ((X → ℝ) × (C → ℝ))) ≃ᵐ (Coordinates X C → ℝ) :=
  ((MeasurableEquiv.refl (X → ℝ)).prodCongr
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : X ⊕ C => ℝ)).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : X ⊕ (X ⊕ C) => ℝ)).symm

lemma pack_preserving : MeasurePreserving (packEquiv (X := X) (C := C))
    (productLaw X C) (Measure.pi (fun _ : Coordinates X C => gaussianReal 0 1)) := by
  exact (measurePreserving_sumPiEquivProdPi_symm (fun _ : X ⊕ (X ⊕ C) => gaussianReal 0 1)).comp
    ((MeasurePreserving.id _).prod (measurePreserving_sumPiEquivProdPi_symm (fun _ : X ⊕ C => gaussianReal 0 1)))

lemma score_packed (v : X → ℝ) (σ η : ℝ) (z : C)
    (p : (X → ℝ) × ((X → ℝ) × (C → ℝ))) :
    score (liftVector v σ η z) (packEquiv p)=score v p.1+σ*score v p.2.1+η*p.2.2 z := by
  classical
  simp only [score,Fintype.sum_sum_type,liftVector,packEquiv,MeasurableEquiv.trans_apply]
  change (∑ x, v x*p.1 x)+((∑ x, (σ*v x)*p.2.1 x)+∑ c, (if c=z then η else 0)*p.2.2 c)=_
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true,mul_assoc,← Finset.mul_sum]
  ring

lemma integral_pack_sign (v w : Coordinates X C → ℝ) :
    (∫ c, ∫ g, ∫ l, signFailure (score v (packEquiv (c,g,l)))
      (score w (packEquiv (c,g,l))) ∂Measure.pi (fun _ : C => gaussianReal 0 1)
      ∂Measure.pi (fun _ : X => gaussianReal 0 1) ∂Measure.pi (fun _ : X => gaussianReal 0 1)) =
    ∫ q, signFailure (score v q) (score w q) ∂Measure.pi (fun _ : Coordinates X C => gaussianReal 0 1) := by
  have hv : Measurable (score v) := by unfold score; fun_prop
  have hw : Measurable (score w) := by unfold score; fun_prop
  have hp := pack_preserving (X := X) (C := C)
  have hi : Integrable (fun p : (X → ℝ) × ((X → ℝ) × (C → ℝ)) =>
      signFailure (score v (packEquiv p)) (score w (packEquiv p))) (productLaw X C) :=
    signFailure_integrable (hv.comp hp.measurable) (hw.comp hp.measurable)
  rw [← hp.integral_comp packEquiv.measurableEmbedding (fun q => signFailure (score v q) (score w q))]
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_right_ae] with c hc
  exact (integral_prod _ hc).symm

lemma first_triple_bound {v : X → ℝ} (hv : ‖vector v‖=1) {σ η : ℝ}
    (hσ : 0≤σ) (hη : 0≤η) (z : C) :
    (∫ c, ∫ g, ∫ l, signFailure (score v c) (score v c+σ*score v g+η*l z)
      ∂Measure.pi (fun _ : C => gaussianReal 0 1) ∂Measure.pi (fun _ : X => gaussianReal 0 1)
      ∂Measure.pi (fun _ : X => gaussianReal 0 1)) ≤ 4*(σ+η) := by
  have h := lift_sign_first hv hσ hη z
  rw [← integral_pack_sign] at h
  simpa only [score_packed,zero_mul,add_zero] using h

lemma second_triple_bound {v w : X → ℝ} (hv : ‖vector v‖=1) (hw : ‖vector w‖=1)
    {σ η : ℝ} (hσ : 0≤σ) (hσ1 : σ≤1) (hη : 0≤η) (z z' : C) :
    (∫ c, ∫ g, ∫ l, signFailure (score v c+σ*score v g+η*l z)
      (score w c+σ*score w g+η*l z')
      ∂Measure.pi (fun _ : C => gaussianReal 0 1) ∂Measure.pi (fun _ : X => gaussianReal 0 1)
      ∂Measure.pi (fun _ : X => gaussianReal 0 1)) ≤ 4*‖vector v-vector w‖+4*η := by
  have h := lift_sign_second hv hw hσ hσ1 hη z z'
  rw [← integral_pack_sign] at h
  simpa only [score_packed] using h
end MinUncut.GaussianBudget

end
end

end OAI
