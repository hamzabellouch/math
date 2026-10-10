import Mathlib
import OAI.Analysis.Conductivity.Sobolev.ParentFullEndH1
import OAI.Analysis.Conductivity.Sources.AngularJet

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus Matrix
open scoped ENNReal
local instance cylinderPointEnergyMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance cylinderPointEnergyIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma deriv_ofReal_im_zero (f : ℝ → ℝ) (t : ℝ) :
    (deriv (fun x => (f x : ℂ)) t).im=0 := by
  by_cases h : DifferentiableAt ℝ (fun x => (f x:ℂ)) t
  · have hh := (Complex.imCLM.hasFDerivAt).comp_hasDerivAt t h.hasDerivAt
    have he := hh.deriv
    have heq : Complex.imCLM ∘ (fun x => (f x:ℂ)) = fun _ => (0:ℝ) := by
      funext x; rfl
    rw [heq,deriv_const] at he
    exact he.symm
  · rw [deriv_zero_of_not_differentiableAt h,Complex.zero_im]

lemma sourceAngularJet_im (f : (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    (j : Fin 4) (z : ℝ × UnitAddTorus (Fin 2)) :
    (sourceAngularJet f a b j z).im=0 := by
  have hd (k : Fin 2) : (torusDirectionalDerivative
      (fun θ => sourceAngularTest f a b (z.1,θ)) k z.2).im=0 :=
    deriv_ofReal_im_zero _ _
  fin_cases j
  · rfl
  · rfl
  · change (torusDirectionalDerivative _ 0 z.2 / (2*Real.pi:ℂ)).im=0
    simp [Complex.div_im,hd]
  · change (torusDirectionalDerivative _ 1 z.2 / (2*Real.pi:ℂ)).im=0
    simp [Complex.div_im,hd]

lemma flatCylinderMatrix_mixed (s u v : Fin 3 → ℝ) :
    u ⬝ᵥ (flatCylinderMatrix s*ᵥv)=
      u 0*v 0+s 0*(u 1*v 1)+s 1*(u 1*v 2+u 2*v 1)+s 2*(u 2*v 2) := by
  simp [flatCylinderMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  ring

lemma cylinderSlopeJet_covector_ae (r R : ℝ) (k : Fin 3) :
    cylinderSlopeJet r R k.succ=ᵐ[(FiniteAxisMeasure R).prod volume]
      fun _ => ((r • Pi.single 0 (1:ℝ)) k : ℂ) := by
  fin_cases k
  · change (cylinderSlopeJet r R 1)=ᵐ[(FiniteAxisMeasure R).prod volume]
      (fun _ => (((r • Pi.single 0 (1:ℝ)) (0:Fin 3)):ℂ))
    simp only [Pi.smul_apply,Pi.single_apply,ite_true,smul_eq_mul,mul_one]
    rw [cylinderSlopeJet_derivative]
    have h1 := cylinderTensor_ae
      (smoothFiniteAxisLp (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R) (mFourierLp 2 0)
    have h2 := (Measure.quasiMeasurePreserving_fst (μ:=FiniteAxisMeasure R)
      (ν:=(volume : Measure (UnitAddTorus (Fin 2))))).ae
      (smoothFiniteAxisLp_ae (continuous_const : Continuous (fun _ : ℝ => (r:ℂ))) R)
    have h3 := (Measure.quasiMeasurePreserving_snd (μ:=FiniteAxisMeasure R)
      (ν:=(volume : Measure (UnitAddTorus (Fin 2))))).ae (coeFn_mFourierLp 2 0)
    filter_upwards [h1,h2,h3] with z hz ht hθ
    change cylinderTensor _ _ z=_
    rw [hz,ht,hθ]
    simp [mFourier]
  · change (cylinderSlopeJet r R 2)=ᵐ[(FiniteAxisMeasure R).prod volume]
      (fun _ => (((r • Pi.single 0 (1:ℝ)) (1:Fin 3)):ℂ))
    simp only [Pi.smul_apply,Pi.single_apply,show (1:Fin 3)≠0 by decide,
      ite_false,smul_eq_mul,mul_zero,Complex.ofReal_zero]
    rw [(cylinderSlopeJet_angular r R).1]
    filter_upwards [Lp.coeFn_zero (ℂ) 2 ((FiniteAxisMeasure R).prod volume)] with z hz
    exact hz
  · change (cylinderSlopeJet r R 3)=ᵐ[(FiniteAxisMeasure R).prod volume]
      (fun _ => (((r • Pi.single 0 (1:ℝ)) (2:Fin 3)):ℂ))
    simp only [Pi.smul_apply,Pi.single_apply,show (2:Fin 3)≠0 by decide,
      ite_false,smul_eq_mul,mul_zero,Complex.ofReal_zero]
    rw [(cylinderSlopeJet_angular r R).2]
    filter_upwards [Lp.coeFn_zero (ℂ) 2 ((FiniteAxisMeasure R).prod volume)] with z hz
    exact hz

lemma cylinderEndJet_covector_ae (s : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (r R : ℝ) (hR : 0≤R) (f : spectralTraceGraph (torusRate s)) :
    ∀ᵐ z∂(FiniteAxisMeasure R).prod volume,
      (fun k : Fin 3 => (cylinderEndJet s hs r R hR f k.succ z).re)=
        fullEndFlatCovector s f r z.1 z.2 := by
  have h (k : Fin 3) : ∀ᵐ z∂(FiniteAxisMeasure R).prod volume,
      (cylinderEndJet s hs r R hR f k.succ z).re=fullEndFlatCovector s f r z.1 z.2 k := by
    filter_upwards [Lp.coeFn_add (endPoissonJet s hs R hR f k.succ)
      (cylinderSlopeJet r R k.succ),endPoissonJet_ae s hs R hR f k.succ,
      cylinderSlopeJet_covector_ae r R k] with z hz hp hr
    change ((endPoissonJet s hs R hR f k.succ+cylinderSlopeJet r R k.succ) z).re=_
    rw [hz]
    simp only [Pi.add_apply,hp,hr,Complex.add_re,Complex.ofReal_re,fullEndFlatCovector]
  filter_upwards [ae_all_iff.mpr h] with z hz
  exact funext hz

lemma flatCylinderEnergy_real_integral (s : Fin 3 → ℝ) {R : ℝ}
    (u v : FiniteCylinderJets R)
    (hv : ∀ k : Fin 3,∀ᵐ z∂(FiniteAxisMeasure R).prod volume,(v k.succ z).im=0) :
    Integrable (fun z => (fun k : Fin 3 => (u k.succ z).re) ⬝ᵥ
      (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re)))
        ((FiniteAxisMeasure R).prod volume) ∧
    (flatCylinderEnergy s u v).re=
      ∫ z,(fun k : Fin 3 => (u k.succ z).re) ⬝ᵥ
        (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re))
          ∂(FiniteAxisMeasure R).prod volume := by
  let P (i j : Fin 4) := fun z => inner ℂ (u i z) (v j z)
  have hP (i j : Fin 4) : Integrable (P i j) ((FiniteAxisMeasure R).prod volume) :=
    L2.integrable_inner (𝕜:=ℂ) _ _
  let F := fun z => P 1 1 z+(s 0:ℂ)*P 2 2 z+
    (s 1:ℂ)*(P 2 3 z+P 3 2 z)+(s 2:ℂ)*P 3 3 z
  have hF : Integrable F ((FiniteAxisMeasure R).prod volume) :=
    (((hP 1 1).add ((hP 2 2).const_mul (s 0:ℂ))).add
      (((hP 2 3).add (hP 3 2)).const_mul (s 1:ℂ))).add ((hP 3 3).const_mul (s 2:ℂ))
  have he : (fun z => (F z).re)=ᵐ[(FiniteAxisMeasure R).prod volume]
      (fun z => (fun k : Fin 3 => (u k.succ z).re) ⬝ᵥ
        (flatCylinderMatrix s*ᵥ(fun k : Fin 3 => (v k.succ z).re))) := by
    filter_upwards [hv 0,hv 1,hv 2] with z h1 h2 h3
    change (v 1 z).im=0 at h1
    change (v 2 z).im=0 at h2
    change (v 3 z).im=0 at h3
    rw [flatCylinderMatrix_mixed]
    simp [F,P,RCLike.inner_apply,Complex.mul_re,h1,h2,h3]
    ring
  refine ⟨hF.re.congr he,?_⟩
  rw [←integral_congr_ae he]
  change _ = ∫ z,RCLike.re (F z) ∂(FiniteAxisMeasure R).prod volume
  rw [integral_re hF]
  congr 1
  change flatCylinderEnergy s u v = ∫ z,F z ∂(FiniteAxisMeasure R).prod volume
  unfold F
  rw [integral_add (f:=fun z => P 1 1 z+(s 0:ℂ)*P 2 2 z+
      (s 1:ℂ)*(P 2 3 z+P 3 2 z)) (g:=fun z => (s 2:ℂ)*P 3 3 z)
      (((hP 1 1).add ((hP 2 2).const_mul (s 0:ℂ))).add
        (((hP 2 3).add (hP 3 2)).const_mul (s 1:ℂ))) ((hP 3 3).const_mul (s 2:ℂ)),
    integral_add (f:=fun z => P 1 1 z+(s 0:ℂ)*P 2 2 z)
      (g:=fun z => (s 1:ℂ)*(P 2 3 z+P 3 2 z))
      ((hP 1 1).add ((hP 2 2).const_mul (s 0:ℂ)))
      (((hP 2 3).add (hP 3 2)).const_mul (s 1:ℂ)),
    integral_add (f:=P 1 1) (g:=fun z => (s 0:ℂ)*P 2 2 z)
      (hP 1 1) ((hP 2 2).const_mul (s 0:ℂ)),integral_const_mul,
    integral_const_mul,integral_const_mul,integral_add (hP 2 3) (hP 3 2)]
  rfl

end ScalarConductivity

end
end

end OAI
