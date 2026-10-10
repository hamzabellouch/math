import Mathlib
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.DensityOverlap
import OAI.Probability.LatticeSurface.Convexity.DensityPrekopa
import OAI.Probability.LatticeSurface.Convexity.EvenIntegral
import OAI.Probability.LatticeSurface.Convexity.MarginalOverlap
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.Survival
import OAI.Probability.LatticeSurface.Convexity.USCEnvelope
import OAI.Probability.LatticeSurface.Convexity.USCGlobal
import OAI.Probability.LatticeSurface.Convexity.USCMarginal
import OAI.Probability.LatticeSurface.Convexity.USCPrekopa
import OAI.Probability.LatticeSurface.Convexity.USCProduct
import OAI.Probability.LatticeSurface.Convexity.Unimodal
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.CompactOverlap
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

end FacetVolume

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

open Set Filter

open scoped Topology

noncomputable section

namespace Overlap

end Overlap

namespace USCEnvelope

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end USCEnvelope

namespace FacetVolume

end FacetVolume

namespace FacetVolume

end FacetVolume

namespace Density

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

end Density

namespace FacetVolume

end FacetVolume

namespace Overlap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

end Overlap

namespace FacetVolume

end FacetVolume

namespace Density

open FacetVolume

end Density

namespace Density

end Density

namespace Density

end Density

namespace Density

end Density

namespace FacetVolume

end FacetVolume

theorem overlap_geometric_tail {n : ℕ} {p : (Fin (n+1) → ℝ) → ℝ} {R T ρ : ℝ}
    (hR : 0<R) (hT : 0<T) (_hρ : 0<ρ) (hρ1 : ρ<1)
    (hp : UpperSemicontinuous p) (hp0 : ∀ x,0≤p x)
    (hpK : ∀ x,R<‖x‖ → p x=0) (heven : ∀ x,p (-x)=p x)
    (hlc : Density.LogConcave p) (hZ : 0<∫ x,p x)
    (hdef : (∫ x,Overlap.overlap p (ContinuousLinearMap.proj 0) T R x) ≤
      (1-ρ)*(∫ x,p x)) :
    ∀ j : ℕ,(∫ x in {x | (j:ℝ)*T≤|x 0|},p x) ≤ (1-ρ)^j*(∫ x,p x) := by
  let a : ℝ → ℝ := fun r => ∫ z : Fin n → ℝ,p (Fin.cons r z)
  let A : (Fin (n+1) → ℝ) → ℝ := Overlap.overlap p (ContinuousLinearMap.proj 0) T R
  let B : ℝ → ℝ := fun r => Real.sqrt (a (r-T)*a (r+T))
  let H : ℝ → ℝ := fun r => (2/(∫ x,p x))*(∫ x in Ici r,a x)
  have ha0 (r : ℝ) : 0≤a r := integral_nonneg (fun z => hp0 _)
  have hpC := FacetVolume.support_cube_of_norm hpK
  have hu : UpperSemicontinuous a := FacetVolume.usc_marginal hp hp0 (by linarith) hpC
  have haK := FacetVolume.marginal_support hpK
  have hai : Integrable a := Density.integrable_real_usc hu ha0 haK
  have hpi : Integrable p := FacetVolume.integrable_usc_compact hp hp0 hpC
  have hmass : (∫ x,a x)=∫ x,p x := (FacetVolume.integral_fin_cons hpi).symm
  have halc : Density.LogConcave a := FacetVolume.logConcave_marginal hp hp0 (by linarith) hpC hlc
  have hae := FacetVolume.marginal_even heven
  have hAu : UpperSemicontinuous A := Overlap.usc_overlap hp hp0 _ _ _
  have hA0 (x : Fin (n+1) → ℝ) : 0≤A x := Overlap.overlap_nonneg _ _ _ _ _
  have hAK (x : Fin (n+1) → ℝ) (hx : R<‖x‖) : A x=0 := Overlap.overlap_support hpK hx
  have hAi : Integrable A := FacetVolume.integrable_usc_compact hAu hA0 (FacetVolume.support_cube_of_norm hAK)
  have hAmu : UpperSemicontinuous (fun r => ∫ z : Fin n → ℝ,A (Fin.cons r z)) :=
    FacetVolume.usc_marginal hAu hA0 (by linarith) (FacetVolume.support_cube_of_norm hAK)
  have hAmi : Integrable (fun r => ∫ z : Fin n → ℝ,A (Fin.cons r z)) :=
    Density.integrable_real_usc hAmu (fun r => integral_nonneg fun z => hA0 _)
      (FacetVolume.marginal_support hAK)
  have hBu : UpperSemicontinuous B := Overlap.usc_sqrt
    (Overlap.usc_mul (hu.comp (continuous_id.sub continuous_const))
      (hu.comp (continuous_id.add continuous_const)) (fun x => ha0 _) (fun x => ha0 _))
  have hBi : Integrable B := Density.integrable_real_usc hBu (fun x => Real.sqrt_nonneg _)
    (Density.midpoint_support haK T)
  have hBbound : (∫ x,B x)≤(1-ρ)*(∫ x,p x) := by
    calc
      _ ≤ ∫ r : ℝ,∫ z : Fin n → ℝ,A (Fin.cons r z) :=
        integral_mono hBi hAmi (fun r => FacetVolume.marginal_overlap hR hp hp0 hpK r T)
      _ = ∫ x,A x := (FacetVolume.integral_fin_cons hAi).symm
      _ ≤ _ := hdef
  have hH0 (x : ℝ) : 0≤H x := mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ici (fun x _ => ha0 x))
  have hHlc : Density.LogConcave H := Density.logConcave_const_mul
    (fun r => setIntegral_nonneg measurableSet_Ici (fun x _ => ha0 x))
    (Density.logConcave_survival hu ha0 (by linarith) haK halc) (by positivity)
  have hHzero : H 0=1 := by
    have hm := Density.even_integral hai hae
    rw [hmass] at hm
    dsimp [H]
    field_simp
    linarith
  have hHT : H T≤1-ρ := by
    have hh := (Density.overlap_survival_bound hT.le hu ha0 haK hae halc).trans hBbound
    dsimp [H]
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hZ).2 (by nlinarith)
  intro j
  change (∫ x in {x : Fin (n+1) → ℝ | x 0∈{r : ℝ | (j:ℝ)*T≤|r|}},p x)≤_
  rw [FacetVolume.integral_coordinate_set hpi (show MeasurableSet {r : ℝ | (j:ℝ)*T≤|r|} from
    isClosed_le continuous_const continuous_abs |>.measurableSet)]
  change (∫ r in {r : ℝ | (j:ℝ)*T≤|r|},a r)≤_
  by_cases hj : j=0
  · subst j
    simp only [Nat.cast_zero,zero_mul,pow_zero,one_mul]
    have he : {r : ℝ | 0≤|r|}=univ := by ext r;simp
    rw [he,setIntegral_univ,hmass]
  have hgeo := Density.geometric_tail hH0 hHlc hHzero (by linarith : 0≤1-ρ) hHT j
  rw [Density.even_tail hai hae (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj)) hT)]
  dsimp [H] at hgeo
  rw [div_mul_eq_mul_div] at hgeo
  exact (div_le_iff₀ hZ).mp hgeo

end
end
end

end OAI
