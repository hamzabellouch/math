import Mathlib
import OAI.Probability.LatticeSurface.Convexity.Concentration
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.DensityOverlap
import OAI.Probability.LatticeSurface.Convexity.DensityPrekopa
import OAI.Probability.LatticeSurface.Convexity.EvenIntegral
import OAI.Probability.LatticeSurface.Convexity.LinearCoordinates
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

open scoped ENNReal NNReal

open MeasureTheory Measure

namespace Density

open MeasureTheory

lemma integral_comp_jacobian {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasureSpace E] [BorelSpace E]
    [MeasureSpace F] [BorelSpace F]
    (e : E ≃L[ℝ] F) (c : ℝ≥0) (hc : Measure.map e volume=(c:ENNReal) • volume)
    (f : F → ℝ) (hf : Measurable f) : (∫ x,f (e x))=(c:ℝ)*(∫ y,f y) := by
  rw [← integral_map e.continuous.measurable.aemeasurable hf.aestronglyMeasurable,hc,integral_smul_measure]
  simp

end Density

namespace Overlap

open MeasureTheory Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]

lemma overlap_equiv {p : E → ℝ} (e : E ≃L[ℝ] F) (l : E →L[ℝ] ℝ) (m : F →L[ℝ] ℝ)
    {T R S : ℝ} (he : ∀ x,m (e x)=l x)
    (hp : UpperSemicontinuous p) (hp0 : ∀ x,0≤p x)
    (hpK : ∀ x,R<‖x‖ → p x=0) (hqK : ∀ y,S<‖y‖ → p (e.symm y)=0) (x : E) :
    overlap (fun y => p (e.symm y)) m T S (e x)=overlap p l T R x := by
  have hq := hp.comp e.symm.continuous
  apply le_antisymm
  · apply overlap_le (overlap_nonneg _ _ _ _ _)
    intro χ hχ
    have heχ : l (e.symm χ)=T := by rw [← he];simpa using hχ.2
    have hb := kernel_le_overlap_all hp hp0 hpK x (e.symm χ) heχ
    simpa [kernel,map_add,map_sub] using hb
  · apply overlap_le (overlap_nonneg _ _ _ _ _)
    intro χ hχ
    have heχ : m (e χ)=T := (he χ).trans hχ.2
    have hb := kernel_le_overlap_all hq (fun _ => hp0 _) hqK (e x) (e χ) heχ
    simpa [Function.comp_def,kernel,← map_add,← map_sub] using hb

end Overlap

open scoped ENNReal NNReal

open MeasureTheory Set

theorem linear_overlap_geometric_tail {I : Type*} [Fintype I]
    {p : (I → ℝ) → ℝ} {R T ρ : ℝ} (l : (I → ℝ) →L[ℝ] ℝ)
    (hR : 0<R) (hT : 0<T) (hρ : 0<ρ) (hρ1 : ρ<1)
    (hp : UpperSemicontinuous p) (hp0 : ∀ x,0≤p x)
    (hpK : ∀ x,R<‖x‖ → p x=0) (heven : ∀ x,p (-x)=p x)
    (hlc : Density.LogConcave p) (hZ : 0<∫ x,p x)
    (hdef : (∫ x,Overlap.overlap p l T R x)≤(1-ρ)*(∫ x,p x)) :
    ∀ j : ℕ,(∫ x in {x | (j:ℝ)*T≤|l x|},p x)≤(1-ρ)^j*(∫ x,p x) := by
  classical
  by_cases hl : l=0
  · intro j
    by_cases hj : j=0
    · subst j
      simp only [Nat.cast_zero,zero_mul,pow_zero,one_mul]
      have hs : {x : I → ℝ | 0≤|l x|}=univ := by ext x;simp
      rw [hs,setIntegral_univ]
    · have hpos := mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hj)) hT
      have hs : {x : I → ℝ | (j:ℝ)*T≤|l x|}=∅ := by ext x;simp [hl,not_le.mpr hpos]
      rw [hs,setIntegral_empty]
      exact mul_nonneg (pow_nonneg (by linarith) _) hZ.le
  obtain ⟨n,e,c,hc,he,hmap⟩ := linear_statistic_coordinates l hl
  have hc' : (0:ℝ)<c := hc
  let q : (Fin (n+1) → ℝ) → ℝ := fun y => p (e.symm y)
  let S : ℝ := ‖(e : (I → ℝ) →L[ℝ] (Fin (n+1) → ℝ))‖*R+1
  have hS : 0<S := by dsimp [S];positivity
  have hq : UpperSemicontinuous q := hp.comp e.symm.continuous
  have hq0 (y) : 0≤q y := hp0 _
  have hqK (y) (hy : S<‖y‖) : q y=0 := by
    apply hpK
    by_contra hh
    have hh := le_of_not_gt hh
    have hn := (e : (I → ℝ) →L[ℝ] (Fin (n+1) → ℝ)).le_opNorm (e.symm y)
    simp only [ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] at hn
    have hn' := mul_le_mul_of_nonneg_left hh (norm_nonneg (e : (I → ℝ) →L[ℝ] (Fin (n+1) → ℝ)))
    dsimp [S] at hy
    linarith
  have hqe (y) : q (-y)=q y := by simpa [q,map_neg] using heven (e.symm y)
  have hqlc : Density.LogConcave q := by
    intro x y s t hs ht hst
    simpa [q,map_add,map_smul] using hlc (e.symm x) (e.symm y) s t hs ht hst
  have hmass : (∫ x,p x)=(c:ℝ)*(∫ y,q y) := by
    have hh := Density.integral_comp_jacobian e c hmap q hq.measurable
    simpa [q] using hh
  have hqZ : 0<∫ y,q y := (mul_pos_iff_of_pos_left hc').mp (hmass ▸ hZ)
  have ho (x) : Overlap.overlap q (ContinuousLinearMap.proj 0) T S (e x)=Overlap.overlap p l T R x :=
    Overlap.overlap_equiv e l (ContinuousLinearMap.proj 0) he hp hp0 hpK hqK x
  have hO : (∫ x,Overlap.overlap p l T R x)=(c:ℝ)*(∫ y,Overlap.overlap q (ContinuousLinearMap.proj 0) T S y) := by
    have hh := Density.integral_comp_jacobian e c hmap _ (Overlap.usc_overlap hq hq0 (ContinuousLinearMap.proj 0) T S).measurable
    simpa only [ho] using hh
  have hqdef : (∫ y,Overlap.overlap q (ContinuousLinearMap.proj 0) T S y)≤(1-ρ)*(∫ y,q y) := by
    rw [hO,hmass] at hdef
    nlinarith
  have htail := overlap_geometric_tail hS hT hρ hρ1 hq hq0 hqK hqe hqlc hqZ hqdef
  intro j
  let U := {y : Fin (n+1) → ℝ | (j:ℝ)*T≤|y 0|}
  let V := {x : I → ℝ | (j:ℝ)*T≤|l x|}
  have hU : MeasurableSet U := (isClosed_le continuous_const ((continuous_apply 0).abs)).measurableSet
  have hV : MeasurableSet V := (isClosed_le continuous_const l.continuous.abs).measurableSet
  have htailmap : (∫ x in V,p x)=(c:ℝ)*(∫ y in U,q y) := by
    have hh := Density.integral_comp_jacobian e c hmap (U.indicator q) (hq.measurable.indicator hU)
    have hid : (fun x => U.indicator q (e x))=V.indicator p := by
      funext x
      by_cases hx : l x∈Set.Ici ((j:ℝ)*T)
      all_goals
        by_cases hv : x∈V
        · have hu : e x∈U := by simpa [U,V,he] using hv
          simp [Set.indicator_of_mem hu,Set.indicator_of_mem hv,q]
        · have hu : e x∉U := by simpa [U,V,he] using hv
          simp [Set.indicator_of_notMem hu,Set.indicator_of_notMem hv]
    rw [hid,integral_indicator hV,integral_indicator hU] at hh
    exact hh
  rw [htailmap,hmass]
  calc
    _ ≤ (c:ℝ)*((1-ρ)^j*(∫ y,q y)) := mul_le_mul_of_nonneg_left (htail j) hc'.le
    _ = _ := by ring

end
end
end

end OAI
