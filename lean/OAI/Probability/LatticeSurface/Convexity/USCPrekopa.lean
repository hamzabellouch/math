import Mathlib
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.USCEnvelope
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
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

lemma tendsto_cubeIntegral_envelope {n : ℕ} {f : (Fin n → ℝ) → ℝ} {a b : ℝ}
    (hf : UpperSemicontinuous f) (hab : a≤b) (hf0 : ∀ x∈cube n a b,0≤f x) :
    Tendsto (fun k => cubeIntegral (USCEnvelope.envelope (cube n a b) f k) a b) atTop
      (𝓝 (cubeIntegral f a b)) := by
  have hK := compact_cube n a b
  have hne : (cube n a b).Nonempty := ⟨fun _ => a,mem_cube.mpr fun _ => ⟨le_rfl,hab⟩⟩
  obtain ⟨M,hM⟩ := (hf.upperSemicontinuousOn _).bddAbove_of_isCompact hK
  have hbd : ∀ z∈cube n a b,f z≤M := fun z hz => hM (mem_image_of_mem f hz)
  have hbound : IntegrableOn (fun _ : Fin n → ℝ => M) (cube n a b) :=
    continuous_const.continuousOn.integrableOn_compact hK
  exact tendsto_integral_of_dominated_convergence (μ:=volume.restrict (cube n a b))
    (fun _ => M) (fun k => (USCEnvelope.continuous_envelope hK hf k).aestronglyMeasurable)
    hbound (fun k => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (USCEnvelope.envelope_nonneg hK hf hne hf0 k x)]
      exact USCEnvelope.envelope_bound hK hf hne hf0 hbd k x)
    ((ae_restrict_mem (measurable_cube _ _ _)).mono fun x hx =>
      USCEnvelope.tendsto_envelope hK hf hf0 hx)

end FacetVolume

namespace FacetVolume

theorem compact_usc_prekopa_leindler (n : ℕ) {a b s t : ℝ}
    {f g h : (Fin n → ℝ) → ℝ} (hf : UpperSemicontinuous f)
    (hg : UpperSemicontinuous g) (hh : UpperSemicontinuous h)
    (hab : a<b) (hs : 0<s) (ht : 0<t) (hst : s+t=1)
    (hf0 : ∀ x∈cube n a b,0≤f x) (hg0 : ∀ x∈cube n a b,0≤g x)
    (hh0 : ∀ x∈cube n a b,0≤h x)
    (hcomb : ∀ x∈cube n a b,∀ y∈cube n a b,
      (f x)^s*(g y)^t≤h (s • x+t • y)) :
    (cubeIntegral f a b)^s*(cubeIntegral g a b)^t≤cubeIntegral h a b := by
  classical
  have hhI : 0≤cubeIntegral h a b := cubeIntegral_nonneg hh0
  by_cases hfp : ∃ x∈cube n a b,0<f x
  swap
  · have hfz : ∀ x∈cube n a b,f x=0 := by
      intro x hx
      exact le_antisymm (le_of_not_gt (fun hp => hfp ⟨x,hx,hp⟩)) (hf0 x hx)
    have hi : cubeIntegral f a b=0 := by
      unfold cubeIntegral
      rw [setIntegral_congr_fun (measurable_cube _ _ _) hfz]
      simp
    rw [hi,Real.zero_rpow hs.ne',zero_mul]
    exact hhI
  by_cases hgp : ∃ x∈cube n a b,0<g x
  swap
  · have hgz : ∀ x∈cube n a b,g x=0 := by
      intro x hx
      exact le_antisymm (le_of_not_gt (fun hp => hgp ⟨x,hx,hp⟩)) (hg0 x hx)
    have hi : cubeIntegral g a b=0 := by
      unfold cubeIntegral
      rw [setIntegral_congr_fun (measurable_cube _ _ _) hgz]
      simp
    rw [hi,Real.zero_rpow ht.ne',mul_zero]
    exact hhI
  have hK := compact_cube n a b
  have hKc : Convex ℝ (cube n a b) := convex_Icc _ _
  have hne : (cube n a b).Nonempty := ⟨fun _ => a,mem_cube.mpr fun _ => ⟨le_rfl,hab.le⟩⟩
  have hPL (k : ℕ) := cube_prekopa_leindler n
    (USCEnvelope.continuous_envelope hK hf k)
    (USCEnvelope.continuous_envelope hK hg k)
    (USCEnvelope.continuous_envelope hK hh k)
    hab hs.le ht.le hst
    (fun x _ => USCEnvelope.envelope_pos hK hf hfp k x)
    (fun x _ => USCEnvelope.envelope_pos hK hg hgp k x)
    (fun x _ => USCEnvelope.envelope_nonneg hK hh hne hh0 k x)
    (fun x _ y _ => USCEnvelope.envelope_combination hK hKc hne hf hg hh hf0 hg0
      hs.le ht.le hst hcomb k x y)
  exact le_of_tendsto_of_tendsto
    (((tendsto_cubeIntegral_envelope hf hab.le hf0).rpow_const (.inr hs.le)).mul
      ((tendsto_cubeIntegral_envelope hg hab.le hg0).rpow_const (.inr ht.le)))
    (tendsto_cubeIntegral_envelope hh hab.le hh0) (Eventually.of_forall hPL)

end FacetVolume

end
end

end OAI
