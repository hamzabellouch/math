import Mathlib
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.USCEnvelope
import OAI.Probability.LatticeSurface.Convexity.USCGlobal
import OAI.Probability.LatticeSurface.Convexity.USCPrekopa
import OAI.Probability.LatticeSurface.Convexity.USCProduct
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

omit [NormedSpace ℝ E] in
lemma le_envelope_global {K : Set E} {f : E → ℝ} (hK : IsCompact K)
    (hf : UpperSemicontinuous f) (hne : K.Nonempty) (hf0 : ∀ x∈K,0≤f x)
    (hfK : ∀ x,x∉K → f x=0) (k : ℕ) (x : E) : f x≤envelope K f k x := by
  by_cases hx : x∈K
  · exact self_le_envelope hK hf hf0 k hx
  · rw [hfK x hx]
    exact envelope_nonneg hK hf hne hf0 k x

omit [NormedSpace ℝ E] in
lemma tendsto_envelope_global {K : Set E} {f : E → ℝ} (hK : IsCompact K)
    (hf : UpperSemicontinuous f) (hne : K.Nonempty) (hf0 : ∀ x,0≤f x)
    (hfK : ∀ x,x∉K → f x=0) (x : E) :
    Tendsto (fun k => envelope K f k x) atTop (𝓝 (f x)) := by
  obtain ⟨M,hM⟩ := (hf.upperSemicontinuousOn K).bddAbove_of_isCompact hK
  have hbd : ∀ z∈K,f z≤M := fun z hz => hM (mem_image_of_mem f hz)
  obtain ⟨z₀,hz₀⟩ := hne
  have hM0 : 0≤M := (hf0 z₀).trans (hbd z₀ hz₀)
  refine tendsto_order.2 ⟨?_,?_⟩
  · intro b hb
    exact Eventually.of_forall fun k => hb.trans_le
      (le_envelope_global hK hf ⟨z₀,hz₀⟩ (fun z _ => hf0 z) hfK k x)
  · intro b hb
    obtain ⟨δ,hδ,hnear⟩ := Metric.mem_nhds_iff.mp (hf x b hb)
    have hlim : Tendsto (fun k : ℕ => M*Real.exp (-(k:ℝ)*δ)) atTop (𝓝 0) := by
      have ht := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_natCast_atTop_atTop : Tendsto (fun k : ℕ => (k:ℝ)) atTop atTop).atTop_mul_const hδ)
      simpa only [mul_zero,Function.comp_def,neg_mul] using ht.const_mul M
    filter_upwards [(tendsto_order.1 hlim).2 b ((hf0 x).trans_lt hb)] with k hk
    obtain ⟨z,hz,heq⟩ := envelope_max hK hf ⟨z₀,hz₀⟩ (fun z _ => hf0 z) k x
    rw [heq]
    have he : Real.exp (-(k:ℝ)*dist x z.1)≤1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) dist_nonneg)
    by_cases hd : dist z.1 x<δ
    · have hzbd : z.2<b := hz.2.2.trans_lt (hnear hd)
      exact (mul_le_mul_of_nonneg_left he hz.2.1).trans_lt (by simpa using hzbd)
    · have hd' : δ≤dist x z.1 := by simpa [dist_comm] using le_of_not_gt hd
      have he' : Real.exp (-(k:ℝ)*dist x z.1)≤Real.exp (-(k:ℝ)*δ) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left hd' (neg_nonpos.mpr (Nat.cast_nonneg _))
      exact (mul_le_mul (hz.2.2.trans (hbd z.1 hz.1)) he'
        (Real.exp_pos _).le hM0).trans_lt hk

end USCEnvelope

namespace FacetVolume

lemma usc_marginal {n : ℕ} {p : (Fin (n+1) → ℝ) → ℝ} {a b : ℝ}
    (hp : UpperSemicontinuous p) (hp0 : ∀ z,0≤p z) (hab : a≤b)
    (hpK : ∀ z,z∉cube (n+1) a b → p z=0) :
    UpperSemicontinuous (fun r => ∫ z : Fin n → ℝ,p (Fin.cons r z)) := by
  let K := cube (n+1) a b
  have hK : IsCompact K := compact_cube _ _ _
  have hne : K.Nonempty := ⟨fun _ => a,mem_cube.mpr fun _ => ⟨le_rfl,hab⟩⟩
  let F : ℕ → ℝ → ℝ := fun k r => cubeIntegral
    (fun z => USCEnvelope.envelope K p k (Fin.cons r z)) a b
  have hF (k : ℕ) : Continuous (F k) := continuous_cube_marginal
    (USCEnvelope.continuous_envelope hK hp k) a b
  have hsliceK (r : ℝ) : ∀ z,z∉cube n a b → p (Fin.cons r z)=0 := by
    intro z hz
    apply hpK
    intro h
    exact hz (fin_cons_mem_cube.mp h).2
  have hsliceI (r : ℝ) : Integrable (fun z => p (Fin.cons r z)) :=
    integrable_usc_compact (hp.comp (continuous_const.finCons continuous_id))
      (fun z => hp0 _) (hsliceK r)
  have hle (k : ℕ) (r : ℝ) : (∫ z,p (Fin.cons r z))≤F k r := by
    rw [integral_eq_cubeIntegral (hsliceK r)]
    apply setIntegral_mono_on (hsliceI r).integrableOn
      (((USCEnvelope.continuous_envelope hK hp k).comp (continuous_const.finCons continuous_id)).continuousOn.integrableOn_compact (compact_cube _ _ _))
    · exact measurable_cube _ _ _
    · intro z hz
      exact USCEnvelope.le_envelope_global hK hp hne (fun z _ => hp0 z) hpK k _
  obtain ⟨M,hM⟩ := (hp.upperSemicontinuousOn K).bddAbove_of_isCompact hK
  have hlim (r : ℝ) : Tendsto (fun k => F k r) atTop (𝓝 (∫ z,p (Fin.cons r z))) := by
    rw [integral_eq_cubeIntegral (hsliceK r)]
    exact tendsto_integral_of_dominated_convergence (μ:=volume.restrict (cube n a b))
      (fun _ => M)
      (fun k => ((USCEnvelope.continuous_envelope hK hp k).comp
        (continuous_const.finCons continuous_id)).aestronglyMeasurable)
      (continuous_const.continuousOn.integrableOn_compact (compact_cube _ _ _))
      (fun k => Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs,abs_of_nonneg (USCEnvelope.envelope_nonneg hK hp hne (fun z _ => hp0 z) k _)]
        exact USCEnvelope.envelope_bound hK hp hne (fun z _ => hp0 z)
          (fun z hz => hM (mem_image_of_mem p hz)) k _)
      (Eventually.of_forall fun z => USCEnvelope.tendsto_envelope_global hK hp hne hp0 hpK _)
  intro r c hc
  obtain ⟨k,hk⟩ := ((tendsto_order.1 (hlim r)).2 c hc).exists
  filter_upwards [((hF k).continuousAt : ContinuousAt (F k) r).preimage_mem_nhds
    (isOpen_Iio.mem_nhds hk)] with y hy
  exact (hle k y).trans_lt hy

end FacetVolume

end
end
end

end OAI
