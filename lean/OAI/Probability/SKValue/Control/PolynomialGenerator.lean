import Mathlib
import OAI.Probability.SKValue.Equations.ForcedGenerator
import OAI.Probability.SKValue.Equations.PolynomialForced
import OAI.Probability.SKValue.Equations.PolynomialObservable
import OAI.Probability.SKValue.Processes.ForcedDiffusion

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
namespace JetExpr
noncomputable def sourceA (e:JetExpr):JetExpr := mul (const (1/2)) (add e.timeB (e.spatialIter 2))
noncomputable def sourceP (e:JetExpr):JetExpr := add e.timeP (mul (coord 0) e.spatial)
end JetExpr
lemma SmoothEvolution.polyJet_source {T:ℝ} {γ:ℝ → ℝ} {V:ℝ → ℝ → ℝ}
    (h:SmoothEvolution T γ V) (e:JetExpr) {t:ℝ} (ht:t∈Icc (0:ℝ) T) (x:ℝ):
    forcedSource γ (fun t ↦ deriv (V t)) (polyJet V e) (polyJet V e.timeB) (polyJet V e.timeP) t x=
      polyJet V e.sourceA t x+γ t*polyJet V e.sourceP t x := by
  have hd:deriv (polyJet V e t)=polyJet V e.spatial t := funext (fun y ↦ (h.polyJet_hasDeriv e ht y).deriv)
  have hdd:=h.polyJet_iterated e ht 2
  simp only [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_zero] at hdd
  unfold forcedSource
  rw [hdd,hd]
  simp only [polyJet,JetExpr.sourceA,JetExpr.sourceP,JetExpr.eval,iteratedDeriv_zero]

lemma IsDiffusion.polyJet_generator {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {T:ℝ} (hT:0<T) (hT1:T<1) (e:JetExpr):
    (∫ z,polyJet (phi W γ) e T (X T z) ∂W.μ)=polyJet (phi W γ) e 0 0+
      ∫ t in (0:ℝ)..T, ((∫ z,polyJet (phi W γ) e.sourceA t (X t z) ∂W.μ)+
        γ.coeff t*(∫ z,polyJet (phi W γ) e.sourceP t (X t z) ∂W.μ)) := by
  have h:=phi_evolution W γ ⟨hT.le,hT1⟩
  have hm:MonotoneOn γ.coeff (Icc (0:ℝ) T):=γ.monotone.mono (fun _ ht ↦ ⟨ht.1,ht.2.trans_lt hT1⟩)
  have hi:IntervalIntegrable γ.coeff volume 0 T := by
    apply MonotoneOn.intervalIntegrable
    simpa only [uIcc_of_le hT.le] using hm
  obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩:=sourceStripRegularity W γ T ⟨hT.le,hT1⟩
  obtain ⟨K',L',hf⟩:=h.polynomial_forced hT.le hi hm (fun t ht ↦ γ.nonneg _ ⟨ht.1,ht.2.trans_lt hT1⟩)
    hG.bounded e
  have hjA:=h.polyJet_joint e.sourceA
  have hjP:=h.polyJet_joint e.sourceP
  obtain ⟨A,hA,hAb⟩:=hjA.bounded
  obtain ⟨P,hP,hPb⟩:=hjP.bounded
  obtain ⟨D1,hD1⟩:=hjA.spatial
  obtain ⟨D2,hD2⟩:=hjP.spatial
  have hlimA:=hX.weightedObservable_tendsto hT hT1 (η:=fun _ ↦ (1:ℝ)) (fun _ _ _ _ _ ↦ le_rfl)
    (by norm_num) hA hjA.continuous hAb hD1
  have hlimP:=hX.weightedObservable_tendsto hT hT1 hm (γ.nonneg _ (by constructor <;> norm_num))
    hP hjP.continuous hPb hD2
  simp only [one_mul] at hlimA
  have hXM (t:ℝ) (ht:t∈Icc (0:ℝ) T):AEStronglyMeasurable (X t) W.μ :=
    (hX.memLp (p:=2) ⟨ht.1,ht.2.trans hT1.le⟩ (by norm_num)).aestronglyMeasurable
  have hpaths:=hX.strip_paths hT.le hT1 hLu (fun t ht s hs x y ↦ hu s hs t ht y x)
  have hAi:IntervalIntegrable (fun t ↦ ∫ z,polyJet (phi W γ) e.sourceA t (X t z) ∂W.μ) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT.le]
    exact mean_observable_continuous hjA.continuous hAb hXM (hpaths.mono (fun _ hz ↦ hz.1))
  have hPi:IntervalIntegrable (fun t ↦ γ.coeff t*(∫ z,polyJet (phi W γ) e.sourceP t (X t z) ∂W.μ)) volume 0 T := by
    apply hi.mul_continuousOn
    rw [uIcc_of_le hT.le]
    exact mean_observable_continuous hjP.continuous hPb hXM (hpaths.mono (fun _ hz ↦ hz.1))
  apply hf.diffusion_generator_of_source_limit W.brownian.toIsPreBrownianReal hT hT1.le hG hLu hu hXM hpaths
  rw [intervalIntegral.integral_add hAi hPi]
  apply (hlimA.add hlimP).congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [←mul_add,←Finset.sum_add_distrib]
  rw [←Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have ht:=mesh_time_mem hT.le hN j.isLt.le
  have hIA:Integrable (fun z ↦ polyJet (phi W γ) e.sourceA (meshTime T N j) (euler T N γ.coeff (gradient W γ) z j))
      (gaussianProduct (Fin (N+1))) := by
    apply Integrable.of_bound
    · exact ((hjA.slice ht).measurable.comp (measurable_euler T N γ.coeff (gradient W γ) (fun i hi ↦ (hG.smooth _ (mesh_time_mem hT.le hN hi.le)).continuous.measurable) j j.isLt.le)).aestronglyMeasurable
    · exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hAb _ ht _)
  have hIP:Integrable (fun z ↦ polyJet (phi W γ) e.sourceP (meshTime T N j) (euler T N γ.coeff (gradient W γ) z j))
      (gaussianProduct (Fin (N+1))) := by
    apply Integrable.of_bound
    · exact ((hjP.slice ht).measurable.comp (measurable_euler T N γ.coeff (gradient W γ) (fun i hi ↦ (hG.smooth _ (mesh_time_mem hT.le hN hi.le)).continuous.measurable) j j.isLt.le)).aestronglyMeasurable
    · exact Eventually.of_forall (fun z ↦ by simpa only [Real.norm_eq_abs] using hPb _ ht _)
  rw [←integral_const_mul,←integral_add hIA (hIP.const_mul _)]
  apply integral_congr_ae
  exact Eventually.of_forall (fun z ↦ (h.polyJet_source e ht _).symm)
end SKValue

end

end OAI
