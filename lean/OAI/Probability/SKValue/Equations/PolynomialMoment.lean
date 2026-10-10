import Mathlib
import OAI.Probability.SKValue.Evolution.HigherPDE
import OAI.Probability.SKValue.Control.PolynomialGenerator

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal BigOperators
namespace SKValue
noncomputable def jetMoment (W:BrownianSpace) (γ:OrderParameter) (X:ℝ → W.Ω → ℝ)
    (e:JetExpr) (t:ℝ):ℝ := ∫ z,polyJet (phi W γ) e t (X t z) ∂W.μ
lemma IsDiffusion.jetMoment_continuous {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {T:ℝ} (hT:T∈Ico (0:ℝ) 1) (e:JetExpr):
    ContinuousOn (jetMoment W γ X e) (Icc (0:ℝ) T) := by
  have hj:=(phi_evolution W γ hT).polyJet_joint e
  obtain ⟨C,hC,hb⟩:=hj.bounded
  apply mean_observable_continuous hj.continuous hb
  · intro t ht;exact (hX.memLp (p:=2) ⟨ht.1,ht.2.trans hT.2.le⟩ (by norm_num)).aestronglyMeasurable
  · obtain ⟨Kv,Lv,K,L,D,Lu,La,hV,hG,hD,hLu,hLa,hDb,hu,ha⟩:=sourceStripRegularity W γ T hT
    exact (hX.strip_paths hT.1 hT.2 hLu (fun t ht s hs x y ↦ hu s hs t ht y x)).mono (fun _ hz ↦ hz.1)
lemma IsDiffusion.jetMoment_hasDerivAt {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1) (hγ:ContinuousAt γ.coeff t)
    (e:JetExpr):HasDerivAt (jetMoment W γ X e)
      (jetMoment W γ X e.sourceA t+γ.coeff t*jetMoment W γ X e.sourceP t) t := by
  obtain ⟨S,htS,hS⟩:=exists_between ht.2
  have hS0:0≤S:=ht.1.le.trans htS.le
  have hSt:S∈Ico (0:ℝ) 1:=⟨hS0,hS⟩
  let F:=fun r ↦ jetMoment W γ X e.sourceA r+γ.coeff r*jetMoment W γ X e.sourceP r
  have hcA:=hX.jetMoment_continuous hSt e.sourceA
  have hcP:=hX.jetMoment_continuous hSt e.sourceP
  have hmono:MonotoneOn γ.coeff (uIcc (0:ℝ) S) := by
    rw [uIcc_of_le hS0];exact γ.monotone.mono (fun _ hr ↦ ⟨hr.1,hr.2.trans_lt hS⟩)
  have hi:IntervalIntegrable F volume 0 S := by
    apply IntervalIntegrable.add
    · exact ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hS0] using hcA)
    · exact hmono.intervalIntegrable.mul_continuousOn (by simpa only [uIcc_of_le hS0] using hcP)
  have hn:Icc (0:ℝ) S∈𝓝 t:=Icc_mem_nhds ht.1 htS
  have hc:ContinuousAt F t := (hcA.continuousAt hn).add (hγ.mul (hcP.continuousAt hn))
  have hsub:uIcc (0:ℝ) t⊆uIcc (0:ℝ) S:=by
    rw [uIcc_of_le ht.1.le,uIcc_of_le hS0];exact Icc_subset_Icc le_rfl htS.le
  have hIi:IntegrableOn F (Icc (0:ℝ) S) volume := by
    simpa only [uIcc_of_le hS0] using (intervalIntegrable_iff').mp hi
  have hd:=((intervalIntegral.integral_hasDerivAt_right (hi.mono_set hsub)
    ⟨Icc (0:ℝ) S,hn,hIi.aestronglyMeasurable⟩ hc).const_add (polyJet (phi W γ) e 0 0))
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 htS] with s hs
  exact hX.polyJet_generator hs.1 (hs.2.trans hS) e
end SKValue

end

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
namespace JetExpr
noncomputable def square (e:JetExpr):JetExpr := mul e e
noncomputable def cube (e:JetExpr):JetExpr := mul (mul e e) e
noncomputable def momentExpr : JetExpr := square (coord 0)
noncomputable def curvatureExpr : JetExpr := square (coord 1)
noncomputable def curvatureSlope (c:ℝ) : JetExpr := add (square (coord 2)) (mul (const (-2*c)) (cube (coord 1)))
lemma momentExpr_eval (R:ℕ → ℝ):eval R momentExpr=(R 0)^2 := by simp only [momentExpr,square,eval,pow_two]
lemma curvatureExpr_eval (R:ℕ → ℝ):eval R curvatureExpr=(R 1)^2 := by simp only [curvatureExpr,square,eval,pow_two]
lemma curvatureSlope_eval (R:ℕ → ℝ) (c:ℝ):eval R (curvatureSlope c)=(R 2)^2-2*c*(R 1)^3 := by
  simp only [curvatureSlope,square,cube,eval];ring
lemma momentExpr_sourceA (R:ℕ → ℝ):eval R momentExpr.sourceA=eval R curvatureExpr := by
  norm_num [momentExpr,curvatureExpr,square,sourceA,timeB,spatialIter,spatial,D,eval];ring
lemma momentExpr_sourceP (R:ℕ → ℝ):eval R momentExpr.sourceP=0 := by
  norm_num [momentExpr,square,sourceP,timeP,spatialIter,spatial,D,eval];ring
lemma curvatureExpr_sourceA (R:ℕ → ℝ):eval R curvatureExpr.sourceA=(R 2)^2 := by
  norm_num [curvatureExpr,square,sourceA,timeB,spatialIter,spatial,D,eval];ring
lemma curvatureExpr_sourceP (R:ℕ → ℝ):eval R curvatureExpr.sourceP= -2*(R 1)^3 := by
  norm_num [curvatureExpr,square,sourceP,timeP,spatialIter,spatial,D,eval];ring
lemma curvatureSlope_sourceA (R:ℕ → ℝ) (c:ℝ):eval R (curvatureSlope c).sourceA=(R 3)^2-6*c*R 1*(R 2)^2 := by
  norm_num [curvatureSlope,square,cube,sourceA,timeB,spatialIter,spatial,D,eval];ring
lemma curvatureSlope_sourceP (R:ℕ → ℝ) (c:ℝ):eval R (curvatureSlope c).sourceP= -6*R 1*(R 2)^2+6*c*(R 1)^4 := by
  norm_num [curvatureSlope,square,cube,sourceP,timeP,spatialIter,spatial,D,eval];ring
end JetExpr
end SKValue

end

end OAI
