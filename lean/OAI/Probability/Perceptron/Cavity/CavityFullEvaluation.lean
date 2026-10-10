import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityFullLog
import OAI.Probability.Perceptron.Cavity.CavityGaussianTransport
import OAI.Probability.Perceptron.Cascade.CascadeConstant

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

theorem cavityLabel_full_evaluation (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (hp0 : ∀ i,0≤cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i≤cavityPairDiagonal n d D i)
    (f : ℝ→ᵇℝ) (z : Fin k→ℝ) (hz : StrictMono z) (hz0 : ∀ i,0<z i) (hz1 : ∀ i,z i<1)
    (a s : ℝ≥0) (ha : (a:ℝ)=D.2.val-(p (Fin.last k)).2.val)
    (hs : (s:ℝ)=D.1.val-(p (Fin.last k)).1.val) :
    let q:=cavityPairProfile n d p
    let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-q (Fin.last k) i)
    (∫ t,Real.log (cavityLabelFullPartition n d k f σ q t)
      ∂(indexedCascadeBaseLaw k z : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)=
    (n+1:ℕ)*a/2+∫ b,finiteCascadeLogRecursion (cavityRPCMarkLaw n d)
      (cavityRPCStep n d (stepFieldIncrement k (fun l=>(p l).2.val/2))
        (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(p l).1.val) j 0)) k z
      (cavityRPCTerminal n d (heatLogBCF s 1 f))
      (cavityRPCRootState n d (Real.sqrt (p 0).2.val) (Real.sqrt (p 0).1.val) b)
      ∂(cavityRPCMarkLaw n d : Measure (CavityRPCMark n d)) := by
  let c : ℝ:=(n+1:ℕ)*a/2
  let σ:=stepFieldIncrement k (fun l=>(p l).2.val/2)
  let τ:=fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(p l).1.val) j 0
  let F:=heatLogBCF s 1 f
  let G:=cavityRPCTerminal n d F ∘ cavityGaussianState n d
  let step:=gaussianLinearMarkStep (fun j=>diagonalMark (Sum.elim (fun _ : Fin (n+1)=>σ j) (fun _ : Fin d=>τ j)))
  let H:=fun v : EuclideanSpace ℝ (Fin (n+1)⊕Fin d)=>
    c+logSphericalExp n (Real.sqrt (n+1:ℕ)) (gaussianSumSplit v).1+∑ i,heatLog s 1 f (v (Sum.inr i))
  have hH : Measurable H := by
    apply (measurable_const.add ((logSphericalExp_lipschitz n _).continuous.measurable.comp
      gaussianSumSplit_measurable.fst)).add
    apply Finset.measurable_sum
    intro i _hi
    exact (heatLog_continuous s 1 f).measurable.comp
      ((measurable_pi_apply (Sum.inr i)).comp (MeasurableEquiv.toLp 2 _).symm.measurable)
  have hterm : (fun x : ℕ→EuclideanSpace ℝ (Fin (n+1)⊕Fin d)=>H (x 0))=(fun x=>c+G x) :=
    funext (cavityGaussian_terminal n d f a s)
  have hstep : (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep (cavityPairProfile n d p) j)))=step := by
    simp only [cavityPairProfile_step]
    rfl
  have hf0 : finiteCascadeFractionalIntegrable (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) step G k z :=
    cavityGaussian_fractional n d k σ τ F z hz0
  have hf : finiteCascadeFractionalIntegrable (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
      (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep (cavityPairProfile n d p) j)))
      (fun x=>H (x 0)) k z := by
    rw [hterm,hstep]
    exact finiteCascadeFractionalIntegrable_add_constant _ step G k z hz0 hf0 c
  have hc:=cavityLabel_full_log_recursion n d p D hp0 hpm hpD f z hz hz0 hz1 H hH
    (cavityPair_residual_formula n d p D f a s ha hs) hf
  let R:=fun b=>finiteCascadeLogRecursion (cavityRPCMarkLaw n d) (cavityRPCStep n d σ τ) k z
    (cavityRPCTerminal n d F) (cavityRPCRootState n d (Real.sqrt (p 0).2.val) (Real.sqrt (p 0).1.val) b)
  have hR : Measurable R := by
    apply (finiteCascadeLogRecursion_measurable _ _ (cavityRPCStep_measurable n d σ τ) k z
      (cavityRPCTerminal_measurable n d F)).comp
    unfold cavityRPCRootState
    fun_prop
  have he y : finiteCascadeLogRecursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
      (gaussianLinearMarkStep (fun j=>diagonalMark (profileGaussianStep (cavityPairProfile n d p) j))) k z
      (fun x=>H (x 0)) (fun _=>diagonalMark (profileGaussianRoot (cavityPairProfile n d p)) y)=
      c+R (cavityGaussianMark n d y) := by
    rw [hterm,hstep,finiteCascadeLogRecursion_add_constant _ step G k z hz0 hf0 c]
    rw [finiteCascadeLogRecursion_transport (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) (cavityRPCMarkLaw n d) step (cavityRPCStep n d σ τ)
      (cavityRPCStep_measurable n d σ τ) (cavityGaussianState n d) (cavityGaussianMark n d)
      (cavityGaussianMark_preserving n d) (cavityGaussianState_step n d σ τ)
      (cavityRPCTerminal n d F) (cavityRPCTerminal_measurable n d F) k z]
    rw [cavityGaussianState_root]
  have hri : Integrable (fun y=>R (cavityGaussianMark n d y))
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) := by
    apply (hc.1.sub (integrable_const c)).congr
    exact ae_of_all _ fun y=>by dsimp only [Pi.sub_apply]; rw [he]; ring
  dsimp only
  rw [hc.2]
  simp_rw [he]
  rw [integral_add (integrable_const c) hri]
  simp only [integral_const,probReal_univ,one_smul]
  have ht:=cavityGaussianMark_preserving n d
  rw [←integral_map ht.measurable.aemeasurable hR.aestronglyMeasurable,ht.map_eq]

theorem cavityLabel_full_value (n d : ℕ) {K : ℝ} {k : ℕ}
    (p : Fin (k+1)→BulkPairRange K) (D : BulkPairRange K)
    (hp0 : ∀ i,0≤cavityPairProfile n d p 0 i)
    (hpm : ∀ i,Monotone (fun l=>cavityPairProfile n d p l i))
    (hpD : ∀ i,cavityPairProfile n d p (Fin.last k) i≤cavityPairDiagonal n d D i)
    (q : Fin (k+1)→Time) (hpR : ∀ l,(p l).1.val=(q l:ℝ)) (hDR : D.1.val=1)
    (w : Fin (k+1)→ℝ) (hw : ∀ l,0<w l) (hw1 : ∑ l,w l=1) (hq : Monotone q)
    (g : Jet3) (P : Measure BrownianPath) [IsProbabilityMeasure P] (hB : IsBrownianReal brownianEval P) :
    let Q:=cavityPairProfile n d p
    let σ:=fun i=>Real.sqrt (cavityPairDiagonal n d D i-Q (Fin.last k) i)
    (∫ t,Real.log (cavityLabelFullPartition n d k g.f σ Q t)
      ∂(indexedCascadeBaseLaw k (stepCumulative w) : Measure (IndexedCascadeBase k)).prod countableGaussianLaw)=
      (n+1:ℕ)*(D.2.val/2+finiteSphericalFieldValue n k w (fun l=>(p l).2.val/2))+
        d*controlValue P g.f (weightedStepTrial w q (fun l=>(hw l).le) hw1) := by
  have hpB : (p (Fin.last k)).2.val≤D.2.val := hpD (Sum.inl 0)
  let a : ℝ≥0:=⟨D.2.val-(p (Fin.last k)).2.val,sub_nonneg.mpr hpB⟩
  let s : ℝ≥0:=⟨1-(q (Fin.last k):ℝ),sub_nonneg.mpr (q (Fin.last k)).prop.2⟩
  have hs : (s:ℝ)=D.1.val-(p (Fin.last k)).1.val := by dsimp [s]; rw [hDR,hpR]; rfl
  have hr:=cavityLabel_full_evaluation n d p D hp0 hpm hpD g.f (stepCumulative w)
    (stepCumulative_strictMono w hw) (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)
    a s rfl hs
  have hh0 : 0≤(p 0).2.val/2:=div_nonneg (hp0 (Sum.inl 0)) (by norm_num)
  have hv:=cavity_finiteRPC_value n d k w (fun l=>(p l).2.val/2) q hw hw1 hh0 hq g P hB 0 D.2.val
  have hb l : 2*((p l).2.val/2)=(p l).2.val := by ring
  have hqf : (fun l (_ : Fin 1)=>(p l).1.val)=(fun l (_ : Fin 1)=>(q l:ℝ)) := by
    funext l i; exact hpR l
  have hval : (n+1:ℕ)*a/2+
      (∫ b,finiteCascadeLogRecursion (cavityRPCMarkLaw n d)
        (cavityRPCStep n d (stepFieldIncrement k (fun l=>(p l).2.val/2))
          (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(p l).1.val) j 0)) k (stepCumulative w)
        (cavityRPCTerminal n d (heatLogBCF s 1 g.f))
        (cavityRPCRootState n d (Real.sqrt (p 0).2.val) (Real.sqrt (p 0).1.val) b)
        ∂(cavityRPCMarkLaw n d : Measure (CavityRPCMark n d)))=
      (n+1:ℕ)*(D.2.val/2+finiteSphericalFieldValue n k w (fun l=>(p l).2.val/2))+
        d*controlValue P g.f (weightedStepTrial w q (fun l=>(hw l).le) hw1) := by
    simp only [zero_add,hb] at hv
    simp_rw [finiteCascade_terminal_log_recursion_of_fractional (cavityRPCMarkLaw n d)
      (cavityRPCStep n d (stepFieldIncrement k (fun l=>(p l).2.val/2))
        (fun j=>profileGaussianStep (fun l (_ : Fin 1)=>(q l:ℝ)) j 0))
      (cavityRPCStep_measurable n d _ _) k (stepCumulative w)
      (stepCumulative_strictMono w hw) (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)
      (cavityRPCTerminal_measurable n d _) (cavityRPC_fractional n d k _ _ _ _ (stepCumulative_pos w hw))] at hv
    erw [Jet3.heatLog_f] at hv
    have ha : (a:ℝ)=D.2.val-(p (Fin.last k)).2.val := rfl
    rw [ha,hqf,hpR]
    exact hv
  exact hr.trans hval

end SphericalPerceptronFreeEnergy
end

end OAI
