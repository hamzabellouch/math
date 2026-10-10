import Mathlib
import OAI.Probability.Perceptron.Interpolation.ArrayGeometry

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy
variable {A S K : Type*} [MeasurableSpace A] [MeasurableSpace S]
variable [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
  [SecondCountableTopology K] [CompactSpace K]
variable (κ : Kernel A S) [IsMarkovKernel κ] (P : Measure A) [IsProbabilityMeasure P]
variable (H : A → S → ℝ) (hH : Measurable (Function.uncurry H))
variable (Q : S → S → K) (hQ : Measurable (Function.uncurry Q))

def overlapArray (x : ℕ → S) : CompactArray K := fun i j => Q (x i) (x j)

include hQ in
omit [TopologicalSpace K] [BorelSpace K] [SecondCountableTopology K] [CompactSpace K] in
lemma overlapArray_measurable : Measurable (overlapArray Q) := by
  unfold overlapArray
  exact Measurable.of_eval fun row => Measurable.of_eval fun column =>
    hQ.comp (show Measurable (fun sequence : ℕ → S => (sequence row,sequence column)) from
      (measurable_pi_apply row).prodMk (measurable_pi_apply column))

def gibbsOverlapArrayLaw : ProbabilityMeasure (CompactArray K) :=
  ⟨(annealedInfiniteReplicaMeasure κ P H hH).map (fun a => overlapArray Q a.2),
    (Measure.isProbabilityMeasure_map_iff
      ((overlapArray_measurable Q hQ).comp measurable_snd).aemeasurable).2 inferInstance⟩

omit [TopologicalSpace K] [BorelSpace K] [SecondCountableTopology K] [CompactSpace K] in
lemma gibbsOverlapArray_integral {F : CompactArray K → ℝ} (hF : Measurable F) :
    (∫ R, F R ∂gibbsOverlapArrayLaw κ P H hH Q hQ) =
      ∫ a, F (overlapArray Q a.2) ∂annealedInfiniteReplicaMeasure κ P H hH :=
  integral_map ((overlapArray_measurable Q hQ).comp measurable_snd).aemeasurable hF.aestronglyMeasurable

omit [CompactSpace K]

lemma gibbsOverlapArray_block (hexp : ∀ᵐ a ∂P,
    Integrable (fun x => Real.exp (H a x)) (κ a)) (r : ℕ)
    (F : CompactBlock K r →ᵇ ℝ) :
    (∫ R, F (compactBlock r R) ∂gibbsOverlapArrayLaw κ P H hH Q hQ) =
      ∫ a, gibbsReplicaMean (κ a) (H a) r
        (fun x => F (fun i j => Q (x i) (x j))) ∂P := by
  rw [gibbsOverlapArray_integral κ P H hH Q hQ
    (F:=fun R => F (compactBlock r R)) (F.continuous.measurable.comp (compactBlock_continuous r).measurable)]
  exact annealedInfiniteReplica_gibbs_prefix κ P H hH hexp r
    (F.continuous.measurable.comp (Measurable.of_eval fun row => Measurable.of_eval fun column =>
      hQ.comp ((measurable_pi_apply row).prodMk (measurable_pi_apply column))))
    (fun x => by
      change |F (fun i j => Q (x i) (x j))|≤‖F‖
      simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (fun i j => Q (x i) (x j)))

lemma compactGGDefect_gibbsOverlapArray (hexp : ∀ᵐ a ∂P,
    Integrable (fun x => Real.exp (H a x)) (κ a))
    (r : ℕ) (i : Fin r) (f : CompactBlock K r →ᵇ ℝ) (g : K →ᵇ ℝ)
    (diag : ℝ) (hdiag : ∀ x, g (Q x x)=diag) (hsymm : ∀ x y, g (Q x y)=g (Q y x)) :
    compactGGDefect (gibbsOverlapArrayLaw κ P H hH Q hQ) r i f g =
      -kernelGGDefect κ P H (fun x y => g (Q x y)) diag r i
        (fun x => f (fun j l => Q (x j) (x l))) := by
  classical
  let μ := gibbsOverlapArrayLaw κ P H hH Q hQ
  let F : CompactArray K →ᵇ ℝ := f.compContinuous ⟨compactBlock r,compactBlock_continuous r⟩
  let E (a b : ℕ) : CompactArray K →ᵇ ℝ := g.compContinuous ⟨fun R => R a b,by fun_prop⟩
  let Es (a b : Fin r) : CompactBlock K r →ᵇ ℝ := g.compContinuous ⟨fun R => R a b,by fun_prop⟩
  have hmean := gibbsOverlapArray_block κ P H hH Q hQ hexp r f
  have hsum := gibbsOverlapArray_block κ P H hH Q hQ hexp r (f * ∑ l, Es i l)
  have hp := gibbsOverlapArray_block κ P H hH Q hQ hexp 2
    (g.compContinuous ⟨fun R => R 0 1,by fun_prop⟩)
  have hpair : (∫ R : CompactArray K, g (R 0 1) ∂μ) =
      ∫ a, gibbsReplicaMean (κ a) (H a) 2 (fun x => g (Q (x 1) (x 0))) ∂P := by
    change (∫ R : CompactArray K, g (R 0 1) ∂μ) =
      ∫ a, gibbsReplicaMean (κ a) (H a) 2 (fun x => g (Q (x 0) (x 1))) ∂P at hp
    rw [hp]
    apply integral_congr_ae
    exact Eventually.of_forall fun a => congrArg (gibbsReplicaMean (κ a) (H a) 2)
      (funext fun x => hsymm (x 0) (x 1))
  let fnew : CompactBlock K (r+1) →ᵇ ℝ :=
    (f.compContinuous ⟨fun R => fun j l => R j.castSucc l.castSucc,by fun_prop⟩) *
      (g.compContinuous ⟨fun R => R i.castSucc (Fin.last r),by fun_prop⟩)
  have hn := gibbsOverlapArray_block κ P H hH Q hQ hexp (r+1) fnew
  have hnew : (∫ R, f (compactBlock r R)*g (R i r) ∂μ) =
      ∫ a, gibbsReplicaMean (κ a) (H a) (r+1)
        (fun x => f (fun j l => Q (x j.succ) (x l.succ))*g (Q (x i.succ) (x 0))) ∂P := by
    change (∫ R, fnew (compactBlock (r+1) R) ∂μ) = _
    rw [hn]
    apply integral_congr_ae
    filter_upwards [hexp] with a ha
    symm
    have hG : Measurable (Function.uncurry (fun (x : Fin r → S) (y : S) =>
        f (fun j l => Q (x j) (x l))*g (Q (x i) y))) := by
      apply Measurable.mul
      · exact f.continuous.measurable.comp (Measurable.of_eval fun row =>
          Measurable.of_eval fun column => hQ.comp
            (show Measurable (fun replica : (Fin r → S)×S =>
              (replica.1 row,replica.1 column)) from by fun_prop))
      · exact g.continuous.measurable.comp (hQ.comp
          (show Measurable (fun a : (Fin r → S)×S => (a.1 i,a.2)) from by fun_prop))
    simpa only [fnew,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk] using gibbsReplicaMean_fresh_last (κ a) (hH.of_uncurry_left) ha r hG
  have hdiagint : (∫ R, f (compactBlock r R)*g (R i i) ∂μ) =
      diag*(∫ R, f (compactBlock r R) ∂μ) := by
    change (∫ R, (F*E i i) R ∂gibbsOverlapArrayLaw κ P H hH Q hQ) =
      diag*(∫ R, F R ∂gibbsOverlapArrayLaw κ P H hH Q hQ)
    rw [gibbsOverlapArray_integral κ P H hH Q hQ (F * E i i).continuous.measurable,
      gibbsOverlapArray_integral κ P H hH Q hQ F.continuous.measurable]
    simp only [F,E,BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.compContinuous_apply,
      ContinuousMap.coe_mk,overlapArray,hdiag]
    rw [integral_mul_const,mul_comm]
  have hsumint : (∫ R, f (compactBlock r R)*∑ l : Fin r, g (R i l) ∂μ) =
      (∑ l ∈ Finset.univ.erase i, ∫ R, f (compactBlock r R)*g (R i l) ∂μ)+
        diag*(∫ R, f (compactBlock r R) ∂μ) := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum (f:=fun (l : Fin r) (R : CompactArray K) => f (compactBlock r R)*g (R i l))
      Finset.univ (fun l _ => by exact (F*E i l).integrable μ)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i),hdiagint]
  simp only [BoundedContinuousFunction.mul_apply,BoundedContinuousFunction.sum_apply,
    Es,BoundedContinuousFunction.compContinuous_apply,ContinuousMap.coe_mk] at hsum
  change (∫ R, f (compactBlock r R)*∑ l : Fin r, g (R i l) ∂μ) = _ at hsum
  unfold compactGGDefect kernelGGDefect
  change _ = - ((_)-diag*(_)+(_)*(_)-r*(_))
  rw [← hmean,← hpair,← hnew,← hsum,hsumint]
  ring

end SphericalPerceptronFreeEnergy
end

end OAI
