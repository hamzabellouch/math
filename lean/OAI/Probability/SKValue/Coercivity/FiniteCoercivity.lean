import Mathlib
import OAI.Probability.SKValue.Equations.GeneralProfileShape
import OAI.Probability.SKValue.Coercivity.IntegratedCoercivity
import OAI.Probability.SKValue.Processes.FiniteProfileLaw

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma BoundedSmooth.pow {f:ℝ → ℝ} (hf:BoundedSmooth f) (n:ℕ) :
    BoundedSmooth (fun x ↦ f x^n) := by
  induction n with
  | zero => simpa only [pow_zero] using BoundedSmooth.const (1:ℝ)
  | succ n ih => simpa only [pow_succ] using ih.mul hf
lemma BoundedSmooth.sub {f g:ℝ → ℝ} (hf:BoundedSmooth f) (hg:BoundedSmooth g) :
    BoundedSmooth (fun x ↦ f x-g x) := by
  simpa only [neg_one_mul,sub_eq_add_neg] using hf.add (hg.const_mul (-1))
lemma SmoothTerminal.spatialJet_boundedSmooth {A:ℝ → ℝ} (hA:SmoothTerminal A)
    (c:ℝ) (n:ℕ) : BoundedSmooth (spatialJet c A n) :=
  (hA.jets.iteratedDeriv n).const_mul c

lemma BackwardShape.profile_coercivity {A:ℝ → ℝ} {C:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape C A) {p:ℝ≥0 × ℝ≥0} {l:HeatProfile}
    (hp:0<(p.2:ℝ)) (ht:0<(p.1:ℝ))
    (hl:(p::l).Pairwise (fun p q ↦ p.2≤q.2)) (hup:∀ q∈p::l,(q.2:ℝ)≤C) :
    (1/1000:ℝ)*profileResponse A (fun x ↦ (spatialJet C A 1 x)^4) (p::l) 0 0≤
      profileResponse A (fun x ↦ (spatialJet C A 3 x)^2-
        12*spatialJet C A 1 x*(spatialJet C A 2 x)^2+6*(spatialJet C A 1 x)^4) (p::l) 0 0 := by
  obtain ⟨E,hE,hpair⟩:=hB.profile_density hA hp ht hl hup
  have hC:0<C := hp.trans_le (hup p (by simp))
  have hv:=hA.spatialJet_boundedSmooth C 1
  have hw:=hA.spatialJet_boundedSmooth C 2
  have hz:=hA.spatialJet_boundedSmooth C 3
  have htest:BoundedSmooth (fun x ↦ (spatialJet C A 3 x)^2-
        12*spatialJet C A 1 x*(spatialJet C A 2 x)^2+6*(spatialJet C A 1 x)^4) :=
    ((hz.pow 2).sub ((hv.const_mul 12).mul (hw.pow 2))).add ((hv.pow 4).const_mul 6)
  rw [hpair _ (hv.pow 4),hpair _ htest]
  have hcert:=hB.integrated_certificate hA hC E
    (fun x ↦ (one_div_pos.mpr E.variance_pos).le.trans (hE.slope x)) hE.concave hE.coupled
  have hcert':(1/1000:ℝ)*(∫ x,(Real.exp (C*A x)*E.weight x)*(spatialJet C A 1 x)^4)≤
      ∫ x,(Real.exp (C*A x)*E.weight x)*((spatialJet C A 3 x)^2-
        12*spatialJet C A 1 x*(spatialJet C A 2 x)^2+6*(spatialJet C A 1 x)^4) := by
    simpa only [mul_comm] using hcert
  have hh:=mul_le_mul_of_nonneg_left hcert'
    (Real.exp_pos (-((p.2:ℝ)*profileValue A (p::l) 0 0))).le
  convert! hh using 1
  ring

lemma BackwardShape.diffusion_coercivity {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
    [IsProbabilityMeasure μ] {B:ℝ≥0 → Ω → ℝ} (hBrown:IsPreBrownianReal B μ)
    {X:ℝ → Ω → ℝ} {A:ℝ → ℝ} {C:ℝ} (hA:SmoothTerminal A)
    (hB:BackwardShape C A) {p:ℝ≥0 × ℝ≥0} {l:HeatProfile}
    (hp:0<(p.2:ℝ)) (ht:0<(p.1:ℝ))
    (hl:(p::l).Pairwise (fun p q ↦ p.2≤q.2)) (hup:∀ q∈p::l,(q.2:ℝ)≤C)
    (hT1:profileTime (p::l)≤1)
    (hXM:∀ t∈Icc (0:ℝ) (profileTime (p::l)),AEStronglyMeasurable (X t) μ)
    (hpaths:∀ᵐ ω ∂μ,ContinuousOn (fun t ↦ X t ω) (Icc (0:ℝ) (profileTime (p::l))) ∧
      IntervalIntegrable (fun s ↦ profileCoeff (p::l) s*deriv (profileValue A (p::l) s) (X s ω)) volume 0 (profileTime (p::l)) ∧
      (∀ t∈Icc (0:ℝ) (profileTime (p::l)),X t ω=B t.toNNReal ω+
        ∫ s in (0:ℝ)..t,profileCoeff (p::l) s*deriv (profileValue A (p::l) s) (X s ω)) ∧ X 0 ω=0) :
    (1/1000:ℝ)*(∫ ω,(spatialJet C A 1 (X (profileTime (p::l)) ω))^4 ∂μ)≤
      ∫ ω,((spatialJet C A 3 (X (profileTime (p::l)) ω))^2-
        12*spatialJet C A 1 (X (profileTime (p::l)) ω)*(spatialJet C A 2 (X (profileTime (p::l)) ω))^2+
        6*(spatialJet C A 1 (X (profileTime (p::l)) ω))^4) ∂μ := by
  have hT:0<profileTime (p::l) := add_pos_of_pos_of_nonneg ht (profileTime_nonneg l)
  have hv:=hA.spatialJet_boundedSmooth C 1
  have hw:=hA.spatialJet_boundedSmooth C 2
  have hz:=hA.spatialJet_boundedSmooth C 3
  have htest:BoundedSmooth (fun x ↦ (spatialJet C A 3 x)^2-
        12*spatialJet C A 1 x*(spatialJet C A 2 x)^2+6*(spatialJet C A 1 x)^4) :=
    ((hz.pow 2).sub ((hv.const_mul 12).mul (hw.pow 2))).add ((hv.pow 4).const_mul 6)
  rw [hA.profile_diffusion_test hBrown hB.even (hv.pow 4) hl hT hT1 hXM hpaths,
    hA.profile_diffusion_test hBrown hB.even htest hl hT hT1 hXM hpaths]
  exact hB.profile_coercivity hA hp ht hl hup
end SKValue

end

end OAI
