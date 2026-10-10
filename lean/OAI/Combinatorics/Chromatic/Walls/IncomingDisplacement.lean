import Mathlib
import OAI.Combinatorics.Chromatic.Walls.IncomingSystem
import OAI.Combinatorics.Chromatic.GradedAlgebra.KernelTraceLog

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit
noncomputable section
variable {R M I : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup M] [Fintype I]
variable (v : Rˣ) (Ω : M→+M→+ℤ) (C : (I→ℤ)→+M)

omit [Algebra ℚ R] in
lemma filter_supported (V : AddSubmonoid M) (P : M→Prop) [DecidablePred P]
    (f : Torus v Ω) (hf : f∈supportedSubring v Ω V) :
    f.filter P∈supportedSubring v Ω V := by
  intro m hm
  simp only [Finsupp.filter_apply,hf m hm,ite_self]

omit [Algebra ℚ R] in
lemma chartThree_supported (h : M→+ℝ) (V : AddSubmonoid M) (F : CompletedPositive v Ω C)
    (hF : ∀n,coeff n F.val∈supportedSubring v Ω V) :
    (∀n,coeff n (chartPositive v Ω C h F).val∈supportedSubring v Ω V) ∧
    (∀n,coeff n (chartZero v Ω C h F).val∈supportedSubring v Ω V) ∧
    (∀n,coeff n (chartNegative v Ω C h F).val∈supportedSubring v Ω V) := by
  classical
  have H:=factors_mem (positiveProject v Ω h) (supportedSubring v Ω V)
    (fun f hf=>filter_supported v Ω V _ f hf) F.val hF
  have H0:=factors_mem (zeroProject v Ω h) (supportedSubring v Ω V)
    (fun f hf=>filter_supported v Ω V _ f hf) (rightFactor (positiveProject v Ω h) F.val) H.2
  exact ⟨H.1,H0.1,H0.2⟩

lemma kernel_zero_log (hΩ : ∀m,Ω m m=0) (r : M) (h : M→+ℝ) (hr : h r=0)
    (F : CompletedPositive v Ω C)
    (hF : ∀n,coeff n F.val∈supportedSubalgebra v Ω (kernelSupport Ω r)) (n : ℕ) :
    coeff n (FormalLog.log (chartZero v Ω C h F).val) r=coeff n (FormalLog.log F.val) r := by
  let A:=chartPositive v Ω C h F
  let B:=chartZero v Ω C h F
  let D:=chartNegative v Ω C h F
  have H:=chartThree_supported v Ω C h (kernelSupport Ω r) F hF
  have H1:=kernel_trace_log_product v Ω hΩ r A.val B.val A.property.1 B.property.1 H.1 H.2.1 n
  have H2:=kernel_trace_log_product v Ω hΩ r (A.val*B.val) D.val
    (by simp [A.property.1,B.property.1]) D.property.1
    (PowerSeriesSplit.mul_mem (supportedSubring v Ω (kernelSupport Ω r)) _ _ H.1 H.2.1) H.2.2 n
  have HS:=chart_three_support v Ω C h F
  have hp:=log_positive_zero v Ω h A.val A.property.1 HS.1 r hr n
  have hn:=log_negative_zero v Ω h D.val D.property.1 HS.2.2 r hr n
  rw [H1,hp,hn,zero_add,add_zero] at H2
  rw [show A.val*B.val*D.val=F.val from chart_three_factorization v Ω C h F] at H2
  exact H2.symm

lemma incoming_chart_supported (r : M) (F : CompletedPositive v Ω C) :
    ∀n,coeff n (chartZero v Ω C (incomingCovector Ω r) F).val∈
      supportedSubalgebra v Ω (kernelSupport Ω r) := by
  intro n m hm
  cases n with
  | zero=>
    rw [coeff_zero_eq_constantCoeff,(chartZero v Ω C (incomingCovector Ω r) F).property.1]
    change (Finsupp.single 0 (1:R)) m=0
    apply Finsupp.single_eq_of_ne
    intro he
    exact hm (he ▸ (kernelSupport Ω r).zero_mem)
  | succ n=>
    by_contra hn
    have H:=(chart_three_support v Ω C (incomingCovector Ω r) F).2.1 n m hn
    apply hm
    change Ω m r=0
    change (Ω m r:ℝ)=0 at H
    exact_mod_cast H

theorem incoming_displacement_log (hΩ : ∀m,Ω m m=0) (r : M) (h : M→+ℝ)
    (hr : h r=0) (F : CompletedPositive v Ω C) (n : ℕ) :
    coeff n (FormalLog.log (chartZero v Ω C h
      (chartZero v Ω C (incomingCovector Ω r) F)).val) r=
    coeff n (FormalLog.log (chartZero v Ω C (incomingCovector Ω r) F).val) r :=
  kernel_zero_log v Ω C hΩ r h hr _ (incoming_chart_supported v Ω C r F) n
end
end ElementaryPositivity.QuantumTorus

end

end OAI
