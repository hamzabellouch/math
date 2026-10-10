import Mathlib
import OAI.Combinatorics.KMedian.Geometry.RationalAllParameters
import OAI.Combinatorics.KMedian.Geometry.RationalParameterizedHistory
import OAI.Combinatorics.KMedian.Optimization.ZeroCostBranch
import OAI.Combinatorics.KMedian.Programs.InstanceFractionalRound

namespace OAI


                                              
section
namespace MetricKMedian.Instance
open Finset Preparation

 theorem nonzeroFractional_spec (I : Instance) (h : ¬I.zeroTest) (r : ℕ) (hr : 0<r) :
    let a := I.computedFractional r hr (I.nonzero_clients h)
    a.Valid I.k ∧ (a.value I.indexedDistance:ℝ)≤(1+3/(r:ℝ))*optimum I := by
  simpa only [dite_eq_right h] using I.initialPhase_spec r hr

 def nonzeroRound (I : Instance) (h : ¬I.zeroTest) (r : ℕ) (hr : 0<r)
    {η τ : ℝ} (p : RationalAllParameters η τ) (C : ℕ) : Option (Finset (Fin I.n)) :=
  I.fractionalRound (I.computedFractional r hr (I.nonzero_clients h))
    (I.nonzeroFractional_spec h r hr).1 (I.nonzero_clients h) p C

 theorem nonzeroRound_spec (I : Instance) (h : ¬I.zeroTest) (r : ℕ) (hr : 0<r)
    {η τ : ℝ} (p : RationalAllParameters η τ) (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
    (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
    ∃ O : Finset (Fin I.n), I.nonzeroRound h r hr p C=some O ∧
      O⊆I.facilities ∧ O.Nonempty ∧ O.card≤I.k+C ∧
      cost I O≤(((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(1+3/(r:ℝ)))*optimum I := by
  obtain ⟨O,hO,hOF,hOn,hOk,hCost⟩ := I.fractionalRound_spec _
    (I.nonzeroFractional_spec h r hr).1 (I.nonzero_clients h) p hη hτ0 hτ C hC
  refine ⟨O,hO,hOF,hOn,hOk,hCost.trans ?_⟩
  rw [mul_assoc _ (1+3/(r:ℝ))]
  apply mul_le_mul_of_nonneg_left (I.nonzeroFractional_spec h r hr).2
  exact mul_nonneg (div_nonneg (by positivity) (by linarith only [hτ])) (by linarith only [hη])

 def computedPseudo (I : Instance) (r : ℕ) (hr : 0<r)
    {η τ : ℝ} (p : RationalAllParameters η τ) (C : ℕ) : Finset (Fin I.n) :=
  if h : I.zeroTest then I.zeroOutput
  else (I.nonzeroRound h r hr p C).getD {I.facilities.min' I.facilities_nonempty}

 theorem computedPseudo_spec (I : Instance) (r : ℕ) (hr : 0<r)
    {η τ : ℝ} (p : RationalAllParameters η τ) (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
    (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
    I.computedPseudo r hr p C⊆I.facilities ∧ (I.computedPseudo r hr p C).Nonempty ∧
      (I.computedPseudo r hr p C).card≤I.k+C ∧
      cost I (I.computedPseudo r hr p C)≤
        (((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(1+3/(r:ℝ)))*optimum I := by
  unfold computedPseudo
  split_ifs with h
  · obtain ⟨hOF,hOn,hOk,hCost⟩ := I.zeroOutput_spec h
    refine ⟨hOF,hOn,hOk.trans (Nat.le_add_right _ _),?_⟩
    rw [hCost,(I.zeroTest_iff.mp h),mul_zero]
  · obtain ⟨O,hO,hOF,hOn,hOk,hCost⟩ := I.nonzeroRound_spec h r hr p hη hτ0 hτ C hC
    rw [hO]
    exact ⟨hOF,hOn,hOk,hCost⟩

end MetricKMedian.Instance
end

end OAI
