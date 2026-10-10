import Mathlib
import OAI.Probability.SKBarriers.Replicas.PairLists
import OAI.Probability.SKBarriers.Parisi.CDFSuffixSemigroup
import OAI.Probability.SKBarriers.Replicas.PairContinuumConvergence

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem pairConstrainedPressure_continuum {N : ℕ} (hN : 0<N) (β : ℝ)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1)
    {q : ℝ} (hq : q∈Icc (0:ℝ) 1)
    (hD : Nonempty (MatrixStates N 2 (pairMatrix 1 q))) :
    matrixConstrainedPressure N 2 β (pairMatrix 1 q) ≤
      2*scalarCDFParisi β α-(scalarCDFOverlap β α q-q)^2/2 := by
  let t := Real.toNNReal q
  let r := Real.toNNReal (1-q)
  have ht : (t:ℝ)=q := Real.coe_toNNReal _ hq.1
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal _ (sub_nonneg.mpr hq.2)
  have ht1 : t ≤ 1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hq.2
  have hr1 : r ≤ 1 := by rw [← NNReal.coe_le_coe,hr,NNReal.coe_one]; linarith [hq.1]
  let l (n : ℕ) := dyadicIntervals α n 0 t
  let R (n : ℕ) := dyadicIntervals α n q r
  have hvalue : Tendsto (fun n => scalarTimeChain β (l n++R n) scalarSpinTerminal 0)
      atTop (𝓝 (scalarCDFValue β α 0 1 0)) := by
    have H := (dyadicScalar_varying_terminal_uniform β ha α.mono
      (fun n => dyadicScalar_regular scalarSpinTerminal_regular β α n q r)
      (scalarCDFValue_regular β ha α.mono q r hr1)
      (scalarCDFValue_lipschitz β ha α.mono q r hr1)
      (dyadicScalar_value_uniform β ha α.mono q r hr1) 0 t ht1).tendsto_at 0
    have he := scalarCDFValue_suffix_semigroup β α ha h1 (s:=0) le_rfl hq.1 hq.2
    simp only [sub_zero,Real.toNNReal_one] at he
    rw [← he] at H
    simpa only [scalarTimeChain_append,l,R,dyadicScalar] using H
  have hpen : Tendsto (fun n => chainQuadraticPenalty 0 (l n++R n)) atTop
      (𝓝 (2*∫ u in Icc (0:ℝ) 1, u*α u)) := by
    have H := (dyadicPenalty_tendsto α.mono 0 t le_rfl (by rw [zero_add,ht]; exact hq.2)).add
      (dyadicPenalty_tendsto α.mono q r hq.1 (by rw [hr]; linarith))
    have hi (a b : ℝ) : IntervalIntegrable (fun u => u*α u) volume a b :=
      α.mono.intervalIntegrable.continuousOn_mul continuous_id.continuousOn
    have he : 2*(∫ u in (0:ℝ)..0+t, u*α u)+2*(∫ u in q..q+r, u*α u)=
        2*∫ u in Icc (0:ℝ) 1, u*α u := by
      rw [zero_add,ht,hr,show q+(1-q)=1 by ring,← mul_add,
        intervalIntegral.integral_add_adjacent_intervals (hi 0 q) (hi q 1),
        intervalIntegral.integral_of_le zero_le_one,← integral_Icc_eq_integral_Ioc]
    rw [he] at H
    convert H using 1
    funext n
    rw [chainQuadraticPenalty_append]
    simp only [l,R,dyadicIntervals_duration,zero_add,ht]
  have hgamma := dyadicPairOverlap_tendsto β ha α.mono hq
  have Hlimit := (hvalue.sub (hpen.const_mul (β^2/4))).const_mul 2 |>.sub
    (((hgamma.sub_const q).pow 2).div_const 2)
  have Hseq (n : ℕ) : matrixConstrainedPressure N 2 β (pairMatrix 1 q) ≤
      2*(scalarTimeChain β (l n++R n) scalarSpinTerminal 0-
        β^2/4*chainQuadraticPenalty 0 (l n++R n))-
        (scalarTimeChainAverage β (l n) (scalarTimeChain β (R n) scalarSpinTerminal)
          (fun x => (scalarTimeChainAverage β (R n) scalarSpinTerminal scalarMagnetization x)^2) 0-q)^2/2 := by
    have hm (p) (hp : p∈l n++R n) : p.1∈Icc (0:ℝ) 1 := by
      rcases List.mem_append.mp hp with hp|hp
      · exact dyadicIntervals_mass_bounds ha n 0 t hp
      · exact dyadicIntervals_mass_bounds ha n q r hp
    have hmono : (l n++R n).Pairwise (fun p q => p.1 ≤ q.1) := by
      refine List.pairwise_append.mpr ⟨dyadicIntervals_pairwise α.mono n 0 t,
        dyadicIntervals_pairwise α.mono n q r,?_⟩
      intro p hp p' hp'
      have H := (dyadicIntervals_mem_bounds α.mono n 0 t hp).2.1
      have H' := (dyadicIntervals_mem_bounds α.mono n q r hp').1
      rw [zero_add,ht] at H
      exact H.trans H'
    have hd : chainDuration (l n)+chainDuration (R n)=1 := by
      simp only [l,R,dyadicIntervals_duration]
      apply NNReal.eq
      simp only [NNReal.coe_add,NNReal.coe_one,ht,hr]
      ring
    have HL : (chainDuration (l n):ℝ)=q := by dsimp only [l]; rw [dyadicIntervals_duration,ht]
    have H := pairConstrainedPressure_lists hN β (l n) (R n) hm hmono hd (by simpa only [HL] using hD)
    simpa only [HL] using H
  have H := ge_of_tendsto Hlimit (Eventually.of_forall Hseq)
  calc
    _ ≤ 2*(scalarCDFValue β α 0 1 0-β^2/4*(2*∫ u in Icc (0:ℝ) 1, u*α u))-
        (scalarCDFOverlap β α q-q)^2/2 := H
    _ = _ := by rw [scalarCDFParisi]; ring

end SK.Analytic

end
end

end OAI
