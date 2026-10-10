import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFAtomicRepresentation
import OAI.Probability.SKBarriers.Parisi.CDFUniformQuantiles
import OAI.Probability.SKBarriers.Parisi.CDFDerivativeConvergence

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOperator_uniform_nonexpansive {f g : ℝ → ℝ}
    (hf : BoundedDerivs f) (hg : BoundedDerivs g) {K L : ℝ≥0}
    (hK : LipschitzWith K f) (hL : LipschitzWith L g)
    (β : ℝ) {α : ℝ → ℝ} (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hm : Monotone α)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) {ε : ℝ} (hfg : ∀ x, |f x-g x|≤ε) (x : ℝ) :
    |scalarCDFOperator β α s t f x-scalarCDFOperator β α s t g x|≤ε := by
  apply le_of_tendsto (((dyadicScalar_general_uniform hf hK β hα hm s t ht).tendsto_at x).sub
    ((dyadicScalar_general_uniform hg hL β hα hm s t ht).tendsto_at x)).abs
  exact Eventually.of_forall (fun n => dyadicScalar_uniform_nonexpansive hf hg β hα n s t hfg x)

theorem scalarCDFValue_semigroup_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    scalarCDFValue β (quantileCDF k Q) 0 1=
      scalarCDFOperator β (quantileCDF k Q) 0 (Real.toNNReal q)
        (scalarCDFValue β (quantileCDF k Q) q (Real.toNNReal (1-q))) := by
  let t := Real.toNNReal q
  let r := Real.toNNReal (1-q)
  have ht : (t:ℝ)=q := Real.coe_toNNReal q hq.1
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal (1-q) (sub_nonneg.mpr hq.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hq.2
  have hr1 : r≤1 := by rw [← NNReal.coe_le_coe,hr,NNReal.coe_one]; linarith [hq.1]
  obtain ⟨l,hd,hm,hmodel,_⟩ := quantile_full_chain Q hQ.1 (hQ.2 0).1 (hQ.2 (Fin.last k)).2
  have hsplit : chainDuration l=t+r := by rw [hd]; apply NNReal.coe_injective; rw [NNReal.coe_add,ht,hr,NNReal.coe_one]; ring
  obtain ⟨l₁,l₂,h₁,h₂,hm₁,hm₂,hs₁,hs₂,he⟩ := scalarTimeChain_split_at β (quantileCDF k Q) l hm 0 hmodel t r hsplit
  have htail : scalarCDFValue β (quantileCDF k Q) q r=scalarTimeChain β l₂ scalarSpinTerminal := by
    funext x
    apply scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
      β (quantileCDF_bounds k Q) (quantileCDF_monotone k Q) l₂ hm₂ q r hr1 h₂
    simpa only [zero_add,ht] using hs₂
  funext x
  change scalarCDFOperator β (quantileCDF k Q) 0 1 scalarSpinTerminal x=
    scalarCDFOperator β (quantileCDF k Q) 0 t (scalarCDFValue β (quantileCDF k Q) q r) x
  rw [htail,scalarCDFOperator_eq_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
    β (quantileCDF_bounds k Q) (quantileCDF_monotone k Q) l hm 0 1 le_rfl hd hmodel,
    scalarCDFOperator_eq_chain (scalarTimeChain_regular scalarSpinTerminal_regular β l₂)
      (scalarTimeChain_lipschitz scalarSpinTerminal_regular scalarSpinTerminal_lipschitz β l₂ (fun p hp => (hm₂ p hp).1))
      β (quantileCDF_bounds k Q) (quantileCDF_monotone k Q) l₁ hm₁ 0 t ht1 h₁ hs₁]
  exact (congrFun (he scalarSpinTerminal scalarSpinTerminal_regular) x).symm

theorem scalarCDFValue_semigroup (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {q : ℝ} (hq : q∈Icc (0:ℝ) 1) :
    scalarCDFValue β α 0 1=
      scalarCDFOperator β α 0 (Real.toNNReal q)
        (scalarCDFValue β α q (Real.toNNReal (1-q))) := by
  let t := Real.toNNReal q
  let r := Real.toNNReal (1-q)
  have ht : (t:ℝ)=q := Real.coe_toNNReal q hq.1
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal (1-q) (sub_nonneg.mpr hq.2)
  have ht1 : t≤1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; exact hq.2
  have hr1 : r≤1 := by rw [← NNReal.coe_le_coe,hr,NNReal.coe_one]; linarith [hq.1]
  let a (n : ℕ) := quantileCDF n (uniformCDFQuantiles n α)
  have hb (n : ℕ) := quantileCDF_bounds n (uniformCDFQuantiles n α)
  have hm (n : ℕ) := quantileCDF_monotone n (uniformCDFQuantiles n α)
  have hD : Tendsto (fun n => cdfDistance (a n) α) atTop (𝓝 0) := uniformCDFQuantiles_L1_tendsto α ha h1
  funext x
  have hleft := (scalarCDFValue_tendstoUniformly β ha α.mono hb hm hD).tendsto_at x
  have herr (n : ℕ) : |scalarCDFOperator β (a n) 0 t (scalarCDFValue β (a n) q r) x-
      scalarCDFOperator β α 0 t (scalarCDFValue β α q r) x|≤
      (scalarTimeMassConstant β+scalarTimeMassConstantK β 1)*cdfDistance (a n) α := by
    have E (z : ℝ) : |scalarCDFValue β (a n) q r z-scalarCDFValue β α q r z|≤
        scalarTimeMassConstant β*cdfDistance (a n) α :=
      (scalarCDFValue_cdf_lipschitz β (hb n) (hm n) ha α.mono q r hr1 z).trans
        (mul_le_mul_of_nonneg_left (cdfDistance_subinterval_le (hm n) α.mono hq.1 (by rw [hr]; linarith))
          (scalarTimeMassConstant_nonneg β))
    have H₁ := scalarCDFOperator_uniform_nonexpansive
      (scalarCDFValue_regular β (hb n) (hm n) q r hr1) (scalarCDFValue_regular β ha α.mono q r hr1)
      (scalarCDFValue_lipschitz β (hb n) (hm n) q r hr1) (scalarCDFValue_lipschitz β ha α.mono q r hr1)
      β (hb n) (hm n) 0 t ht1 E x
    have H₂ := (scalarCDFOperator_cdf_lipschitz (scalarCDFValue_regular β ha α.mono q r hr1)
      (scalarCDFValue_lipschitz β ha α.mono q r hr1) β (hb n) (hm n) ha α.mono 0 t ht1 x).trans
      (mul_le_mul_of_nonneg_left (cdfDistance_subinterval_le (hm n) α.mono le_rfl (by simpa only [zero_add,ht] using hq.2))
        (scalarTimeMassConstantK_nonneg β 1))
    exact (abs_sub_le _ _ _).trans ((add_le_add H₁ H₂).trans_eq (by ring))
  have he (n : ℕ) : scalarCDFValue β (a n) 0 1 x=
      scalarCDFOperator β (a n) 0 t (scalarCDFValue β (a n) q r) x :=
    congrFun (scalarCDFValue_semigroup_quantile β (uniformCDFQuantiles n α)
      (uniformCDFQuantiles_admissible n α h1) hq) x
  have H := le_of_tendsto_of_tendsto
    (hleft.sub_const (scalarCDFOperator β α 0 t (scalarCDFValue β α q r) x)).abs
    (hD.const_mul (scalarTimeMassConstant β+scalarTimeMassConstantK β 1))
    (Eventually.of_forall (fun n => by
      change |scalarCDFValue β (a n) 0 1 x-scalarCDFOperator β α 0 t (scalarCDFValue β α q r) x|≤_
      rw [he n]
      exact herr n))
  simp only [mul_zero] at H
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H (abs_nonneg _)))

end SK.Analytic

end
end

end OAI
