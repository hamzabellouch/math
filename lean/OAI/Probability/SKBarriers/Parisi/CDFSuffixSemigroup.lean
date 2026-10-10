import Mathlib
import OAI.Probability.SKBarriers.Parisi.CDFSemigroup

namespace OAI

section

noncomputable section
open scoped NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem scalarCDFOperator_semigroup_of_chain {f : ℝ → ℝ}
    (hf : BoundedDerivs f) {K : ℝ≥0} (hK : LipschitzWith K f)
    (β : ℝ) {α : ℝ → ℝ} (ha : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (s : ℝ) (t r : ℝ≥0) (htr : t+r ≤ 1) (l : List (ℝ × ℝ≥0))
    (hm : ∀ p∈l, p.1∈Icc (0:ℝ) 1) (hd : chainDuration l=t+r)
    (hmodel : TimeChainModels α s l) :
    scalarCDFOperator β α s (t+r) f=
      scalarCDFOperator β α s t (scalarCDFOperator β α (s+t) r f) := by
  have ht : t ≤ 1 := (le_add_of_nonneg_right (show (0:ℝ≥0) ≤ r from bot_le)).trans htr
  have hr : r ≤ 1 := (le_add_of_nonneg_left (show (0:ℝ≥0) ≤ t from bot_le)).trans htr
  obtain ⟨l₁,l₂,h₁,h₂,hm₁,hm₂,hs₁,hs₂,he⟩ := scalarTimeChain_split_at β α l hm s hmodel t r hd
  have htail : scalarCDFOperator β α (s+t) r f=scalarTimeChain β l₂ f := by
    funext x
    exact scalarCDFOperator_eq_chain hf hK β ha hmono l₂ hm₂ (s+t) r hr h₂ hs₂ x
  funext x
  rw [htail,scalarCDFOperator_eq_chain hf hK β ha hmono l hm s (t+r) htr hd hmodel,
    scalarCDFOperator_eq_chain (scalarTimeChain_regular hf β l₂)
      (scalarTimeChain_lipschitz hf hK β l₂ (fun p hp => (hm₂ p hp).1))
      β ha hmono l₁ hm₁ s t ht h₁ hs₁]
  exact (congrFun (he f hf) x).symm

theorem quantile_suffix_chain {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    ∃ l : List (ℝ × ℝ≥0), chainDuration l=Real.toNNReal (1-s) ∧
      (∀ p∈l, p.1∈Icc (0:ℝ) 1) ∧ TimeChainModels (quantileCDF k Q) s l := by
  obtain ⟨l,hd,hm,hmodel,_⟩ := quantile_full_chain Q hQ.1 (hQ.2 0).1 (hQ.2 (Fin.last k)).2
  have he : chainDuration l=Real.toNNReal s+Real.toNNReal (1-s) := by
    rw [hd]
    apply NNReal.coe_injective
    rw [NNReal.coe_add,Real.coe_toNNReal s hs.1,Real.coe_toNNReal (1-s) (sub_nonneg.mpr hs.2),NNReal.coe_one]
    ring
  obtain ⟨_,l₂,_,h₂,_,hm₂,_,hs₂,_⟩ := scalarTimeChain_split_at β (quantileCDF k Q) l hm 0 hmodel _ _ he
  exact ⟨l₂,h₂,hm₂,by simpa only [zero_add,Real.coe_toNNReal s hs.1] using hs₂⟩

theorem scalarCDFValue_suffix_semigroup_quantile {k : ℕ} (β : ℝ) (Q : Fin (k+1) → ℝ)
    (hQ : Q∈admissibleQuantiles k) {s q : ℝ} (hs : 0  ≤  s) (hsq : s  ≤  q) (hq : q  ≤  1) :
    scalarCDFValue β (quantileCDF k Q) s (Real.toNNReal (1-s))=
      scalarCDFOperator β (quantileCDF k Q) s (Real.toNNReal (q-s))
        (scalarCDFValue β (quantileCDF k Q) q (Real.toNNReal (1-q))) := by
  let t := Real.toNNReal (q-s)
  let r := Real.toNNReal (1-q)
  have ht : (t:ℝ)=q-s := Real.coe_toNNReal _ (sub_nonneg.mpr hsq)
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal _ (sub_nonneg.mpr hq)
  have hb : t+r=Real.toNNReal (1-s) := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add,ht,hr,Real.coe_toNNReal _ (by linarith)]
    ring
  have htr : t+r ≤ 1 := by rw [← NNReal.coe_le_coe,NNReal.coe_add,ht,hr,NNReal.coe_one]; linarith
  obtain ⟨l,hd,hm,hmodel⟩ := quantile_suffix_chain β Q hQ ⟨hs,hsq.trans hq⟩
  have H := scalarCDFOperator_semigroup_of_chain scalarSpinTerminal_regular scalarSpinTerminal_lipschitz
    β (quantileCDF_bounds k Q) (quantileCDF_monotone k Q) s t r htr l hm (hd.trans hb.symm) hmodel
  rw [hb,show s+(t:ℝ)=q by rw [ht]; ring] at H
  exact H

theorem scalarCDFValue_suffix_semigroup (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) {s q : ℝ}
    (hs : 0  ≤  s) (hsq : s  ≤  q) (hq : q  ≤  1) :
    scalarCDFValue β α s (Real.toNNReal (1-s))=
      scalarCDFOperator β α s (Real.toNNReal (q-s))
        (scalarCDFValue β α q (Real.toNNReal (1-q))) := by
  let t := Real.toNNReal (q-s)
  let r := Real.toNNReal (1-q)
  let u := Real.toNNReal (1-s)
  have ht : (t:ℝ)=q-s := Real.coe_toNNReal _ (sub_nonneg.mpr hsq)
  have hr : (r:ℝ)=1-q := Real.coe_toNNReal _ (sub_nonneg.mpr hq)
  have hu : (u:ℝ)=1-s := Real.coe_toNNReal _ (sub_nonneg.mpr (hsq.trans hq))
  have ht1 : t ≤ 1 := by rw [← NNReal.coe_le_coe,ht,NNReal.coe_one]; linarith
  have hr1 : r ≤ 1 := by rw [← NNReal.coe_le_coe,hr,NNReal.coe_one]; linarith
  have hu1 : u ≤ 1 := by rw [← NNReal.coe_le_coe,hu,NNReal.coe_one]; linarith
  let a (n : ℕ) := quantileCDF n (uniformCDFQuantiles n α)
  have hb (n : ℕ) := quantileCDF_bounds n (uniformCDFQuantiles n α)
  have hm (n : ℕ) := quantileCDF_monotone n (uniformCDFQuantiles n α)
  have hD : Tendsto (fun n => cdfDistance (a n) α) atTop (𝓝 0) := uniformCDFQuantiles_L1_tendsto α ha h1
  funext x
  have hvalue (n : ℕ) {b : ℝ} {v : ℝ≥0} (hb0 : 0 ≤ b) (hv1 : b+v ≤ 1) (hv : v ≤ 1) (z : ℝ) :
      |scalarCDFValue β (a n) b v z-scalarCDFValue β α b v z| ≤ scalarTimeMassConstant β*cdfDistance (a n) α :=
    (scalarCDFValue_cdf_lipschitz β (hb n) (hm n) ha α.mono b v hv z).trans
      (mul_le_mul_of_nonneg_left (cdfDistance_subinterval_le (hm n) α.mono hb0 hv1)
        (scalarTimeMassConstant_nonneg β))
  have herr (n : ℕ) : |scalarCDFValue β α s u x-
      scalarCDFOperator β α s t (scalarCDFValue β α q r) x| ≤
      (2*scalarTimeMassConstant β+scalarTimeMassConstantK β 1)*cdfDistance (a n) α := by
    have E := hvalue n (hs.trans hsq) (v:=r) (by rw [hr]; linarith) hr1
    have H₁ := scalarCDFOperator_uniform_nonexpansive
      (scalarCDFValue_regular β (hb n) (hm n) q r hr1) (scalarCDFValue_regular β ha α.mono q r hr1)
      (scalarCDFValue_lipschitz β (hb n) (hm n) q r hr1) (scalarCDFValue_lipschitz β ha α.mono q r hr1)
      β (hb n) (hm n) s t ht1 E x
    have H₂ := (scalarCDFOperator_cdf_lipschitz (scalarCDFValue_regular β ha α.mono q r hr1)
      (scalarCDFValue_lipschitz β ha α.mono q r hr1) β (hb n) (hm n) ha α.mono s t ht1 x).trans
      (mul_le_mul_of_nonneg_left (cdfDistance_subinterval_le (hm n) α.mono hs (by rw [ht]; linarith))
        (scalarTimeMassConstantK_nonneg β 1))
    have H₀ := hvalue n hs (v:=u) (by rw [hu]; linarith) hu1 x
    rw [abs_sub_comm] at H₀
    have he := congrFun (scalarCDFValue_suffix_semigroup_quantile β (uniformCDFQuantiles n α)
      (uniformCDFQuantiles_admissible n α h1) hs hsq hq) x
    calc
      _  ≤  |scalarCDFValue β α s u x-scalarCDFValue β (a n) s u x|+
          |scalarCDFValue β (a n) s u x-scalarCDFOperator β α s t (scalarCDFValue β α q r) x| := abs_sub_le _ _ _
      _  ≤  scalarTimeMassConstant β*cdfDistance (a n) α+
          (scalarTimeMassConstant β+scalarTimeMassConstantK β 1)*cdfDistance (a n) α := by
        apply add_le_add H₀
        change |scalarCDFValue β (quantileCDF n (uniformCDFQuantiles n α)) s (Real.toNNReal (1-s)) x-_| ≤ _
        rw [he]
        exact (abs_sub_le _ _ _).trans ((add_le_add H₁ H₂).trans_eq (by ring))
      _ = _ := by ring
  have H := ge_of_tendsto (hD.const_mul (2*scalarTimeMassConstant β+scalarTimeMassConstantK β 1))
    (Eventually.of_forall herr)
  simp only [mul_zero] at H
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H (abs_nonneg _)))

end SK.Analytic

end
end

end OAI
