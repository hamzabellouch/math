import Mathlib
import OAI.Probability.SKBarriers.Scalar.ScalarGeneralTerminal
import OAI.Probability.SKBarriers.Hierarchy.TimeChainSplit

namespace OAI

section

noncomputable section
open scoped NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem TimeChainModels.mass_bounds {α : ℝ → ℝ} (hα : Monotone α)
    {s : ℝ} {l : List (ℝ × ℝ≥0)} (hl : TimeChainModels α s l)
    {p : ℝ × ℝ≥0} (hp : p∈l) (ht : 0<p.2) :
    α s≤p.1 ∧ p.1≤α (s+chainDuration l) := by
  induction l generalizing s with
  | nil => simp at hp
  | cons q l ih =>
    rcases q with ⟨m,d⟩
    rcases hl with ⟨hcell,htail⟩
    rcases List.mem_cons.mp hp with rfl|hp
    · have he : α s=m := hcell s ⟨le_rfl,by exact lt_add_of_pos_right s ht⟩
      refine ⟨he.le,?_⟩
      rw [← he]
      exact hα (le_add_of_nonneg_right (chainDuration ((m,d)::l)).coe_nonneg)
    · obtain ⟨h₁,h₂⟩ := ih htail hp
      refine ⟨(hα (le_add_of_nonneg_right d.coe_nonneg)).trans h₁,?_⟩
      simpa only [chainDuration_cons,NNReal.coe_add,add_assoc] using h₂

theorem scalarTimeChain_constant_error {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β a : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p∈l, p.1 ∈ Icc (0:ℝ) 1)
    (ht : chainDuration l≤1) {ω : ℝ}
    (hω : ∀ p∈l, 0<p.2 → |p.1-a| ≤ ω) (x : ℝ) :
    |scalarTimeChain β l f x-scalarTimeStep β a (chainDuration l) f x| ≤
      scalarTimeMassConstantK β K*(chainDuration l:ℝ)*ω := by
  induction l generalizing x with
  | nil => simp [scalarTimeChain]
  | cons p l ih =>
    rcases p with ⟨m,d⟩
    have hd : d≤1 := (le_add_of_nonneg_right (chainDuration l).coe_nonneg).trans ht
    have hl : chainDuration l≤1 := (le_add_of_nonneg_left d.coe_nonneg).trans ht
    have hm' (p) (hp:p∈l) := hm p (List.mem_cons_of_mem _ hp)
    have hω' (p) (hp:p∈l) := hω p (List.mem_cons_of_mem _ hp)
    let g := scalarTimeStep β a (chainDuration l) f
    have hg : BoundedDerivs g := scalarTimeStep_regular hf β a _
    have hLipg : LipschitzWith K g := scalarTimeStep_lipschitz hf hLip ha.1 β _
    have H₁ := scalarStep_uniform_nonexpansive (scalarTimeChain_regular hf β l) hg
      (hm (m,d) (List.mem_cons_self)).1 (fun y => ih hm' hl hω' y) (β*Real.sqrt (d:ℝ)) x
    have H₂ := scalarTimeStep_mass_lipschitz_general hg hLipg β hd ha
      (hm (m,d) (List.mem_cons_self)) x
    have Herr : scalarTimeMassConstantK β K*(d:ℝ)*|m-a| ≤ scalarTimeMassConstantK β K*(d:ℝ)*ω := by
      by_cases hd0 : d=0
      · simp [hd0]
      · exact mul_le_mul_of_nonneg_left (hω (m,d) (List.mem_cons_self) (pos_iff_ne_zero.mpr hd0))
          (mul_nonneg (scalarTimeMassConstantK_nonneg β K) d.coe_nonneg)
    rw [chainDuration_cons,← scalarTimeStep_semigroup hf]
    calc
      _ ≤ |scalarTimeStep β m d (scalarTimeChain β l f) x-scalarTimeStep β m d g x|+
          |scalarTimeStep β m d g x-scalarTimeStep β a d g x| := abs_sub_le _ _ _
      _ ≤ _+_ := add_le_add H₁ (H₂.trans Herr)
      _ = _ := by rw [NNReal.coe_add]; ring

theorem dyadicScalar_chain_error {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α) (n : ℕ)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p∈l, p.1 ∈ Icc (0:ℝ) 1)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hdur : chainDuration l=t)
    (hmodel : TimeChainModels α s l) (x : ℝ) :
    |dyadicScalar β α n s t f x-scalarTimeChain β l f x| ≤
      scalarTimeMassConstantK β K*(t:ℝ)/(2:ℝ)^n*(α (s+t)-α s) := by
  induction n generalizing f l s t x with
  | zero =>
    simp only [dyadicScalar_zero,pow_zero,div_one,abs_sub_comm]
    rw [← hdur]
    apply scalarTimeChain_constant_error hf hLip β (α s) (hα s) l hm (hdur ▸ ht)
    intro p hp hpos
    have H := hmodel.mass_bounds hmono hp hpos
    rw [abs_of_nonneg (sub_nonneg.mpr H.1)]
    exact sub_le_sub_right H.2 _
  | succ n ih =>
    have hhalf : t/2≤1 := (div_le_self (show (0:ℝ≥0)≤t from bot_le) (by norm_num)).trans ht
    have hc : ((t/2:ℝ≥0):ℝ)=(t:ℝ)/2 := by norm_num
    have hsplit : chainDuration l=t/2+t/2 := hdur.trans (by ring)
    obtain ⟨l₁,l₂,h₁,h₂,hm₁,hm₂,ht₁,ht₂,he⟩ := scalarTimeChain_split_at β α l hm s hmodel (t/2) (t/2) hsplit
    rw [dyadicScalar_succ,← congrFun (he f hf) x]
    let g := scalarTimeChain β l₂ f
    have hg : BoundedDerivs g := scalarTimeChain_regular hf β l₂
    have hLipg : LipschitzWith K g := scalarTimeChain_lipschitz hf hLip β l₂ (fun p hp => (hm₂ p hp).1)
    have H₂ := ih hf hLip l₂ hm₂ (s+(t:ℝ)/2) (t/2) hhalf h₂ (hc ▸ ht₂)
    have H₁ := dyadicScalar_uniform_nonexpansive (dyadicScalar_regular hf β α n _ _) hg β hα n s (t/2) H₂ x
    have H₀ := ih hg hLipg l₁ hm₁ s (t/2) hhalf h₁ ht₁ x
    calc
      _ ≤ |dyadicScalar β α n s (t/2) (dyadicScalar β α n (s+(t:ℝ)/2) (t/2) f) x-
            dyadicScalar β α n s (t/2) g x|+
          |dyadicScalar β α n s (t/2) g x-scalarTimeChain β l₁ g x| := abs_sub_le _ _ _
      _ ≤ _+_ := add_le_add H₁ H₀
      _ = _ := by rw [hc,show s+(t:ℝ)/2+(t:ℝ)/2=s+t by ring,pow_succ]; ring

theorem scalarCDFOperator_eq_chain {f : ℝ → ℝ} (hf : BoundedDerivs f)
    {K : ℝ≥0} (hLip : LipschitzWith K f) (β : ℝ) {α : ℝ → ℝ}
    (hα : ∀ z, α z∈Icc (0:ℝ) 1) (hmono : Monotone α)
    (l : List (ℝ × ℝ≥0)) (hm : ∀ p∈l, p.1 ∈ Icc (0:ℝ) 1)
    (s : ℝ) (t : ℝ≥0) (ht : t≤1) (hdur : chainDuration l=t)
    (hmodel : TimeChainModels α s l) (x : ℝ) :
    scalarCDFOperator β α s t f x=scalarTimeChain β l f x := by
  have hv := (dyadicScalar_general_uniform hf hLip β hα hmono s t ht).tendsto_at x
  have hz : Tendsto (fun n : ℕ => scalarTimeMassConstantK β K*(t:ℝ)/(2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have H := le_of_tendsto_of_tendsto (hv.sub_const (scalarTimeChain β l f x)).abs
    (hz.mul_const (α (s+t)-α s)) (Eventually.of_forall
      (fun n => dyadicScalar_chain_error hf hLip β hα hmono n l hm s t ht hdur hmodel x))
  simp only [zero_mul] at H
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm H (abs_nonneg _)))

end SK.Analytic

end
end

end OAI
