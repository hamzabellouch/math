import Mathlib
import OAI.Probability.UnimodularPercolation.Exploration.FractionalMoments

namespace OAI

/-! Tail Bounds for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterTailDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteClusterTail_derivative_bound (G : BondGraph V E) (Q : Finset E) (x : V)
    (n : ℕ) (p h : unitInterval) (hn : 1 ≤ (h:ℝ)*n) (α C : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hC0 : 0 < C) (hsmall : C*(h:ℝ)^α ≤ 1/4)
    (hfin : ∀ y, ∀ᵐ ω ∂law p, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law p))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law p) ≤ C) :
    finiteClusterTail G Q x n p ≤ 8*C*(h:ℝ)^α*deriv (finiteClusterTail G Q x n) p := by
  have hmark := (markedConnection_le_cluster_power G Q x h p α hα hα1 (hfin x) (hI x)).trans
    (mul_le_mul_of_nonneg_left (hC x) (Real.rpow_nonneg h.2.1 α))
  rw [mul_comm ((h:ℝ)^α) C] at hmark
  have hlow := finiteSeed_covariance_lower G Q x n p h hn (C*(h:ℝ)^α) hmark
  have hupp := finiteSeed_covariance_upper G Q x p h α C hα hα1 hfin hI hC
    (finiteClusterTailIndicator G x n) (finiteClusterTailIndicator_mono G x n)
  have hF := finiteClusterTail_nonneg G Q x n p
  have hd := finiteClusterTail_deriv_nonneg G Q x n p
  have hp : (p:ℝ)*(1-(p:ℝ)) ≤ 1 := by nlinarith [p.2.1,p.2.2]
  have hprod := mul_le_mul_of_nonneg_right hp hd
  have hR : 0 ≤ 2*C*(h:ℝ)^α := mul_nonneg (by positivity) (Real.rpow_nonneg h.2.1 α)
  have hh := mul_le_mul_of_nonneg_left hprod hR
  have ha := le_abs_self (finiteCovariance Q p (finiteClusterTailIndicator G x n)
    (fun ω => finiteSeedProbability G (insert x (searchVertices G Q)) ω x h))
  have hs := mul_le_mul_of_nonneg_right hsmall hF
  change |_| ≤ _*deriv (finiteClusterTail G Q x n) p at hupp
  nlinarith

theorem exponential_transfer_of_deriv_lower (H : ℝ → ℝ) (a b K : ℝ)
    (hH : Differentiable ℝ H) (hab : a ≤ b)
    (hb : ∀ t ∈ Set.Icc a b, K*H t ≤ deriv H t) :
    H a ≤ Real.exp (-K*(b-a))*H b := by
  let F (t : ℝ) := Real.exp (-K*(t-a))*H t
  have hF (t : ℝ) : HasDerivAt F (Real.exp (-K*(t-a))*(deriv H t-K*H t)) t := by
    have he := (((hasDerivAt_id t).sub_const a).const_mul (-K)).exp
    convert! he.mul (hH t).hasDerivAt using 1
    simp only [id_eq]
    ring
  have hmono : MonotoneOn F (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun t _ => (hF t).continuousAt.continuousWithinAt)
      (fun t _ => (hF t).differentiableAt.differentiableWithinAt)
    intro t ht
    rw [(hF t).deriv]
    exact mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr (hb t (interior_subset ht)))
  have hh := hmono ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  simpa only [F,sub_self,mul_zero,Real.exp_zero,one_mul] using hh

end ClusterTailDerivative
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteStretchedTail
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_finite_ae_mono [Countable E] (G : BondGraph V E)
    (x : V) (p q : unitInterval) (hpq : p ≤ q)
    (hq : ∀ᵐ ω ∂law q, (cluster G ω x).Finite) :
    ∀ᵐ ω ∂law p, (cluster G ω x).Finite := by
  have hlabels : ∀ᵐ labels ∂(labelLaw : Measure (E → unitInterval)),
      (cluster G (openEdges labels q) x).Finite := by
    apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
      (p := fun ω : Set E => (cluster G ω x).Finite) (measurable_openEdges q).aemeasurable
    rwa [map_openEdges]
  rw [←map_openEdges p]
  apply (ae_map_iff (measurable_openEdges p).aemeasurable
    (by simpa only [Set.compl_ofPred,Set.not_infinite] using (measurableSet_infinite_cluster G x).compl)).mpr
  filter_upwards [hlabels] with labels hl
  exact hl.subset (fun y h => conn_mono G (openEdges_mono labels hpq) h)

theorem finiteClusterTail_le_markedConnection (G : BondGraph V E) (Q : Finset E)
    (x : V) (n : ℕ) (p h : unitInterval) (hn : 1 ≤ (h:ℝ)*n) :
    finiteClusterTail G Q x n p ≤ 2*markedConnectionPolynomial G Q x h p := by
  have hh : (1:ℝ)/2*finiteClusterTail G Q x n p ≤ markedConnectionPolynomial G Q x h p := by
    rw [finiteClusterTail,←bernoulliPolynomial_const_mul,markedConnection_component_polynomial]
    apply bernoulliPolynomial_mono _ _ _ p p.2
    intro ω _
    unfold finiteClusterTailIndicator
    by_cases hs : n ≤ (finiteRootComponent G ω x).card
    · simp only [ite_eq_left hs,mul_one]
      apply one_sub_pow_one_sub_ge_half
      exact hn.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hs) h.2.1)
    · simp only [ite_eq_right hs,mul_zero]
      apply sub_nonneg.mpr
      exact pow_le_one₀ (sub_nonneg.mpr h.2.2) (by linarith [h.2.1])
  linarith

 

theorem finiteClusterTail_stretched [Countable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (x : V) (n : ℕ) (p q h : unitInterval) (hpq : p ≤ q)
    (hh : 0 < (h:ℝ)) (hn : 1 ≤ (h:ℝ)*n) (α C : ℝ)
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hC0 : 0 < C) (hsmall : C*(h:ℝ)^α ≤ 1/4)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C) :
    finiteClusterTail G Q x n p ≤
      Real.exp (-((q:ℝ)-(p:ℝ))/(8*C*(h:ℝ)^α))*(2*C*(h:ℝ)^α) := by
  have hden : 0 < 8*C*(h:ℝ)^α := by positivity
  have hexp := exponential_transfer_of_deriv_lower (finiteClusterTail G Q x n) p q
    (1/(8*C*(h:ℝ)^α)) (fun t => (hasDerivAt_bernoulliPolynomial Q _ t).differentiableAt) hpq
  have hder : ∀ t ∈ Set.Icc (p:ℝ) (q:ℝ),
      (1/(8*C*(h:ℝ)^α))*finiteClusterTail G Q x n t ≤ deriv (finiteClusterTail G Q x n) t := by
    intro t ht
    let r : unitInterval := ⟨t,⟨p.2.1.trans ht.1,ht.2.trans q.2.2⟩⟩
    have hrq : r ≤ q := ht.2
    have hmoment (y : V) := cluster_power_mono_integral G hloc y r q hrq α hα (hfin y) (hI y)
    have he := finiteClusterTail_derivative_bound G Q x n r h hn α C hα hα1 hC0 hsmall
      (fun y => cluster_finite_ae_mono G y r q hrq (hfin y)) (fun y => (hmoment y).1)
      (fun y => (hmoment y).2.trans (hC y))
    rw [one_div,mul_comm,←div_eq_mul_inv]
    apply (div_le_iff₀ hden).mpr
    simpa only [mul_comm (deriv (finiteClusterTail G Q x n) t)] using he
  have he := hexp hder
  have hb := (finiteClusterTail_le_markedConnection G Q x n q h hn).trans
    (mul_le_mul_of_nonneg_left ((markedConnection_le_cluster_power G Q x h q α hα hα1 (hfin x) (hI x)).trans
      (mul_le_mul_of_nonneg_left (hC x) (Real.rpow_nonneg hh.le α))) (by norm_num : (0:ℝ) ≤ 2))
  have hm := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-((q:ℝ)-(p:ℝ))/(8*C*(h:ℝ)^α))).le
  have heq : -(1/(8*C*(h:ℝ)^α))*((q:ℝ)-(p:ℝ)) = -((q:ℝ)-(p:ℝ))/(8*C*(h:ℝ)^α) := by ring
  rw [heq] at he
  have hb' : Real.exp (-((q:ℝ)-(p:ℝ))/(8*C*(h:ℝ)^α))*(2*((h:ℝ)^α*C)) =
      Real.exp (-((q:ℝ)-(p:ℝ))/(8*C*(h:ℝ)^α))*(2*C*(h:ℝ)^α) := by ring
  exact he.trans (hm.trans_eq hb')

end FiniteStretchedTail
end Percolation

 
namespace Percolation
open MeasureTheory Filter
section ExponentialPowerBound

 

theorem exists_exp_neg_le_rpow (r : ℝ) (hr : 0 ≤ r) :
    ∃ K : ℝ, 0 < K ∧ ∀ t : ℝ, 0 < t → Real.exp (-t) ≤ K*t^(-r) := by
  obtain ⟨m,hm⟩ := exists_nat_ge r
  let K : ℝ := m.factorial
  have hK1 : 1 ≤ K := by
    dsimp [K]
    exact_mod_cast (Nat.succ_le_of_lt (Nat.factorial_pos m))
  refine ⟨K,by linarith,?_⟩
  intro t ht
  rw [Real.rpow_neg ht.le,←div_eq_mul_inv]
  apply (le_div_iff₀ (Real.rpow_pos_of_pos ht r)).mpr
  by_cases ht1 : t ≤ 1
  · have hp := Real.rpow_le_one ht.le ht1 hr
    have he : Real.exp (-t) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    exact (mul_le_of_le_one_left (Real.rpow_nonneg ht.le r) he).trans (hp.trans hK1)
  · have hpow : t^r ≤ t^m := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le (le_of_not_ge ht1) hm
    have hTaylor : t^m ≤ K*Real.exp t := by
      have hh := Real.pow_div_factorial_le_exp t ht.le m
      exact (div_le_iff₀ (show (0:ℝ) < (m.factorial:ℝ) by positivity)).mp hh |>.trans_eq (mul_comm _ _)
    calc
      _ ≤ Real.exp (-t)*(K*Real.exp t) :=
        mul_le_mul_of_nonneg_left (hpow.trans hTaylor) (Real.exp_pos _).le
      _ = K := by rw [Real.exp_neg]; field_simp

end ExponentialPowerBound
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section PolynomialTails
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exp_stretched_power_bound (r K δ C z : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hz : 0 < z) (hK : ∀ t : ℝ, 0 < t → Real.exp (-t) ≤ K*t^(-r)) :
    Real.exp (-δ/(8*C*z))*(2*C*z) ≤
      (2*C*K*(8*C)^r)*δ^(-r)*z^(1+r) := by
  have he := mul_le_mul_of_nonneg_right (hK (δ/(8*C*z)) (by positivity))
    (by positivity : 0 ≤ 2*C*z)
  have hid : (δ/(8*C*z))^(-r)*(2*C*z) =
      (2*C*(8*C)^r)*δ^(-r)*z^(1+r) := by
    rw [Real.div_rpow hδ.le (by positivity),Real.mul_rpow (by positivity : 0 ≤ 8*C) hz.le,
      Real.rpow_neg (by positivity : 0 ≤ 8*C),Real.rpow_neg hz.le,
      Real.rpow_add hz,Real.rpow_one]
    field_simp
  calc
    _ ≤ K*(δ/(8*C*z))^(-r)*(2*C*z) := by simpa only [neg_div] using he
    _ = K*((δ/(8*C*z))^(-r)*(2*C*z)) := by ring
    _ = _ := by rw [hid]; ring

 

theorem finiteClusterTail_polynomial_large [Countable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (q : unitInterval) (α C r : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hC0 : 0 < C)
    (hr : 0 ≤ r)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (Q : Finset E) (x : V) (p : unitInterval), p < q →
      ∀ n : ℕ, 1 ≤ n → C*(n:ℝ)^(-α) ≤ 1/4 →
      finiteClusterTail G Q x n p ≤ A*((q:ℝ)-(p:ℝ))^(-r)*(n:ℝ)^(-α*(1+r)) := by
  obtain ⟨K,hK,hKb⟩ := exists_exp_neg_le_rpow r hr
  refine ⟨2*C*K*(8*C)^r,by positivity,?_⟩
  intro Q x p hp n hn hsmall
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let h : unitInterval := ⟨1/(n:ℝ),⟨by positivity,by apply (div_le_one hn0).mpr; exact_mod_cast hn⟩⟩
  have hh : 0 < (h:ℝ) := by dsimp [h]; positivity
  have hhpow : (h:ℝ)^α = (n:ℝ)^(-α) := by
    dsimp [h]
    rw [one_div,Real.inv_rpow hn0.le,Real.rpow_neg hn0.le]
  have hhprod : 1 ≤ (h:ℝ)*n := by dsimp [h]; rw [one_div,inv_mul_cancel₀ hn0.ne']
  have hst := finiteClusterTail_stretched G hloc Q x n p q h hp.le hh hhprod α C hα hα1 hC0
    (by rwa [hhpow]) hfin hI hC
  have he := exp_stretched_power_bound r K ((q:ℝ)-(p:ℝ)) C ((h:ℝ)^α)
    (sub_pos.mpr hp) hC0 (Real.rpow_pos_of_pos hh α) hKb
  apply hst.trans
  convert! he using 1
  rw [hhpow,←Real.rpow_mul hn0.le]

end PolynomialTails
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section UniformPolynomialTails
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteClusterTail_le_one (G : BondGraph V E) (Q : Finset E) (x : V)
    (n : ℕ) (p : unitInterval) : finiteClusterTail G Q x n p ≤ 1 := by
  rw [finiteClusterTail,←bernoulliPolynomial_const Q 1 p]
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  unfold finiteClusterTailIndicator
  split_ifs <;> norm_num

 

theorem finiteClusterTail_polynomial [Countable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (q : unitInterval) (α C r : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hC0 : 0 < C)
    (hr : 0 ≤ r)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C) :
    ∃ A : ℝ, 0 < A ∧ ∀ (Q : Finset E) (x : V) (p : unitInterval), p < q →
      ∀ n : ℕ, 1 ≤ n →
      finiteClusterTail G Q x n p ≤ A*((q:ℝ)-(p:ℝ))^(-r)*(n:ℝ)^(-α*(1+r)) := by
  obtain ⟨A,hA,hbig⟩ := finiteClusterTail_polynomial_large G hloc q α C r hα.le hα1 hC0 hr hfin hI hC
  have ht : Tendsto (fun n : ℕ => C*(n:ℝ)^(-α)) atTop (nhds 0) := by
    simpa only [mul_zero,Function.comp_apply] using tendsto_const_nhds.mul
      ((tendsto_rpow_neg_atTop hα).comp tendsto_natCast_atTop_atTop)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4)))
  let s := α*(1+r)
  have hs : 0 ≤ s := by dsimp [s]; positivity
  let B : ℝ := ((N+1:ℕ):ℝ)^s+A
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B,hB,?_⟩
  intro Q x p hp n hn
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hδ : 0 < (q:ℝ)-(p:ℝ) := sub_pos.mpr hp
  have hhead : 1 ≤ ((q:ℝ)-(p:ℝ))^(-r) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ (by linarith [p.2.1,q.2.2]) (by linarith)
  by_cases hnN : N ≤ n
  · apply (hbig Q x p hp n hn (hN n hnN).le).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by dsimp [B]; linarith [Real.rpow_nonneg (Nat.cast_nonneg (N+1)) s]) (Real.rpow_nonneg hδ.le _)) (Real.rpow_nonneg hn0.le _)
  · have hnB : (n:ℝ)^s ≤ B := by
      apply (Real.rpow_le_rpow hn0.le (show (n:ℝ) ≤ ((N+1:ℕ):ℝ) by exact_mod_cast (by omega : n ≤ N+1)) hs).trans
      dsimp [B]
      linarith
    have hBδ : B ≤ B*((q:ℝ)-(p:ℝ))^(-r) := by nlinarith
    have hbound : 1 ≤ B*((q:ℝ)-(p:ℝ))^(-r)*(n:ℝ)^(-s) := by
      rw [Real.rpow_neg hn0.le,←div_eq_mul_inv]
      exact (one_le_div (Real.rpow_pos_of_pos hn0 s)).mpr (hnB.trans hBδ)
    exact (finiteClusterTail_le_one G Q x n p).trans (by simpa only [s,neg_mul] using hbound)

end UniformPolynomialTails
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section TailSummation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem natCast_eq_sum_tail (k M : ℕ) (hk : k ≤ M) :
    (k:ℝ) = ∑ i ∈ Finset.range M, if i+1 ≤ k then (1:ℝ) else 0 := by
  rw [Finset.sum_boole]
  congr 1
  have hh : (Finset.range M).filter (fun i => i+1 ≤ k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [hh,Finset.card_range]

theorem finiteClusterSize_eq_sum_tail (G : BondGraph V E) (Q : Finset E) (x : V) (p : ℝ) :
    bernoulliPolynomial Q (fun ω => ((finiteRootComponent G ω x).card:ℝ)) p =
      ∑ n ∈ Finset.range (insert x (searchVertices G Q)).card, finiteClusterTail G Q x (n+1) p := by
  simp only [finiteClusterTail]
  rw [←bernoulliPolynomial_sum]
  apply bernoulliPolynomial_congr
  intro ω hω
  exact natCast_eq_sum_tail _ _ (Finset.card_le_card (finiteRootComponent_subset G Q _ x ω hω (by rfl)))

theorem summable_shifted_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => ((n+1:ℕ):ℝ)^(-s)) := by
  exact (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))

 
theorem finiteClusterSize_bound_of_tail (G : BondGraph V E) (Q : Finset E) (x : V)
    (p : unitInterval) (A s : ℝ) (hA : 0 ≤ A) (hs : 1 < s)
    (hf : ∀ n : ℕ, 1 ≤ n → finiteClusterTail G Q x n p ≤ A*(n:ℝ)^(-s)) :
    bernoulliPolynomial Q (fun ω => ((finiteRootComponent G ω x).card:ℝ)) p ≤
      A*(∑' n : ℕ, ((n+1:ℕ):ℝ)^(-s)) := by
  rw [finiteClusterSize_eq_sum_tail,←tsum_mul_left]
  have hsumm := (summable_shifted_rpow s hs).mul_left A
  apply (Finset.sum_le_sum (fun n _ => hf (n+1) (by omega))).trans
  exact hsumm.sum_le_tsum _ (fun n _ => mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg _) _))

end TailSummation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section SusceptibilityExhaustion
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finite_connection_row_le_size (G : BondGraph V E) (Q : Finset E)
    (x : V) (K : Finset V) (p : unitInterval) :
    (∑ y ∈ K, bernoulliPolynomial Q (fun ω => if Conn G ω x y then (1:ℝ) else 0) p) ≤
      bernoulliPolynomial Q (fun ω => ((finiteRootComponent G ω x).card:ℝ)) p := by
  rw [←bernoulliPolynomial_sum]
  apply bernoulliPolynomial_mono _ _ _ p p.2
  intro ω _
  rw [Finset.sum_boole]
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro y hy
  change y ∈ (finiteRootComponent G ω x : Set V)
  rw [coe_finiteRootComponent]
  exact (Finset.mem_filter.mp hy).2

 

theorem susceptibility_bound_of_finite_size [Countable E] (G : BondGraph V E)
    (x : V) (p : unitInterval) (B : ℝ)
    (hB : ∀ Q : Finset E, bernoulliPolynomial Q (fun ω => ((finiteRootComponent G ω x).card:ℝ)) p ≤ B) :
    Summable (twoPoint G p x) ∧ susceptibility G p x ≤ B := by
  let : Encodable E := Encodable.ofCountable E
  let Q := vertexExhaustion (V := E)
  have hrow (K : Finset V) : (∑ y ∈ K, twoPoint G p x y) ≤ B := by
    have ht (y : V) : Tendsto (fun n => bernoulliPolynomial (Q n)
        (fun ω => if Conn G ω x y then (1:ℝ) else 0) p) atTop (nhds (twoPoint G p x y)) := by
      have hc (e : E) (_ : e ∈ (Set.univ : Set E)) : ∃ n, e ∈ Q n := by
        obtain ⟨n,hn⟩ := subset_vertexExhaustion ({e} : Finset E)
        exact ⟨n,hn (by simp)⟩
      simpa only [Set.inter_univ,twoPoint,Measure.real] using! finite_connection_polynomial_tendsto G Set.univ Q
        vertexExhaustion_mono (fun _ => Set.subset_univ _) hc p x y
    apply le_of_tendsto (tendsto_finsetSum K (fun y _ => ht y))
    exact Filter.Eventually.of_forall (fun n => (finite_connection_row_le_size G (Q n) x K p).trans (hB (Q n)))
  exact ⟨summable_of_sum_le (twoPoint_nonneg G p x) hrow,
    Real.tsum_le_of_sum_le (twoPoint_nonneg G p x) hrow⟩

end SusceptibilityExhaustion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section SusceptibilityPowerFromMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem susceptibility_power_of_uniform_moment [Countable E] (G : BondGraph V E) (hloc : LocallyFinite G)
    (q : unitInterval) (α C r : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hC0 : 0 < C)
    (hr : 0 ≤ r) (hs : 1 < α*(1+r))
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hI : ∀ y, Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q))
    (hC : ∀ y, (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : unitInterval), p < q → ∀ x,
      Summable (twoPoint G p x) ∧ susceptibility G p x ≤ D*((q:ℝ)-(p:ℝ))^(-r) := by
  obtain ⟨A,hA,hbound⟩ := finiteClusterTail_polynomial G hloc q α C r hα hα1 hC0 hr hfin hI hC
  let S := ∑' n : ℕ, ((n+1:ℕ):ℝ)^(-(α*(1+r)))
  have hS : 0 ≤ S := tsum_nonneg (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨1+A*S,by positivity,?_⟩
  intro p hp x
  have hδ : 0 < (q:ℝ)-(p:ℝ) := sub_pos.mpr (show (p:ℝ)<(q:ℝ) from hp)
  apply susceptibility_bound_of_finite_size
  intro Q
  have hh := finiteClusterSize_bound_of_tail G Q x p (A*((q:ℝ)-(p:ℝ))^(-r)) (α*(1+r))
    (mul_nonneg hA.le (Real.rpow_nonneg hδ.le _)) hs (by
      intro n hn
      simpa only [neg_mul] using hbound Q x p hp n hn)
  calc
    _ ≤ (A*((q:ℝ)-(p:ℝ))^(-r))*S := hh
    _ = (A*S)*((q:ℝ)-(p:ℝ))^(-r) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hδ.le _)

 

theorem almost_linear_susceptibility_of_moments [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (q : unitInterval)
    (hfin : ∀ y, ∀ᵐ ω ∂law q, (cluster G ω y).Finite)
    (hmom : ∀ α : ℝ, 0 < α → α < 1/2 → ∃ C : ℝ, 0 < C ∧ ∀ y,
      Integrable (fun ω => ((cluster G ω y).ncard:ℝ)^α) (law q) ∧
      (∫ ω, ((cluster G ω y).ncard:ℝ)^α ∂law q) ≤ C)
    (η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : unitInterval), p < q → ∀ x,
      Summable (twoPoint G p x) ∧ susceptibility G p x ≤ D*((q:ℝ)-(p:ℝ))^(-1-η) := by
  let α : ℝ := 1/(2+η/2)
  have hden : 0 < 2+η/2 := by linarith
  have hα : 0 < α := one_div_pos.mpr hden
  have hαhalf : α < 1/2 := by
    apply (div_lt_div_iff₀ hden (by norm_num : (0:ℝ) < 2)).mpr
    linarith
  have hs : 1 < α*(1+(1+η)) := by
    dsimp [α]
    rw [one_div,mul_comm,←div_eq_mul_inv]
    apply (one_lt_div hden).mpr
    linarith
  obtain ⟨C,hC,hm⟩ := hmom α hα hαhalf
  obtain ⟨D,hD,hbound⟩ := susceptibility_power_of_uniform_moment G hloc q α C (1+η) hα
    (by linarith) hC (by linarith) hs hfin (fun y => (hm y).1) (fun y => (hm y).2)
  refine ⟨D,hD,?_⟩
  intro p hp x
  simpa only [neg_add_rev,sub_eq_add_neg,add_comm] using hbound p hp x

end SusceptibilityPowerFromMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section SourceAlmostLinear
attribute [local instance] Classical.propDecidable Classical.decEq

theorem cluster_finite_ae_covariant [Countable E] (G : BondGraph V E) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V)
    (hx : ∀ᵐ ω ∂law p, (cluster G ω x).Finite) :
    ∀ᵐ ω ∂law p, (cluster G ω (a x)).Finite := by
  have hh : ∀ᵐ ω ∂law p, (cluster G (b ⁻¹' ω) x).Finite := by
    apply ae_of_ae_map (μ := law p) (p := fun ω : Set E => (cluster G ω x).Finite)
      (measurable_set_preimage b).aemeasurable
    rwa [law_map_preimage_equiv]
  filter_upwards [hh] with ω hω
  rw [←cluster_aut G hab ω x]
  exact hω.image a

 

theorem almost_linear_susceptibility
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (η : ℝ) (hη : 0 < η) :
    ∃ D : ℝ, 0 < D ∧ ∀ (p : unitInterval), p < pc G → ∀ x,
      susceptibility G p x ≤ D*((pc G:ℝ)-(p:ℝ))^(-1-η) := by
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  have hfinite : ∀ x, ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
    intro x
    obtain ⟨i,a,b,hab,rfl⟩ := hcover x
    exact cluster_finite_ae_covariant G (pc G) hab (root i) (hfin i)
  have hmom (α : ℝ) (hα : 0 < α) (hα1 : α < 1/2) :=
    uniform_cluster_power_of_root G hloc (pc G) root hcover α
      (critical_root_power_integrable G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α hα hα1)
  obtain ⟨D,hD,hb⟩ := almost_linear_susceptibility_of_moments G hloc (pc G) hfinite hmom η hη
  exact ⟨D,hD,fun p hp x => (hb p hp x).2⟩

end SourceAlmostLinear
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section QueryTranscriptLaw
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EdgeQueryTree

@[reducible] def forget : EdgeQueryTree E → ProbeTree
  | .done b => .done b
  | .query _ t₀ t₁ => .edge t₀.forget t₁.forget

noncomputable def leaf (ω : Finset E) : (t : EdgeQueryTree E) → t.forget.Leaf
  | .done _ => ()
  | .query e t₀ t₁ => if e ∈ ω then Sum.inr (t₁.leaf ω) else Sum.inl (t₀.leaf ω)

theorem leaf_congr (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    {ω η : Finset E} (h : ∀ e ∈ Q, e ∈ ω ↔ e ∈ η) : t.leaf ω = t.leaf η := by
  induction t generalizing Q with
  | done => rfl
  | query e t₀ t₁ ih₀ ih₁ =>
    simp only [leaf,h e ht.1]
    split
    · rw [ih₁ ht.2.2 (fun a ha => h a (Finset.mem_of_mem_erase ha))]
    · rw [ih₀ ht.2.1 (fun a ha => h a (Finset.mem_of_mem_erase ha))]

theorem leaf_insert (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    {e : E} (he : e ∉ Q) (ω : Finset E) : t.leaf (insert e ω) = t.leaf ω := by
  apply leaf_congr t ht
  intro a ha
  simp [show a ≠ e from fun h => he (h ▸ ha)]

 
theorem leaf_expectation (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : ℝ) (f : t.forget.Leaf → ℝ) :
    bernoulliPolynomial Q (fun ω => f (t.leaf ω)) p =
      ∑ l, ProbeTree.weight p 0 t.forget l*f l := by
  induction t generalizing Q with
  | done b =>
    change bernoulliPolynomial Q (fun _ => f ()) p = ∑ l : Unit, 1*f l
    simp [bernoulliPolynomial_const,Finset.sum_singleton]
  | query e t₀ t₁ ih₀ ih₁ =>
    obtain ⟨he,h₀,h₁⟩ := ht
    conv_lhs => rw [←Finset.insert_erase he]
    rw [bernoulliPolynomial_insert _ e (Finset.notMem_erase e Q)]
    have hc : bernoulliPolynomial (Q.erase e) (fun ω => f ((query e t₀ t₁).leaf ω)) p =
        bernoulliPolynomial (Q.erase e) (fun ω => f (Sum.inl (t₀.leaf ω))) p := by
      apply bernoulliPolynomial_congr
      intro ω hω
      simp only [leaf,show e ∉ ω from fun h => Finset.notMem_erase e Q (hω h),ite_false]
    have ho : bernoulliPolynomial (Q.erase e) (fun ω => f ((query e t₀ t₁).leaf (insert e ω))) p =
        bernoulliPolynomial (Q.erase e) (fun ω => f (Sum.inr (t₁.leaf ω))) p := by
      apply bernoulliPolynomial_congr
      intro ω _
      simp only [leaf,Finset.mem_insert_self,ite_true,
        leaf_insert t₁ h₁ (Finset.notMem_erase e Q)]
    rw [hc,ho,ih₀ h₀ (fun l => f (Sum.inl l)),ih₁ h₁ (fun l => f (Sum.inr l))]
    change _ = ∑ l : t₀.forget.Leaf ⊕ t₁.forget.Leaf, _
    simp only [Fintype.sum_sum_type,ProbeTree.weight,Finset.mul_sum,mul_assoc]

noncomputable def score (p : ℝ) (t : EdgeQueryTree E) (ω : Finset E) : ℝ :=
  ProbeTree.score p t.forget (t.leaf ω)

noncomputable def queryCount (t : EdgeQueryTree E) (ω : Finset E) : ℕ :=
  ProbeTree.queries t.forget (t.leaf ω)

 
theorem score_mgf (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (lam : ℝ) :
    bernoulliPolynomial Q (fun ω => Real.exp (lam*t.score p ω-lam^2*(t.queryCount ω:ℝ)/8)) p ≤ 1 := by
  change bernoulliPolynomial Q (fun ω => Real.exp (lam*ProbeTree.score p t.forget (t.leaf ω)-
    lam^2*(ProbeTree.queries t.forget (t.leaf ω):ℝ)/8)) p ≤ 1
  rw [leaf_expectation t ht p (fun l => Real.exp (lam*ProbeTree.score p t.forget l-
    lam^2*(ProbeTree.queries t.forget l:ℝ)/8))]
  exact ProbeTree.score_mgf p 0 lam t.forget

end EdgeQueryTree
end QueryTranscriptLaw
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section CappedQueryConcentration
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EdgeQueryTree

 

theorem capped_score_mgf (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (lam : ℝ) (N : ℕ) (hN : ∀ ω ⊆ Q, t.queryCount ω ≤ N) :
    bernoulliPolynomial Q (fun ω => Real.exp (lam*t.score p ω)) p ≤ Real.exp (lam^2*(N:ℝ)/8) := by
  calc
    _ ≤ bernoulliPolynomial Q (fun ω => Real.exp (lam^2*(N:ℝ)/8)*
        Real.exp (lam*t.score p ω-lam^2*(t.queryCount ω:ℝ)/8)) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω hω
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hn : (t.queryCount ω:ℝ) ≤ (N:ℝ) := Nat.cast_le.mpr (hN ω hω)
      nlinarith [sq_nonneg lam]
    _ = Real.exp (lam^2*(N:ℝ)/8)*bernoulliPolynomial Q
        (fun ω => Real.exp (lam*t.score p ω-lam^2*(t.queryCount ω:ℝ)/8)) p :=
      bernoulliPolynomial_const_mul _ _ _ _
    _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left (t.score_mgf ht p lam) (Real.exp_pos _).le

theorem capped_score_chernoff (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (lam a : ℝ) (hlam : 0 ≤ lam) (N : ℕ)
    (hN : ∀ ω ⊆ Q, t.queryCount ω ≤ N) :
    bernoulliPolynomial Q (fun ω => if a ≤ t.score p ω then 1 else 0) p ≤
      Real.exp (-lam*a+lam^2*(N:ℝ)/8) := by
  calc
    _ ≤ bernoulliPolynomial Q (fun ω => Real.exp (-lam*a)*Real.exp (lam*t.score p ω)) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω _
      split_ifs with h
      · rw [←Real.exp_add]
        exact Real.one_le_exp (by nlinarith)
      · positivity
    _ = Real.exp (-lam*a)*bernoulliPolynomial Q (fun ω => Real.exp (lam*t.score p ω)) p :=
      bernoulliPolynomial_const_mul _ _ _ _
    _ ≤ Real.exp (-lam*a)*Real.exp (lam^2*(N:ℝ)/8) :=
      mul_le_mul_of_nonneg_left (t.capped_score_mgf ht p lam N hN) (Real.exp_pos _).le
    _ = _ := (Real.exp_add _ _).symm

theorem capped_neg_score_chernoff (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (lam a : ℝ) (hlam : 0 ≤ lam) (N : ℕ)
    (hN : ∀ ω ⊆ Q, t.queryCount ω ≤ N) :
    bernoulliPolynomial Q (fun ω => if a ≤ -t.score p ω then 1 else 0) p ≤
      Real.exp (-lam*a+lam^2*(N:ℝ)/8) := by
  calc
    _ ≤ bernoulliPolynomial Q (fun ω => Real.exp (-lam*a)*Real.exp ((-lam)*t.score p ω)) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω _
      split_ifs with h
      · rw [←Real.exp_add]
        exact Real.one_le_exp (by nlinarith)
      · positivity
    _ = Real.exp (-lam*a)*bernoulliPolynomial Q (fun ω => Real.exp ((-lam)*t.score p ω)) p :=
      bernoulliPolynomial_const_mul _ _ _ _
    _ ≤ Real.exp (-lam*a)*Real.exp ((-lam)^2*(N:ℝ)/8) :=
      mul_le_mul_of_nonneg_left (t.capped_score_mgf ht p (-lam) N hN) (Real.exp_pos _).le
    _ = _ := by rw [←Real.exp_add]; congr 1; ring

 

theorem capped_score_tail (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (p : unitInterval) (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN0 : 0 < N)
    (hN : ∀ ω ⊆ Q, t.queryCount ω ≤ N) :
    bernoulliPolynomial Q (fun ω => if a ≤ |t.score p ω| then 1 else 0) p ≤
      2*Real.exp (-2*a^2/(N:ℝ)) := by
  let lam : ℝ := 4*a/(N:ℝ)
  have hNr : 0 < (N:ℝ) := Nat.cast_pos.mpr hN0
  have hlam : 0 ≤ lam := div_nonneg (by positivity) hNr.le
  have he : -lam*a+lam^2*(N:ℝ)/8 = -2*a^2/(N:ℝ) := by
    dsimp [lam]
    field_simp
    ring
  calc
    _ ≤ bernoulliPolynomial Q (fun ω => (if a ≤ t.score p ω then 1 else 0)+
        (if a ≤ -t.score p ω then 1 else 0)) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω _
      by_cases h : a ≤ |t.score p ω|
      · rcases le_abs.mp h with h₁ | h₂
        · simp only [ite_eq_left h,ite_eq_left h₁]; split_ifs <;> norm_num
        · simp only [ite_eq_left h,ite_eq_left h₂]; split_ifs <;> norm_num
      · simp only [ite_eq_right h]; split_ifs <;> norm_num
    _ = bernoulliPolynomial Q (fun ω => if a ≤ t.score p ω then 1 else 0) p+
        bernoulliPolynomial Q (fun ω => if a ≤ -t.score p ω then 1 else 0) p :=
      bernoulliPolynomial_add _ _ _ _
    _ ≤ Real.exp (-lam*a+lam^2*(N:ℝ)/8)+Real.exp (-lam*a+lam^2*(N:ℝ)/8) :=
      add_le_add (t.capped_score_chernoff ht p lam a hlam N hN)
        (t.capped_neg_score_chernoff ht p lam a hlam N hN)
    _ = _ := by rw [he]; ring

end EdgeQueryTree
end CappedQueryConcentration
end Percolation

 
namespace Percolation
universe v
variable {E : Type v}
section QueryScoreSets
attribute [local instance] Classical.propDecidable Classical.decEq
namespace EdgeQueryTree

noncomputable def readSet (t : EdgeQueryTree E) (Q ω : Finset E) : Finset E :=
  Q.filter (fun e => t.reads ω e)

@[simp] theorem mem_readSet (t : EdgeQueryTree E) (Q ω : Finset E) (e : E) :
    e ∈ t.readSet Q ω ↔ e ∈ Q ∧ t.reads ω e := Finset.mem_filter

theorem readSet_query (e : E) (t₀ t₁ : EdgeQueryTree E) {Q : Finset E}
    (ht : (query e t₀ t₁).Valid Q) (ω : Finset E) :
    (query e t₀ t₁).readSet Q ω = insert e
      (if e ∈ ω then t₁.readSet (Q.erase e) ω else t₀.readSet (Q.erase e) ω) := by
  ext i
  by_cases hie : i = e
  · subst i
    simp only [mem_readSet,reads,true_or,and_true,Finset.mem_insert_self,iff_true]
    exact ht.1
  · by_cases heω : e ∈ ω <;> simp [mem_readSet,reads,hie,heω]

theorem score_query (e : E) (t₀ t₁ : EdgeQueryTree E) (ω : Finset E) (p : ℝ) :
    (query e t₀ t₁).score p ω =
      (if e ∈ ω then t₁.score p ω else t₀.score p ω)+(if e ∈ ω then 1 else 0)-p := by
  by_cases h : e ∈ ω
  · simp only [score,leaf,ite_eq_left h,ProbeTree.score]; ring
  · simp only [score,leaf,ite_eq_right h,ProbeTree.score]; ring

theorem queryCount_query (e : E) (t₀ t₁ : EdgeQueryTree E) (ω : Finset E) :
    (query e t₀ t₁).queryCount ω =
      (if e ∈ ω then t₁.queryCount ω else t₀.queryCount ω)+1 := by
  by_cases h : e ∈ ω <;> simp [queryCount,leaf,h,ProbeTree.queries]

theorem queryCount_eq_card (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (ω : Finset E) : t.queryCount ω = (t.readSet Q ω).card := by
  induction t generalizing Q with
  | done b =>
    have hs : (done b : EdgeQueryTree E).readSet Q ω = ∅ := by
      ext e
      simp only [mem_readSet,reads,and_false,Finset.notMem_empty]
    rw [hs]
    rfl
  | query e t₀ t₁ ih₀ ih₁ =>
    rw [queryCount_query,readSet_query _ _ _ ht]
    have h₀ : e ∉ t₀.readSet (Q.erase e) ω := by simp [readSet]
    have h₁ : e ∉ t₁.readSet (Q.erase e) ω := by simp [readSet]
    by_cases heω : e ∈ ω
    · simp only [ite_eq_left heω,Finset.card_insert_of_notMem h₁,ih₁ ht.2.2]
    · simp only [ite_eq_right heω,Finset.card_insert_of_notMem h₀,ih₀ ht.2.1]

 
theorem score_eq_sum (t : EdgeQueryTree E) {Q : Finset E} (ht : t.Valid Q)
    (ω : Finset E) (p : ℝ) :
    t.score p ω = ∑ e ∈ t.readSet Q ω, ((if e ∈ ω then 1 else 0)-p) := by
  induction t generalizing Q with
  | done b =>
    have hs : (done b : EdgeQueryTree E).readSet Q ω = ∅ := by
      ext e
      simp only [mem_readSet,reads,and_false,Finset.notMem_empty]
    rw [hs,Finset.sum_empty]
    rfl
  | query e t₀ t₁ ih₀ ih₁ =>
    rw [score_query,readSet_query _ _ _ ht]
    have h₀ : e ∉ t₀.readSet (Q.erase e) ω := by simp [readSet]
    have h₁ : e ∉ t₁.readSet (Q.erase e) ω := by simp [readSet]
    by_cases heω : e ∈ ω
    · simp only [ite_eq_left heω,Finset.sum_insert h₁,ih₁ ht.2.2]; ring
    · simp only [ite_eq_right heω,Finset.sum_insert h₀,ih₀ ht.2.1]; ring

end EdgeQueryTree
end QueryScoreSets
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IncidenceExploration
attribute [local instance] Classical.propDecidable Classical.decEq

 

def IncidencePending (G : BondGraph V E) (Q : Finset E) (R : Finset V) : Prop :=
  ∃ t : E × V × V, t.1 ∈ Q ∧ t.2.1 ∈ R ∧ G t.1 = s(t.2.1,t.2.2)

noncomputable def incidencePick (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (h : IncidencePending G Q R) : E × V × V := Classical.choose h

theorem incidencePick_spec (G : BondGraph V E) (Q : Finset E) (R : Finset V)
    (h : IncidencePending G Q R) :
    (incidencePick G Q R h).1 ∈ Q ∧ (incidencePick G Q R h).2.1 ∈ R ∧
      G (incidencePick G Q R h).1 = s((incidencePick G Q R h).2.1,(incidencePick G Q R h).2.2) :=
  Classical.choose_spec h

noncomputable def incidenceSearch (G : BondGraph V E) :
    ℕ → Finset E → Finset V → EdgeQueryTree E
  | 0, _, _ => .done false
  | n+1, Q, R =>
    if hc : IncidencePending G Q R then
      let t := incidencePick G Q R hc
      .query t.1 (incidenceSearch G n (Q.erase t.1) R)
        (incidenceSearch G n (Q.erase t.1) (insert t.2.2 R))
    else .done false

theorem incidenceSearch_valid (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R : Finset V) :
    (incidenceSearch G n Q R).Valid Q := by
  induction n generalizing Q R with
  | zero => trivial
  | succ n ih =>
    simp only [incidenceSearch]
    split_ifs with hc
    · exact ⟨(incidencePick_spec G Q R hc).1,ih _ _,ih _ _⟩
    · trivial

theorem incidenceSearch_cap (G : BondGraph V E) (n : ℕ) (Q : Finset E) (R : Finset V)
    (ω : Finset E) : (incidenceSearch G n Q R).queryCount ω ≤ n := by
  induction n generalizing Q R with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [incidenceSearch]
    split_ifs
    · rw [EdgeQueryTree.queryCount_query]
      split <;> exact Nat.add_le_add_right (ih _ _) 1
    · exact Nat.zero_le _

 

structure IncidenceInvariant (G : BondGraph V E) (Q ω : Finset E) (R C : Finset V) : Prop where
  discovered : R ⊆ C
  closed : ∀ a ∈ C, ∀ e ∈ ω, ∀ b, G e = s(a,b) → b ∈ C
  reachable : ∀ y ∈ C, ∃ r ∈ R, Conn G ((ω ∩ Q : Finset E):Set E) r y

theorem incidentBonds_erase (G : BondGraph V E) (Q : Finset E) (C : Finset V) (e : E) :
    incidentBonds G (Q.erase e) C = (incidentBonds G Q C).erase e := by
  ext f
  simp only [mem_incidentBonds,Finset.mem_erase]
  tauto

theorem incidencePending_of_mem (G : BondGraph V E) {Q : Finset E} {R : Finset V}
    {e : E} (h : e ∈ incidentBonds G Q R) : IncidencePending G Q R := by
  obtain ⟨he,a,ha,hae⟩ := (mem_incidentBonds G Q R e).mp h
  obtain ⟨b,hab⟩ := Sym2.mem_iff_exists.mp hae
  exact ⟨(e,a,b),he,ha,hab⟩

end IncidenceExploration
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IncidenceInvariantSteps
attribute [local instance] Classical.propDecidable Classical.decEq

namespace IncidenceInvariant

theorem closed_step {G : BondGraph V E} {Q ω : Finset E} {R C : Finset V}
    (h : IncidenceInvariant G Q ω R C) (e : E) (he : e ∉ ω) :
    IncidenceInvariant G (Q.erase e) ω R C := by
  refine ⟨h.discovered,h.closed,?_⟩
  have heq : ω ∩ Q.erase e = ω ∩ Q := by ext f; simp only [Finset.mem_inter,Finset.mem_erase]; grind
  simpa only [heq] using h.reachable

theorem open_step {G : BondGraph V E} {Q ω : Finset E} {R C : Finset V}
    (h : IncidenceInvariant G Q ω R C) {e : E} (heQ : e ∈ Q) (heω : e ∈ ω)
    {a b : V} (ha : a ∈ R) (hab : G e = s(a,b)) :
    IncidenceInvariant G (Q.erase e) ω (insert b R) C := by
  have hb : b ∈ C := h.closed a (h.discovered ha) e heω b hab
  refine ⟨Finset.insert_subset hb h.discovered,h.closed,?_⟩
  have heq : ((ω ∩ Q : Finset E):Set E) = insert e ((ω ∩ Q.erase e : Finset E):Set E) := by
    ext f
    simp only [Finset.mem_coe,Finset.mem_inter,Finset.mem_erase,Set.mem_insert_iff]
    grind
  intro y hy
  obtain ⟨r,hr,hry⟩ := h.reachable y hy
  rw [heq] at hry
  rcases (conn_insert_iff G _ e a b r y hab).mp hry with h₀ | h₁ | h₁
  · exact ⟨r,Finset.mem_insert_of_mem hr,h₀⟩
  · exact ⟨b,Finset.mem_insert_self _ _,h₁.2⟩
  · exact ⟨a,Finset.mem_insert_of_mem ha,h₁.2⟩

theorem no_pending {G : BondGraph V E} {Q ω : Finset E} {R C : Finset V}
    (h : IncidenceInvariant G Q ω R C) (hp : ¬ IncidencePending G Q R) :
    incidentBonds G Q C = ∅ := by
  have hCR : C ⊆ R := by
    intro y hy
    obtain ⟨r,hr,hry⟩ := h.reachable y hy
    clear hy
    induction hry with
    | refl => exact hr
    | @tail a b _ hab ih =>
      obtain ⟨e,he,heab⟩ := hab
      exact (hp ⟨(e,a,b),(Finset.mem_inter.mp he).2,ih,heab⟩).elim
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  apply hp
  apply incidencePending_of_mem G (e := e)
  obtain ⟨heQ,a,ha,hae⟩ := (mem_incidentBonds G Q C e).mp he
  exact (mem_incidentBonds G Q R e).mpr ⟨heQ,a,hCR ha,hae⟩

end IncidenceInvariant
end IncidenceInvariantSteps
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section IncidenceCompletion
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem incidenceSearch_readSet (G : BondGraph V E) (n : ℕ) (Q ω : Finset E) (R C : Finset V)
    (hinv : IncidenceInvariant G Q ω R C) (hn : (incidentBonds G Q C).card ≤ n) :
    (incidenceSearch G n Q R).readSet Q ω = incidentBonds G Q C := by
  induction n generalizing Q R with
  | zero =>
    have he : incidentBonds G Q C = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
    simp [incidenceSearch,EdgeQueryTree.readSet,EdgeQueryTree.reads,he]
  | succ n ih =>
    simp only [incidenceSearch]
    split_ifs with hc
    · obtain ⟨he,ha,hab⟩ := incidencePick_spec G Q R hc
      have heC : (incidencePick G Q R hc).1 ∈ incidentBonds G Q C :=
        (mem_incidentBonds G Q C _).mpr ⟨he,_,hinv.discovered ha,by rw [hab]; simp⟩
      have hn' : (incidentBonds G (Q.erase (incidencePick G Q R hc).1) C).card ≤ n := by
        rw [incidentBonds_erase,Finset.card_erase_of_mem heC]
        have hh := Finset.card_pos.mpr ⟨_,heC⟩
        omega
      rw [EdgeQueryTree.readSet_query _ _ _ ⟨he,incidenceSearch_valid ..,incidenceSearch_valid ..⟩]
      by_cases heω : (incidencePick G Q R hc).1 ∈ ω
      · rw [ite_eq_left heω,ih _ _ (hinv.open_step he heω ha hab) hn',incidentBonds_erase,
          Finset.insert_erase heC]
      · rw [ite_eq_right heω,ih _ _ (hinv.closed_step _ heω) hn',incidentBonds_erase,
          Finset.insert_erase heC]
    · rw [hinv.no_pending hc]
      ext e
      simp only [EdgeQueryTree.mem_readSet,EdgeQueryTree.reads,
        Finset.notMem_empty,and_false]

theorem incidenceInvariant_root (G : BondGraph V E) (Q ω : Finset E) (hω : ω ⊆ Q) (x : V) :
    IncidenceInvariant G Q ω {x} (finiteRootComponent G ω x) := by
  have hmem (y : V) : y ∈ finiteRootComponent G ω x ↔ Conn G (ω:Set E) x y := by
    change y ∈ ((finiteRootComponent G ω x:Set V)) ↔ _
    rw [coe_finiteRootComponent]
    rfl
  refine ⟨?_,?_,?_⟩
  · intro y hy
    rw [Finset.mem_singleton] at hy
    subst y
    exact (hmem x).mpr (conn_refl G _ _)
  · intro a ha e he b hab
    exact (hmem b).mpr ((hmem a).mp ha |>.tail ⟨e,he,hab⟩)
  · intro y hy
    refine ⟨x,Finset.mem_singleton_self _,?_⟩
    rw [Finset.inter_eq_left.mpr hω]
    exact (hmem y).mp hy

 

theorem incidenceSearch_completed_score (G : BondGraph V E) (n : ℕ) (Q ω : Finset E)
    (hω : ω ⊆ Q) (x : V) (p : ℝ)
    (hn : (incidentBonds G Q (finiteRootComponent G ω x)).card ≤ n) :
    (incidenceSearch G n Q {x}).score p ω =
      ∑ e ∈ incidentBonds G Q (finiteRootComponent G ω x), ((if e ∈ ω then 1 else 0)-p) := by
  rw [EdgeQueryTree.score_eq_sum _ (incidenceSearch_valid ..),
    incidenceSearch_readSet G n Q ω {x} _ (incidenceInvariant_root G Q ω hω x) hn]

theorem incidenceSearch_score_tail (G : BondGraph V E) (n : ℕ) (hn : 0 < n)
    (Q : Finset E) (R : Finset V) (p : unitInterval) (a : ℝ) (ha : 0 ≤ a) :
    bernoulliPolynomial Q (fun ω => if a ≤ |(incidenceSearch G n Q R).score p ω| then 1 else 0) p ≤
      2*Real.exp (-2*a^2/(n:ℝ)) :=
  EdgeQueryTree.capped_score_tail _ (incidenceSearch_valid ..) p a ha n hn
    (fun ω _ => incidenceSearch_cap G n Q R ω)

end IncidenceCompletion
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExteriorExplorationLaw
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem cluster_exterior_expectation_bound (G : BondGraph V E) (Q : Finset E)
    (x : V) (p : unitInterval) (f : Finset V → Finset E → ℝ) (K : ℝ)
    (hf : ∀ W : Finset V, bernoulliPolynomial (exteriorBonds G Q (W:Set V)) (f W) p ≤ K) :
    bernoulliPolynomial Q (fun ω => f (finiteRootComponent G ω x)
      (exteriorBonds G ω (finiteRootComponent G ω x:Set V))) p ≤ K := by
  let F := insert x (searchVertices G Q)
  have hpoint (ω : Finset E) (hω : ω ⊆ Q) :
      f (finiteRootComponent G ω x) (exteriorBonds G ω (finiteRootComponent G ω x:Set V)) =
      ∑ W ∈ F.powerset, (if cluster G ω x = (W:Set V) then (1:ℝ) else 0)*
        f W (exteriorBonds G ω (W:Set V)) := by
    rw [←sum_component_partition G Q F x ω hω (by rfl)
      (fun W => f W (exteriorBonds G ω (W:Set V)))]
    apply Finset.sum_congr rfl
    intro W _
    split_ifs <;> simp
  rw [bernoulliPolynomial_congr Q hpoint,bernoulliPolynomial_sum]
  calc
    _ = ∑ W ∈ F.powerset,
        bernoulliPolynomial Q (fun ω => if cluster G ω x = (W:Set V) then (1:ℝ) else 0) p*
        bernoulliPolynomial (exteriorBonds G Q (W:Set V)) (f W) p := by
      apply Finset.sum_congr rfl
      intro W _
      rw [cluster_cell_exterior_factor,←cluster_cell_incident_probability G Q x (W:Set V) p]
    _ ≤ ∑ W ∈ F.powerset,
        bernoulliPolynomial Q (fun ω => if cluster G ω x = (W:Set V) then (1:ℝ) else 0) p*K := by
      apply Finset.sum_le_sum
      intro W _
      apply mul_le_mul_of_nonneg_left (hf W)
      exact bernoulliPolynomial_nonneg _ _ p p.2 (fun _ _ => by split_ifs <;> norm_num)
    _ = K := by
      rw [←Finset.sum_mul,←bernoulliPolynomial_sum]
      have hh : bernoulliPolynomial Q (fun ω => ∑ W ∈ F.powerset,
          if cluster G ω x = (W:Set V) then (1:ℝ) else 0) p = 1 := by
        trans bernoulliPolynomial Q (fun _ => (1:ℝ)) p
        · apply bernoulliPolynomial_congr
          intro ω hω
          exact sum_component_partition G Q F x ω hω (by rfl) (fun _ => 1)
        · exact bernoulliPolynomial_const Q 1 p
      rw [hh,one_mul]

noncomputable def exteriorSearchScore (G : BondGraph V E) (n : ℕ) (Q : Finset E)
    (x v : V) (p : ℝ) (ω : Finset E) : ℝ :=
  let W := finiteRootComponent G ω x
  if v ∈ W then 0 else
    (incidenceSearch G n (exteriorBonds G Q (W:Set V)) {v}).score p (exteriorBonds G ω (W:Set V))

theorem exteriorSearchScore_tail (G : BondGraph V E) (n : ℕ) (hn : 0 < n)
    (Q : Finset E) (x v : V) (p : unitInterval) (a : ℝ) (ha : 0 < a) :
    bernoulliPolynomial Q (fun ω => if a ≤ |exteriorSearchScore G n Q x v p ω| then 1 else 0) p ≤
      2*Real.exp (-2*a^2/(n:ℝ)) := by
  apply cluster_exterior_expectation_bound G Q x p
    (fun W η => if a ≤ |if v ∈ W then 0 else
      (incidenceSearch G n (exteriorBonds G Q (W:Set V)) {v}).score p η| then 1 else 0)
  intro W
  by_cases hv : v ∈ W
  · simp only [ite_eq_left hv,abs_zero,ite_eq_right (not_le.mpr ha),bernoulliPolynomial_zero]
    positivity
  · simp only [ite_eq_right hv]
    exact incidenceSearch_score_tail G n hn _ _ p a ha.le

end ExteriorExplorationLaw
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ClosedClusterContacts
attribute [local instance] Classical.propDecidable Classical.decEq

 

noncomputable def contactBonds (G : BondGraph V E) (Q : Finset E) (A B : Finset V) : Finset E :=
  Q.filter (fun e => ∃ a ∈ A, ∃ b ∈ B, G e = s(a,b))

theorem incident_exterior_subset (G : BondGraph V E) (Q : Finset E) (A B : Finset V) :
    incidentBonds G (exteriorBonds G Q (A:Set V)) B ⊆ incidentBonds G Q B := by
  intro e he
  obtain ⟨he,b,hb,hbe⟩ := (mem_incidentBonds G _ B e).mp he
  exact (mem_incidentBonds G Q B e).mpr ⟨(Finset.mem_filter.mp he).1,b,hb,hbe⟩

 

theorem incident_exterior_difference (G : BondGraph V E) (Q : Finset E) (A B : Finset V)
    (hAB : Disjoint A B) :
    incidentBonds G Q B \ incidentBonds G (exteriorBonds G Q (A:Set V)) B =
      contactBonds G Q A B := by
  ext e
  simp only [Finset.mem_sdiff,mem_incidentBonds,contactBonds,Finset.mem_filter]
  constructor
  · rintro ⟨⟨he,b,hb,hbe⟩,hn⟩
    obtain ⟨a,hea⟩ := Sym2.mem_iff_exists.mp hbe
    have hbA : b ∉ A := fun hh => Finset.disjoint_left.mp hAB hh hb
    have ha : a ∈ A := by
      by_contra ha
      apply hn
      refine ⟨Finset.mem_filter.mpr ⟨he,?_⟩,b,hb,hbe⟩
      exact (mem_internalEdges_of_ends G (A:Set V)ᶜ e b a hea).mpr ⟨hbA,ha⟩
    exact ⟨he,a,ha,b,hb,hea.trans (Sym2.eq_swap ..)⟩
  · rintro ⟨he,a,ha,b,hb,hab⟩
    refine ⟨⟨he,b,hb,by rw [hab]; simp⟩,?_⟩
    rintro ⟨he',_⟩
    exact (Finset.mem_filter.mp he').2 a (by rw [hab]; simp) ha

theorem finiteRootComponent_disjoint (G : BondGraph V E) (ω : Finset E) (x v : V)
    (h : ¬Conn G (ω:Set E) x v) :
    Disjoint (finiteRootComponent G ω x) (finiteRootComponent G ω v) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have h₁ : Conn G (ω:Set E) x z := by
    change z ∈ (finiteRootComponent G ω x:Set V) at hz
    rwa [coe_finiteRootComponent] at hz
  have h₂ : Conn G (ω:Set E) v z := by
    change z ∈ (finiteRootComponent G ω v:Set V) at hz'
    rwa [coe_finiteRootComponent] at hz'
  exact h (h₁.trans (conn_symm G _ h₂))

theorem distinct_contact_closed (G : BondGraph V E) (Q ω : Finset E) (x v : V)
    (h : ¬Conn G (ω:Set E) x v) {e : E}
    (he : e ∈ contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)) : e ∉ ω := by
  obtain ⟨_,a,ha,b,hb,hab⟩ := Finset.mem_filter.mp he
  have h₁ : Conn G (ω:Set E) x a := by
    change a ∈ (finiteRootComponent G ω x:Set V) at ha
    rwa [coe_finiteRootComponent] at ha
  have h₂ : Conn G (ω:Set E) v b := by
    change b ∈ (finiteRootComponent G ω v:Set V) at hb
    rwa [coe_finiteRootComponent] at hb
  intro heω
  exact h ((h₁.tail ⟨e,heω,hab⟩).trans (conn_symm G _ h₂))

theorem finiteRootComponent_exterior (G : BondGraph V E) (ω : Finset E) (x v : V)
    (h : ¬Conn G (ω:Set E) x v) :
    finiteRootComponent G (exteriorBonds G ω (finiteRootComponent G ω x:Set V)) v =
      finiteRootComponent G ω v := by
  apply Finset.coe_injective
  simp only [coe_finiteRootComponent,coe_exteriorBonds]
  ext z
  exact conn_exterior_of_cluster_eq G ω x v z (cluster G ω x) rfl h

end ClosedClusterContacts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ExplorationScoreDifference
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem incidence_exterior_score_difference (G : BondGraph V E) (n : ℕ) (Q ω : Finset E)
    (hω : ω ⊆ Q) (x v : V) (p : ℝ) (h : ¬Conn G (ω:Set E) x v)
    (hn : (incidentBonds G Q (finiteRootComponent G ω v)).card ≤ n) :
    (incidenceSearch G n Q {v}).score p ω - exteriorSearchScore G n Q x v p ω =
      -p*(contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω v)).card := by
  let A := finiteRootComponent G ω x
  let B := finiteRootComponent G ω v
  let R := exteriorBonds G Q (A:Set V)
  let η := exteriorBonds G ω (A:Set V)
  have hv : v ∉ A := by
    intro hv
    apply h
    change v ∈ (A:Set V) at hv
    simpa only [A,coe_finiteRootComponent,cluster,Set.mem_ofPred_eq] using hv
  have hη : η ⊆ R := by
    intro e he
    obtain ⟨he,heA⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨hω he,heA⟩
  have hB : finiteRootComponent G η v = B := finiteRootComponent_exterior G ω x v h
  have hsub : incidentBonds G R B ⊆ incidentBonds G Q B := incident_exterior_subset G Q A B
  have hn' : (incidentBonds G R (finiteRootComponent G η v)).card ≤ n := by
    rw [hB]
    exact (Finset.card_le_card hsub).trans hn
  have hs₁ := incidenceSearch_completed_score G n Q ω hω v p hn
  have hs₂ := incidenceSearch_completed_score G n R η hη v p hn'
  rw [hB] at hs₂
  have hb (e : E) (he : e ∈ incidentBonds G R B) : (e ∈ η ↔ e ∈ ω) := by
    have heR := ((mem_incidentBonds G R B e).mp he).1
    change e ∈ exteriorBonds G ω (A:Set V) ↔ e ∈ ω
    simp only [exteriorBonds,Finset.mem_filter]
    exact and_iff_left (Finset.mem_filter.mp heR).2
  have hs₂' : (incidenceSearch G n R {v}).score p η =
      ∑ e ∈ incidentBonds G R B, ((if e ∈ ω then 1 else 0)-p) := by
    rw [hs₂]
    exact Finset.sum_congr rfl (fun e he => by simp only [hb e he])
  change (incidenceSearch G n Q {v}).score p ω -
    (if v ∈ A then 0 else (incidenceSearch G n R {v}).score p η) = _
  rw [ite_eq_right hv,hs₁,hs₂',←Finset.sum_sdiff hsub,add_sub_cancel_right]
  change (∑ e ∈ incidentBonds G Q B \ incidentBonds G (exteriorBonds G Q (A:Set V)) B,
    ((if e ∈ ω then (1:ℝ) else 0)-p)) = _
  rw [incident_exterior_difference G Q A B (finiteRootComponent_disjoint G ω x v h)]
  have hc (e : E) (he : e ∈ contactBonds G Q A B) : e ∉ ω := distinct_contact_closed G Q ω x v h he
  rw [show (∑ e ∈ contactBonds G Q A B, ((if e ∈ ω then (1:ℝ) else 0)-p)) =
      ∑ _e ∈ contactBonds G Q A B, -p from Finset.sum_congr rfl (fun e he => by rw [ite_eq_right (hc e he)]; ring)]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

end ExplorationScoreDifference
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section ContactConcentration
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contactBonds_comm (G : BondGraph V E) (Q : Finset E) (A B : Finset V) :
    contactBonds G Q A B = contactBonds G Q B A := by
  ext e
  simp only [contactBonds,Finset.mem_filter]
  constructor <;> rintro ⟨he,a,ha,b,hb,hab⟩
  · exact ⟨he,b,hb,a,ha,hab.trans (Sym2.eq_swap ..)⟩
  · exact ⟨he,b,hb,a,ha,hab.trans (Sym2.eq_swap ..)⟩

 

theorem ordered_cluster_contact_tail (G : BondGraph V E) (Q : Finset E)
    (x v : V) (p : unitInterval) (N : ℕ) (hN : 0 < N) (a : ℝ) (ha : 0 < a) :
    bernoulliPolynomial Q (fun ω => if ¬Conn G (ω:Set E) x v ∧
      (incidentBonds G Q (finiteRootComponent G ω v)).card ≤ N ∧
      2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x)
        (finiteRootComponent G ω v)).card then 1 else 0) p ≤
      4*Real.exp (-2*a^2/(N:ℝ)) := by
  calc
    _ ≤ bernoulliPolynomial Q (fun ω =>
        (if a ≤ |(incidenceSearch G N Q {v}).score p ω| then 1 else 0)+
        (if a ≤ |exteriorSearchScore G N Q x v p ω| then 1 else 0)) p := by
      apply bernoulliPolynomial_mono _ _ _ p p.2
      intro ω hω
      by_cases h : ¬Conn G (ω:Set E) x v ∧
          (incidentBonds G Q (finiteRootComponent G ω v)).card ≤ N ∧
          2*a ≤ (p:ℝ)*(contactBonds G Q (finiteRootComponent G ω x)
            (finiteRootComponent G ω v)).card
      · have hd := incidence_exterior_score_difference G N Q ω hω x v p h.1 h.2.1
        have huo : a ≤ |(incidenceSearch G N Q {v}).score p ω| ∨
            a ≤ |exteriorSearchScore G N Q x v p ω| := by
          by_contra hh
          push Not at hh
          have h₁ := (abs_lt.mp hh.1).1
          have h₂ := (abs_lt.mp hh.2).2
          nlinarith [h.2.2]
        simp only [ite_eq_left h]
        rcases huo with huo | huo <;> simp only [ite_eq_left huo] <;> split_ifs <;> norm_num
      · simp only [ite_eq_right h]; split_ifs <;> norm_num
    _ = bernoulliPolynomial Q (fun ω =>
        if a ≤ |(incidenceSearch G N Q {v}).score p ω| then 1 else 0) p+
        bernoulliPolynomial Q (fun ω =>
        if a ≤ |exteriorSearchScore G N Q x v p ω| then 1 else 0) p :=
      bernoulliPolynomial_add _ _ _ _
    _ ≤ 2*Real.exp (-2*a^2/(N:ℝ))+2*Real.exp (-2*a^2/(N:ℝ)) :=
      add_le_add (incidenceSearch_score_tail G N hN Q {v} p a ha.le)
        (exteriorSearchScore_tail G N hN Q x v p a ha)
    _ = _ := by ring

end ContactConcentration
end Percolation

end OAI
