import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal Topology

lemma subadditive_chain_finite {E : Type*} [AddCommGroup E] (p : E→ℝ)
    (hp : ∀ x y,p (x+y) ≤ p x+p y) (u : ℕ→E) (r : ℕ→ℝ)
    (hr : ∀ k,p (u (k+1)-u k) ≤ r k) (n : ℕ) :
    p (u n) ≤ p (u 0)+∑ k∈Finset.range n,r k := by
  induction n with
  | zero => simp
  | succ n hn =>
      have hh := hp (u n) (u (n+1)-u n)
      rw [add_sub_cancel] at hh
      rw [Finset.sum_range_succ]
      linarith only [hh,hn,hr n]

lemma subadditive_chain_limit {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    (p : E→ℝ) (hc : Continuous p) (hp : ∀ x y,p (x+y) ≤ p x+p y)
    (u : ℕ→E) {x : E} (hu : Tendsto u atTop (𝓝 x)) (r : ℕ→ℝ)
    (hr0 : ∀ k,0 ≤ r k) (hrs : Summable r) (hr : ∀ k,p (u (k+1)-u k) ≤ r k) :
    p x ≤ p (u 0)+∑' k,r k := by
  apply le_of_tendsto (hc.tendsto x |>.comp hu)
  exact Eventually.of_forall (fun n=>(subadditive_chain_finite p hp u r hr n).trans
    (add_le_add_right (hrs.sum_le_tsum (Finset.range n) (fun i _=>hr0 i)) _))

lemma arithmetic_half_geometric_hasSum :
    HasSum (fun k : ℕ=>((k:ℝ)+1)*(1/2:ℝ)^k) 4 := by
  have h₁ := hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)
  have h₂ := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ)<1)
  have h : HasSum (fun k : ℕ => ((k:ℝ)+1)*(1/2:ℝ)^k)
      (1/2/(1-1/2)^2+(1-1/2)⁻¹) := by
    convert h₁.add h₂ using 1
    ext k
    ring
  norm_num at h
  exact h

theorem continuous_chaining_probability
    {Ω T E : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [TopologicalSpace T] [AddCommGroup E] [TopologicalSpace E]
    (p : E→ℝ) (hc : Continuous p) (hp : ∀ x y,p (x+y) ≤ p x+p y)
    (F : T→Ω→E) (hF : ∀ ω,Continuous (fun t=>F t ω))
    (S : Set T) (ι : ℕ→Type*) [∀ k,Fintype (ι k)]
    (v : ∀ k,ι k→T) (edges : ∀ k,Finset (ι k×ι (k+1)))
    (hcover : ∀ t∈S,∃ a : ∀ k,ι k,
      (∀ k,(a k,a (k+1))∈edges k) ∧ Tendsto (fun k=>v k (a k)) atTop (𝓝 t))
    (r : ℕ→ℝ) (hr0 : ∀ k,0 ≤ r k) (hrs : Summable r)
    (b : ℝ) (q₀ : ℝ≥0∞) (q : ℕ→ℝ≥0∞)
    (hb : ∀ i,μ {ω | b < p (F (v 0 i) ω)} ≤ q₀)
    (hi : ∀ k, ∀ e∈edges k,μ {ω | r k < p (F (v (k+1) e.2) ω-F (v k e.1) ω)} ≤ q k) :
    μ {ω | ∃ t∈S,b+(∑' k,r k) < p (F t ω)} ≤
      (Fintype.card (ι 0):ℝ≥0∞)*q₀+∑' k,((edges k).card:ℝ≥0∞)*q k := by
  classical
  let B : Set Ω := ⋃ i : ι 0,{ω | b < p (F (v 0 i) ω)}
  let I : ℕ→Set Ω := fun k=>⋃ e∈edges k,{ω | r k < p (F (v (k+1) e.2) ω-F (v k e.1) ω)}
  have hs : {ω | ∃ t∈S,b+(∑' k,r k) < p (F t ω)} ⊆ B ∪ ⋃ k,I k := by
    intro ω hω
    by_contra hh
    have hh' := not_or.mp hh
    obtain ⟨t,ht,htp⟩ := hω
    obtain ⟨a,ha,hat⟩ := hcover t ht
    have hbase : p (F (v 0 (a 0)) ω) ≤ b := by
      by_contra hn
      exact hh'.1 (mem_iUnion.mpr ⟨a 0,not_le.mp hn⟩)
    have hinc : ∀ k,p (F (v (k+1) (a (k+1))) ω-F (v k (a k)) ω) ≤ r k := by
      intro k
      by_contra hn
      apply hh'.2
      exact mem_iUnion.mpr ⟨k,mem_iUnion₂.mpr ⟨(a k,a (k+1)),ha k,not_le.mp hn⟩⟩
    have hl := subadditive_chain_limit p hc hp (fun k=>F (v k (a k)) ω)
      ((hF ω).tendsto t |>.comp hat) r hr0 hrs hinc
    linarith only [hl,hbase,htp]
  apply (measure_mono hs).trans
  apply (measure_union_le _ _).trans
  apply add_le_add
  · exact (measure_iUnion_fintype_le μ _).trans ((Finset.sum_le_sum (fun i _=>hb i)).trans_eq (by simp))
  · apply (measure_iUnion_le I).trans
    apply ENNReal.tsum_le_tsum
    intro k
    apply (measure_biUnion_finset_le (edges k) _).trans
    exact (Finset.sum_le_sum (fun e he=>hi k e he)).trans_eq (by simp)
end SKGap
end
end

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal Topology

lemma exponential_series_bound {c : ℝ} (hc : log 2 ≤ c) :
    (∑' k : ℕ,ENNReal.ofReal (exp (-c*((k:ℝ)+1)))) ≤ ENNReal.ofReal (2*exp (-c)) := by
  have hc0 : 0 < c := lt_of_lt_of_le (log_pos (by norm_num : (1:ℝ)<2)) hc
  have hr : exp (-c) < 1 := by rw [exp_lt_one_iff];linarith
  have hr2 : exp (-c) ≤ 1/2 := by
    rw [← exp_log (by norm_num : (0:ℝ)<(1/2))]
    apply exp_le_exp.mpr
    rw [log_div (by norm_num) (by norm_num),log_one]
    linarith only [hc]
  have he (k : ℕ) : exp (-c*((k:ℝ)+1))=exp (-c)*exp (-c)^k := by
    rw [← exp_nat_mul,← exp_add]
    congr 1;ring
  have hs : HasSum (fun k : ℕ=>exp (-c*((k:ℝ)+1))) (exp (-c)*(1-exp (-c))⁻¹) := by
    simpa only [he] using (hasSum_geometric_of_lt_one (exp_pos (-c)).le hr).mul_left (exp (-c))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _=>(exp_pos _).le) hs.summable,hs.tsum_eq]
  apply ENNReal.ofReal_le_ofReal
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by linarith only [hr] : 0 < 1-exp (-c))).mpr
  nlinarith only [mul_le_mul_of_nonneg_left hr2 (exp_pos (-c)).le]

lemma chaining_entropy_tail_product {n : ℕ} (_hn : 1 ≤ n)
    {A B c : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (hA : B+c ≤ A)
    (k : ℕ) {m q : ℝ≥0∞}
    (hm : m ≤ ENNReal.ofReal (exp (B*((k:ℝ)+1)*(n:ℝ))))
    (hq : q ≤ ENNReal.ofReal (exp (-A*((k:ℝ)+1)^2*(n:ℝ)))) :
    m*q ≤ ENNReal.ofReal (exp (-c*(n:ℝ)*((k:ℝ)+1))) := by
  apply (mul_le_mul' hm hq).trans
  rw [← ENNReal.ofReal_mul (exp_pos _).le,← exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply exp_le_exp.mpr
  have hkn : 1 ≤ (k:ℝ)+1 := by
    have hk : (0:ℝ) ≤ k := by positivity
    linarith only [hk]
  have hnn : 0 ≤ (n:ℝ) := by positivity
  have hA0 : 0 ≤ A := by linarith
  have hs : (k:ℝ)+1 ≤ ((k:ℝ)+1)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hs hA0
  have hh' := mul_le_mul_of_nonneg_right hA (show 0 ≤ (k:ℝ)+1 by positivity)
  have hh'' := mul_le_mul_of_nonneg_right (show c*((k:ℝ)+1) ≤ A*((k:ℝ)+1)^2-B*((k:ℝ)+1) by linarith only [hh,hh']) hnn
  linarith only [hh'']

lemma chaining_entropy_series {n : ℕ} (hn : 1 ≤ n)
    {A B c : ℝ} (hB : 0 ≤ B) (hc : log 2 ≤ c) (hA : B+c ≤ A)
    (m q : ℕ→ℝ≥0∞)
    (hm : ∀ k,m k ≤ ENNReal.ofReal (exp (B*((k:ℝ)+1)*(n:ℝ))))
    (hq : ∀ k,q k ≤ ENNReal.ofReal (exp (-A*((k:ℝ)+1)^2*(n:ℝ)))) :
    (∑' k,m k*q k) ≤ ENNReal.ofReal (2*exp (-c*(n:ℝ))) := by
  have hc0 : 0 < c := lt_of_lt_of_le (log_pos (by norm_num : (1:ℝ)<2)) hc
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  apply (ENNReal.tsum_le_tsum (fun k=>chaining_entropy_tail_product hn hB hc0 hA k (hm k) (hq k))).trans
  have hcn : log 2 ≤ c*(n:ℝ) := hc.trans (by nlinarith only [hn',hc0])
  simpa only [neg_mul] using exponential_series_bound hcn
end SKGap
end
end

end OAI
