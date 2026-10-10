import Mathlib
import OAI.Probability.SKGap.Model

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology

lemma weighted_markov_transfer {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (L p : Ω→ℝ)
    (hL : ∀ x,0 ≤ L x) (hp : ∀ x,0 ≤ p x)
    (hi : Integrable (fun x=>L x*p x) μ) {l v : ℝ} (hl : 0 < l) (hv : 0 < v) :
    μ.real {x | v < p x} ≤ μ.real {x | L x < l}+(∫ x,L x*p x ∂μ)/(l*v) := by
  have hs : {x | v < p x} ⊆ {x | L x < l} ∪ {x | l*v ≤ L x*p x} := by
    intro x hx
    by_cases hh : L x < l
    · exact Or.inl hh
    · exact Or.inr (mul_le_mul (not_lt.mp hh) hx.le hv.le (hL x))
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all μ (fun x=>mul_nonneg (hL x) (hp x))) hi (l*v)
  have hm' : μ.real {x | l*v ≤ L x*p x} ≤ (∫ x,L x*p x ∂μ)/(l*v) := by
    apply (le_div_iff₀ (mul_pos hl hv)).mpr
    rwa [mul_comm]
  exact (measureReal_mono hs (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add_right hm' _))

lemma exponential_size_bias_transfer
    {Ω : ℕ→Type*} [∀ n,MeasurableSpace (Ω n)]
    (μ : ∀ n,Measure (Ω n)) [∀ n,IsProbabilityMeasure (μ n)]
    (L p : ∀ n,Ω n→ℝ)
    (hL : ∀ n x,0 ≤ L n x) (hp : ∀ n x,0 ≤ p n x)
    (hi : ∀ n,Integrable (fun x=>L n x*p n x) (μ n))
    {a C : ℝ} (ha : 0 < a) (_hC : 0 ≤ C)
    (htail : Tendsto (fun n=>(μ n).real {x | L n x < exp (-(a/4)*(n:ℝ))}) atTop (𝓝 0))
    (hann : ∀ᶠ n : ℕ in atTop,(∫ x,L n x*p n x ∂μ n) ≤ C*exp (-a*(n:ℝ))) :
    Tendsto (fun n=>(μ n).real {x | exp (-(a/4)*(n:ℝ)) < p n x}) atTop (𝓝 0) := by
  have hn : ∀ᶠ n : ℕ in atTop,(μ n).real {x | exp (-(a/4)*(n:ℝ)) < p n x} ≤
      (μ n).real {x | L n x < exp (-(a/4)*(n:ℝ))}+C*exp (-(a/2)*(n:ℝ)) := by
    filter_upwards [hann] with n hn
    have hh := weighted_markov_transfer (μ n) (L n) (p n) (hL n) (hp n) (hi n)
      (exp_pos (-(a/4)*(n:ℝ))) (exp_pos (-(a/4)*(n:ℝ)))
    apply hh.trans
    apply add_le_add_right
    apply (div_le_iff₀ (mul_pos (exp_pos _) (exp_pos _))).mpr
    apply hn.trans_eq
    rw [mul_assoc,← exp_add,← exp_add]
    congr 2
    ring
  have he : Tendsto (fun n : ℕ=>C*exp (-(a/2)*(n:ℝ))) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ=>(a/2)*(n:ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : 0 < a/2)
    have hx := tendsto_exp_neg_atTop_nhds_zero.comp hh
    have hce := hx.const_mul C
    simpa only [mul_zero,neg_mul,Function.comp_def] using hce
  have ht := htail.add he
  rw [add_zero] at ht
  exact squeeze_zero' (Eventually.of_forall (fun _=>measureReal_nonneg)) hn ht
end SKGap
end
end

end OAI
