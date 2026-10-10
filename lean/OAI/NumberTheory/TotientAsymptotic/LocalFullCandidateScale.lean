import OAI.NumberTheory.TotientAsymptotic.LocalFullCandidateCount
import OAI.NumberTheory.TotientAsymptotic.FullFiberValueCount
import OAI.NumberTheory.TotientAsymptotic.FordScaleUpper

namespace OAI

/-! Convert a positive fixed-prefix family into the natural counting scale.
These finite-family bridges will be applied after the regular residual
comparison estimate has been proved. -/
noncomputable section
open scoped Topology
open Filter
attribute [local instance] Classical.propDecidable
namespace TotientAsymptotic

/-- The fixed-prefix normalization differs from the natural scale by a positive
constant, and every retained candidate has the exact full-fiber property. -/
theorem full_fiber_scale_of_local_count {c δ : ℝ} (hc : 0<c) (hδ : 0<δ)
    (d : ℕ) (hd : 0<d) (L : ℕ)
    (hcount : ∀ᶠ H : ℕ in atTop,∀ᶠ x : ℝ in atTop,
      (δ/(16*d))*(x/Real.log x*G x (m x-H)) ≤
        ((localFullCandidates x c d L H).card:ℝ)) :
    ∃ a K : ℝ,0<a ∧ 0<K ∧ ∀ᶠ x : ℝ in atTop,
      0<x ∧ ∃ S : Finset ℕ,a*(x/Real.log x)*G x (m x) ≤ (S.card:ℝ) ∧
        ∀ b∈S,0<b ∧ ((d*b.totient:ℕ):ℝ)≤x ∧
          FullFiber d b ∧ (b:ℝ)/b.totient≤K := by
  obtain ⟨K,hK,harith⟩ := local_normal_candidate_arithmetic hc d hd L
  obtain ⟨H,hcount,harith⟩ := (hcount.and harith).exists
  obtain ⟨a,ha,hprefix⟩ := fixed_prefix_volume_lower H
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  refine ⟨δ/(16*d)*a,K,by positivity,hK,?_⟩
  filter_upwards [hcount,harith,hprefix,eventually_gt_atTop (1:ℝ)]
    with x hcount harith hprefix hx
  refine ⟨zero_lt_one.trans hx,localFullCandidates x c d L H,?_,?_⟩
  · have hscale : 0≤x/Real.log x :=
      div_nonneg (zero_lt_one.trans hx).le (Real.log_pos hx).le
    have hh := mul_le_mul_of_nonneg_left hprefix
      (mul_nonneg (by positivity : 0≤δ/(16*d)) hscale)
    apply le_trans _ hcount
    convert hh using 1 <;> ring
  · intro b hb
    obtain ⟨hb,hfull⟩ := Finset.mem_filter.mp hb
    obtain ⟨hpos,hvalue,hratio⟩ := harith b hb
    exact ⟨hpos,hvalue,hfull,hratio⟩

/-- Ford's upper counting bound converts the constructed family into the
published full-fiber density conclusion. -/
theorem ppt_bounded_fiber_of_scale_family (d : ℕ)
    (hfamily : ∃ a K : ℝ,0<a ∧ 0<K ∧ ∀ᶠ x : ℝ in atTop,
      0<x ∧ ∃ S : Finset ℕ,a*(x/Real.log x)*G x (m x) ≤ (S.card:ℝ) ∧
        ∀ b∈S,0<b ∧ ((d*b.totient:ℕ):ℝ)≤x ∧
          FullFiber d b ∧ (b:ℝ)/b.totient≤K) :
    PPTBoundedFiberPropagation d := by
  obtain ⟨a,K,ha,hK,hfamily⟩ := hfamily
  obtain ⟨C,hC,hupper⟩ := ford_scale_upper
  refine ⟨a/C,K,div_pos ha hC,hK,?_⟩
  filter_upwards [hfamily,hupper] with x hx hupper
  obtain ⟨hx,S,hcard,hS⟩ := hx
  refine ⟨hx,S,?_,hS⟩
  have hh := mul_le_mul_of_nonneg_left hupper (div_pos ha hC).le
  apply le_trans _ hcard
  convert hh using 1
  field_simp

/-- With seed one the totient map is injective on the constructed family,
so its positive mass proves Ford's lower counting bound. -/
theorem ford_scale_lower_of_one_family
    (hfamily : ∃ a K : ℝ,0<a ∧ 0<K ∧ ∀ᶠ x : ℝ in atTop,
      0<x ∧ ∃ S : Finset ℕ,a*(x/Real.log x)*G x (m x) ≤ (S.card:ℝ) ∧
        ∀ b∈S,0<b ∧ ((1*b.totient:ℕ):ℝ)≤x ∧
          FullFiber 1 b ∧ (b:ℝ)/b.totient≤K) :
    ∃ a : ℝ,0<a ∧ ∀ᶠ x : ℝ in atTop,a*(x/Real.log x)*G x (m x)≤V x := by
  obtain ⟨a,K,ha,_hK,hfamily⟩ := hfamily
  refine ⟨a,ha,?_⟩
  filter_upwards [hfamily] with x hx
  obtain ⟨_hx,S,hcard,hS⟩ := hx
  apply hcard.trans (fullFiber_one_card_le_V S ?_)
  intro b hb
  obtain ⟨hpos,hvalue,hfull,_hratio⟩ := hS b hb
  exact ⟨hpos,by simpa only [one_mul] using hvalue,hfull⟩

end TotientAsymptotic

end

end OAI
