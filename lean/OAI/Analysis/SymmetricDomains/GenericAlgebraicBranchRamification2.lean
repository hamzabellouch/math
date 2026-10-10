import Mathlib
import OAI.Analysis.SymmetricDomains.GenericAlgebraicBranchRamification

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory Metric

theorem remove_ramification_scale {n l : ℕ} {s : Fin n → ℝ} {r c : ℝ}
    (hc : 0 < c) (hl : 0 < l)
    (F : (Fin n → ℂ) × ℂ → ℂ)
    (hFa : AnalyticOnNhd ℂ F (ball 0 r ×ˢ ball 0 (1/2)))
    (b : (Fin n → ℝ) × ℝ → ℂ)
    (hF : ∀ x ∈ ball 0 r, ∀ t ∈ Ioo (0 : ℝ) (1/2),
      F (realParameter x,t) = b (s+x,c*t^l)) :
    ∃ ε > 0, ∃ H : (Fin n → ℂ) × ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (realParameter s) r ×ˢ ball 0 ε) ∧
      ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) ε,
        H (realParameter x,t) = b (x,t^l) := by
  let a : ℝ := c ^ (l : ℝ)⁻¹
  have ha : 0 < a := Real.rpow_pos_of_pos hc _
  have hal : a^l = c := Real.rpow_inv_natCast_pow hc.le hl.ne'
  let T : ((Fin n → ℂ) × ℂ) → ((Fin n → ℂ) × ℂ) :=
    fun p => (p.1-realParameter s,p.2/(a : ℂ))
  have hTa (p : (Fin n → ℂ) × ℂ) : AnalyticAt ℂ T p :=
    (((ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ).analyticAt p).sub analyticAt_const).prod
      (((ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ).analyticAt p).div_const)
  have hTmem (p : (Fin n → ℂ) × ℂ)
      (hp : p ∈ ball (realParameter s) r ×ˢ ball 0 (a/2)) :
      T p ∈ ball 0 r ×ˢ ball 0 (1/2) := by
    constructor
    · simpa only [T,mem_ball,dist_eq_norm,sub_zero] using hp.1
    · simp only [T,mem_ball,dist_zero_right,norm_div,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos ha]
      apply (div_lt_iff₀ ha).mpr
      have ht := hp.2
      simp only [mem_ball,dist_zero_right] at ht
      linarith
  refine ⟨a/2,by positivity,F ∘ T,?_,?_⟩
  · intro p hp
    exact (hFa _ (hTmem p hp)).comp (hTa p)
  · intro x hx t ht
    have hx' : x-s ∈ ball 0 r := by
      simpa only [mem_ball,dist_eq_norm,sub_zero] using hx
    have ht' : t/a ∈ Ioo (0 : ℝ) (1/2) := by
      refine ⟨div_pos ht.1 ha,(div_lt_iff₀ ha).mpr ?_⟩
      linarith [ht.2]
    have he : T (realParameter x,(t : ℂ)) = (realParameter (x-s),((t/a : ℝ) : ℂ)) := by
      apply Prod.ext
      · ext i
        simp only [T,Pi.sub_apply,realParameter,Complex.ofReal_sub]
      · simp only [T,Complex.ofReal_div]
    change F (T (realParameter x,(t : ℂ))) = _
    rw [he,hF (x-s) hx' (t/a) ht']
    congr 1
    apply Prod.ext
    · abel_nf
    · rw [div_pow,hal]
      exact mul_div_cancel₀ (t^l) hc.ne'

theorem generic_algebraic_branch_ramification {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin (n+1)) ℂ))
    (hP : P ≠ 0) (hres : P.resultant P.derivative ≠ 0)
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (b : (Fin n → ℝ) × ℝ → ℂ)
    (hb : ContinuousOn b (B ×ˢ Ioo 0 ε))
    (hbr : ∀ p ∈ B ×ˢ Ioo 0 ε,
      Polynomial.eval₂ (MvPolynomial.eval (Fin.cons (p.2 : ℂ) (realParameter p.1))) (b p) P = 0)
    {M : ℝ} (hbound : ∀ p ∈ B ×ˢ Ioo 0 ε, ‖b p‖ ≤ M) :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ r > 0, ∃ l : ℕ, 0 < l ∧ ∃ η > 0,
        ∃ F : (Fin n → ℂ) × ℂ → ℂ,
          ball s r ⊆ B ∧
          AnalyticOnNhd ℂ F (ball (realParameter s) r ×ˢ ball 0 η) ∧
          ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η,
            F (realParameter x,t) = b (x,t^l) := by
  obtain ⟨E,hE,hg⟩ := generic_algebraic_branch_ramification_scaled P hP hres hB hε b hb hbr hbound
  refine ⟨E,hE,?_⟩
  intro s hs hsE
  obtain ⟨r,hr,c,hc,l,hl,F,hsr,hFa,hF⟩ := hg s hs hsE
  obtain ⟨η,hη,H,hHa,hH⟩ := remove_ramification_scale hc hl F hFa b hF
  exact ⟨r,hr,l,hl,η,hη,H,hsr,hHa,hH⟩

end Release061

end

end OAI
