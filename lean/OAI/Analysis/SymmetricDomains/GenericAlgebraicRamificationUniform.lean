import Mathlib
import OAI.Analysis.SymmetricDomains.AlgebraicGraphPolynomial
import OAI.Analysis.SymmetricDomains.AlgebraicBranchRamification
import OAI.Analysis.SymmetricDomains.GenericFinParameterPolynomial
import OAI.Analysis.SymmetricDomains.RegularSimpleSheet

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

section
open Polynomial Set Filter Topology

theorem semialgebraic_function_analytic_off_polynomial {n : ℕ}
    (B : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (hgraph : PolynomialSignSet id
      {x : Option (Fin n) → ℝ |
        (fun i => x (some i)) ∈ B ∧ x none = f (fun i => x (some i))}) :
    ∃ D : MvPolynomial (Fin n) ℝ, D ≠ 0 ∧
      ∀ a ∈ B, MvPolynomial.eval a D ≠ 0 → AnalyticAt ℝ f a := by
  obtain ⟨p,hp,hpr⟩ := semialgebraic_graph_polynomial B f hgraph
  let P := MvPolynomial.optionEquivLeft ℝ (Fin n) p
  have hP : P ≠ 0 := (MvPolynomial.optionEquivLeft ℝ (Fin n)).injective.ne hp
  obtain ⟨q,hq,hqs,D₀,hD₀,hqe⟩ :=
    squarefree_relation_off_denominator (K := FractionRing (MvPolynomial (Fin n) ℝ)) P hP
  have hres : q.resultant q.derivative ≠ 0 :=
    resultant_derivative_ne_zero_of_generic_separable q hqs
  obtain ⟨D₁,hD₁,hreg⟩ := hgraph.regular_on_simple_sheet q
  refine ⟨D₀*D₁*q.leadingCoeff*(q.resultant q.derivative),
    mul_ne_zero (mul_ne_zero (mul_ne_zero hD₀ hD₁)
      (Polynomial.leadingCoeff_ne_zero.mpr hq)) hres,?_⟩
  intro a ha hD
  have hD₀a : MvPolynomial.eval a D₀ ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,zero_mul]
  have hD₁a : MvPolynomial.eval a D₁ ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero,zero_mul]
  have hl : MvPolynomial.eval a q.leadingCoeff ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero,zero_mul]
  have hd : MvPolynomial.eval a (q.resultant q.derivative) ≠ 0 := by
    intro hz; apply hD; simp only [map_mul,hz,mul_zero]
  have hpr' : P.eval₂ (MvPolynomial.eval a) (f a) = 0 := by
    simpa only [MvPolynomial.optionEquivLeft_elim_eval,eval_map,P] using hpr a ha
  have hqr : q.eval₂ (MvPolynomial.eval a) (f a) = 0 :=
    (hqe (MvPolynomial.eval a) hD₀a (f a)).mp hpr'
  have hsep := separable_map_of_leading_resultant_ne_zero q (MvPolynomial.eval a) hl hd
  have hder : q.derivative.eval₂ (MvPolynomial.eval a) (f a) ≠ 0 := by
    have hh := Polynomial.Separable.eval₂_derivative_ne_zero (RingHom.id ℝ) hsep
      (x := f a) (by simpa only [Polynomial.eval₂_id,Polynomial.eval_map] using hqr)
    simpa only [Polynomial.eval₂_id,Polynomial.derivative_map,Polynomial.eval_map] using hh
  obtain ⟨g,hga,hgf,hgr,_⟩ := real_polynomial_analytic_root q a (f a) hqr hder
  have hder' : q.derivative.eval₂ (MvPolynomial.eval a) (g a) ≠ 0 := by
    simpa only [hgf] using hder
  rcases hreg g a hga.continuousAt hgr hder' hD₁a with hyes | hno
  · have he : g =ᶠ[𝓝 a] f := by
      filter_upwards [hyes] with y hy
      exact hy.2
    exact hga.congr he
  · have hn := hno.self_of_nhds
    exact (hn ⟨ha,hgf⟩).elim

end

open Set Filter Topology MeasureTheory Metric
theorem generic_algebraic_ramification_uniform {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin (n+1)) ℂ))
    (hP : P ≠ 0) (hres : P.resultant P.derivative ≠ 0)
 :
    ∃ E : Set (Fin n → ℝ), volume E = 0 ∧
      ∀ s ∉ E, ∀ {B : Set (Fin n → ℝ)}, IsOpen B → s ∈ B →
      ∀ {ε : ℝ}, 0 < ε → ∀ (b : (Fin n → ℝ) × ℝ → ℂ),
      ContinuousOn b (B ×ˢ Ioo 0 ε) →
      (∀ p ∈ B ×ˢ Ioo 0 ε,
        Polynomial.eval₂ (MvPolynomial.eval (Fin.cons (p.2 : ℂ) (realParameter p.1))) (b p) P = 0) →
      ∀ {M : ℝ}, (∀ p ∈ B ×ˢ Ioo 0 ε, ‖b p‖ ≤ M) →
      ∃ r > 0, ∃ c > 0, ∃ l : ℕ, 0 < l ∧
        ∃ F : (Fin n → ℂ) × ℂ → ℂ,
          ball s r ⊆ B ∧
          AnalyticOnNhd ℂ F (ball 0 r ×ˢ ball 0 (1/2)) ∧
          ∀ x ∈ ball 0 r, ∀ t ∈ Ioo (0 : ℝ) (1/2),
            F (realParameter x,t) = b (s+x,c*t^l) := by
  obtain ⟨E,hE,hg⟩ := generic_fin_parameter_polynomial_separable P hP hres
  refine ⟨E,hE,?_⟩
  intro s hsE B hB hs ε hε b hb hbr M hbound
  obtain ⟨δ,hδ,hg⟩ := hg s hsE
  obtain ⟨ρ,hρ,hρB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds hs)
  let r := min δ ρ
  let c := min δ ε / 2
  have hr : 0 < r := lt_min hδ hρ
  have hc : 0 < c := by dsimp [c]; positivity
  have hcδ : c ≤ δ := by dsimp [c]; linarith [min_le_left δ ε,lt_min hδ hε]
  have hcε : c ≤ ε := by dsimp [c]; linarith [min_le_right δ ε,lt_min hδ hε]
  have hsr : ball s r ⊆ B := (ball_subset_ball (min_le_right δ ρ)).trans hρB
  have hreal (x : Fin n → ℝ) (hx : x ∈ ball 0 r) : s+x ∈ B := by
    apply hsr
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hx
  have hcomplex (x : Fin n → ℂ) (hx : x ∈ ball 0 r) :
      realParameter s + x ∈ ball (realParameter s) δ := by
    have hx' := ball_subset_ball (min_le_left δ ρ) hx
    simpa only [mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hx'
  let A : (Fin n → ℂ) × ℂ → (Fin (n+1) → ℂ) :=
    fun p => Fin.cons ((c : ℂ)*p.2) (realParameter s+p.1)
  have hA : AnalyticOnNhd ℂ A (ball 0 r ×ˢ ball 0 1) := by
    intro p _
    apply analyticAt_pi_iff.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact analyticAt_const.mul ((ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ).analyticAt p)
    · exact analyticAt_const.add (((ContinuousLinearMap.proj j :
        (Fin n → ℂ) →L[ℂ] ℂ).analyticAt p.1).comp
          ((ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ).analyticAt p))
  have hroot (p : (Fin n → ℂ) × ℂ)
      (hp : p ∈ ball 0 r ×ˢ {u : ℂ | u ≠ 0 ∧ ‖u‖ < 1}) :
      MvPolynomial.eval (A p) P.leadingCoeff ≠ 0 ∧
        (P.map (MvPolynomial.eval (A p))).Separable := by
    apply hg (realParameter s+p.1) (hcomplex p.1 hp.1) ((c : ℂ)*p.2)
    · simp only [mem_ball,dist_zero_right,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc]
      exact (mul_lt_mul_of_pos_left hp.2.2 hc).trans_le (by simpa using hcδ)
    · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hc.ne') hp.2.1
  let β : ((Fin n → ℝ) × ℝ) → ((Fin n → ℝ) × ℝ) := fun p => (s+p.1,c*p.2)
  have hβ : Continuous β := (continuous_const.add continuous_fst).prodMk
    (continuous_const.mul continuous_snd)
  have hβmem (p : (Fin n → ℝ) × ℝ) (hp : p ∈ ball 0 r ×ˢ Ioo 0 1) :
      β p ∈ B ×ˢ Ioo 0 ε :=
    ⟨hreal p.1 hp.1,mul_pos hc hp.2.1,
      (mul_lt_mul_of_pos_left hp.2.2 hc).trans_le (by simpa using hcε)⟩
  have hb' : ContinuousOn (b ∘ β) (ball 0 r ×ˢ Ioo 0 1) := hb.comp hβ.continuousOn hβmem
  have hbr' : ∀ (p : (Fin n → ℝ) × ℝ), p ∈ ball 0 r ×ˢ Ioo 0 1 →
      Polynomial.eval₂ (MvPolynomial.eval (A (realParameter p.1,p.2))) ((b ∘ β) p) P = 0 := by
    intro p hp
    have hadd : realParameter (s+p.1) = realParameter s+realParameter p.1 := by
      ext i
      simp only [realParameter,Pi.add_apply,Complex.ofReal_add]
    simpa only [A,β,Function.comp_apply,Complex.ofReal_mul,hadd] using hbr (β p) (hβmem p hp)
  obtain ⟨l,hl,F,hFa,hF⟩ := bounded_algebraic_branch_ramification P A hr hA
    (fun p hp => (hroot p hp).1) (fun p hp => (hroot p hp).2)
    (b ∘ β) hb' hbr' (fun p hp => hbound (β p) (hβmem p hp))
  exact ⟨r,hr,c,hc,l,hl,F,hsr,hFa,hF⟩

end Release061

end

end OAI
