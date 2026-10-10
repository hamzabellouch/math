import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicRamificationParametersComplex

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
open Set Metric
open scoped Topology
lemma analyticAt_real_parameter_product {n : ℕ} (p : (Fin n → ℝ) × ℝ) :
    AnalyticAt ℝ (fun q : (Fin n → ℝ) × ℝ => (realParameter q.1,(q.2 : ℂ))) p := by
  have h₁ : AnalyticAt ℝ (fun q : (Fin n → ℝ) × ℝ => realParameter q.1) p := by
    apply analyticAt_pi_iff.mpr
    intro i
    exact (Complex.ofRealCLM.analyticAt _).comp
      (((ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).analyticAt _).comp
        ((ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ).analyticAt p))
  exact h₁.prod ((Complex.ofRealCLM.analyticAt _).comp
    ((ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ).analyticAt p))

lemma analyticAt_real_part_restriction {n : ℕ} (F : (Fin n → ℂ) × ℂ → ℂ)
    (p : (Fin n → ℝ) × ℝ)
    (hF : AnalyticAt ℂ F (realParameter p.1,(p.2 : ℂ))) :
    AnalyticAt ℝ (fun q : (Fin n → ℝ) × ℝ => (F (realParameter q.1,(q.2 : ℂ))).re) p := by
  have ha := (hF.restrictScalars (𝕜 := ℝ)).comp
    (f := fun q : (Fin n → ℝ) × ℝ => (realParameter q.1,(q.2 : ℂ)))
    (analyticAt_real_parameter_product p)
  exact (Complex.reCLM.analyticAt _).comp ha

end

section
open Set Filter Topology Metric MeasureTheory

theorem semialgebraic_ramification_with_parameters {n : ℕ}
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (b : (Fin (n+1) → ℝ) → ℝ)
    (hgraph : PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = b (fun i => x (some i))})
    {M : ℝ} (hbound : ∀ x : Fin (n+1) → ℝ, Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε → ‖b x‖ ≤ M) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ r > 0, ∃ l : ℕ, 0 < l ∧ ∃ η > 0,
        ∃ F : (Fin n → ℝ) × ℝ → ℝ,
          ball s r ⊆ B ∧
          AnalyticOnNhd ℝ F (ball s r ×ˢ ball 0 η) ∧
          ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η,
            F (x,t) = b (Fin.cons (t^l) x) := by
  obtain ⟨E,hEB,hE,hg⟩ := semialgebraic_ramification_with_parameters_complex hB hε b hgraph hbound
  refine ⟨E,hEB,hE,?_⟩
  intro s hs hsE
  obtain ⟨r,hr,l,hl,η,hη,F,hrB,hFa,hF⟩ := hg s hs hsE
  refine ⟨r,hr,l,hl,η,hη,(fun p => (F (realParameter p.1,(p.2 : ℂ))).re),hrB,?_,?_⟩
  · intro p hp
    apply analyticAt_real_part_restriction
    apply hFa
    refine ⟨?_,?_⟩
    · simpa only [mem_ball,realParameter_dist] using hp.1
    · simpa only [mem_ball,dist_zero_right,Complex.norm_real] using hp.2
  · intro x hx t ht
    change (F (realParameter x,(t : ℂ))).re = _
    rw [hF x hx t ht,Complex.ofReal_re]

end

open Filter Set Metric Topology

theorem joint_limit_of_ramification {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b F : E × ℝ → ℝ) (s : E) {r η : ℝ} (hr : 0 < r) (hη : 0 < η)
    {l : ℕ} (hl : 0 < l) (hFc : ContinuousAt F (s,0))
    (hF : ∀ x ∈ ball s r, ∀ u ∈ Ioo (0 : ℝ) η, F (x,u) = b (x,u^l)) :
    Tendsto b (𝓝[{p : E × ℝ | 0 < p.2}] (s,0)) (𝓝 (F (s,0))) := by
  let a : ℝ := (l : ℝ)⁻¹
  have ha : 0 < a := inv_pos.mpr (Nat.cast_pos.mpr hl)
  let e : E × ℝ → E × ℝ := fun p => (p.1,p.2^a)
  have he : Continuous e :=
    continuous_fst.prodMk ((Real.continuous_rpow_const ha.le).comp continuous_snd)
  have he₀ : e (s,0) = (s,0) := by
    simp only [e,Real.zero_rpow ha.ne']
  have hT : Tendsto e (𝓝 (s,0)) (𝓝 (s,0)) := by
    simpa only [he₀] using he.continuousAt.tendsto (x := (s,0))
  have hN : ball s r ×ˢ ball (0 : ℝ) η ∈ 𝓝 ((s,0) : E × ℝ) :=
    (isOpen_ball.prod isOpen_ball).mem_nhds ⟨mem_ball_self hr,mem_ball_self hη⟩
  have hen := hT hN
  have heq : b =ᶠ[𝓝[{p : E × ℝ | 0 < p.2}] (s,0)] F ∘ e := by
    filter_upwards [nhdsWithin_le_nhds hen,self_mem_nhdsWithin] with p hp hp0
    have hu : 0 < p.2^a := Real.rpow_pos_of_pos hp0 _
    have hut : p.2^a < η := by
      have hh := hp.2
      change dist (p.2^a) 0 < η at hh
      simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_pos hu] using hh
    have hpw : (p.2^a)^l = p.2 := Real.rpow_inv_natCast_pow hp0.le hl.ne'
    change b p = F (p.1,p.2^a)
    rw [hF p.1 hp.1 (p.2^a) ⟨hu,hut⟩,hpw]
  exact ((hFc.tendsto.comp hT).mono_left nhdsWithin_le_nhds).congr' heq.symm

end Release061

end

end OAI
