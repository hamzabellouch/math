import Mathlib
import OAI.Analysis.SymmetricDomains.GenericAlgebraicBranchRamification2
import OAI.Analysis.SymmetricDomains.GenericRealParameterPolynomial

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
open Set Filter Topology Metric MeasureTheory

theorem semialgebraic_ramification_with_parameters_complex {n : ℕ}
    {B : Set (Fin n → ℝ)} (hB : IsOpen B) {ε : ℝ} (hε : 0 < ε)
    (b : (Fin (n+1) → ℝ) → ℝ)
    (hgraph : PolynomialSignSet id
      {x : Option (Fin (n+1)) → ℝ |
        ((fun i => x (some i.succ)) ∈ B ∧ x (some 0) ∈ Ioo 0 ε) ∧
          x none = b (fun i => x (some i))})
    {M : ℝ} (hbound : ∀ x : Fin (n+1) → ℝ, Fin.tail x ∈ B → x 0 ∈ Ioo 0 ε → ‖b x‖ ≤ M) :
    ∃ E : Set (Fin n → ℝ), E ⊆ B ∧ volume E = 0 ∧
      ∀ s ∈ B, s ∉ E → ∃ r > 0, ∃ l : ℕ, 0 < l ∧ ∃ η > 0,
        ∃ F : (Fin n → ℂ) × ℂ → ℂ,
          ball s r ⊆ B ∧
          AnalyticOnNhd ℂ F (ball (realParameter s) r ×ˢ ball 0 η) ∧
          ∀ x ∈ ball s r, ∀ t ∈ Ioo (0 : ℝ) η,
            F (realParameter x,t) = (b (Fin.cons (t^l) x) : ℂ) := by
  let T : Set (Fin (n+1) → ℝ) := {x | Fin.tail x ∈ B ∧ x 0 ∈ Ioo 0 ε}
  obtain ⟨D,hD,P,hP,hres,hdata⟩ := semialgebraic_function_algebraic_data T b hgraph
  obtain ⟨E₀,hE₀,hDgood⟩ := generic_real_parameter_polynomial_nonzero D hD
  obtain ⟨E₁,hE₁,hgood⟩ := generic_algebraic_ramification_uniform P hP hres
  refine ⟨(E₀ ∪ E₁) ∩ B,inter_subset_right,
    measure_mono_null inter_subset_left (measure_union_null hE₀ hE₁),?_⟩
  intro s hs hsE
  have hs₀ : s ∉ E₀ := fun h => hsE ⟨Or.inl h,hs⟩
  have hs₁ : s ∉ E₁ := fun h => hsE ⟨Or.inr h,hs⟩
  obtain ⟨δ,hδ,hDgood⟩ := hDgood s hs₀
  obtain ⟨ρ,hρ,hρB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds hs)
  let r := min δ ρ
  let τ := min δ ε
  have hr : 0 < r := lt_min hδ hρ
  have hτ : 0 < τ := lt_min hδ hε
  have hrB : ball s r ⊆ B := (ball_subset_ball (min_le_right δ ρ)).trans hρB
  have hsub : ball s r ×ˢ Ioo 0 τ ⊆ B ×ˢ Ioo 0 ε := by
    rintro p ⟨hx,ht⟩
    exact ⟨hrB hx,ht.1,ht.2.trans_le (min_le_right δ ε)⟩
  have hDne (p : (Fin n → ℝ) × ℝ) (hp : p ∈ ball s r ×ˢ Ioo 0 τ) :
      MvPolynomial.eval (Fin.cons p.2 p.1) D ≠ 0 :=
    hDgood p.1 (ball_subset_ball (min_le_left δ ρ) hp.1) p.2
      ⟨hp.2.1,hp.2.2.trans_le (min_le_left δ ε)⟩
  let c : (Fin n → ℝ) × ℝ → (Fin (n+1) → ℝ) := fun p => Fin.cons p.2 p.1
  have hc : Continuous c := by
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_snd
    · exact (continuous_apply j).comp continuous_fst
  let β : (Fin n → ℝ) × ℝ → ℂ := fun p => (b (c p) : ℂ)
  have hT (p : (Fin n → ℝ) × ℝ) (hp : p ∈ ball s r ×ˢ Ioo 0 τ) : c p ∈ T := by
    exact hsub hp
  have hβ : ContinuousOn β (ball s r ×ˢ Ioo 0 τ) := by
    intro p hp
    exact (Complex.continuous_ofReal.continuousAt.comp
      ((hdata (c p) (hT p hp) (hDne p hp)).1.continuousAt.comp hc.continuousAt)).continuousWithinAt
  have hroot (p : (Fin n → ℝ) × ℝ) (hp : p ∈ ball s r ×ˢ Ioo 0 τ) :
      P.eval₂ (MvPolynomial.eval (Fin.cons (p.2 : ℂ) (realParameter p.1))) (β p) = 0 := by
    have hh := (hdata (c p) (hT p hp) (hDne p hp)).2
    have he : realParameter (c p) = Fin.cons (p.2 : ℂ) (realParameter p.1) := by
      ext i
      refine Fin.cases rfl (fun _ => rfl) i
    simpa only [he,β] using hh
  have hβbound (p : (Fin n → ℝ) × ℝ) (hp : p ∈ ball s r ×ˢ Ioo 0 τ) : ‖β p‖ ≤ M := by
    simpa only [β,Complex.norm_real] using hbound (c p) (hT p hp).1 (hT p hp).2
  obtain ⟨r',hr',c',hc',l,hl,F,hr's,hFa,hF⟩ := hgood s hs₁ isOpen_ball (mem_ball_self hr)
    hτ β hβ hroot hβbound
  obtain ⟨η,hη,H,hHa,hH⟩ := remove_ramification_scale hc' hl F hFa β hF
  exact ⟨r',hr',l,hl,η,hη,H,hr's.trans hrB,hHa,hH⟩

end Release061

end

end OAI
