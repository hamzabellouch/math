import Mathlib
import OAI.Analysis.SymmetricDomains.GraphBoundaryFirstHomotopy
import OAI.Analysis.SymmetricDomains.BishopPathInterior

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
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

theorem bishop_positive_interior {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    {ε : ℝ} (D : LocalBishopData k f ε) {Ω : Set (Fin k → ℂ)}
    (hΩ : IsOpen Ω) (hCP : DiscContinuityWithin k Ω ε)
    {α d u₀ L : ℝ} (hα : 0 < α) (hαr : α < D.radius)
    (hdr : d < D.radius) (hL : 1 ≤ L) (hu : α*L+d < u₀)
    (hG : ContinuousOn (graphPoint f) (closedBall 0 ε ×ˢ Icc α (α+d)))
    (hgraph : ∀ x ∈ closedBall 0 ε, ∀ u ∈ Ioo 0 u₀, graphPoint f (x,u) ∈ Ω)
    (hlam : ∀ θ, realEvaluation θ D.lam ≤ L) :
    ∃ e₀ : ℝ, 0 < e₀ ∧ ∀ b : Fin k → ℝ, ‖b‖ < D.radius →
      ∀ e : Fin k → ℝ, ‖e‖ < e₀ → ∀ δ ∈ Ioc 0 d, ∀ z : ClosedDisc,
        (fun i => bishopDisc D.Y (b,e,α,δ) i z) ∈ Ω := by
  obtain ⟨e₁,he₁,hpert⟩ := Release061.graph_boundary_perturbation hΩ hα hL (norm_nonneg D.eta) hu
    hG hgraph (fun θ => ⟨(D.cut_nonneg θ).1,hlam θ⟩)
    (fun θ => realEvaluation_bound θ D.eta) D.cut_nested
  let e₀ := min D.radius e₁
  have he₀ : 0 < e₀ := lt_min D.radius_pos he₁
  refine ⟨e₀,he₀,?_⟩
  intro b hb e he δ hδ z
  have her : ‖e‖ < D.radius := he.trans_le (min_le_left _ _)
  have hδr : |δ| < D.radius := by rw [abs_of_pos hδ.1]; exact hδ.2.trans_lt hdr
  have hx {p : BishopParams k} (hp : p ∈ ball 0 D.radius) (θ : Circle) :
      (fun i => realEvaluation θ (D.X p i)) ∈ closedBall 0 ε := by
    exact mem_closedBall_zero_iff.mpr ((evaluation_vector_norm_le θ (D.X p)).trans (D.small p hp).1.le)
  let p₁ : Icc (0 : ℝ) 1 → BishopParams k := fun s => (b,0,(s : ℝ)*α,δ)
  have hsa (s : Icc (0 : ℝ) 1) : (s : ℝ)*α ∈ Icc 0 α :=
    ⟨mul_nonneg s.property.1 hα.le,by nlinarith [s.property.2]⟩
  have hp₁ (s : Icc (0 : ℝ) 1) : p₁ s ∈ ball 0 D.radius := by
    apply bishopParams_mem_ball hb (by simpa only [norm_zero] using D.radius_pos) _ hδr
    rw [abs_of_nonneg (hsa s).1]
    exact (hsa s).2.trans_lt hαr
  have hi₁ := bishop_path_interior D hCP p₁ (by fun_prop) hp₁ (fun s θ => ?_) (fun w => ?_)
  · let p₂ : Icc (0 : ℝ) 1 → BishopParams k := fun s => (b,(s : ℝ) • e,α,δ)
    have hse (s : Icc (0 : ℝ) 1) : ‖(s : ℝ) • e‖ ≤ ‖e‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg s.property.1]
      exact mul_le_of_le_one_left (norm_nonneg _) s.property.2
    have hp₂ (s : Icc (0 : ℝ) 1) : p₂ s ∈ ball 0 D.radius :=
      bishopParams_mem_ball hb ((hse s).trans_lt her) (by rwa [abs_of_pos hα]) hδr
    have hi₂ := bishop_path_interior D hCP p₂ (by fun_prop) hp₂ (fun s θ => ?_) (fun w => ?_)
    · simpa only [p₂,one_smul] using hi₂ ⟨1,by simp⟩ z
    · rw [bishop_boundary_eq_graph D (hp₂ s)]
      apply hpert _ (hx (hp₂ s) θ) θ δ hδ
      rw [imaginaryVector_norm]
      exact (hse s).trans_lt (he.trans_le (min_le_right _ _))
    · simpa only [p₂,p₁,zero_smul,one_mul] using hi₁ ⟨1,by simp⟩ w
  · rw [bishop_boundary_eq_graph D (hp₁ s)]
    have hz : imaginaryVector (0 : Fin k → ℝ) = 0 := by ext; simp [imaginaryVector]
    change graphPoint f ((fun i => realEvaluation θ (D.X (p₁ s) i)),
      (s : ℝ)*α*realEvaluation θ D.lam+δ)+realEvaluation θ D.eta • imaginaryVector 0 ∈ Ω
    rw [hz,smul_zero,add_zero]
    exact Release061.graph_boundary_first_homotopy hα.le hu hgraph
      (fun θ => ⟨(D.cut_nonneg θ).1,hlam θ⟩) (hx (hp₁ s) θ) θ (hsa s) hδ
  · have hq : (b,δ) ∈ ball (0 : (Fin k → ℝ) × ℝ) D.radius := by
      simpa only [mem_ball,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,max_lt_iff] using And.intro hb hδr
    have heq : (fun i => bishopDisc D.Y (p₁ ⟨0,by simp⟩) i w) = graphPoint f (b,δ) := by
      funext i
      simpa only [p₁,zero_mul,graphPoint] using D.constant (b,δ) hq i w
    rw [heq]
    refine hgraph b ?_ δ ?_
    · have hbε : ‖b‖ < ε := by
        have hh := (D.small (p₁ ⟨0,by simp⟩) (hp₁ ⟨0,by simp⟩)).1
        have hxconst := (D.equation (p₁ ⟨0,by simp⟩) (hp₁ ⟨0,by simp⟩)).1
        have heval : (fun i => realEvaluation (0 : Circle) (D.X (p₁ ⟨0,by simp⟩) i)) = b := by
          funext i
          rw [hxconst i]
          simp only [map_add,realEvaluation_constant,normalizedHilbert_eval_zero,add_zero,p₁]
        rw [← heval]
        exact (evaluation_vector_norm_le _ _).trans_lt hh
      exact mem_closedBall_zero_iff.mpr hbε.le
    · exact ⟨hδ.1,by have := mul_pos hα (lt_of_lt_of_le zero_lt_one hL); linarith [hδ.2]⟩

end Release061.Wiener

end

end OAI
