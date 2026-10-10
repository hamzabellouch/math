import Mathlib
import OAI.Probability.SKGap.Brownian.IntervalMesh
import OAI.Probability.SKGap.Localization.ChainingCore

namespace OAI

section
noncomputable section
namespace SKGap
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped BigOperators ENNReal Topology
variable {α : Type*} [Fintype α] [DecidableEq α]

def boxMeshEdges (k : ℕ) : Finset ((α→Fin (4^k+1))×(α→Fin (4^(k+1)+1))) :=
  Finset.univ.filter (fun e=>dist (boxMeshPoint (k+1) e.2) (boxMeshPoint k e.1)≤2*(1/4:ℝ)^k)

lemma boxMesh_base_exp : (Fintype.card (α→Fin (4^0+1)):ℝ)≤exp (log 16*(Fintype.card α:ℝ)) := by
  have hh : (Fintype.card (α→Fin (4^0+1)):ℝ)≤(16:ℝ)^(Fintype.card α) := by
    simp only [Fintype.card_fun,Fintype.card_fin,pow_zero];norm_num
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  apply hh.trans_eq
  rw [←exp_log (by norm_num : (0:ℝ)<16),←exp_nat_mul]
  simp only [log_exp]
  congr 1;ring

theorem box_chaining_probability {Ω E : Type*} [MeasurableSpace Ω]
    [AddCommGroup E] [TopologicalSpace E] (μ : Measure Ω)
    (p : E→ℝ) (hc : Continuous p) (hp : ∀ x y,p (x+y)≤p x+p y)
    (F : (α→Icc (0:ℝ) 1)→Ω→E) (hF : ∀ ω,Continuous (fun t=>F t ω))
    {n : ℕ} (hn : 1≤n) {A B : ℝ} (hB : 0≤B) (hA : B+1≤A)
    (hdim : log 16*(Fintype.card α:ℝ)≤B*(n:ℝ))
    (b : ℝ) (r : ℕ→ℝ) (hr : ∀ k,0≤r k) (hrs : Summable r)
    (hb : ∀ θ,μ {ω | b<p (F θ ω)}≤ENNReal.ofReal (exp (-A*(n:ℝ))))
    (hi : ∀ k θ η,dist θ η≤2*(1/4:ℝ)^k→
      μ {ω | r k<p (F θ ω-F η ω)}≤ENNReal.ofReal (exp (-A*((k:ℝ)+1)^2*(n:ℝ)))) :
    μ {ω | ∃ θ,b+(∑' k,r k)<p (F θ ω)}≤ENNReal.ofReal (3*exp (-(n:ℝ))) := by
  classical
  have hq := continuous_chaining_probability μ p hc hp F hF univ
    (fun k=>α→Fin (4^k+1)) boxMeshPoint boxMeshEdges (by
      intro θ _
      refine ⟨boxMeshIndex θ,?_,boxMeshIndex_tendsto θ⟩
      intro k
      simpa only [boxMeshEdges,Finset.mem_filter,Finset.mem_univ,true_and] using boxMeshIndex_increment θ k)
    r hr hrs b (ENNReal.ofReal (exp (-A*(n:ℝ))))
    (fun k=>ENNReal.ofReal (exp (-A*((k:ℝ)+1)^2*(n:ℝ))))
    (fun i=>hb (boxMeshPoint 0 i)) (by
      intro k e he
      exact hi k _ _ (Finset.mem_filter.mp he).2)
  simp only [mem_univ,true_and] at hq
  apply hq.trans
  have hc1 : log 2≤(1:ℝ) := by
    have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh ⊢;exact hh
  have hbcard : (Fintype.card (α→Fin (4^0+1)):ℝ≥0∞)≤ENNReal.ofReal (exp (B*(n:ℝ))) := by
    rw [←ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (boxMesh_base_exp.trans (exp_le_exp.mpr hdim))
  have hbcost := chaining_entropy_tail_product hn hB (by norm_num : (0:ℝ)<1) hA 0
    (m := (Fintype.card (α→Fin (4^0+1)):ℝ≥0∞))
    (q := ENNReal.ofReal (exp (-A*(n:ℝ))))
    (by simpa only [Nat.cast_zero,zero_add,mul_one] using hbcard) (by simp)
  have hecard (k : ℕ) : ((boxMeshEdges (α:=α) k).card:ℝ≥0∞)≤ENNReal.ofReal (exp (B*((k:ℝ)+1)*(n:ℝ))) := by
    rw [←ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    apply (boxMesh_edges_exp k _).trans
    apply exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_right hdim (by positivity : 0≤(k:ℝ)+1)
    nlinarith only [hh]
  have hicost := chaining_entropy_series hn hB hc1 hA
    (fun k=>((boxMeshEdges (α:=α) k).card:ℝ≥0∞))
    (fun k=>ENNReal.ofReal (exp (-A*((k:ℝ)+1)^2*(n:ℝ)))) hecard (fun _=>le_rfl)
  apply (add_le_add hbcost hicost).trans_eq
  simp only [Nat.cast_zero,zero_add,mul_one,one_mul,neg_mul]
  rw [←ENNReal.ofReal_add (exp_pos _).le (by positivity)]
  congr 1;ring
end SKGap
end
end

end OAI
