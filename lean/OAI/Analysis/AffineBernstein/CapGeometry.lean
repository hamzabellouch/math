import Mathlib
import OAI.Analysis.AffineBernstein.Basic

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter Metric
open scoped Topology

/-- A bounded cap quantitatively separates a unit recession direction from
its horizontal hyperplane. This is the ray argument in bounds.tex:45–59. -/
theorem cap_recession_component_lower {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {D : Set E} (ell : E →L[ℝ] ℝ) {b R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hcap : ∀ x ∈ D, ell x ≤ b → ‖x‖ ≤ R)
    {o e : E} (ho : o ∈ D) (hgap : ell o ≤ b-ε) (he : ‖e‖ = 1)
    (hrec : ∀ t : ℝ, 0 ≤ t → o+t • e ∈ D) :
    ε/(2*R+1) < ell e := by
  have hT : 0 < 2*R+1 := by positivity
  have hoR : ‖o‖ ≤ R := hcap o ho (by linarith)
  by_contra hn
  have hle : (2*R+1)*ell e ≤ ε := by
    simpa only [mul_comm] using ((le_div_iff₀ hT).mp (not_lt.mp hn))
  have hptop : ell (o+(2*R+1) • e) ≤ b := by
    simp only [map_add,map_smul,smul_eq_mul]
    linarith
  have hpR := hcap (o+(2*R+1) • e) (hrec _ hT.le) hptop
  have htri := norm_sub_le (o+(2*R+1) • e) o
  have hnorm : ‖(o+(2*R+1) • e)-o‖ = 2*R+1 := by
    rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hT,he,mul_one]
  rw [hnorm] at htri
  linarith

/-- The normalized vertical has uniformly bounded norm. -/
theorem cap_normalized_vertical_bound {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {D : Set E} (ell : E →L[ℝ] ℝ) {b R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hcap : ∀ x ∈ D, ell x ≤ b → ‖x‖ ≤ R)
    {o e : E} (ho : o ∈ D) (hgap : ell o ≤ b-ε) (he : ‖e‖ = 1)
    (hrec : ∀ t : ℝ, 0 ≤ t → o+t • e ∈ D) :
    0 < ell e ∧ ell ((ell e)⁻¹ • e) = 1 ∧
      ‖(ell e)⁻¹ • e‖ ≤ (2*R+1)/ε := by
  have hl := cap_recession_component_lower ell hR hε hcap ho hgap he hrec
  have hT : 0 < 2*R+1 := by positivity
  have hp : 0 < ell e := (div_pos hε hT).trans hl
  refine ⟨hp,by simp [hp.ne'],?_⟩
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),he,mul_one]
  apply (le_div_iff₀ hε).mpr
  have hle : ε ≤ ell e*(2*R+1) := ((div_lt_iff₀ hT).mp hl).le
  have hi := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hp.le)
  simpa only [← mul_assoc,inv_mul_cancel₀ hp.ne',one_mul] using hi

/-- Compactness of a closed graph sublevel follows from compactness of the
entire epigraph cap, without a boundary regularity hypothesis. -/
lemma isCompact_graph_sublevel_of_cap {n : ℕ} {Ω : Set (Space n)}
    {u : Space n → ℝ} {b : ℝ}
    (hK : IsCompact {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2 ∧ p.2 ≤ b}) :
    IsCompact {x | x ∈ Ω ∧ u x ≤ b} := by
  have he : Prod.fst '' {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2 ∧ p.2 ≤ b} =
      {x | x ∈ Ω ∧ u x ≤ b} := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨hp.1,hp.2.1.trans hp.2.2⟩
    · intro hx
      exact ⟨(x,u x),⟨hx.1,le_rfl,hx.2⟩,rfl⟩
  rw [← he]
  exact hK.image continuous_fst

/-- The ambient ball supplies the graph's base ball at the center's height. -/
lemma graph_ball_of_epigraph_ball {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {o : Space n × ℝ} {r : ℝ}
    (hball : Metric.ball o r ⊆ {p : Space n × ℝ | p.1 ∈ Ω ∧ u p.1 ≤ p.2}) :
    ∀ x ∈ Metric.ball o.1 r, x ∈ Ω ∧ u x ≤ o.2 := by
  intro x hx
  exact hball (show (x,o.2) ∈ Metric.ball o r from by
    simpa [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using hx)

/-- A cap radius bounds distances to the center in its base. -/
lemma graph_cap_radius_bound {n : ℕ} {Ω : Set (Space n)} {u : Space n → ℝ}
    {b R : ℝ} {c : Space n} (hc : ‖c‖ ≤ R)
    (hcap : ∀ p : Space n × ℝ, p.1 ∈ Ω → u p.1 ≤ p.2 → p.2 ≤ b → ‖p‖ ≤ R) :
    ∀ x, x ∈ Ω → u x < b → ‖x-c‖ ≤ 2*R := by
  intro x hx hxb
  have hp := hcap (x,u x) hx le_rfl hxb.le
  have hxR : ‖x‖ ≤ R := (norm_fst_le (x,u x)).trans hp
  linarith [norm_sub_le x c]

end AffineBernstein
end

end OAI
