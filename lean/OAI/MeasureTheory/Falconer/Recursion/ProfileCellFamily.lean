import OAI.MeasureTheory.Falconer.Recursion.ProfilePrefix
import OAI.MeasureTheory.Falconer.Recursion.ProfileRestriction

namespace OAI

/-! Invariants for the finite profile-merging recursion. The original equal
width cells are retained as witnesses when their active prefixes are shortened. -/
namespace Falconer
open Set

structure ProfileCellFamily (f : ℝ → ℝ) (H r η m b : ℝ) (S : List (ℝ × ℝ)) : Prop where
  ordered : S.Pairwise (fun c d => c.1+H ≤ d.1)
  bounds : ∀ c ∈ S, 0 ≤ c.1 ∧ c.1+H ≤ m ∧ r ≤ c.2 ∧ c.2 ≤ H ∧ c.1+c.2 ≤ b
  linear : ∀ c ∈ S, ∀ x ∈ Icc c.1 (c.1+H), |intervalSecantError f c.1 H x| ≤ η^2*H

structure StructuredProfilePieces (f : ℝ → ℝ) (r θ s b : ℝ) (S : List (ℝ × ℝ)) : Prop where
  ordered : S.Pairwise (fun c d => c.1+c.2 ≤ d.1)
  bounds : ∀ c ∈ S, 0 ≤ c.1 ∧ c.1+c.2 ≤ b ∧ r ≤ c.2
  alternatives : ∀ c ∈ S,
    (s ≤ intervalSecantSlope f c.1 c.2 ∧
      ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ θ*c.2) ∨
    (intervalSecantSlope f c.1 c.2 = s ∧
      ∀ x ∈ Icc c.1 (c.1+c.2), -θ*c.2 ≤ intervalSecantError f c.1 c.2 x)

theorem ProfileCellFamily.actual_ordered {f : ℝ → ℝ} {H r η m b : ℝ}
    {S : List (ℝ × ℝ)} (hF : ProfileCellFamily f H r η m b S) :
    S.Pairwise (fun c d => c.1+c.2 ≤ d.1) := by
  apply hF.ordered.imp_of_mem
  intro c d hc _ hcd
  exact (add_le_add le_rfl (hF.bounds c hc).2.2.2.1).trans hcd

theorem ProfileCellFamily.clip {f : ℝ → ℝ} {H r η m b u : ℝ}
    {S : List (ℝ × ℝ)} (hF : ProfileCellFamily f H r η m b S) :
    ProfileCellFamily f H r η m u (clipProfilePrefix u r S) := by
  refine ⟨clipProfilePrefix_ordered hF.ordered (fun c hc => (hF.bounds c hc).2.2.1),?_,?_⟩
  · intro d hd
    obtain ⟨c,hc,he,hmin,hsize,hend⟩ := clipProfilePrefix_spec
      (fun c hc => (hF.bounds c hc).2.2.1) hd
    have hb := hF.bounds c hc
    exact ⟨by simpa only [he] using hb.1,by simpa only [he] using hb.2.1,
      hmin,hsize.trans hb.2.2.2.1,hend⟩
  · intro d hd x hx
    obtain ⟨c,hc,he,_⟩ := clipProfilePrefix_spec (fun c hc => (hF.bounds c hc).2.2.1) hd
    simpa only [he] using hF.linear c hc x (by simpa only [he] using hx)

theorem ProfileCellFamily.active_linear {f : ℝ → ℝ} {H η m b : ℝ}
    {S : List (ℝ × ℝ)} (hη : 0 < η) (hH : 0 < H)
    (hF : ProfileCellFamily f H (η*H) η m b S) {c : ℝ × ℝ} (hc : c ∈ S) :
    ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ (2*η)*c.2 := by
  have hb := hF.bounds c hc
  have hcpos : 0 < c.2 := lt_of_lt_of_le (mul_pos hη hH) hb.2.2.1
  exact fun x hx => linear_interval_restrict_proportion hcpos hb.2.2.2.1 hη hb.2.2.1
    (hF.linear c hc) hx

theorem StructuredProfilePieces.nil (f : ℝ → ℝ) (r θ s b : ℝ) :
    StructuredProfilePieces f r θ s b [] := by
  constructor <;> simp

theorem StructuredProfilePieces.append_interval {f : ℝ → ℝ} {r θ s a b : ℝ}
    {S : List (ℝ × ℝ)} (hS : StructuredProfilePieces f r θ s a S) (c : ℝ × ℝ)
    (hc0 : a ≤ c.1) (hcb : c.1+c.2 ≤ b) (hcr : r ≤ c.2) (hca : 0 ≤ c.1)
    (halt : (s ≤ intervalSecantSlope f c.1 c.2 ∧
      ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ θ*c.2) ∨
    (intervalSecantSlope f c.1 c.2 = s ∧
      ∀ x ∈ Icc c.1 (c.1+c.2), -θ*c.2 ≤ intervalSecantError f c.1 c.2 x))
    (hcpos : 0 ≤ c.2) : StructuredProfilePieces f r θ s b (S++[c]) := by
  constructor
  · rw [List.pairwise_append]
    refine ⟨hS.ordered,by simp,?_⟩
    intro d hd e he
    have hec : e = c := by simpa only [List.mem_singleton] using he
    subst e
    exact (hS.bounds d hd).2.1.trans hc0
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · have hb := hS.bounds d hd
      exact ⟨hb.1,hb.2.1.trans (by linarith),hb.2.2⟩
    · have he : d = c := by simpa only [List.mem_singleton] using hd
      subst d
      exact ⟨hca,hcb,hcr⟩
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hS.alternatives d hd
    · have he : d = c := by simpa only [List.mem_singleton] using hd
      subst d
      exact halt

end Falconer

end OAI
