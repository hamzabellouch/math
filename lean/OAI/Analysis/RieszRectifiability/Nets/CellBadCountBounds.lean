import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellChainComposition

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

def cellBadCountBound {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (N : ℕ) (x : Ambient d) : Prop :=
  ∀ F : Finset (SupportCellDescendant μ R hR k z),
    (∀ i ∈ F, Bad i ∧ q.depth ≤ i.depth ∧ i.cell ⊆ q.cell ∧ x ∈ i.cell) → F.card ≤ N

theorem cellBadCountBound_mono_subcell {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q w : SupportCellDescendant μ R hR k z) (hdepth : q.depth ≤ w.depth)
    (hsub : w.cell ⊆ q.cell) (N : ℕ) (x : Ambient d)
    (hcount : cellBadCountBound Bad q N x) : cellBadCountBound Bad w N x := by
  intro F hF
  exact hcount F (fun i hi =>
    ⟨(hF i hi).1, hdepth.trans (hF i hi).2.1, (hF i hi).2.2.1.trans hsub, (hF i hi).2.2.2⟩)

theorem cellBadCountBound_zero_forbids_bad_descendant
    {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q i : SupportCellDescendant μ R hR k z) (hdepth : q.depth ≤ i.depth)
    (hsub : i.cell ⊆ q.cell) (x : Ambient d) (hx : x ∈ i.cell)
    (hcount : cellBadCountBound Bad q 0 x) : ¬ Bad i := by
  classical
  intro hbad
  have h := hcount {i} (by
    intro j hj
    have heq : j = i := Finset.mem_singleton.mp hj
    subst j
    exact ⟨hbad, hdepth, hsub, hx⟩)
  norm_num at h

theorem cellBadCountBound_descend_past_bad
    {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q i w : SupportCellDescendant μ R hR k z)
    (hqi : q.depth ≤ i.depth) (hiq : i.cell ⊆ q.cell) (hbad : Bad i)
    (hiw : i.depth < w.depth) (hwi : w.cell ⊆ i.cell)
    (N : ℕ) (x : Ambient d) (hx : x ∈ w.cell)
    (hcount : cellBadCountBound Bad q (N + 1) x) : cellBadCountBound Bad w N x := by
  classical
  intro F hF
  have hnot : i ∉ F := by
    intro hi
    have h := (hF i hi).2.1
    omega
  have h := hcount (insert i F) (by
    intro j hj
    rcases Finset.mem_insert.mp hj with heq | hjF
    · subst j
      exact ⟨hbad, hqi, hiq, hwi hx⟩
    · have hj := hF j hjF
      exact ⟨hj.1, hqi.trans (hiw.le.trans hj.2.1),
        hj.2.2.1.trans (hwi.trans hiq), hj.2.2.2⟩)
  rw [Finset.card_insert_of_notMem hnot] at h
  omega

theorem cellBadCountBound_of_subtype_incidence_bound
    {d : ℕ} {μ : Measure (Ambient d)} {R : ℝ} {hR : 0 < R}
    {k : ℕ} {z : (supportLatticeNets μ R hR k).points}
    (Bad : SupportCellDescendant μ R hR k z → Prop)
    (q : SupportCellDescendant μ R hR k z) (N : ℕ) (x : Ambient d)
    (hcount : ∀ F : Finset {i : SupportCellDescendant μ R hR k z // Bad i},
      (∀ i ∈ F, x ∈ i.val.cell) → F.card ≤ N) : cellBadCountBound Bad q N x := by
  classical
  intro F hF
  let e : F ↪ {i : SupportCellDescendant μ R hR k z // Bad i} :=
    ⟨fun i => ⟨i.val, (hF i.val i.property).1⟩,
      fun i j h => by
        apply Subtype.ext
        exact congrArg (fun a : {i : SupportCellDescendant μ R hR k z // Bad i} => a.val) h⟩
  have h := hcount (F.attach.map e) (by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
    exact (hF j.val j.property).2.2.2)
  simpa only [Finset.card_map, Finset.card_attach] using! h

end

end RieszRectifiability

end OAI
