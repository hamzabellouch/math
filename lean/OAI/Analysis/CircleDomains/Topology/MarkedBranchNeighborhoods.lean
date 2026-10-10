import OAI.Analysis.CircleDomains.Selection.MeanMarkedBranchBands

namespace OAI

/-! Common neighborhoods of marked points retain the very branches used
to define their band endpoints. The local limiting oscillation is then
exactly the selected width, including after intersecting all patches. -/

open Set Function Filter Classical
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem exists_marked_branch_neighborhoods
    {n : ℕ} {S : Type*} (L : Fin n → Type*)
    (U : Set Sphere) (M : Fin n → Set Sphere) (hM : ∀ l, IsClosed (M l))
    (hboundary : ∀ l, frontier (M l) ⊆ U)
    (σ : S → Sphere) (hσ : ∀ s, σ s ∉ U) (singular : Fin n → Sphere)
    (P : ∀ l, L l → Set Sphere) (hP : ∀ l i, IsOpen (P l i))
    (v : ∀ l, L l → Sphere → ℝ) (B : ∀ l, L l → ℝ)
    (hbound : ∀ l i x, |v l i x| ≤ B l i)
    (a b : Fin n → S → ℝ)
    (hband : ∀ s l, σ s ∈ M l → σ s ≠ singular l → ∃ i : L l,
      σ s ∈ P l i ∧ a l s = liminf (v l i) (𝓝[U] (σ s)) ∧
        b l s = limsup (v l i) (𝓝[U] (σ s))) :
    ∃ (N : S → Set Sphere) (u : S → Fin n → Sphere → ℝ) (C : S → Fin n → ℝ),
      (∀ s, IsOpen (N s) ∧ σ s ∈ N s) ∧
      (∀ s l, σ s ∈ M l → N s ⊆ interior (M l)) ∧
      (∀ s l, σ s ∉ M l → Disjoint (N s) (M l)) ∧
      (∀ s l x, |u s l x| ≤ C s l) ∧
      (∀ s l, σ s ∈ M l → σ s ≠ singular l → ∃ i : L l,
        N s ⊆ P l i ∧ u s l = v l i) ∧
      ∀ s l, σ s ∈ M l → σ s ≠ singular l →
        limsup (u s l) (𝓝[U ∩ N s] (σ s)) -
          liminf (u s l) (𝓝[U ∩ N s] (σ s)) = b l s - a l s := by
  let A (s : S) (l : Fin n) : Prop := σ s ∈ M l ∧ σ s ≠ singular l
  let idx (s : S) (l : Fin n) (h : A s l) : L l := Classical.choose (hband s l h.1 h.2)
  have hi (s : S) (l : Fin n) (h : A s l) :
      σ s ∈ P l (idx s l h) ∧ a l s = liminf (v l (idx s l h)) (𝓝[U] (σ s)) ∧
        b l s = limsup (v l (idx s l h)) (𝓝[U] (σ s)) := Classical.choose_spec (hband s l h.1 h.2)
  let V (s : S) (l : Fin n) : Set Sphere :=
    if h : A s l then interior (M l) ∩ P l (idx s l h)
    else if σ s ∈ M l then interior (M l) else (M l)ᶜ
  let N (s : S) : Set Sphere := ⋂ l, V s l
  let u (s : S) (l : Fin n) : Sphere → ℝ :=
    if h : A s l then v l (idx s l h) else fun _ => 0
  let C (s : S) (l : Fin n) : ℝ := if h : A s l then B l (idx s l h) else 0
  have hint (s : S) (l : Fin n) (hs : σ s ∈ M l) : σ s ∈ interior (M l) :=
    (mem_interior_iff_notMem_frontier hs).mpr (fun hb => hσ s (hboundary l hb))
  have hV (s : S) (l : Fin n) : IsOpen (V s l) ∧ σ s ∈ V s l := by
    by_cases h : A s l
    · simp only [V, dite_eq_left h]
      exact ⟨isOpen_interior.inter (hP l _), hint s l h.1, (hi s l h).1⟩
    · simp only [V, dite_eq_right h]
      by_cases hm : σ s ∈ M l
      · simp only [ite_eq_left hm]
        exact ⟨isOpen_interior, hint s l hm⟩
      · simp only [ite_eq_right hm]
        exact ⟨(hM l).isOpen_compl, hm⟩
  have hN (s : S) : IsOpen (N s) ∧ σ s ∈ N s :=
    ⟨isOpen_iInter_of_finite (fun l => (hV s l).1), mem_iInter.mpr (fun l => (hV s l).2)⟩
  have hsub (s : S) (l : Fin n) : N s ⊆ V s l := iInter_subset (V s) l
  refine ⟨N, u, C, hN, ?_, ?_, ?_, ?_, ?_⟩
  · intro s l hm x hx
    have hxV := hsub s l hx
    by_cases h : A s l
    · have hx' : x ∈ interior (M l) ∩ P l (idx s l h) := by
        simpa only [V, dite_eq_left h] using hxV
      exact hx'.1
    · simpa only [V, dite_eq_right h, ite_eq_left hm] using hxV
  · intro s l hm
    have ha : ¬A s l := fun h => hm h.1
    have hs : N s ⊆ (M l)ᶜ := by
      simpa only [V, dite_eq_right ha, ite_eq_right hm] using hsub s l
    exact Set.disjoint_left.mpr (fun _ hx hxm => hs hx hxm)
  · intro s l x
    by_cases h : A s l
    · simpa only [u, C, dite_eq_left h] using hbound l (idx s l h) x
    · simp only [u, C, dite_eq_right h, abs_zero, le_refl]
  · intro s l hm hb
    let h : A s l := ⟨hm, hb⟩
    refine ⟨idx s l h, ?_, by simp only [u, dite_eq_left h]⟩
    intro x hx
    have hxV : x ∈ interior (M l) ∩ P l (idx s l h) := by
      simpa only [V, dite_eq_left h] using hsub s l hx
    exact hxV.2
  · intro s l hm hb
    let h : A s l := ⟨hm, hb⟩
    have hn : 𝓝[U ∩ N s] (σ s) = 𝓝[U] (σ s) :=
      nhdsWithin_inter_of_mem' (nhdsWithin_le_nhds ((hN s).1.mem_nhds (hN s).2))
    rw [hn]
    simp only [u, dite_eq_left h]
    rw [← (hi s l h).2.1, ← (hi s l h).2.2]

end CircleDomainRigidity

end

end OAI
