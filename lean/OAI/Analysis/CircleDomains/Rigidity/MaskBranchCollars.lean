import OAI.Analysis.CircleDomains.Rigidity.ExteriorMaskReplacement
import OAI.Analysis.CircleDomains.Selection.PhysicalTerminals

namespace OAI

/-! Disjoint compact boundaries admit smaller closed collars. Coordinate
absence on a collar is realized by a constant exterior replacement;
present coordinates retain their given local real branches. -/

open Set Filter Function MeasureTheory Classical
open scoped Topology ContDiff

noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem exists_disjoint_closed_collars
    {I : Type*} [Finite I] (B : I → Set (ℝ × ℝ))
    (hB : ∀ i, IsCompact (B i)) (hdisj : Pairwise (Disjoint on B))
    (V : I → Set (ℝ × ℝ)) (hV : ∀ i, IsOpen (V i)) (hBV : ∀ i, B i ⊆ V i) :
    ∃ O C : I → Set (ℝ × ℝ),
      (∀ i, IsOpen (O i) ∧ B i ⊆ O i ∧ IsClosed (C i) ∧ O i ⊆ C i ∧ C i ⊆ V i) ∧
      Pairwise (Disjoint on C) := by
  have hn : Pairwise (Disjoint on fun i => 𝓝ˢ (B i)) := fun i j hij =>
    disjoint_nhdsSet_nhdsSet (hB i).isClosed (hB j).isClosed (hdisj hij)
  obtain ⟨W, hW, hWd⟩ := hn.exists_mem_filter_basis_of_disjoint (fun i => hasBasis_nhdsSet (B i))
  have hc (i : I) : ∃ O, IsOpen O ∧ B i ⊆ O ∧ closure O ⊆ W i ∩ V i :=
    (hB i).exists_isOpen_closure_subset
      (((hW i).1.inter (hV i)).mem_nhdsSet.mpr (subset_inter (hW i).2 (hBV i)))
  choose O hOo hBO hOsub using hc
  refine ⟨O, fun i => closure (O i), fun i =>
    ⟨hOo i, hBO i, isClosed_closure, subset_closure, (hOsub i).trans inter_subset_right⟩, ?_⟩
  exact fun i j hij => (hWd hij).mono
    ((hOsub i).trans inter_subset_left) ((hOsub j).trans inter_subset_left)

 theorem midpoint_notMem_shiftedLattice {h θ : ℝ} (hh : 0 < h) :
    θ + h / 2 ∉ shiftedLattice h θ := by
  rintro ⟨k, hk⟩
  have heq : (k : ℝ) = 1 / 2 := by nlinarith
  have hk0 : (0 : ℤ) < k := by exact_mod_cast (show (0 : ℝ) < (k : ℝ) by rw [heq]; norm_num)
  have hk1 : k < (1 : ℤ) := by exact_mod_cast (show (k : ℝ) < 1 by rw [heq]; norm_num)
  omega

 theorem exists_mask_branch_collars
    {I : Type*} [Fintype I] {n : ℕ}
    (B : I → Set (ℝ × ℝ)) (hB : ∀ i, IsCompact (B i))
    (hdisj : Pairwise (Disjoint on B))
    (V : I → Set (ℝ × ℝ)) (hV : ∀ i, IsOpen (V i)) (hBV : ∀ i, B i ⊆ V i)
    {K : Set (ℝ × ℝ)} (hVK : ∀ i, Disjoint (V i) K)
    (M : Fin n → Set (ℝ × ℝ)) (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (present : I → Fin n → Prop)
    (habsent : ∀ i l, ¬present i l → Disjoint (V i) (M l))
    (v : I → Fin n → (ℝ × ℝ) → ℝ)
    (hv : ∀ i l, present i l → ContDiffOn ℝ ∞ (v i l) (V i))
    (hproj : ∀ i l, present i l → ∀ x ∈ V i, (v i l x : UnitAddCircle) = f l x)
    {h : ℝ} (hh : 0 < h) (θ : Fin n → ℝ)
    (active : I → Fin n)
    (havoid : ∀ i l, present i l → l ≠ active i →
      Disjoint (v i l '' B i) (shiftedLattice h (θ l))) :
    ∃ (O : I → Set (ℝ × ℝ)) (W : Fin n → Set (ℝ × ℝ))
      (u : I → Fin n → (ℝ × ℝ) → ℝ),
      (∀ i, IsOpen (O i) ∧ B i ⊆ O i ∧ O i ⊆ V i) ∧
      (∀ l, IsClosed (W l) ∧ Disjoint (W l) (M l) ∧ Disjoint (W l) K) ∧
      (∀ i l, ContDiffOn ℝ ∞ (u i l) (O i)) ∧
      (∀ i l x, x ∈ O i → (u i l x : UnitAddCircle) =
        exteriorMaskReplacement (W l) ((θ l + h / 2 : ℝ) : UnitAddCircle) (f l) x) ∧
      (∀ i l, l ≠ active i → Disjoint (u i l '' B i) (shiftedLattice h (θ l))) ∧
      (∀ i l, present i l → EqOn (u i l) (v i l) (O i)) := by
  obtain ⟨O, C, hC, hCd⟩ := exists_disjoint_closed_collars B hB hdisj V hV hBV
  let W : Fin n → Set (ℝ × ℝ) := fun l => ⋃ i : {i // ¬present i l}, C i
  let u : I → Fin n → (ℝ × ℝ) → ℝ := fun i l =>
    if present i l then v i l else fun _ => θ l + h / 2
  have hWM (l : Fin n) : Disjoint (W l) (M l) := by
    apply Set.disjoint_left.mpr
    rintro x hx hm
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (habsent i l i.property) ((hC i).2.2.2.2 hi) hm
  have hWK (l : Fin n) : Disjoint (W l) K := by
    apply Set.disjoint_left.mpr
    rintro x hx hk
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact Set.disjoint_left.mp (hVK i) ((hC i).2.2.2.2 hi) hk
  have hpW (i : I) (l : Fin n) (hi : present i l) {x} (hx : x ∈ O i) : x ∉ W l := by
    intro hw
    obtain ⟨j, hj⟩ := mem_iUnion.mp hw
    have hne : i ≠ j.val := fun heq => j.property (heq ▸ hi)
    exact Set.disjoint_left.mp (hCd hne) ((hC i).2.2.2.1 hx) hj
  refine ⟨O, W, u, fun i => ⟨(hC i).1, (hC i).2.1,
    ((hC i).2.2.2.1).trans (hC i).2.2.2.2⟩,
    fun l => ⟨isClosed_iUnion_of_finite fun i => (hC i).2.2.1, hWM l, hWK l⟩, ?_, ?_, ?_, ?_⟩
  · intro i l
    by_cases hi : present i l
    · simpa only [u, ite_eq_left hi] using (hv i l hi).mono
        (((hC i).2.2.2.1).trans (hC i).2.2.2.2)
    · simp only [u, ite_eq_right hi]
      exact contDiffOn_const
  · intro i l x hx
    by_cases hi : present i l
    · rw [show u i l x = v i l x by simp only [u, ite_eq_left hi]]
      rw [exteriorMaskReplacement, piecewise_eq_of_notMem _ _ _ (hpW i l hi hx)]
      exact hproj i l hi x (((hC i).2.2.2.1).trans (hC i).2.2.2.2 hx)
    · have hxW : x ∈ W l := mem_iUnion.mpr ⟨⟨i, hi⟩, (hC i).2.2.2.1 hx⟩
      simp only [u, ite_eq_right hi, exteriorMaskReplacement, piecewise_eq_of_mem _ _ _ hxW]
  · intro i l hla
    by_cases hi : present i l
    · simpa only [u, ite_eq_left hi] using havoid i l hi hla
    · apply Set.disjoint_left.mpr
      rintro r ⟨x, _, rfl⟩ hr
      exact midpoint_notMem_shiftedLattice hh (by simpa only [u, ite_eq_right hi] using hr)
  · intro i l hi x _
    simp only [u, ite_eq_left hi]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
