import OAI.Analysis.CircleDomains.Modulus.OrderedHolePayment

namespace OAI

/-!
# Payment through an unordered finite set of holes

A finite set of disjoint closed intervals is sorted inside Lean; the
variation estimate is then applied to its actual complementary gaps.
-/

open Set Function Filter MeasureTheory
open scoped Topology

namespace CircleDomainRigidity

theorem line_payment_of_disjoint_holes
    {a b : ℝ} (hab : a < b) (F : Finset (ℝ × ℝ))
    (hinside : ∀ z ∈ F, a < z.1 ∧ z.1 ≤ z.2 ∧ z.2 < b)
    (hdisj : (↑F : Set (ℝ × ℝ)).PairwiseDisjoint (fun z => Icc z.1 z.2))
    {f d ρ : ℝ → ℝ} (A : ℝ × ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b ∩ (⋃ z ∈ F, Icc z.1 z.2)ᶜ, HasDerivAt f (d x) x)
    (hcd : ContinuousOn d (Icc a b ∩ (⋃ z ∈ F, Icc z.1 z.2)ᶜ))
    (hρ : Integrable ρ) (hpos : ∀ x, 0 ≤ ρ x)
    (hdom : ∀ x ∈ Icc a b ∩ (⋃ z ∈ F, Icc z.1 z.2)ᶜ, |d x| ≤ ρ x)
    (ha : ContinuousAt f a) (hb : ContinuousAt f b) (hzero : f a = 0) (hone : f b = 1)
    (hjump : ∀ z ∈ F, ∀ u v,
      MapClusterPt u (𝓝[Icc a b ∩ (⋃ w ∈ F, Icc w.1 w.2)ᶜ] z.1) f →
      MapClusterPt v (𝓝[Icc a b ∩ (⋃ w ∈ F, Icc w.1 w.2)ᶜ] z.2) f → |v - u| ≤ A z) :
    1 ≤ (∫ x, ρ x) + ∑ z ∈ F, A z := by
  classical
  let H := F.orderEmbOfFin (α := ℝ ×ₗ ℝ) rfl
  have hmem (i : Fin F.card) : H i ∈ F := F.orderEmbOfFin_mem (α := ℝ ×ₗ ℝ) rfl i
  have honto (z : ℝ × ℝ) (hz : z ∈ F) : ∃ i : Fin F.card, H i = z := by
    let z' : (F : Finset (ℝ ×ₗ ℝ)) := ⟨z, hz⟩
    refine ⟨(F.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).symm z', ?_⟩
    exact congrArg Subtype.val ((F.orderIsoOfFin (α := ℝ ×ₗ ℝ) rfl).apply_symm_apply z')
  have hcover : (⋃ i, Icc (H i).1 (H i).2) = ⋃ z ∈ F, Icc z.1 z.2 := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨H i, mem_iUnion.mpr ⟨hmem i, hi⟩⟩
    · intro hx
      obtain ⟨z, hz, hx⟩ := mem_iUnion₂.mp hx
      obtain ⟨i, rfl⟩ := honto z hz
      exact mem_iUnion.mpr ⟨i, hx⟩
  have h := line_payment_of_ordered_holes hab H (fun i => hinside _ (hmem i))
    (sorted_holes_separated F (fun z hz => (hinside z hz).2.1) hdisj)
    (fun i => A (H i))
    (by simpa only [hcover] using hd) (by simpa only [hcover] using hcd) hρ hpos
    (by simpa only [hcover] using hdom) ha hb hzero hone
    (by
      intro i u v hu hv
      apply hjump (H i) (hmem i) u v
      · simpa only [hcover] using hu
      · simpa only [hcover] using hv)
  have hsum : (∑ i : Fin F.card, A (H i)) = ∑ z ∈ F, A z := by
    apply Finset.sum_bij (fun i _ => H i)
    · exact fun i _ => hmem i
    · exact fun i _ j _ hij => H.injective hij
    · intro z hz
      obtain ⟨i, hi⟩ := honto z hz
      exact ⟨i, Finset.mem_univ _, hi⟩
    · exact fun _ _ => rfl
  exact h.trans_eq (congrArg (fun t => (∫ x, ρ x) + t) hsum)

end CircleDomainRigidity

end OAI
