import OAI.Geometry.SurfaceImmersion.Geometry.PreferredNormalFromCover

namespace OAI

/-! Strict normal conditions on the disk boundary determine an open collar
that works simultaneously for every later curve. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4
variable {M κ : Type*} [TopologicalSpace M] [Fintype κ]

lemma normal_boundary_collar {D U V : Set M} (hD : IsOpen D) (hU : IsOpen U) (hV : IsOpen V)
    (hDU : closure D ⊆ U) (hDV : Dᶜ ⊆ V)
    {a b : M → Space} (ha : ContinuousOn a U) (hb : ContinuousOn b V)
    (hne : ∀ p ∈ frontier D, b p ≠ -a p)
    (C : κ → Set M) (hC : ∀ k, IsClosed (C k)) (B : κ → M → Space)
    (hB : ∀ k, ContinuousOn (B k) (U ∩ V))
    (hpositive : ∀ k p, p ∈ C k → p ∈ frontier D →
      0 < inner ℝ (B k p) (a p) ∧ 0 < inner ℝ (B k p) (b p)) :
    ∃ W : Set M, IsOpen W ∧ frontier D ⊆ W ∧ W ⊆ U ∩ V ∧
      (∀ p ∈ W, b p ≠ -a p) ∧
      ∀ k p, p ∈ C k → p ∈ W →
        0 < inner ℝ (B k p) (a p) ∧ 0 < inner ℝ (B k p) (b p) := by
  classical
  have hfUV : frontier D ⊆ U ∩ V := by
    intro p hp
    refine ⟨hDU (frontier_subset_closure hp),hDV ?_⟩
    change p ∉ D
    simpa only [hD.interior_eq] using hp.2
  let Ω := U ∩ V
  have hΩ : IsOpen Ω := hU.inter hV
  let O := Ω ∩ (fun p => b p-(-a p)) ⁻¹' ({0} : Set Space)ᶜ
  have hO : IsOpen O := ((hb.mono inter_subset_right).sub
    (ha.mono inter_subset_left).neg).isOpen_inter_preimage hΩ isClosed_singleton.isOpen_compl
  let P : κ → Set M := fun k => Ω ∩
    (fun p => (inner ℝ (B k p) (a p),inner ℝ (B k p) (b p))) ⁻¹' (Ioi 0 ×ˢ Ioi 0)
  have hP (k : κ) : IsOpen (P k) :=
    (((hB k).inner (ha.mono inter_subset_left)).prodMk
      ((hB k).inner (hb.mono inter_subset_right))).isOpen_inter_preimage hΩ
      (isOpen_Ioi.prod isOpen_Ioi)
  let W := O ∩ ⋂ k : κ, (C k)ᶜ ∪ P k
  refine ⟨W,hO.inter (isOpen_iInter_of_finite (fun k => (hC k).isOpen_compl.union (hP k))),?_,?_,?_,?_⟩
  · intro p hp
    refine ⟨⟨hfUV hp,sub_ne_zero.mpr (hne p hp)⟩,mem_iInter.mpr ?_⟩
    intro k
    by_cases hpk : p ∈ C k
    · exact Or.inr ⟨hfUV hp,hpositive k p hpk hp⟩
    · exact Or.inl hpk
  · exact fun _ hp => hp.1.1
  · intro p hp
    exact sub_ne_zero.mp hp.1.2
  · intro k p hpC hpW
    exact (Or.resolve_left (mem_iInter.mp hpW.2 k) (not_not.mpr hpC)).2

end ClosedSurfaceR4

end

end OAI
