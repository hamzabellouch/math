import Mathlib

namespace OAI

/-! Choose disjoint crossing neighborhoods inside prescribed open sets,
avoiding every curve that does not participate in that crossing. -/
noncomputable section
open Set
namespace ClosedSurfaceR4
variable {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Fintype ι] [Fintype κ]

theorem finite_crossing_neighborhoods (x : ι → X) (hx : Function.Injective x)
    (left right : ι → κ) (C : κ → Set X) (hC : ∀ k, IsClosed (C k))
    (honly : ∀ i k, x i ∈ C k → k = left i ∨ k = right i)
    (V : ι → Set X) (hV : ∀ i, IsOpen (V i)) (hxV : ∀ i, x i ∈ V i) :
    ∃ O : ι → Set X, (∀ i, IsOpen (O i)) ∧ (∀ i, x i ∈ O i) ∧
      (∀ i, O i ⊆ V i) ∧ Pairwise (fun i j => Disjoint (O i) (O j)) ∧
      ∀ i k y, y ∈ O i → y ∈ C k → k = left i ∨ k = right i := by
  classical
  obtain ⟨W,hW,hdisj⟩ := (Set.finite_range x).t2_separation
  let O : ι → Set X := fun i => W (x i) ∩ V i ∩
    ⋂ k : κ, if k = left i ∨ k = right i then univ else (C k)ᶜ
  have hopen (i : ι) : IsOpen (O i) := by
    apply ((hW (x i)).2.inter (hV i)).inter
    apply isOpen_iInter_of_finite
    intro k
    split_ifs
    · exact isOpen_univ
    · exact (hC k).isOpen_compl
  have hmem (i : ι) : x i ∈ O i := by
    refine ⟨⟨(hW (x i)).1,hxV i⟩,?_⟩
    apply mem_iInter.mpr
    intro k
    split_ifs with h
    · trivial
    · exact fun hc => h (honly i k hc)
  refine ⟨O,hopen,hmem,(fun i y hy => hy.1.2),?_,?_⟩
  · intro i j hij
    exact (hdisj (mem_range_self i) (mem_range_self j) (fun h => hij (hx h))).mono
      (fun y hy => hy.1.1) (fun y hy => hy.1.1)
  · intro i k y hy hyC
    by_contra h
    have hy' := mem_iInter.mp hy.2 k
    simp only [h,ite_false,mem_compl_iff] at hy'
    exact hy' hyC

end ClosedSurfaceR4

end

end OAI
