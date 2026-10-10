import OAI.Geometry.SurfaceImmersion.Primitive.ConstructedSurfaceLoop

namespace OAI

/-! A finite family of closed regular arcs supplies the local defining
functions needed to control angular derivatives away from its finite exceptions. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma finite_curve_local_definers {ι : Type*} [Fintype ι]
    (C V : ι → Set Base) (f : ι → Base → ℝ)
    (hC : ∀ i, IsClosed (C i)) (hV : ∀ i, IsOpen (V i))
    (hCV : ∀ i, C i ⊆ V i) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (V i))
    (hzero : ∀ i x, x ∈ C i → f i x = 0)
    {K P : Set Base} (hK : K ⊆ ⋃ i, C i)
    (hcross : ∀ i j, i ≠ j → C i ∩ C j ⊆ P)
    (hregular : ∀ i x, x ∈ K \ P → x ∈ C i → fderiv ℝ (f i) x dy ≠ 0) :
    ∀ p ∈ K \ P, ∃ N : Set Base, IsOpen N ∧ p ∈ N ∧
      ∃ g : Base → ℝ, ContDiffOn ℝ ∞ g N ∧ (∀ x ∈ K ∩ N, g x = 0) ∧
        fderiv ℝ g p dy ≠ 0 := by
  classical
  intro p hp
  obtain ⟨i,hi⟩ := mem_iUnion.mp (hK hp.1)
  let W : Set Base := ⋂ j, if j = i then univ else (C j)ᶜ
  have hW : IsOpen W := by
    apply isOpen_iInter_of_finite
    intro j
    split_ifs
    · exact isOpen_univ
    · exact (hC j).isOpen_compl
  have hpW : p ∈ W := by
    apply mem_iInter.mpr
    intro j
    by_cases hji : j = i
    · simp [hji]
    · simp only [hji,ite_false,mem_compl_iff]
      intro hj
      exact hp.2 (hcross i j (Ne.symm hji) ⟨hi,hj⟩)
  refine ⟨V i ∩ W,(hV i).inter hW,⟨hCV i hi,hpW⟩,f i,(hf i).mono inter_subset_left,?_,
    hregular i p hp hi⟩
  intro x hx
  obtain ⟨j,hj⟩ := mem_iUnion.mp (hK hx.1)
  have hji : j = i := by
    by_contra hne
    have havoid := mem_iInter.mp hx.2.2 j
    simp only [hne,ite_false,mem_compl_iff] at havoid
    exact havoid hj
  exact hzero i x (by simpa only [hji] using hj)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
