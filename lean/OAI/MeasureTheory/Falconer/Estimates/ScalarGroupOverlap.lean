import OAI.MeasureTheory.Falconer.Geometry.ScalarGroupGeometry

namespace OAI

/-! A fixed nine-fold overlap bound for all projected horizontal groups.
 The number of children and occupied grid cells is unrestricted. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_group_projection_overlap {δ r η b z w : ℝ} (hδ : 0 < δ)
    (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (X Y : Finset ℝ) (j : ℤ) (hYgrid : ∀ y ∈ Y, ⌊(y-w)/η⌋ = j)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r) (I : Finset ℤ) :
    (∑ k ∈ I, (scalarCells δ
      (((scalarGridFiber η z X k).biUnion U)+(Y.biUnion V).image (fun c => b*c))).card) ≤
      9*(scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  let G := fun k : ℤ => scalarCells δ
    (((scalarGridFiber η z X k).biUnion U)+(Y.biUnion V).image (fun c => b*c))
  let Z := scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))
  have hsub : ∀ k ∈ I, G k ⊆ Z := by
    intro k _ q hq
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨a,ha,c,hc,rfl⟩ := Finset.mem_add.mp hs
    obtain ⟨x,hx,hax⟩ := Finset.mem_biUnion.mp ha
    refine Finset.mem_image.mpr ⟨a+c,Finset.add_mem_add ?_ hc,rfl⟩
    exact Finset.mem_biUnion.mpr ⟨x,(Finset.mem_filter.mp hx).1,hax⟩
  apply finite_family_sum_card_le I Z G 9 hsub
  intro q _hq
  let l : ℤ := ⌊((q:ℝ)*δ-z-b*(w+(j:ℝ)*η))/η⌋
  have hcontain : I.filter (fun k => q ∈ G k) ⊆ Finset.Icc (l-4) (l+4) := by
    intro k hk
    obtain ⟨_,hqk⟩ := Finset.mem_filter.mp hk
    obtain ⟨s,hs,hsq⟩ := Finset.mem_image.mp hqk
    obtain ⟨a,ha,bc,hbc,hs⟩ := Finset.mem_add.mp hs
    obtain ⟨c,hc,hbc⟩ := Finset.mem_image.mp hbc
    obtain ⟨x,hx,hax⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨y,hy,hcy⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨hx,hxk⟩ := Finset.mem_filter.mp hx
    have hsum : s = a+b*c := by rw [← hbc] at hs; exact hs.symm
    have hqeq : ⌊(a+b*c)/δ⌋ = q := by rw [← hsum]; exact hsq
    exact scalar_group_index_near hη hδ hδr hrη hb0 hb1 hxk
      (hYgrid y hy) (hU x hx a hax) (hV y hy c hcy) hqeq
  have hi : (Finset.Icc (l-4) (l+4)).card = 9 := by
    rw [Int.card_Icc]
    have he : l+4+1-(l-4) = (9:ℤ) := by omega
    rw [he]; rfl
  simpa only [G] using (Finset.card_le_card hcontain).trans_eq hi

end Falconer

end OAI
