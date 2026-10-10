import OAI.MeasureTheory.Falconer.Geometry.ScalarGroupReverseGeometry

namespace OAI

/-! Bounded overlap when the fixed dense group is in the first
 coordinate. Coefficients in [1/3,1] preserve the vertical group spacing. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_group_reverse_projection_overlap {δ r η b z w : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hδr : δ ≤ r) (hrη : 10*r ≤ η)
    (hb0 : 1/3 ≤ b)
    (X Y : Finset ℝ) (j : ℤ) (hXgrid : ∀ x ∈ X, ⌊(x-z)/η⌋ = j)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ u ∈ U x, |u-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ v ∈ V y, |v-y| ≤ r) (I : Finset ℤ) :
    (∑ k ∈ I, (scalarCells δ
      ((X.biUnion U)+((scalarGridFiber η w Y k).biUnion V).image (fun c => b*c))).card) ≤
      17*(scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  let G := fun k : ℤ => scalarCells δ
    ((X.biUnion U)+((scalarGridFiber η w Y k).biUnion V).image (fun c => b*c))
  let Z := scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))
  have hsub : ∀ k ∈ I, G k ⊆ Z := by
    intro k _ q hq
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨a,ha,bc,hbc,rfl⟩ := Finset.mem_add.mp hs
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hbc
    obtain ⟨y,hy,hcy⟩ := Finset.mem_biUnion.mp hc
    exact Finset.mem_image.mpr ⟨a+b*c,Finset.add_mem_add ha
      (Finset.mem_image.mpr ⟨c,Finset.mem_biUnion.mpr ⟨y,(Finset.mem_filter.mp hy).1,hcy⟩,rfl⟩),rfl⟩
  apply finite_family_sum_card_le I Z G 17 hsub
  intro q _hq
  let l : ℤ := ⌊((q:ℝ)*(δ/b)-w-(1/b)*(z+(j:ℝ)*η))/η⌋
  have hcontain : I.filter (fun k => q ∈ G k) ⊆ Finset.Icc (l-8) (l+8) := by
    intro k hk
    obtain ⟨_,hqk⟩ := Finset.mem_filter.mp hk
    obtain ⟨s,hs,hsq⟩ := Finset.mem_image.mp hqk
    obtain ⟨a,ha,bc,hbc,hs⟩ := Finset.mem_add.mp hs
    obtain ⟨c,hc,hbc⟩ := Finset.mem_image.mp hbc
    obtain ⟨x,hx,hax⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨y,hy,hcy⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨hy,hyk⟩ := Finset.mem_filter.mp hy
    have hsum : s = a+b*c := by rw [← hbc] at hs; exact hs.symm
    have hqeq : ⌊(a+b*c)/δ⌋ = q := by rw [← hsum]; exact hsq
    exact scalar_group_reverse_index_near hη hδ hδr hrη hb0
      (hXgrid x hx) hyk (hU x hx a hax) (hV y hy c hcy) hqeq
  have hi : (Finset.Icc (l-8) (l+8)).card = 17 := by
    rw [Int.card_Icc]
    have he : l+8+1-(l-8) = (17:ℤ) := by omega
    rw [he]; rfl
  simpa only [G] using (Finset.card_le_card hcontain).trans_eq hi

end Falconer

end OAI
