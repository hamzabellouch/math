import OAI.GroupTheory.Hyperbolic.BasedWords

namespace OAI

namespace Release075.MarkedLineData
attribute [local instance] Classical.propDecidable Classical.decEq
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)

theorem presentation_finiteOrder_eq_one (g : (d.presentation hr).GroupType)
    (hg : IsOfFinOrder g) : g = 1 := by
  let P := d.presentation hr
  let H := Subgroup.zpowers g
  let : Finite H := hg.finite_zpowers
  let : Fintype H := Fintype.ofFinite H
  let t : H := ⟨g,Subgroup.mem_zpowers g⟩
  have ht : ∀ x : H, x ∈ Subgroup.zpowers t := by
    intro x
    obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp x.property
    exact Subgroup.mem_zpowers_iff.mpr ⟨n,Subtype.ext hn⟩
  obtain ⟨w,hw⟩ := P.exists_lifted_path g
  let W := P.powerWord g w (orderOf g)
  have hW : WordPath P.liftedFlip P.liftedTarget (.o,1) (.o,1) W := by
    simpa only [pow_orderOf_eq_one] using P.powerWord_typed g hw (orderOf g)
  obtain ⟨D⟩ := P.lifted_closed_fillable hW
  have hD : D.full.AllTriangles := D.full_triangular
  have hrot : W.map (P.shiftEdge g) = W.rotate w.length :=
    P.powerWord_shift_rotate g w hg.orderOf_pos (pow_orderOf_eq_one g)
  have hinv : chainShift g D.full.faceChain = D.full.faceChain := by
    have hu := d.fullChain_unique hr (BlockPresentation.WordPath.shift P hW g)
      (D.full.shift g) ((D.full.rotate w.length).reword hrot.symm)
      (D.full.allTriangles_shift hD g)
      ((D.full.rotate w.length).allTriangles_reword
        (D.full.allTriangles_rotate hD w.length) hrot.symm)
    simpa only [FullFilling.faceChain_shift,FullFilling.faceChain_reword,
      FullFilling.faceChain_rotate] using hu
  apply FreeChain.cyclic_chain_obstruction H t ht P.boundary₁ P.boundary₂
    (fun h c => P.boundary₁_shift h c) (fun h c => P.boundary₂_shift h c)
    P.boundary₁_boundary₂ P.augmentation_boundary₁
    (Finsupp.single (.o,1) 1) (by simp) (P.wordChain w) _ D.full.faceChain _ hinv
  · simpa only [chainShift_single,one_mul,mul_one] using P.boundary₁_wordChain hw
  · exact (D.full.boundary₂_faceChain hD).trans (P.powerWord_chain_norm g hg w)

theorem presentation_torsionFree : TorsionFree (d.presentation hr).GroupType := by
  intro g n hn hg
  exact d.presentation_finiteOrder_eq_one hr g (isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,hg⟩)

end Release075.MarkedLineData

end OAI
