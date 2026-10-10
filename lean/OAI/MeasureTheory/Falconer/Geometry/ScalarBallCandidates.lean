import OAI.MeasureTheory.Falconer.Measures.ScalarProductBalls

namespace OAI

/-! Finite critical radii for maximizing scalar local density. -/
namespace Falconer

noncomputable def scalarBallCandidates (δ : ℝ) (E : Finset ℝ) : Finset (ℝ × ℝ) :=
  (E ×ˢ E).image (fun p => (p.1,max δ |p.2-p.1|)) ∪ E.image (fun x => (x,2))

noncomputable def scalarBallMass (E : Finset ℝ) (u r : ℝ) : ℝ :=
  ((E.filter fun x => |x-u| ≤ r).card : ℝ)

 theorem scalarBallCandidates_nonempty (δ : ℝ) {E : Finset ℝ} (hE : E.Nonempty) :
    (scalarBallCandidates δ E).Nonempty := by
  obtain ⟨x,hx⟩ := hE
  exact ⟨(x,2),Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩)⟩

 theorem scalarBallCandidate_bounds {δ : ℝ} (hδ : δ ≤ 1) (E : Finset ℝ)
    (hE : ∀ x ∈ E, |x| ≤ 1) {p : ℝ × ℝ} (hp : p ∈ scalarBallCandidates δ E) :
    p.1 ∈ E ∧ δ ≤ p.2 ∧ p.2 ≤ 2 := by
  rcases Finset.mem_union.mp hp with hp | hp
  · obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    refine ⟨hx,le_max_left _ _,max_le (hδ.trans (by norm_num)) ?_⟩
    exact (abs_sub y x).trans (by linarith [hE y hy,hE x hx])
  · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    exact ⟨hx,hδ.trans (by norm_num),le_rfl⟩

 theorem scalarBallMass_nonneg (E : Finset ℝ) (u r : ℝ) : 0 ≤ scalarBallMass E u r :=
  Nat.cast_nonneg _

 theorem scalarBallMass_at_two (E : Finset ℝ) (hE : ∀ x ∈ E, |x| ≤ 1)
    {x : ℝ} (hx : x ∈ E) : scalarBallMass E x 2 = (E.card : ℝ) := by
  have he : E.filter (fun y => |y-x| ≤ 2) = E := by
    apply Finset.filter_eq_self.mpr
    intro y hy
    exact (abs_sub y x).trans (by linarith [hE y hy,hE x hx])
  unfold scalarBallMass
  rw [he]

 theorem scalarBallMass_majorized_candidate {δ u r : ℝ} (hδ : 0 < δ) (hdr : δ ≤ r)
    (E : Finset ℝ) (hball : (E.filter fun x => |x-u| ≤ r).Nonempty) :
    ∃ p ∈ scalarBallCandidates δ E, p.2 ≤ 2*r ∧
      scalarBallMass E u r ≤ scalarBallMass E p.1 p.2 := by
  classical
  let F := E.filter fun x => |x-u| ≤ r
  obtain ⟨x,hx⟩ := hball
  obtain ⟨y,hy,hmax⟩ := F.exists_max_image (fun y => |y-x|) ⟨x,hx⟩
  have hxE := (Finset.mem_filter.mp hx).1
  have hyE := (Finset.mem_filter.mp hy).1
  have hrad : max δ |y-x| ≤ 2*r := by
    apply max_le
    · linarith
    · calc
        |y-x| ≤ |y-u|+|u-x| := abs_sub_le y u x
        _ ≤ r+r := add_le_add (Finset.mem_filter.mp hy).2
          (by simpa only [abs_sub_comm] using (Finset.mem_filter.mp hx).2)
        _ = _ := by ring
  refine ⟨(x,max δ |y-x|),Finset.mem_union_left _
    (Finset.mem_image.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hxE,hyE⟩,rfl⟩),hrad,?_⟩
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro z hz
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
    (hmax z hz).trans (le_max_right _ _)⟩

end Falconer

end OAI
