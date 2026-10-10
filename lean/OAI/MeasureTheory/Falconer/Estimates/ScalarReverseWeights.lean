import OAI.MeasureTheory.Falconer.Estimates.ScalarClusterWeights

namespace OAI

/-! The fallback weight when the dense group is in the first coordinate.
 A positive lower coefficient bound preserves the second-coordinate gaps. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_cluster_one_row {δ r μ b : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (hgap : 5*r < b*μ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (X Y : Finset ℝ) (x : ℝ) (hx : x ∈ X)
    (hY : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → μ ≤ |y-z|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ c ∈ V y, |c-y| ≤ r) :
    (∑ y ∈ Y, (scalarCells δ (U x+(V y).image (fun c => b*c))).card) ≤
      (scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  let G := fun y => scalarCells δ (U x+(V y).image (fun c => b*c))
  have hb : |b| ≤ 1 := by rwa [abs_of_nonneg hb0]
  have hd : (Y : Set ℝ).PairwiseDisjoint G := by
    intro y hy z hz hyz
    have hc : 5*r < |(x+b*y)-(x+b*z)| := by
      calc
        _ < b*μ := hgap
        _ ≤ b*|y-z| := mul_le_mul_of_nonneg_left (hY y hy z hz hyz) hb0
        _ = _ := by rw [show (x+b*y)-(x+b*z) = b*(y-z) by ring,abs_mul,abs_of_nonneg hb0]
    exact scalar_cells_disjoint_of_centers hδ hr hc _ _
      (scalar_cluster_sum_near hb _ _ hU (hV y hy))
      (scalar_cluster_sum_near hb _ _ hU (hV z hz))
  have hs : Y.biUnion G ⊆ scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c)) := by
    intro k hk
    obtain ⟨y,hy,hk⟩ := Finset.mem_biUnion.mp hk
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨a,ha,v,hv,rfl⟩ := Finset.mem_add.mp hs
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨a+b*c,Finset.add_mem_add
      (Finset.mem_biUnion.mpr ⟨x,hx,ha⟩)
      (Finset.mem_image.mpr ⟨c,Finset.mem_biUnion.mpr ⟨y,hy,hc⟩,rfl⟩),rfl⟩
  exact (Finset.card_biUnion hd).symm.trans_le (Finset.card_le_card hs)

 theorem scalar_cluster_reverse_fallback {δ r μ b : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (hgap : 5*r < b*μ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (X Y : Finset ℝ)
    (hY : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → μ ≤ |y-z|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ c ∈ V y, |c-y| ≤ r) :
    (∑ p ∈ X ×ˢ Y, (scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card) ≤
      X.card*(scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  rw [Finset.sum_product]
  calc
    _ ≤ ∑ _x ∈ X, (scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card :=
      Finset.sum_le_sum (fun x hx => scalar_cluster_one_row hδ hr hgap hb0 hb1 X Y x hx hY U V (hU x hx) hV)
    _ = _ := by simp

 theorem scalar_cluster_reverse_weighted_cells {δ r μ b : ℝ} (hδ : 0 < δ) (hr : δ ≤ r)
    (hgap : 5*r < b*μ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (B X Y : Finset ℝ) (hbB : b ∈ B) (hX : X.Nonempty)
    (hY : ∀ y ∈ Y, ∀ z ∈ Y, y ≠ z → μ ≤ |y-z|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ c ∈ V y, |c-y| ≤ r) :
    scalarCollisionWeight (X.card : ℝ) (scalarBadClusterCoefficients B X Y (5*r)) b *
      (∑ p ∈ X ×ˢ Y, ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ)) ≤
      ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
  by_cases hg : b ∈ scalarBadClusterCoefficients B X Y (5*r)
  · simp only [scalarCollisionWeight,ite_eq_left hg]
    have hs : (∑ p ∈ X ×ˢ Y, ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ)) ≤
        (X.card : ℝ)*((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
      exact_mod_cast scalar_cluster_reverse_fallback hδ hr hgap hb0 hb1 X Y hY U V hU hV
    have hn : 0 < (X.card : ℝ) := by exact_mod_cast hX.card_pos
    calc
      _ ≤ (X.card : ℝ)⁻¹*((X.card : ℝ)*
          ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)
      _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul]
  · simp only [scalarCollisionWeight,ite_eq_right hg,one_mul]
    have hb : |b| ≤ 1 := by rwa [abs_of_nonneg hb0]
    exact_mod_cast scalar_cluster_sums_cells hδ hr B X Y hbB hb hg U V hU hV

end Falconer

end OAI
