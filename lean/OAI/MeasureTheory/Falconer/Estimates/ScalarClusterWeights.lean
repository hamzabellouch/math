import OAI.MeasureTheory.Falconer.Estimates.ScalarClusterSums
import OAI.MeasureTheory.Falconer.Estimates.ScalarCorrelatedWeights

namespace OAI

/-! The one-level porous inequality, including a positive fallback weight
 for every coefficient. This permits later multiplication of the level
 weights even when their exceptional sets are correlated. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_cluster_one_column {δ r μ b : ℝ} (hδ : 0 < δ)
    (hr : δ ≤ r) (hgap : 5*r < μ) (hb : |b| ≤ 1)
    (X Y : Finset ℝ) (y : ℝ) (hy : y ∈ Y)
    (hX : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → μ ≤ |x-z|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ c ∈ V y, |c-y| ≤ r) :
    (∑ x ∈ X, (scalarCells δ (U x+(V y).image (fun c => b*c))).card) ≤
      (scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  have hg : b ∉ scalarBadClusterCoefficients {b} X {y} (5*r) := by
    intro hbad
    obtain ⟨_,p,hp,q,hq,hpq,he⟩ := Finset.mem_filter.mp hbad
    obtain ⟨hpx,hpy⟩ := Finset.mem_product.mp hp
    obtain ⟨hqx,hqy⟩ := Finset.mem_product.mp hq
    have hpy' : p.2 = y := Finset.mem_singleton.mp hpy
    have hqy' : q.2 = y := Finset.mem_singleton.mp hqy
    have hx : p.1 ≠ q.1 := by intro heq; exact hpq (Prod.ext heq (hpy'.trans hqy'.symm))
    have hh := hX p.1 hpx q.1 hqx hx
    have hid : (p.1+b*p.2)-(q.1+b*q.2) = p.1-q.1 := by rw [hpy',hqy']; ring
    rw [hid] at he
    linarith
  have hs := scalar_cluster_sums_cells hδ hr {b} X {y} (Finset.mem_singleton_self b)
    hb hg U V hU (fun z hz => by simpa only [Finset.mem_singleton.mp hz] using hV)
  simp only [Finset.sum_product,Finset.sum_singleton,Finset.singleton_biUnion] at hs
  apply hs.trans
  apply Finset.card_le_card
  apply Finset.image_subset_image
  apply Finset.add_subset_add (Finset.Subset.refl _)
  apply Finset.image_subset_image
  intro c hc
  exact Finset.mem_biUnion.mpr ⟨y,hy,hc⟩

 theorem scalar_cluster_fallback {δ r μ b : ℝ} (hδ : 0 < δ)
    (hr : δ ≤ r) (hgap : 5*r < μ) (hb : |b| ≤ 1)
    (X Y : Finset ℝ)
    (hX : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → μ ≤ |x-z|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ c ∈ V y, |c-y| ≤ r) :
    (∑ p ∈ X ×ˢ Y, (scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card) ≤
      Y.card*(scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card := by
  rw [Finset.sum_product,Finset.sum_comm]
  calc
    _ ≤ ∑ _y ∈ Y, (scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card :=
      Finset.sum_le_sum (fun y hy => scalar_cluster_one_column hδ hr hgap hb X Y y hy hX U V hU (hV y hy))
    _ = _ := by simp

 theorem scalar_cluster_weighted_cells {δ r μ b : ℝ} (hδ : 0 < δ)
    (hr : δ ≤ r) (hgap : 5*r < μ) (hb : |b| ≤ 1)
    (B X Y : Finset ℝ) (hbB : b ∈ B) (hY : Y.Nonempty)
    (hX : ∀ x ∈ X, ∀ z ∈ X, x ≠ z → μ ≤ |x-z|)
    (U V : ℝ → Finset ℝ)
    (hU : ∀ x ∈ X, ∀ a ∈ U x, |a-x| ≤ r)
    (hV : ∀ y ∈ Y, ∀ c ∈ V y, |c-y| ≤ r) :
    scalarCollisionWeight (Y.card : ℝ) (scalarBadClusterCoefficients B X Y (5*r)) b *
      (∑ p ∈ X ×ˢ Y, ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ)) ≤
      ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
  by_cases hg : b ∈ scalarBadClusterCoefficients B X Y (5*r)
  · simp only [scalarCollisionWeight,ite_eq_left hg]
    have hs : (∑ p ∈ X ×ˢ Y, ((scalarCells δ (U p.1+(V p.2).image (fun c => b*c))).card : ℝ)) ≤
        (Y.card : ℝ)*((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ) := by
      exact_mod_cast scalar_cluster_fallback hδ hr hgap hb X Y hX U V hU hV
    have hn : 0 < (Y.card : ℝ) := by exact_mod_cast hY.card_pos
    calc
      _ ≤ (Y.card : ℝ)⁻¹*((Y.card : ℝ)*
          ((scalarCells δ ((X.biUnion U)+(Y.biUnion V).image (fun c => b*c))).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hn.le)
      _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hn.ne',one_mul]
  · simp only [scalarCollisionWeight,ite_eq_right hg,one_mul]
    exact_mod_cast scalar_cluster_sums_cells hδ hr B X Y hbB hb hg U V hU hV

end Falconer

end OAI
