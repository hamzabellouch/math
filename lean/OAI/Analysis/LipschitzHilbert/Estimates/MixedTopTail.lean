import OAI.Analysis.LipschitzHilbert.Estimates.ThinTopTail
import OAI.Analysis.LipschitzHilbert.Estimates.FatTopTail

namespace OAI

/-! A mixed family of clipped tops is split by aspect ratio. Both pieces
use the same published Lacey--Li input, and the resulting constant is
uniform in the finite family and dilation. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace LipschitzHilbert

theorem mixed_top_weighted_tail (hLL : LaceyLiInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox)
      (D l r : ℝ), 0 < D → (∀ i, 0 < (T i).clipLength D l r) →
      (∀ i, |(T i).slope| ≤ 1) → ∀ (u : Plane → ℝ) (K δ : ℝ≥0),
      LipschitzWith K u → 0 < δ → δ ≤ 1/2 →
      300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ (E : ι → Set (ℝ × ℝ)) (w : ι → ℝ≥0∞) (α : ℝ≥0∞),
      (∀ i, MeasurableSet (E i)) → (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation D) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, (δ:ℝ≥0∞)*ENNReal.ofReal (8*D^2*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) →
      (∀ i, α*w i ≤ (volume.prod volume) (E i)) →
      ∀ Q : Set (ℝ × ℝ), MeasurableSet Q → (volume.prod volume) Q ≠ ∞ →
      (∀ z ∈ Q, z.1 ∈ Icc l r) → ∀ a : ι → ℝ,
      (∀ i, 0 ≤ a i) →
      (∀ i, ENNReal.ofReal (a i*(8*D^2*(T i).length*(T i).width)) ≤
        (volume.prod volume) (Q ∩ (T i).radialDilation D)) →
      ∀ t : ℝ≥0, 0 < t →
      (t:ℝ≥0∞)^2*α*(∑ i, if (t:ℝ)<a i then w i else 0) ≤
        (C:ℝ≥0∞)^2/(δ:ℝ≥0∞)*(volume.prod volume) Q := by
  classical
  obtain ⟨Ct,hCt,ht⟩ := thin_top_weighted_tail hLL
  obtain ⟨Cf,hCf,hf⟩ := fat_top_weighted_tail hLL
  refine ⟨Ct+Cf, by positivity, ?_⟩
  intro ι _ T D l r hD ha hs u K δ hu hδ hδhalf hlength
    E w α hEmeas hdisj hE hclose hpop hsize Q hQ hQfin hstrip a ha0 havg t hpos
  let p : ι → Prop := fun i => 2*D*(T i).width ≤ (T i).clipLength D l r
  have hthin := ht {i // p i} (fun i => T i) D l r hD (fun i => ha i)
    (fun i => i.property) (fun i => hs i) u K δ hu hδ (hδhalf.trans_lt (by norm_num))
    hlength (fun i => E i) (fun i => w i) α (fun i => hEmeas i)
    (fun i j hij => hdisj (fun heq => hij (Subtype.ext heq)))
    (fun i => hE i) (fun i => hclose i) (fun i => hpop i) (fun i => hsize i)
    Q hQ hQfin hstrip (fun i => a i) (fun i => ha0 i) (fun i => havg i) t hpos
  have hfat := hf {i // ¬p i} (fun i => T i) D l r hD (fun i => ha i)
    (fun i => (lt_of_not_ge i.property).le) (fun i => hs i)
    (fun i => E i) (fun i => w i) α (fun i => hEmeas i)
    (fun i j hij => hdisj (fun heq => hij (Subtype.ext heq)))
    (fun i => hE i) (fun i => hsize i) Q hQ hQfin hstrip
    (fun i => a i) (fun i => ha0 i) (fun i => havg i) t hpos
  have hden : (δ:ℝ≥0∞) ≤ 1/2 := by
    calc
      _ ≤ ((1/2:ℝ≥0):ℝ≥0∞) := ENNReal.coe_le_coe.mpr hδhalf
      _ = _ := by norm_num
  have hfat' : (t:ℝ≥0∞)^2*α*(∑ i : {i // ¬p i}, if (t:ℝ)<a i then w i else 0) ≤
      (Cf:ℝ≥0∞)^2/(δ:ℝ≥0∞)*(volume.prod volume) Q := by
    apply hfat.trans
    gcongr
  have hsplit := Fintype.sum_subtype_add_sum_subtype p
    (fun i => if (t:ℝ)<a i then w i else 0)
  have hsq : (Ct:ℝ≥0∞)^2+(Cf:ℝ≥0∞)^2 ≤ (↑(Ct+Cf):ℝ≥0∞)^2 := by
    exact_mod_cast (show (Ct:ℝ)^2+(Cf:ℝ)^2 ≤ ((Ct+Cf:ℝ≥0):ℝ)^2 by
      push_cast
      nlinarith [mul_nonneg Ct.coe_nonneg Cf.coe_nonneg])
  calc
    _ = (t:ℝ≥0∞)^2*α*(∑ i : {i // p i}, if (t:ℝ)<a i then w i else 0) +
        (t:ℝ≥0∞)^2*α*(∑ i : {i // ¬p i}, if (t:ℝ)<a i then w i else 0) := by
      rw [← mul_add, hsplit]
    _ ≤ (Ct:ℝ≥0∞)^2/(δ:ℝ≥0∞)*(volume.prod volume) Q +
        (Cf:ℝ≥0∞)^2/(δ:ℝ≥0∞)*(volume.prod volume) Q := add_le_add hthin hfat'
    _ = ((Ct:ℝ≥0∞)^2+(Cf:ℝ≥0∞)^2)/(δ:ℝ≥0∞)*(volume.prod volume) Q := by
      simp only [div_eq_mul_inv]
      ring
    _ ≤ _ := by gcongr

end LipschitzHilbert

end

end OAI
