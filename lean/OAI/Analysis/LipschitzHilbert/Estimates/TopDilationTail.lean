import OAI.Analysis.LipschitzHilbert.Estimates.MixedTopTail

namespace OAI

/-! Scaling the mixed rectangle bound by the actual top area gives a
quadratic distribution bound. The density loses exactly two powers of
the dilation radius, which will give a cubic testing cost. -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
namespace LipschitzHilbert

theorem top_dilation_square_tail (hLL : LaceyLiInput) :
    ∃ C : ℝ≥0, 0 < C ∧ ∀ (ι : Type*) [Fintype ι] (T : ι → SlopeBox)
      (D l r : ℝ), 1 ≤ D → (∀ i, |(T i).slope| ≤ 1) →
      ∀ (u : Plane → ℝ) (K α : ℝ≥0), LipschitzWith K u → 0 < α → α ≤ 1 →
      300*((2*K:ℝ≥0):ℝ)*(r-l) ≤ 1 →
      ∀ E : ι → Set (ℝ × ℝ), (∀ i, MeasurableSet (E i)) →
      (Pairwise fun i j => Disjoint (E i) (E j)) →
      (∀ i z, z ∈ E i → z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation D) →
      (∀ i z, z ∈ E i → |u (planeCoordinates z)-(T i).slope| ≤
        (T i).width/(12*(T i).length)) →
      (∀ i, ENNReal.ofReal ((α:ℝ)*(T i).length*(T i).width) ≤
        (volume.prod volume) (E i)) →
      ∀ Q : Set (ℝ × ℝ), MeasurableSet Q → (volume.prod volume) Q ≠ ∞ →
      (∀ z ∈ Q, z.1 ∈ Icc l r) → ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) →
      (∀ i, ENNReal.ofReal (a i*(8*D^2*(T i).length*(T i).width)) ≤
        (volume.prod volume) (Q ∩ (T i).radialDilation D)) →
      ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t^2)*(∑ i, if t<a i then
        ENNReal.ofReal ((T i).length*(T i).width) else 0) ≤
      ENNReal.ofReal ((4*(C:ℝ)*D/(α:ℝ))^2 * (volume.prod volume).real Q) := by
  classical
  obtain ⟨C,hC,hbound⟩ := mixed_top_weighted_tail hLL
  refine ⟨C,hC,?_⟩
  intro ι _ T D l r hD hs u K α hu hα hα1 hlength E hEmeas hdisj hE hclose
    hsize Q hQ hQfin hstrip a ha havg t ht
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hαR : (0:ℝ) < α := hα
  let δ : ℝ≥0 := ⟨(α:ℝ)/(8*D^2), by positivity⟩
  have hδ : 0 < δ := by change (0:ℝ) < (α:ℝ)/(8*D^2); positivity
  have hδhalf : δ ≤ 1/2 := by
    change (α:ℝ)/(8*D^2) ≤ ((1/2:ℝ≥0):ℝ)
    norm_num
    apply (div_le_iff₀ (by positivity : 0 < 8*D^2)).mpr
    have hα' : (α:ℝ) ≤ 1 := hα1
    nlinarith [sq_nonneg (D-1)]
  have hED (i : ι) (z : ℝ × ℝ) (hz : z ∈ E i) :
      z.1 ∈ Icc l r ∧ z ∈ (T i).radialDilation D :=
    hE i z hz
  have hclip (i : ι) : 0 < (T i).clipLength D l r := by
    apply (T i).clipLength_pos_of_positive_witness D l r (E i) _ (hED i)
    exact lt_of_lt_of_le (by have := (T i).length_pos; have := (T i).width_pos; positivity)
      (hsize i)
  have hpop (i : ι) : (δ:ℝ≥0∞)*ENNReal.ofReal (8*D^2*(T i).length*(T i).width) ≤
      (volume.prod volume) (E i) := by
    rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul δ.coe_nonneg]
    have hid : (δ:ℝ)*(8*D^2*(T i).length*(T i).width) = (α:ℝ)*(T i).length*(T i).width := by
      change ((α:ℝ)/(8*D^2))*(8*D^2*(T i).length*(T i).width) = _
      field_simp
    rw [hid]
    exact hsize i
  let τ : ℝ≥0 := ⟨t, ht.le⟩
  have hm := hbound ι T D l r hDpos hclip hs u K δ hu hδ hδhalf hlength E
    (fun i => ENNReal.ofReal ((T i).length*(T i).width)) α hEmeas hdisj hED hclose
    hpop (by
      intro i
      rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul α.coe_nonneg]
      convert hsize i using 1
      congr 1
      ring)
    Q hQ hQfin hstrip a ha havg τ ht
  have hscale : (C:ℝ≥0∞)^2/(δ:ℝ≥0∞)*(volume.prod volume) Q ≤
      (α:ℝ≥0∞)*ENNReal.ofReal ((4*(C:ℝ)*D/(α:ℝ))^2*(volume.prod volume).real Q) := by
    rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_pow C.coe_nonneg,
      ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_div_of_pos (show (0:ℝ)<δ from hδ),
      ← ENNReal.ofReal_toReal hQfin, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul α.coe_nonneg]
    apply ENNReal.ofReal_le_ofReal
    change (C:ℝ)^2/((α:ℝ)/(8*D^2))*(volume.prod volume).real Q ≤ _
    have hid : (C:ℝ)^2/((α:ℝ)/(8*D^2)) = 8*(C:ℝ)^2*D^2/(α:ℝ) := by field_simp
    have hid' : (α:ℝ)*(4*(C:ℝ)*D/(α:ℝ))^2 = 16*(C:ℝ)^2*D^2/(α:ℝ) := by field_simp; ring
    rw [hid, ← mul_assoc, hid']
    gcongr
    norm_num
  apply (ENNReal.mul_le_mul_iff_left (show (α:ℝ≥0∞) ≠ 0 by positivity)
    ENNReal.coe_ne_top).mp
  calc
    _ = (τ:ℝ≥0∞)^2*(α:ℝ≥0∞)*(∑ i, if (τ:ℝ)<a i then
        ENNReal.ofReal ((T i).length*(T i).width) else 0) := by
      have hτ : ENNReal.ofReal t = (τ:ℝ≥0∞) := (ENNReal.coe_nnreal_eq τ).symm
      rw [ENNReal.ofReal_pow ht.le, hτ]
      have hτR : (τ:ℝ) = t := rfl
      rw [hτR]
      ring
    _ ≤ (α:ℝ≥0∞)*ENNReal.ofReal ((4*(C:ℝ)*D/(α:ℝ))^2*(volume.prod volume).real Q) :=
      hm.trans hscale
    _ = _ := mul_comm _ _

end LipschitzHilbert

end

end OAI
