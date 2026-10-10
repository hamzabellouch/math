import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.SliceGeometry
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

lemma sliceVolume_pos_between {n : ℕ} {K : Set (Fin (n+1) → ℝ)} {z : Fin (n+1) → ℝ}
    {a b t : ℝ} (hK : IsCompact K) (hcK : Convex ℝ K) (hz : z ∈ K) (hza : z 0 = a)
    (ht : t ∈ Ioo a b) (hb : 0 < sliceVolume K b) : 0 < sliceVolume K t := by
  let θ := (t-a)/(b-a)
  have hab : a < b := ht.1.trans ht.2
  have hθ : 0 < θ := div_pos (sub_pos.mpr ht.1) (sub_pos.mpr hab)
  have hθ1 : θ < 1 := by
    rw [div_lt_one (sub_pos.mpr hab)]
    linarith [ht.2]
  have heq : (1-θ)*a+θ*b=t := by
    dsimp only [θ]
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  have hsub : AffineMap.homothety (Fin.tail z) θ '' slice K b ⊆ slice K t := by
    rintro x ⟨y,hy,rfl⟩
    have hh := hcK hz hy (by linarith : 0 ≤ 1-θ) hθ.le (by ring : 1-θ+θ=1)
    change Fin.cons t (AffineMap.homothety (Fin.tail z) θ y) ∈ K
    convert hh using 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.cons_zero, hza] using heq.symm
    · simp only [AffineMap.homothety_apply, vadd_eq_add, vsub_eq_sub, Fin.cons_succ,
        Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Fin.tail]
      ring
  have hp : 0 < volume (AffineMap.homothety (Fin.tail z) θ '' slice K b) := by
    rw [Measure.addHaar_image_homothety]
    exact pos_iff_ne_zero.mpr (mul_ne_zero
      (ENNReal.ofReal_pos.mpr (abs_pos.mpr (pow_ne_zero _ hθ.ne'))).ne'
      (ENNReal.toReal_pos_iff.mp hb).1.ne')
  apply ENNReal.toReal_pos
  · exact ne_of_gt (hp.trans_le (measure_mono hsub))
  · exact (compact_slice hK t).measure_ne_top

lemma sliceVolume_pos_Ioc {n : ℕ} {K : Set (Fin (n+1) → ℝ)} {z : Fin (n+1) → ℝ}
    {a b : ℝ} (hK : IsCompact K) (hcK : Convex ℝ K) (hz : z ∈ K) (hza : z 0 = a)
    (hb : 0 < sliceVolume K b) : ∀ t ∈ Ioc a b, 0 < sliceVolume K t := by
  intro t ht
  rcases ht.2.eq_or_lt with rfl | htb
  · exact hb
  · exact sliceVolume_pos_between hK hcK hz hza ⟨ht.1, htb⟩ hb

lemma sliceVolume_eq_zero_outside {n : ℕ} {K : Set (Fin (n+1) → ℝ)} {a b t : ℝ}
    (hproj : ∀ z ∈ K, z 0 ∈ Icc a b) (ht : t ∉ Icc a b) : sliceVolume K t = 0 := by
  have he : slice K t = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact ht (hproj (Fin.cons t x) hx)
  simp [sliceVolume, he]

lemma intervalIntegral_sliceVolume {n : ℕ} {K : Set (Fin (n+1) → ℝ)} {a b : ℝ}
    (hK : IsCompact K) (hab : a ≤ b) (hproj : ∀ z ∈ K, z 0 ∈ Icc a b) :
    (∫ t in a..b, sliceVolume K t) = (volume K).toReal := by
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  rw [← integral_sliceVolume hK]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  exact sliceVolume_eq_zero_outside hproj ht

end FacetVolume

end

end OAI
