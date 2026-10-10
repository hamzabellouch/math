import Mathlib
import OAI.MeasureTheory.Falconer.Fourier.BinKernel
import OAI.MeasureTheory.Falconer.Geometry.BinOffsets
import OAI.MeasureTheory.Falconer.Geometry.Bins
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAmbient

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FarGrid
open MeasureTheory Set

theorem diagonal_bin_mass_le {ι : Type*} [Countable ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (I : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (I i))
    (hdisj : Pairwise fun i j => Disjoint (I i) (I j)) (w : ℝ)
    (hdiam : ∀ i x, x ∈ I i → ∀ y, y ∈ I i → |x-y| ≤ w) :
    (∑' i, (μ (I i))^2) ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
  have hd : Pairwise fun i j => Disjoint (I i ×ˢ I i) (I j ×ˢ I j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact Set.disjoint_left.mp (hdisj hij) hi.1 hj.1
  calc
    (∑' i, (μ (I i))^2) = ∑' i, (μ.prod μ) (I i ×ˢ I i) := by
      simp only [Measure.prod_prod, pow_two]
    _ = (μ.prod μ) (⋃ i, I i ×ˢ I i) :=
      (measure_iUnion hd (fun i => (hmeas i).prod (hmeas i))).symm
    _ ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
      apply measure_mono
      intro z hz
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      exact hdiam i z.1 hi.1 z.2 hi.2

def realBin (w : ℝ) (j : ℤ) : Set ℝ :=
  Set.Ico ((j : ℝ)*w) (((j+1 : ℤ) : ℝ)*w)

theorem realBin_measurable (w : ℝ) (j : ℤ) : MeasurableSet (realBin w j) :=
  measurableSet_Ico

theorem realBin_disjoint {w : ℝ} (hw : 0 < w) :
    Pairwise fun i j => Disjoint (realBin w i) (realBin w j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : ((i+1 : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxj.1.trans' hm)) hxi.2
  · have hc : ((j+1 : ℤ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show j+1 ≤ i by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxi.1.trans' hm)) hxj.2

theorem realBin_diameter (w : ℝ) (j : ℤ) {x y : ℝ}
    (hx : x ∈ realBin w j) (hy : y ∈ realBin w j) : |x-y| ≤ w := by
  simp only [realBin, Set.mem_Ico, Int.cast_add, Int.cast_one] at hx hy
  apply abs_le.mpr
  constructor <;> nlinarith

theorem real_bin_collision_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {w : ℝ} (hw : 0 < w) :
    (∑' j : ℤ, (μ (realBin w j))^2) ≤
      (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} :=
  diagonal_bin_mass_le μ (realBin w) (realBin_measurable w) (realBin_disjoint hw) w
    (fun j _ hx _ hy => realBin_diameter w j hx hy)

end Attempt4FarGrid
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FarGrid
open MeasureTheory Set
open scoped ENNReal

noncomputable def binL2Norm (μ : Measure ℝ) (w : ℝ) : ℝ≥0∞ :=
  (∑' j : ℤ, (μ (realBin w j))^2)^(1/2 : ℝ)

 theorem ennreal_offset_cauchy (a b : ℤ → ℝ≥0∞) (h : ℤ) :
    (∑' j : ℤ, a j*b (j-h)) ≤
      (∑' j : ℤ, (a j)^2)^(1/2 : ℝ) * (∑' j : ℤ, (b j)^2)^(1/2 : ℝ) := by
  have hpq : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ℤ) hpq
    (measurable_of_countable a).aemeasurable
    (measurable_of_countable (fun j => b (j-h))).aemeasurable
  simp only [lintegral_count, ENNReal.rpow_two] at hh
  have he : (∑' j : ℤ, (b (j-h))^2) = ∑' j : ℤ, (b j)^2 :=
    (Equiv.subRight h).tsum_eq (fun j => (b j)^2)
  simpa only [one_div, he, Pi.mul_apply] using hh

 theorem realBin_cover {w : ℝ} (hw : 0 < w) (x : ℝ) :
    x ∈ realBin w ⌊x/w⌋ := by
  constructor
  · exact (le_div_iff₀ hw).mp (Int.floor_le (x/w))
  · simpa only [Int.cast_add,Int.cast_one] using
      (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (x/w))

 theorem offset_rectangles_mass_le (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (w : ℝ) (h : ℤ) :
    (μ.prod ν) (⋃ j : ℤ, realBin w j ×ˢ realBin w (j-h)) ≤
      binL2Norm μ w * binL2Norm ν w := by
  apply (measure_iUnion_le _).trans
  simp only [Measure.prod_prod]
  exact ennreal_offset_cauchy (fun j => μ (realBin w j)) (fun j => ν (realBin w j)) h

 theorem finite_offset_rectangles_mass_le (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (w : ℝ) (H : Finset ℤ) :
    (μ.prod ν) (⋃ h ∈ H, ⋃ j : ℤ, realBin w j ×ˢ realBin w (j-h)) ≤
      (H.card : ℝ≥0∞) * (binL2Norm μ w * binL2Norm ν w) := by
  calc
    _ ≤ ∑ h ∈ H, (μ.prod ν) (⋃ j : ℤ, realBin w j ×ˢ realBin w (j-h)) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _h ∈ H, binL2Norm μ w * binL2Norm ν w :=
      Finset.sum_le_sum (fun h _ => offset_rectangles_mass_le μ ν w h)
    _ = _ := by simp

end Attempt4FarGrid
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FarGrid
open MeasureTheory Set
open scoped ENNReal

 theorem half_le_abs_int_add_half (h : ℤ) : (1/2:ℝ) ≤ |(h:ℝ)+1/2| := by
  by_cases hh : 0 ≤ h
  · have hr : (0:ℝ) ≤ h := by exact_mod_cast hh
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hr : (h:ℝ) ≤ -1 := by exact_mod_cast (show h ≤ -1 by omega)
    rw [abs_of_nonpos (by linarith)]
    linarith

 theorem realBin_kernel_bound {w x y : ℝ} (hw : 0 < w) {i j : ℤ}
    (hi : x ∈ realBin w i) (hj : y ∈ realBin w j) :
    1/(1+|x-y|/w)^2 ≤ 4/(((i-j:ℤ):ℝ)+1/2)^2 := by
  have hi1 : (i:ℝ) ≤ x/w := (le_div_iff₀ hw).mpr hi.1
  have hi2 : x/w < (i:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hi.2
  have hj1 : (j:ℝ) ≤ y/w := (le_div_iff₀ hw).mpr hj.1
  have hj2 : y/w < (j:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hj.2
  have hd : |(((i-j:ℤ):ℝ)+1/2)| ≤ 2*(1+|x-y|/w) := by
    rw [abs_le]
    have h1 := neg_abs_le ((x-y)/w)
    have h2 := le_abs_self ((x-y)/w)
    rw [abs_div,abs_of_pos hw,sub_div] at h1 h2
    simp only [Int.cast_sub]
    constructor <;> linarith [div_nonneg (abs_nonneg (x-y)) hw.le]
  have hpos : 0 < 1+|x-y|/w := by positivity
  have hh := half_le_abs_int_add_half (i-j)
  have hsq : 0 < ((((i-j:ℤ):ℝ)+1/2)^2) := by
    nlinarith [sq_abs ((((i-j:ℤ):ℝ)+1/2))]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpos) hsq).mpr
  nlinarith [sq_abs ((((i-j:ℤ):ℝ)+1/2)), sq_nonneg (2*(1+|x-y|/w)-|(((i-j:ℤ):ℝ)+1/2)|)]

noncomputable def binKernelWeight (h : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (4/((h:ℝ)+1/2)^2)

noncomputable def binKernelConstant : ℝ≥0∞ := ∑' h : ℤ, binKernelWeight h

 theorem binKernelConstant_ne_top : binKernelConstant ≠ ∞ := by
  have hs := (Real.summable_one_div_int_add_rpow (1/2) 2).mpr (by norm_num)
  have ht : Summable (fun h : ℤ => 4/((h:ℝ)+1/2)^2) := by
    simpa only [Real.rpow_two,sq_abs,mul_one_div] using hs.mul_left 4
  exact ht.tsum_ofReal_ne_top

 theorem weighted_offset_kernel_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (w : ℝ) (c : ℤ → ℝ≥0∞) :
    (∫⁻ z : ℝ × ℝ, ∑' h : ℤ, ∑' j : ℤ,
      (realBin w j ×ˢ realBin w (j-h)).indicator (fun _ => c h) z ∂μ.prod ν) ≤
      (∑' h : ℤ, c h) * (binL2Norm μ w * binL2Norm ν w) := by
  have hm (h j : ℤ) : Measurable ((realBin w j ×ˢ realBin w (j-h)).indicator
      (fun _ : ℝ × ℝ => c h)) :=
    measurable_const.indicator ((realBin_measurable w j).prod (realBin_measurable w (j-h)))
  rw [lintegral_tsum (fun h => (Measurable.tsum (fun j => hm h j)).aemeasurable)]
  simp_rw [lintegral_tsum (fun j => (hm _ j).aemeasurable)]
  simp_rw [lintegral_indicator_const ((realBin_measurable w _).prod (realBin_measurable w _)),
    Measure.prod_prod, ENNReal.tsum_mul_left]
  calc
    _ ≤ ∑' h : ℤ, c h * (binL2Norm μ w * binL2Norm ν w) := by
      apply ENNReal.tsum_le_tsum
      intro h
      exact mul_le_mul_right (ennreal_offset_cauchy (fun j => μ (realBin w j))
        (fun j => ν (realBin w j)) h) (c h)
    _ = _ := ENNReal.tsum_mul_right

 theorem real_bin_decaying_kernel_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {w : ℝ} (hw : 0 < w) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/w)^2) ∂μ.prod ν) ≤
      binKernelConstant * (binL2Norm μ w * binL2Norm ν w) := by
  apply le_trans (lintegral_mono (fun z => ?_))
    (weighted_offset_kernel_bound μ ν w binKernelWeight)
  let i : ℤ := ⌊z.1/w⌋
  let j : ℤ := ⌊z.2/w⌋
  have hi := realBin_cover hw z.1
  have hj := realBin_cover hw z.2
  have he : i-(i-j)=j := by omega
  have hz : z ∈ realBin w i ×ˢ realBin w (i-(i-j)) := ⟨hi,by simpa only [he] using hj⟩
  calc
    _ ≤ binKernelWeight (i-j) := ENNReal.ofReal_le_ofReal (realBin_kernel_bound hw hi hj)
    _ = (realBin w i ×ˢ realBin w (i-(i-j))).indicator
        (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z := (indicator_of_mem hz (fun _ : ℝ × ℝ => binKernelWeight (i-j))).symm
    _ ≤ ∑' k : ℤ, (realBin w k ×ˢ realBin w (k-(i-j))).indicator
        (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z :=
      ENNReal.le_tsum (f := fun index : ℤ =>
        (realBin w index ×ˢ realBin w (index-(i-j))).indicator
          (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z) i
    _ ≤ ∑' h : ℤ, ∑' k : ℤ, (realBin w k ×ˢ realBin w (k-h)).indicator
        (fun _ : ℝ × ℝ => binKernelWeight h) z :=
      ENNReal.le_tsum (f := fun offset : ℤ => ∑' index : ℤ,
        (realBin w index ×ˢ realBin w (index-offset)).indicator
          (fun _ : ℝ × ℝ => binKernelWeight offset) z) (i-j)

end Attempt4FarGrid
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4FullFar
open Set MeasureTheory Attempt4FarGrid
open scoped ENNReal

lemma mixed_bin_collisionND (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {w : ℝ} (hw : 0<w) :
    (∫⁻ z : ℝ×ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/w)^2) ∂μ.prod ν) ≤
      binKernelConstant*max ((μ.prod μ) {z : ℝ×ℝ | |z.1-z.2|≤w})
        ((ν.prod ν) {z : ℝ×ℝ | |z.1-z.2|≤w}) := by
  apply (real_bin_decaying_kernel_bound μ ν hw).trans
  apply mul_le_mul_right
  let M := max ((μ.prod μ) {z : ℝ×ℝ | |z.1-z.2|≤w})
        ((ν.prod ν) {z : ℝ×ℝ | |z.1-z.2|≤w})
  have hm : binL2Norm μ w≤M^(1/2:ℝ) :=
    ENNReal.rpow_le_rpow ((real_bin_collision_bound μ hw).trans (le_max_left _ _)) (by norm_num)
  have hn : binL2Norm ν w≤M^(1/2:ℝ) :=
    ENNReal.rpow_le_rpow ((real_bin_collision_bound ν hw).trans (le_max_right _ _)) (by norm_num)
  apply (mul_le_mul' hm hn).trans_eq
  rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
  norm_num [M]

section Metric
variable {V : Type*} [PseudoMetricSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

noncomputable def positiveDistanceLawND (μ : Measure (V×V)) : Measure ℝ :=
  Measure.map (fun z : V×V => dist z.1 z.2) μ

noncomputable def positiveDistanceCountND (μ : Measure (V×V)) (d : ℕ) (v a M : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2:ℝ)^(v-a)/M^4) *
    (μ.prod μ) {z : (V×V)×(V×V) | |dist z.1.1 z.1.2-dist z.2.1 z.2.2|≤(100*(d+1:ℝ))*(2:ℝ)^(-v)}

instance positiveDistanceLawND_finite (μ : Measure (V×V)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (positiveDistanceLawND μ) := by
  unfold positiveDistanceLawND
  infer_instance

lemma positiveDistanceLawND_prod (μ ν : Measure (V×V)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (positiveDistanceLawND μ).prod (positiveDistanceLawND ν)=
      Measure.map (fun z : (V×V)×(V×V) => (dist z.1.1 z.1.2,dist z.2.1 z.2.2)) (μ.prod ν) :=
  Measure.map_prod_map _ _ (continuous_fst.dist continuous_snd).measurable
    (continuous_fst.dist continuous_snd).measurable

lemma positiveDistanceLawND_collision (μ : Measure (V×V)) [IsFiniteMeasure μ] (w : ℝ) :
    ((positiveDistanceLawND μ).prod (positiveDistanceLawND μ)) {z : ℝ×ℝ | |z.1-z.2|≤w} =
      (μ.prod μ) {z : (V×V)×(V×V) | |dist z.1.1 z.1.2-dist z.2.1 z.2.2|≤w} := by
  rw [positiveDistanceLawND_prod,Measure.map_apply (by fun_prop) (by measurability)]
  rfl

omit [BorelSpace V] [SecondCountableTopology V] in
lemma positiveDistanceCountND_ne_top (μ : Measure (V×V)) [IsFiniteMeasure μ] (d : ℕ) (v a M : ℝ) :
    positiveDistanceCountND μ d v a M≠⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

omit [BorelSpace V] [SecondCountableTopology V] in
lemma positiveDistanceCountND_unnormalized (μ : Measure (V×V)) (d : ℕ) (v a M : ℝ) (hM : 0<M) :
    ENNReal.ofReal (M^4*(2:ℝ)^(-(v-a)))*positiveDistanceCountND μ d v a M =
      (μ.prod μ) {z : (V×V)×(V×V) | |dist z.1.1 z.1.2-dist z.2.1 z.2.2|≤(100*(d+1:ℝ))*(2:ℝ)^(-v)} := by
  unfold positiveDistanceCountND
  rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity)]
  have he : M^4*(2:ℝ)^(-(v-a))*((2:ℝ)^(v-a)/M^4)=1 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    field_simp
  rw [he,ENNReal.ofReal_one,one_mul]

theorem positiveDistance_kernel_maxND (μ ν : Measure (V×V))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (d : ℕ) (v a M : ℝ) (hM : 0<M) :
    (∫⁻ z : (V×V)×(V×V), ENNReal.ofReal
      (1/(1+(2:ℝ)^v*|dist z.1.1 z.1.2-dist z.2.1 z.2.2|)^2) ∂μ.prod ν) ≤
      binKernelConstant*ENNReal.ofReal (M^4*(2:ℝ)^(-(v-a)))*
        max (positiveDistanceCountND μ d v a M) (positiveDistanceCountND ν d v a M) := by
  have h := mixed_bin_collisionND (positiveDistanceLawND μ) (positiveDistanceLawND ν)
    (show 0<(2:ℝ)^(-v) from Real.rpow_pos_of_pos (by norm_num) (-v))
  rw [positiveDistanceLawND_prod,lintegral_map (by fun_prop) (by fun_prop)] at h
  simp only [positiveDistanceLawND_collision] at h
  have hw (x : ℝ) : x/(2:ℝ)^(-v)=(2:ℝ)^v*x := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),div_inv_eq_mul,mul_comm]
  simp only [hw] at h
  apply h.trans
  rw [mul_assoc]
  apply mul_le_mul_right
  rw [mul_max_of_nonneg _ _ (by positivity),
    positiveDistanceCountND_unnormalized μ d v a M hM,
    positiveDistanceCountND_unnormalized ν d v a M hM]
  have hwle : (2:ℝ)^(-v) ≤ (100*(d+1:ℝ))*(2:ℝ)^(-v) := by
    have hd := Nat.cast_nonneg (α := ℝ) d
    nlinarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) (-v)]
  apply max_le_max <;> apply measure_mono <;> intro z hz <;>
    exact le_trans hz hwle

end Metric
end Attempt4FullFar
end GraphLiteralSupport
end
end

end OAI
