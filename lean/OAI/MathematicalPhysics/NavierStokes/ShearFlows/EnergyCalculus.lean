import OAI.MathematicalPhysics.NavierStokes.ShearFlows.PeriodicCalculus

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

open Set MeasureTheory
open scoped BigOperators ContDiff Topology
namespace ShearFlows

theorem norm_sq_le_dot_self (v : Space) : ‖v‖ ^ 2 ≤ dot v v := by
  have h0 := dot_self_nonneg v
  apply (Real.le_sqrt (norm_nonneg _) h0).mp
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro j
  apply (Real.le_sqrt (norm_nonneg _) h0).mpr
  have h := Finset.single_le_sum (fun k _ => mul_self_nonneg (v k))
    (Finset.mem_univ j)
  rw [Real.norm_eq_abs, sq_abs, sq]
  exact h

theorem abs_dot_le (a b : Space) : |dot a b| ≤ 3 * ‖a‖ * ‖b‖ := by
  calc
    |dot a b| ≤ ∑ j, |a j * b j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, ‖a‖ * ‖b‖ := Finset.sum_le_sum (fun j _ => by
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm a j) (norm_le_pi_norm b j)
        (abs_nonneg _) (norm_nonneg _))
    _ = _ := by simp; ring

theorem dot_linear_bound (A : Space →L[ℝ] Space) (v : Space) :
    |dot v (A v)| ≤ 3 * ‖A‖ * dot v v := by
  calc
    |dot v (A v)| ≤ 3 * ‖v‖ * ‖A v‖ := abs_dot_le _ _
    _ ≤ 3 * ‖v‖ * (‖A‖ * ‖v‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm _) (by positivity)
    _ = (3 * ‖A‖) * ‖v‖ ^ 2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_sq_le_dot_self _) (by positivity)

theorem continuousOn_spatial_slice {E : Type*} [TopologicalSpace E]
    {g : SpaceTime → E} {a b t : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ univ)) (ht : t ∈ Icc a b) :
    Continuous (fun x => g (t,x)) := by
  exact hg.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨ht,mem_univ _⟩)

theorem continuousOn_cube_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : SpaceTime → E} {a b L : ℝ} (hg : ContinuousOn g (Icc a b ×ˢ univ)) :
    ContinuousOn (fun t => ∫ x in fundamentalCube L, g (t,x)) (Icc a b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply continuous_parametric_integral_of_continuous (s := fundamentalCube L) _ isCompact_Icc
  exact hg.comp_continuous (continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd)
    (fun y => ⟨y.1.property,mem_univ _⟩)

theorem hasDerivAt_cube_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g g' : SpaceTime → E} {a b t L : ℝ}
    (hg : ContinuousOn g (Icc a b ×ˢ univ))
    (hg' : ContinuousOn g' (Icc a b ×ˢ univ))
    (hd : ∀ s ∈ Ioo a b, ∀ x, HasDerivAt (fun r => g (r,x)) (g' (s,x)) s)
    (ht : t ∈ Ioo a b) :
    HasDerivAt (fun r => ∫ x in fundamentalCube L, g (r,x))
      (∫ x in fundamentalCube L, g' (t,x)) t := by
  have hsubset : Icc a b ×ˢ fundamentalCube L ⊆ Icc a b ×ˢ (univ : Set Space) :=
    fun _ h => ⟨h.1,mem_univ _⟩
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod (isCompact_Icc (a := (0 : Space))
    (b := fun _ => L))).bddAbove_image (hg'.norm.mono hsubset)
  have hbound : ∀ᵐ x ∂(volume.restrict (fundamentalCube L)),
      ∀ s ∈ Ioo a b, ‖g' (s,x)‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    intro s hs
    exact hB (mem_image_of_mem _ ⟨Ioo_subset_Icc_self hs,hx⟩)
  have hmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (fun x => g (s,x))
      (volume.restrict (fundamentalCube L)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact (continuousOn_spatial_slice hg (Ioo_subset_Icc_self hs)).aestronglyMeasurable
  have hint : IntegrableOn (fun x => g (t,x)) (fundamentalCube L) :=
    (continuousOn_spatial_slice hg (Ioo_subset_Icc_self ht)).integrableOn_Icc
  have h'meas : AEStronglyMeasurable (fun x => g' (t,x))
      (volume.restrict (fundamentalCube L)) :=
    (continuousOn_spatial_slice hg' (Ioo_subset_Icc_self ht)).aestronglyMeasurable
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Ioo_mem_nhds ht.1 ht.2)
    hmeas hint h'meas hbound (by exact integrableOn_const (s := fundamentalCube L) (hs := isCompact_Icc.measure_lt_top.ne))
    (Filter.Eventually.of_forall (fun x s hs => hd s hs x))).2

theorem hasDerivAt_dot_self {v : ℝ → Space} {v' : Space} {t : ℝ}
    (hv : HasDerivAt v v' t) : HasDerivAt (fun s => dot (v s) (v s)) (2 * dot (v t) v') t := by
  have hj (j : Fin 3) : HasDerivAt (fun s => v s j) (v' j) t :=
    (ContinuousLinearMap.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t hv
  have hh := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hj j).mul (hj j))
  have he : (∑ j : Fin 3, (v' j * v t j + v t j * v' j)) = 2 * dot (v t) v' := by
    simp only [dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  exact he ▸ hh

end ShearFlows

end

end OAI
