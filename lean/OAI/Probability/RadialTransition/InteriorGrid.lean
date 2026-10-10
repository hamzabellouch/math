import OAI.Probability.RadialTransition.KernelError

namespace OAI

noncomputable section


open Function MeasureTheory Set Filter

open scoped BigOperators ENNReal NNReal ContDiff

namespace RadialTransition

lemma grid_inner_coords {m D : ℕ} {i : GridIndex m} (hi : i ∉ boundaryGrid m D) (d : Fin 3) :
    D ≤ (i d:ℕ) ∧ (i d:ℕ)+D < m := by
  have hn : ¬ ((i d:ℕ) < D ∨ m-D ≤ (i d:ℕ)) := fun h => hi (mem_boundaryGrid.mpr ⟨d,h⟩)
  omega

lemma grid_inner_reach {m : ℕ} {T : ℝ} (hT : 0 ≤ T) (i : GridIndex m)
    (hi : i ∉ boundaryGrid m (cellMargin T).toNat) {j : Cell} (hj : CellReach T (gridEmbed i) j) :
    ∃ k : GridIndex m, gridEmbed k = j := by
  have hD : 0 ≤ cellMargin T := by unfold cellMargin; have := Int.ceil_nonneg (by positivity : 0 ≤ 4*T); omega
  have hd (d : Fin 3) : 0 ≤ j d ∧ j d < (m:ℤ) := by
    have hc := grid_inner_coords hi d
    have ha := abs_le.mp (hj d)
    have he : ((cellMargin T).toNat:ℤ) = cellMargin T := Int.toNat_of_nonneg hD
    change -cellMargin T ≤ j d-(i d:ℤ) ∧ j d-(i d:ℤ) ≤ cellMargin T at ha
    omega
  refine ⟨fun d => ⟨(j d).toNat, by have := hd d; omega⟩, ?_⟩
  funext d
  exact Int.toNat_of_nonneg (hd d).1

lemma macroKernel_support_inside {q m : ℕ} (hq : 0 < q) {R : ℝ} (hR : 0 ≤ R) (i : GridIndex m)
    (hi : i ∉ boundaryGrid m (cellMargin (R/q+1)).toNat) :
    ∀ y ∉ halfCube ((m:ℝ)*q/4), scaledBump R (macroOrigin q (gridEmbed i)-y) = 0 := by
  intro y hy
  by_cases hR0 : R = 0
  · simp [hR0, scaledBump]
  have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hR0)
  apply scaledBump_zero hRpos
  rw [← dist_eq_norm]
  apply le_of_not_gt
  intro hd
  have hm : y ∈ macroRegion q (macroOf q (cellOf y)) := rfl
  have hr := macroReach_of_dist hq (macroOrigin_mem hq (gridEmbed i)) hm hd.le
  have hT : 0 ≤ R/(q:ℝ)+1 := by positivity
  obtain ⟨j, hj⟩ := grid_inner_reach hT i hi hr
  rw [← hj] at hm
  exact hy (macroRegion_subset_halfCube hq j hm)

lemma macroKernelLower_diagonal {q : ℕ} {R : ℝ} (hR : 0 < R) (i : Cell) :
    macroKernelLower q R i i ≤ (R^3)⁻¹*bumpIntegral⁻¹ := by
  apply max_le
  · have := bumpIntegral_pos; positivity
  · have hb := scaledBump_bound hR (macroOrigin q i-macroOrigin q i)
    have hn := macroKernelError_nonneg q R i i
    have ha := le_abs_self (scaledBump R (macroOrigin q i-macroOrigin q i))
    change macroKernel q R i i ≤ _ at ha
    linarith

def kernelRowError (q : ℕ) (R : ℝ) : ℝ :=
  (10000*(bumpLip:ℝ)+bumpIntegral⁻¹)*(q:ℝ)/R

lemma kernelRowError_nonneg (q : ℕ) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ kernelRowError q R := by
  unfold kernelRowError
  have := bumpIntegral_pos
  positivity

lemma macroKernelLower_row {q m : ℕ} (hq : 0 < q) {R : ℝ} (hR : (q:ℝ)/4 ≤ R) (i : GridIndex m)
    (hi : i ∉ boundaryGrid m (cellMargin (R/q+1)).toNat) :
    1-kernelRowError q R ≤ ((q:ℝ)/4)^3*∑ j : GridIndex m,
      (if i = j then 0 else macroKernelLower q R (gridEmbed i) (gridEmbed j)) := by
  classical
  have hq0 : (0:ℝ) < q := by exact_mod_cast hq
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR
  have hall := macroKernelLower_row_all hq hR (gridEmbed i) (macroKernel_support_inside hq hR0.le i hi)
  have hs : (∑ j : GridIndex m, if i = j then (0:ℝ) else macroKernelLower q R (gridEmbed i) (gridEmbed j)) =
      (∑ j : GridIndex m, macroKernelLower q R (gridEmbed i) (gridEmbed j))-macroKernelLower q R (gridEmbed i) (gridEmbed i) := by
    have hh := Finset.sum_erase_add (Finset.univ : Finset (GridIndex m))
      (fun j => macroKernelLower q R (gridEmbed i) (gridEmbed j)) (Finset.mem_univ i)
    have he : (∑ j : GridIndex m, if i = j then (0:ℝ) else macroKernelLower q R (gridEmbed i) (gridEmbed j)) =
        ∑ j ∈ Finset.univ.erase i, macroKernelLower q R (gridEmbed i) (gridEmbed j) := by
      simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add]
      congr 1
      ext j
      simp [ne_comm]
    rw [he]
    linarith
  rw [hs, mul_sub]
  have hd := mul_le_mul_of_nonneg_left (macroKernelLower_diagonal (q := q) hR0 (gridEmbed i)) (show 0 ≤ ((q:ℝ)/4)^3 by positivity)
  have hsq : ((q:ℝ)/4)^2 ≤ R^2 := pow_le_pow_left₀ (by positivity) hR 2
  have hd' : ((q:ℝ)/4)^3*((R^3)⁻¹*bumpIntegral⁻¹) ≤ bumpIntegral⁻¹*q/R := by
    apply (le_div_iff₀ hR0).mpr
    have hb := bumpIntegral_pos
    have he : ((q:ℝ)/4)^3*((R^3)⁻¹*bumpIntegral⁻¹)*R =
        bumpIntegral⁻¹*((q:ℝ)/4)*(((q:ℝ)/4)^2/R^2) := by field_simp
    rw [he]
    have hh : ((q:ℝ)/4)^2/R^2 ≤ 1 := (div_le_one (by positivity)).mpr hsq
    calc
      _ ≤ bumpIntegral⁻¹*((q:ℝ)/4)*1 := mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ _ := by nlinarith [inv_nonneg.mpr hb.le]
  unfold kernelRowError
  linear_combination hall + hd + hd'

lemma kernelInterior_ratio (D : ℕ) :
    Tendsto (fun m : ℕ => (((Finset.univ : Finset (GridIndex m)) \ boundaryGrid m D).card:ℝ)/(m:ℝ)^3)
      atTop (nhds 1) := by
  classical
  have hcard (m : ℕ) : (((Finset.univ : Finset (GridIndex m)) \ boundaryGrid m D).card:ℝ) =
      (m:ℝ)^3-((boundaryGrid m D).card:ℝ) := by
    have hh := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (GridIndex m)) (boundaryGrid m D)
    simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fun, Fintype.card_fin] at hh
    have hr : (((Finset.univ : Finset (GridIndex m)) \ boundaryGrid m D).card:ℝ)+((boundaryGrid m D).card:ℝ) = (m:ℝ)^3 := by exact_mod_cast hh
    linarith
  have hz : Tendsto (fun m : ℕ => (6:ℝ)*D/(m:ℝ)) atTop (nhds (0:ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun m : ℕ => ((boundaryGrid m D).card:ℝ)/(m:ℝ)^3) atTop (nhds (0:ℝ)) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) ?_ hz
    filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
    have hm0 : (0:ℝ) < m := by exact_mod_cast hm
    have hb : ((boundaryGrid m D).card:ℝ) ≤ 6*D*(m:ℝ)^2 := by exact_mod_cast card_boundaryGrid m D
    apply (div_le_iff₀ (by positivity : 0 < (m:ℝ)^3)).mpr
    calc
      _ ≤ 6*D*(m:ℝ)^2 := hb
      _ = _ := by field_simp
  have ht' : Tendsto (fun m : ℕ => 1-((boundaryGrid m D).card:ℝ)/(m:ℝ)^3) atTop (nhds (1:ℝ)) := by
    simpa using (tendsto_const_nhds.sub hsmall : Tendsto (fun m : ℕ => (1:ℝ)-((boundaryGrid m D).card:ℝ)/(m:ℝ)^3) atTop (nhds (1-0)))
  apply ht'.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  rw [hcard]
  field_simp

end RadialTransition

end

end OAI
