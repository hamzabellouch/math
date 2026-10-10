import OAI.InformationTheory.BooleanNoise.EntropyScalars
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace OAI

noncomputable section

open Filter Set
open scoped Topology

namespace LeanBlast.CourtadeKumar

theorem tendsto_artanh_div_id_zero_right :
    Tendsto (fun u : ℝ => Real.artanh u / u) (𝓝[>] 0) (𝓝 1) := by
  have hd : HasDerivAt Real.artanh 1 0 := by
    simpa using hasDerivAt_artanh (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right

theorem tendsto_id_div_artanh_zero_right :
    Tendsto (fun u : ℝ => u / Real.artanh u) (𝓝[>] 0) (𝓝 1) := by
  simpa only [inv_div, inv_one] using
    tendsto_artanh_div_id_zero_right.inv₀ (show (1 : ℝ) ≠ 0 by norm_num)

theorem tendsto_entropy_inverse_derivative_zero_right :
    Tendsto (fun u : ℝ => 1 + u / ((1 - u ^ 2) * Real.artanh u))
      (𝓝[>] 0) (𝓝 2) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hden : Tendsto (fun u : ℝ => 1 - u ^ 2) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hu.pow 2)
  have hquot := tendsto_id_div_artanh_zero_right.div hden (show (1 : ℝ) ≠ 0 by norm_num)
  have hadd :
    Tendsto (fun u : ℝ => 1 + (u / Real.artanh u) / (1 - u ^ 2))
      (𝓝[>] 0) (𝓝 ((1 : ℝ) + 1 / 1)) := tendsto_const_nhds.add hquot
  norm_num [div_div, mul_comm] at hadd ⊢
  exact hadd

theorem tendsto_artanh_mul_id_div_psi_zero_right :
    Tendsto (fun u : ℝ => (u * Real.artanh u) / psi u) (𝓝[>] 0) (𝓝 2) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hda : HasDerivAt Real.artanh 1 0 := by
    simpa using hasDerivAt_artanh (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)
  have ha : Tendsto Real.artanh (𝓝[>] 0) (𝓝 0) := by
    simpa using hda.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hp : Tendsto psi (𝓝[>] 0) (𝓝 0) := by
    simpa [psi] using
      (hasDerivAt_psi (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
  have hquot : Tendsto
      (fun u : ℝ => (Real.artanh u + u / (1 - u ^ 2)) / Real.artanh u)
      (𝓝[>] 0) (𝓝 2) := by
    apply tendsto_entropy_inverse_derivative_zero_right.congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
    have hne : Real.artanh u ≠ 0 := ne_of_gt (Real.artanh_pos hu)
    rw [add_div, div_self hne, div_div]
  apply HasDerivAt.lhopital_zero_right_on_Ioo
    (f' := fun u => Real.artanh u + u / (1 - u ^ 2))
    (g' := Real.artanh) (show (0 : ℝ) < 1 by norm_num)
  · intro u hu
    convert! (hasDerivAt_id u).mul
      (hasDerivAt_artanh (show u ∈ Ioo (-1) 1 from ⟨by linarith [hu.1], hu.2⟩)) using 1
    simp [id_eq, div_eq_mul_inv]
  · intro u hu
    exact hasDerivAt_psi ⟨by linarith [hu.1], hu.2⟩
  · intro u hu
    exact ne_of_gt (Real.artanh_pos hu)
  · simpa using hu.mul ha
  · exact hp
  · exact hquot

theorem tendsto_psi_div_sq_zero_right :
    Tendsto (fun u : ℝ => psi u / u ^ 2) (𝓝[>] 0) (𝓝 (1 / 2 : ℝ)) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  apply HasDerivAt.lhopital_zero_right_on_Ioo
    (f' := Real.artanh) (g' := fun u => 2 * u) (show (0 : ℝ) < 1 by norm_num)
  · intro u hu
    exact hasDerivAt_psi ⟨by linarith [hu.1], hu.2⟩
  · intro u _
    convert! (hasDerivAt_id u).pow 2 using 1
    simp
  · intro u hu
    exact mul_ne_zero (by norm_num) (ne_of_gt hu.1)
  · simpa using (continuous_psi.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · simpa using hu.pow 2
  · simpa [div_div, mul_comm] using tendsto_artanh_div_id_zero_right.div_const 2

private theorem endpoint_one_sub_sq_pos {u : ℝ} (hu : u ∈ Ioo 0 1) :
    0 < 1 - u ^ 2 := by
  have h := mul_pos (show 0 < 1 + u by linarith [hu.1]) (sub_pos.mpr hu.2)
  nlinarith

theorem tendsto_artanh_sub_id_div_cube_zero_right :
    Tendsto (fun u : ℝ => (Real.artanh u - u) / u ^ 3)
      (𝓝[>] 0) (𝓝 (1 / 3 : ℝ)) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hda : HasDerivAt Real.artanh 1 0 := by
    simpa using hasDerivAt_artanh (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num)
  have ha : Tendsto Real.artanh (𝓝[>] 0) (𝓝 0) := by
    simpa using hda.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun u : ℝ => 3 * (1 - u ^ 2)) (𝓝[>] 0) (𝓝 3) := by
    convert tendsto_const_nhds.mul (tendsto_const_nhds.sub (hu.pow 2)) using 1
    norm_num
  have hquot : Tendsto (fun u : ℝ => (1 / (1 - u ^ 2) - 1) / (3 * u ^ 2))
      (𝓝[>] 0) (𝓝 (1 / 3 : ℝ)) := by
    apply (tendsto_const_nhds.div hden (show (3 : ℝ) ≠ 0 by norm_num)).congr'
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
    have hu0 := ne_of_gt hu.1
    have hsq := ne_of_gt (endpoint_one_sub_sq_pos hu)
    dsimp
    field_simp
    ring
  apply HasDerivAt.lhopital_zero_right_on_Ioo
    (f' := fun u => 1 / (1 - u ^ 2) - 1) (g' := fun u => 3 * u ^ 2)
    (show (0 : ℝ) < 1 by norm_num)
  · intro u hu
    exact (hasDerivAt_artanh ⟨by linarith [hu.1], hu.2⟩).sub (hasDerivAt_id u)
  · intro u _
    convert! (hasDerivAt_id u).pow 3 using 1
    simp
  · intro u hu
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (ne_of_gt hu.1))
  · simpa using ha.sub hu
  · simpa using hu.pow 3
  · exact hquot

theorem tendsto_entropy_inverse_second_derivative_zero_right :
    Tendsto (fun u : ℝ =>
      ((1 + u ^ 2) * Real.artanh u - u) /
        ((1 - u ^ 2) ^ 2 * (Real.artanh u) ^ 3))
      (𝓝[>] 0) (𝓝 (4 / 3 : ℝ)) := by
  have hu : Tendsto (fun u : ℝ => u) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hnum : Tendsto
      (fun u : ℝ => (Real.artanh u - u) / u ^ 3 + Real.artanh u / u)
      (𝓝[>] 0) (𝓝 (4 / 3 : ℝ)) := by
    convert tendsto_artanh_sub_id_div_cube_zero_right.add tendsto_artanh_div_id_zero_right
      using 1
    norm_num
  have hden : Tendsto
      (fun u : ℝ => (1 - u ^ 2) ^ 2 * (Real.artanh u / u) ^ 3)
      (𝓝[>] 0) (𝓝 1) := by
    convert ((tendsto_const_nhds.sub (hu.pow 2)).pow 2).mul
      (tendsto_artanh_div_id_zero_right.pow 3) using 1
    norm_num
  have h := hnum.div hden (show (1 : ℝ) ≠ 0 by norm_num)
  simp only [div_one] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
  have hu0 := ne_of_gt hu.1
  have ha0 := ne_of_gt (Real.artanh_pos hu)
  have hsq := ne_of_gt (endpoint_one_sub_sq_pos hu)
  dsimp
  field_simp
  ring

end LeanBlast.CourtadeKumar

end

end OAI
