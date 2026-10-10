import OAI.MeasureTheory.Falconer.Estimates.SuffixCollision

namespace OAI

/-! # Transferring the suffix witness test to the cell-center direction

The test is imposed on the full conditional law in the witness direction.
Only the direction changes; its quadratic error is absorbed by the test
width before the original-law collision estimate is used.
-/

namespace Falconer
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalized_difference_le (u v : E) (hu : 0 < ‖u‖) (hv : 0 < ‖v‖) :
    ‖‖v‖⁻¹ • v - ‖u‖⁻¹ • u‖ ≤ 2*‖v-u‖/‖u‖ := by
  have he : ‖v‖⁻¹ • v - ‖u‖⁻¹ • u =
      ‖u‖⁻¹ • (v-u) + (‖v‖⁻¹-‖u‖⁻¹) • v := by module
  have hnorm : ‖(‖v‖⁻¹-‖u‖⁻¹) • v‖ = |‖u‖-‖v‖|/‖u‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    calc
      _ = |(‖v‖⁻¹-‖u‖⁻¹)*‖v‖| := by rw [abs_mul,abs_of_pos hv]
      _ = |(‖u‖-‖v‖)/‖u‖| := by congr 1; field_simp
      _ = _ := by rw [abs_div,abs_of_pos hu]
  rw [he]
  calc
    _ ≤ ‖‖u‖⁻¹ • (v-u)‖ + ‖(‖v‖⁻¹-‖u‖⁻¹) • v‖ := norm_add_le _ _
    _ = ‖v-u‖/‖u‖ + |‖u‖-‖v‖|/‖u‖ := by
      rw [hnorm,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hu]
      ring
    _ ≤ ‖v-u‖/‖u‖ + ‖v-u‖/‖u‖ := by
      exact add_le_add le_rfl (div_le_div_of_nonneg_right
        (by simpa only [abs_sub_comm] using abs_norm_sub_norm_le v u) hu.le)
    _ = _ := by ring

theorem DyadicCube.pair_direction_approximation {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    {g : ℝ} (hg : 0 < g) (hsep : g ≤ ‖P.center-Q.center‖)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) (hxy : x ≠ y) :
    ‖‖x-y‖⁻¹ • (x-y) - ‖P.center-Q.center‖⁻¹ • (P.center-Q.center)‖ ≤
      4*Real.sqrt d*P.side/g := by
  have hQp : 0 < Q.side := by rwa [hQ]
  have hδ : ‖(x-y)-(P.center-Q.center)‖ ≤ 2*Real.sqrt d*P.side := by
    have h₁ := P.dist_le hP.le hx (P.center_mem hP)
    have h₂ := Q.dist_le hQp.le hy (Q.center_mem hQp)
    rw [hQ] at h₂
    simpa only [dist_eq_norm,two_mul,mul_add,add_mul] using
      pair_displacement_bound x y P.center Q.center h₁ h₂
  calc
    _ ≤ 2*‖(x-y)-(P.center-Q.center)‖/‖P.center-Q.center‖ :=
      normalized_difference_le _ _ (hg.trans_le hsep) (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))
    _ ≤ 2*(2*Real.sqrt d*P.side)/g :=
      div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hδ (by norm_num)) hg hsep
    _ = _ := by ring

theorem cell_projection_direction_transfer {d : ℕ}
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (Q : DyadicCube d)
    (hQ : 0 ≤ Q.side) (e f : Space d) {κ w W : ℝ} (hκ : 0 ≤ κ)
    (hef : ‖e-f‖ ≤ κ) (hwidth : w+κ*Real.sqrt d*Q.side ≤ W) :
    ((μ.restrict Q.carrier).prod (μ.restrict Q.carrier))
      {z : Space d × Space d | |inner ℝ e (z.1-z.2)| ≤ w} ≤
    ((μ.restrict Q.carrier).prod (μ.restrict Q.carrier))
      {z : Space d × Space d | |inner ℝ f (z.1-z.2)| ≤ W} := by
  apply measure_mono_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem Q.measurable),
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem Q.measurable)] with z hz₁ hz₂
  intro hz
  have hdist := Q.dist_le hQ hz₁ hz₂
  rw [dist_eq_norm] at hdist
  have herr : |inner ℝ (f-e) (z.1-z.2)| ≤ κ*Real.sqrt d*Q.side := by
    calc
      _ ≤ ‖f-e‖*‖z.1-z.2‖ := abs_real_inner_le_norm _ _
      _ ≤ κ*(Real.sqrt d*Q.side) := mul_le_mul
        (by simpa only [norm_sub_rev] using hef) hdist (norm_nonneg _) hκ
      _ = _ := by ring
  have hid : inner ℝ f (z.1-z.2) =
      inner ℝ e (z.1-z.2)+inner ℝ (f-e) (z.1-z.2) := by
    rw [inner_sub_left]; ring
  rw [hid]
  exact ((abs_add_le _ _).trans (add_le_add hz herr)).trans hwidth

theorem suffix_witness_projection_transfer {d : ℕ}
    (ν : Measure (Space d)) [IsFiniteMeasure ν] (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    {g w W : ℝ} (hg : 0 < g) (hsep : g ≤ ‖P.center-Q.center‖)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) (hxy : x ≠ y)
    (hwidth : w+4*(d:ℝ)*P.side^2/g ≤ W) :
    ((ν.restrict Q.carrier).prod (ν.restrict Q.carrier))
      {z : Space d × Space d |
        |inner ℝ (‖P.center-Q.center‖⁻¹ • (P.center-Q.center)) (z.1-z.2)| ≤ w} ≤
    ((ν.restrict Q.carrier).prod (ν.restrict Q.carrier))
      {z : Space d × Space d | |inner ℝ (‖x-y‖⁻¹ • (x-y)) (z.1-z.2)| ≤ W} := by
  apply cell_projection_direction_transfer ν Q (by rw [hQ]; exact hP.le) _ _
    (show 0 ≤ 4*Real.sqrt d*P.side/g by positivity)
    (by simpa only [norm_sub_rev] using P.pair_direction_approximation Q hP hQ hg hsep hx hy hxy)
  rw [hQ]
  convert hwidth using 1
  rw [show 4*Real.sqrt (d:ℝ)*P.side/g*Real.sqrt d*P.side =
    4*(Real.sqrt d)^2*P.side^2/g by ring,Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) d)]

end Falconer

end OAI
