import OAI.MeasureTheory.Falconer.Shells.PositiveTests

namespace OAI

/-! # The suffix scale hypotheses in the manuscript's separated geometry -/

namespace Falconer
open Set MeasureTheory

theorem sqrt_dimension_le (d : ℕ) : Real.sqrt (d : ℝ) ≤ (d : ℝ)+1 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith [sq_nonneg (d : ℝ),Nat.cast_nonneg (α := ℝ) d]

theorem dyadic_side_mono {a p : ℕ} (h : a ≤ p) :
    1/(2:ℝ)^p ≤ 1/(2:ℝ)^a :=
  div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (pow_le_pow_right₀ (by norm_num) h)

theorem dyadic_side_le_radius {σ : ℝ} (hσ : 0 ≤ σ) (N L : ℕ) :
    1/(2:ℝ)^L ≤ angularTestRadius N σ L := by
  apply le_min
  · exact (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
  · exact le_mul_of_one_le_right (by positivity)
      (Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity))

theorem suffix_linearization_scale (d : ℕ) {a p t : ℕ} (hapt : a+t ≤ 2*p) :
    2*(d:ℝ)*(1/(2:ℝ)^p)^2/(100*((d:ℝ)+1)/(2:ℝ)^a) ≤ 1/(2:ℝ)^t := by
  have hc : 2*(d:ℝ)/(100*((d:ℝ)+1)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) d])
  calc
    _ = (2*(d:ℝ)/(100*((d:ℝ)+1))) *
        ((1/(2:ℝ)^p)^2/(1/(2:ℝ)^a)) := by field_simp
    _ ≤ 1*((1/(2:ℝ)^p)^2/(1/(2:ℝ)^a)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ _ := by simpa only [one_mul] using dyadic_suffix_error hapt

theorem suffix_direction_small (d : ℕ) {a p : ℕ} (hap : a ≤ p) :
    2*Real.sqrt d*(1/(2:ℝ)^p) < 100*((d:ℝ)+1)/(2:ℝ)^a := by
  calc
    _ ≤ 2*((d:ℝ)+1)*(1/(2:ℝ)^a) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (sqrt_dimension_le d) (by norm_num))
        (dyadic_side_mono hap) (by positivity) (by positivity)
    _ < 100*((d:ℝ)+1)/(2:ℝ)^a := by
      have hp : 0 < ((d:ℝ)+1)/(2:ℝ)^a := by positivity
      calc
        _ = 2*(((d:ℝ)+1)/(2:ℝ)^a) := by ring
        _ < 100*(((d:ℝ)+1)/(2:ℝ)^a) := mul_lt_mul_of_pos_right (by norm_num) hp
        _ = _ := by ring

theorem suffix_direction_buffer (d : ℕ) {σ : ℝ} (hσ : 0 ≤ σ)
    (N : ℕ) {a p L : ℕ} (hap : a ≤ p) (hL : L ≤ p-a) :
    8*Real.sqrt d*(1/(2:ℝ)^p)/(100*((d:ℝ)+1)/(2:ℝ)^a) ≤
      angularTestRadius N σ L := by
  have hc : 8*Real.sqrt d/(100*((d:ℝ)+1)) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by
      have hs := sqrt_dimension_le d
      nlinarith [Nat.cast_nonneg (α := ℝ) d])
  have hp : (2:ℝ)^a*(2:ℝ)^(p-a) = (2:ℝ)^p := by
    rw [← pow_add,Nat.add_sub_of_le hap]
  calc
    _ = (8*Real.sqrt d/(100*((d:ℝ)+1)))*(1/(2:ℝ)^(p-a)) := by
      rw [← hp]
      field_simp
    _ ≤ 1/(2:ℝ)^(p-a) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc
        (by positivity : 0 ≤ 1/(2:ℝ)^(p-a))
    _ ≤ 1/(2:ℝ)^L := dyadic_side_mono hL
    _ ≤ _ := dyadic_side_le_radius hσ N L

theorem uniform_suffix_witness_width (d : ℕ) {σ : ℝ} (hσ : 0 < σ)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a p t : ℕ, a+t ≤ 2*p → ∀ i ≤ J,
      1/(2:ℝ)^t+4*(d:ℝ)*(1/(2:ℝ)^p)^2/(100*((d:ℝ)+1)/(2:ℝ)^a) ≤
        angularTestWidth N σ J i t := by
  obtain ⟨N₀,h₀⟩ := uniform_suffix_test_width hσ hJ 1
    (4*(d:ℝ)/(100*((d:ℝ)+1))) (by positivity)
  refine ⟨N₀,?_⟩
  intro N hN a p t hapt i hi
  convert h₀ N hN a p t hapt i hi using 1
  field_simp

theorem DyadicCube.separated_pairs_lower {d : ℕ} (P Q : DyadicCube d)
    (hP : 0 < P.side) (hQ : Q.side = P.side)
    (hsep : 125*((d:ℝ)+1)*P.side ≤ ‖P.center-Q.center‖)
    {x y : Space d} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    100*((d:ℝ)+1)*P.side ≤ ‖x-y‖ := by
  have hQp : 0 < Q.side := by rwa [hQ]
  have h₁ := P.dist_le hP.le hx (P.center_mem hP)
  have h₂ := Q.dist_le hQp.le hy (Q.center_mem hQp)
  rw [hQ] at h₂
  have hδ : ‖(x-y)-(P.center-Q.center)‖ ≤ 2*Real.sqrt d*P.side := by
    simpa only [dist_eq_norm,two_mul,mul_add,add_mul] using
      pair_displacement_bound x y P.center Q.center h₁ h₂
  have hnorm : ‖P.center-Q.center‖ ≤ ‖x-y‖+‖(x-y)-(P.center-Q.center)‖ := by
    have he : P.center-Q.center = (x-y)-((x-y)-(P.center-Q.center)) := by abel
    calc
      _ = ‖(x-y)-((x-y)-(P.center-Q.center))‖ := congrArg norm he
      _ ≤ _ := norm_sub_le _ _
  have hs := mul_le_mul_of_nonneg_right (sqrt_dimension_le d) hP.le
  nlinarith [Nat.cast_nonneg (α := ℝ) d]

end Falconer

end OAI
