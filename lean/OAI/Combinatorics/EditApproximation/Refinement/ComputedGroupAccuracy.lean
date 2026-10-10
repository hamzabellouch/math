import OAI.Combinatorics.EditApproximation.Geometry.CellGroupSelection
import OAI.Combinatorics.EditApproximation.Refinement.ComputedGroupNumerical
import OAI.Combinatorics.EditApproximation.Refinement.ComputedBandSpacing

namespace OAI

/-! One actual whole cell has simultaneous gamma*b accuracy with failure at most H^-4. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

theorem computed_cellGroupEstimate_failure {α : Type*} (source target : List α)
    (N : ℕ) (hN : 0 < N) (hell : 1764 ≤ inputSmallLog N)
    {M P b Q thetaExponent T : ℕ} [NeZero M]
    [MeasurableSpace (Fin M)] [MeasurableSingletonClass (Fin M)]
    (hM : 0 < M) (hMeq : M = (integerParameters N).M)
    (hPeq : P = (integerParameters N).P) (eb : ℕ) (hbeq : b = 2 ^ eb)
    (hQeq : Q = inputSmallLog N ^ 80) (hthetaeq : thetaExponent = 40 * smallLogExponent N)
    (parent : TargetInterval source.length) (a : ℚ)
    (parentInitial : TargetInterval target.length → ℚ)
    (child initial value : Fin M → TargetInterval target.length → ℚ) (cell : ℕ × ℕ)
    (scales : Fin T → ℚ) (count : Fin T → ℕ)
    (hscales : List.ofFn scales = groupDyadicScales M b (inputSmallLog N))
    (hcount : ∀ scale, count scale = groupSampleCount M Q b (scales scale))
    (hspatial : ∀ i s t, initial i s ≤ initial i t +
      (32 * inputSmallLog N : ℚ) * targetEndpointDistance s t)
    (hvalue : ∀ i s, 0 ≤ value i s ∧ value i s ≤ initial i s)
    (bernstein : ∀ scale : Fin T, FiniteBernsteinInput
      (Measure.pi fun _ : Fin (count scale) => (PMF.uniformOfFintype (Fin M)).toMeasure)) :
    let members := cellUnskippedBands source target parent b P (inputSmallLog N) thetaExponent
      (rationalParameters (inputSmallLog N)).tau a parentInitial child initial cell
    (groupSharedDrawLaw count).real
      {draw | ∃ member ∈ members, ((rationalParameters (inputSmallLog N)).gamma : ℝ) * b <
        |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} ≤
      1 / (inputHeight N : ℝ) ^ 4 := by
  let ell := inputSmallLog N
  let members := cellUnskippedBands source target parent b P ell thetaExponent
    (rationalParameters ell).tau a parentInitial child initial cell
  let deviation : ℚ := 1 / (2 * (ell : ℚ) ^ 21)
  let μ := groupSharedDrawLaw (M := M) count
  let : IsProbabilityMeasure μ := by dsimp only [μ]; infer_instance
  have hellQ : (2 : ℚ) ≤ ell := by exact_mod_cast (show 2 ≤ ell from by omega)
  have hellpos : (0 : ℚ) < ell := by linarith only [hellQ]
  have hb : 0 < b := hbeq ▸ Nat.two_pow_pos eb
  have hQ : 0 < Q := by rw [hQeq]; exact pow_pos (by omega : 0 < inputSmallLog N) 80
  have htheta : (2 : ℚ) ^ (-(thetaExponent : ℤ)) = 1 / (ell : ℚ) ^ 40 := by
    rw [hthetaeq]
    exact (computed_theta_dyadic N).symm
  have hsmall : 2 * (32 * ell : ℚ) * (2 : ℚ) ^ (-(thetaExponent : ℤ)) ≤ 1 := by
    rw [htheta]
    have h := (basic_band_small_constants hellQ).2.2.2.2
    convert h using 1
    ring
  have hdev : 0 < deviation := by dsimp only [deviation]; positivity
  have htail := unskippedGroupEstimate_failure scales count Q hscales hcount value members hM hQ hb
    hellpos (32 * ell) (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hsmall hspatial hvalue deviation hdev bernstein
  have hT : T ≤ 2 * ell := by
    have hlength := congrArg List.length hscales
    simp only [List.length_ofFn] at hlength
    rw [hlength, hMeq, hbeq]
    exact computed_group_scale_count N eb hN (by omega)
  have hTQ : (T : ℚ) ≤ 2 * ell := by exact_mod_cast hT
  have hbudget : (T : ℚ) * deviation ≤ (rationalParameters ell).gamma := by
    have h := mul_le_mul_of_nonneg_right hTQ hdev.le
    have hid : (2 * ell : ℚ) * deviation = (rationalParameters ell).gamma := by
      dsimp only [deviation, rationalParameters]
      field_simp
    exact h.trans_eq hid
  have hbudgetR : (T : ℝ) * (deviation : ℝ) * b ≤
      ((rationalParameters ell).gamma : ℝ) * b := by
    have h := mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg (α := ℚ) b)
    exact_mod_cast h
  have hsubset : {draw | ∃ member ∈ members, ((rationalParameters ell).gamma : ℝ) * b <
        |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} ⊆
      {draw | ∃ member ∈ members, (T : ℝ) * (deviation : ℝ) * b <
        |((unskippedGroupEstimate scales count value member draw -
          rationalEndpointActionValue member.center member.rounded value : ℚ) : ℝ)|} := by
    rintro draw ⟨member, hm, he⟩
    exact ⟨member, hm, hbudgetR.trans_lt he⟩
  have hmembers : members.length ≤ ((integerParameters N).P + 1) ^ 2 := by
    rw [← hPeq]
    exact cellUnskippedBands_length_le source target parent b P ell thetaExponent _ a parentInitial
      child initial cell ⟨eb, hbeq⟩ ⟨_, hPeq.trans (computed_P_dyadic N)⟩
  have hnumerical := computed_group_union_failure N eb members.length hN hell hmembers
  dsimp only at hnumerical
  have hTeq : T = (groupDyadicScales (integerParameters N).M (2 ^ eb) ell).length := by
    have hlength := congrArg List.length hscales
    simpa only [List.length_ofFn, hMeq, hbeq] using hlength
  change μ.real _ ≤ _
  apply (measureReal_mono hsubset (measure_ne_top μ _)).trans
  apply htail.trans
  rw [hQeq, hTeq]
  simpa only [deviation, ell, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_one, Nat.cast_pow, neg_mul, neg_div] using hnumerical

end EditApproximation

end OAI
