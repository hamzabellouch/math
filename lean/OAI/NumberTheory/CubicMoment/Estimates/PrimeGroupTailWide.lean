import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailBilinear
import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDyadPartition
import OAI.NumberTheory.CubicMoment.Estimates.OverlapScale

namespace OAI

/-! Fixed-width supports are split into their actual norm dyads. The resulting
height bound has no upper restriction on height or on its translation. -/
noncomputable section
open Filter
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem primeGroupTail_wide_bilinear_log_saving
    {C Mα Mβ D : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ)
    (hD : 1 ≤ D) (k dα dβ : ℕ) (Q : ℝ) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
      (B A T u : ℝ), B₀ ≤ B → (2*D*B)^(27/25:ℝ) ≤ A →
      A ≤ B^(19/10:ℝ) → (2*D*B)^(1/50:ℝ) ≤ T →
      (∀ a ∈ P, primary a ∧ A ≤ norm a ∧ norm a ≤ Q*A) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ B ≤ norm b ∧ norm b ≤ D*B) →
      (∑ a ∈ P, ‖α a‖^2) ≤ Mα*A*(1+Real.log B)^dα →
      (∑ b ∈ S, ‖β b‖^2) ≤ Mβ*B*(1+Real.log B)^dβ →
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist (u+t) (a*b)‖) T ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^k := by
  let G := 3*(2*(k+1)+dα+dβ)
  obtain ⟨K,hK,hbound⟩ := primeGroupTail_bilinear_log_saving hMV hC hHuxley
    hMα hMβ (k+1) dα dβ Q
  obtain ⟨C₀,hC₀,hcount⟩ := metaplectic_dyad_count_log_bound
  obtain ⟨B₀,hB₀⟩ := eventually_atTop.mp
    (overlap_power_log_saving (by norm_num : (0:ℝ) < 1/10) G 0)
  let K₀ := C₀*(1+Real.log D)*K*(2*D)^(5/6:ℝ)
  refine ⟨K₀,max 65536 B₀,by dsimp [K₀]; positivity [Real.log_nonneg hD],?_⟩
  intro P S α β B A T u hB hA hAhi hT hP hS hα hβ
  have hBlarge : 65536 ≤ B := (le_max_left _ _).trans hB
  have hB₁ : 1 ≤ B := by linarith
  have hBp : 0 < B := by linarith
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hAp : 0 < A := (Real.rpow_pos_of_pos (by positivity : 0 < 2*D*B) _).trans_le hA
  have hTp : 0 < T := (Real.rpow_pos_of_pos (by positivity : 0 < 2*D*B) _).trans_le hT
  have hL : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB₁]
  let I := S.image stoppedNormDyadIndex
  let F := fun j t => ∑ a ∈ P, ∑ b ∈ stoppedNormDyad S j,
    α a*β b*gauss (a*b)*normTwist (u+t) (a*b)
  have hfc (j : ℕ) : Continuous (F j) := by
    apply continuous_finsetSum
    intro a ha
    apply continuous_finsetSum
    intro b hb
    exact continuous_const.mul ((continuous_normTwist (a*b)).comp
      (continuous_const.add continuous_id))
  have he (t : ℝ) : (∑ a ∈ P, ∑ b ∈ S,
      α a*β b*gauss (a*b)*normTwist (u+t) (a*b)) = ∑ j ∈ I, F j t := by
    rw [Finset.sum_comm]
    rw [stoppedNormDyad_partition S]
    apply Finset.sum_congr rfl
    intro j hj
    exact Finset.sum_comm
  have hrow (j : ℕ) (hj : j ∈ I) :
      dyadicHeightMean (fun t => ‖F j t‖) T ≤
        K*(2*D)^(5/6:ℝ)*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^(k+1) := by
    let Z := stoppedNormDyadLength j
    obtain ⟨b,hb,hbj⟩ := Finset.mem_image.mp hj
    have hb' : b ∈ stoppedNormDyad S j := Finset.mem_filter.mpr ⟨hb,hbj⟩
    have hz := stoppedNormDyad_bounds hb' (by linarith [(hS b hb).2.2.1])
    have hBZ : B ≤ Z := (hS b hb).2.2.1.trans hz.2
    have hZB : Z ≤ 2*D*B := by
      have hlo : Z/2 < norm b := hz.1
      linarith [(hS b hb).2.2.2]
    have hZ₁ : 1 ≤ Z := hB₁.trans hBZ
    have hZp : 0 < Z := hBp.trans_le hBZ
    have hlog : 1+Real.log B ≤ 1+Real.log Z := by
      linarith [Real.log_le_log hBp hBZ]
    have hlogZ : (1+Real.log Z)^G ≤ Z^(1/10:ℝ) := by
      have hh := hB₀ Z (((le_max_right _ _).trans hB).trans hBZ)
      simpa only [Nat.mul_zero,pow_zero,div_one,one_mul] using
        (div_le_iff₀ (Real.rpow_pos_of_pos hZp (1/10:ℝ))).mp hh
    have hupper : A ≤ Z^2/(1+Real.log Z)^G := by
      apply (le_div_iff₀ (pow_pos (by linarith [Real.log_nonneg hZ₁]) G)).mpr
      calc
        _ ≤ Z^(19/10:ℝ)*Z^(1/10:ℝ) := mul_le_mul
          (hAhi.trans (Real.rpow_le_rpow hBp.le hBZ (by norm_num))) hlogZ
          (pow_nonneg (hL.le.trans hlog) G) (Real.rpow_nonneg hZp.le _)
        _ = _ := by rw [←Real.rpow_add hZp]; norm_num
    have hS' : ∀ b ∈ stoppedNormDyad S j,
        primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z := by
      intro b hb
      have hs := hS b (Finset.mem_filter.mp hb).1
      have hd := stoppedNormDyad_bounds hb (by linarith [hs.2.2.1])
      exact ⟨hs.1,hs.2.1,hd.1.le,hd.2⟩
    have ha' : (∑ a ∈ P, ‖α a‖^2) ≤ Mα*A*(1+Real.log Z)^dα :=
      hα.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le hlog dα) (by positivity))
    have hb' : (∑ b ∈ stoppedNormDyad S j, ‖β b‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ := by
      apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)).trans
      exact hβ.trans (mul_le_mul
        (mul_le_mul_of_nonneg_left hBZ hMβ) (pow_le_pow_left₀ hL.le hlog dβ)
        (by positivity) (by positivity))
    have hh := hbound P (stoppedNormDyad S j) α β Z A T u (hBlarge.trans hBZ)
      ((Real.rpow_le_rpow hZp.le hZB (by norm_num)).trans hA) hupper
      ((Real.rpow_le_rpow hZp.le hZB (by norm_num)).trans hT) hP hS' ha' hb'
    apply hh.trans
    calc
      _ ≤ K*A^(5/6:ℝ)*(2*D*B)^(5/6:ℝ)/(1+Real.log B)^(k+1) := by
        apply div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hZp.le hZB (by norm_num)) (by positivity))
          (pow_pos hL _) (pow_le_pow_left₀ hL.le hlog _)
      _ = _ := by rw [Real.mul_rpow (by positivity : 0 ≤ 2*D) hBp.le]; ring
  have hcard : (I.card:ℝ) ≤ C₀*(1+Real.log D)*(1+Real.log B) := by
    have hc := stoppedNormDyad_count S (fun b hb => (hS b hb).2.2.2)
    have hm : Nat.log 2 ⌊D*B⌋₊+1 ≤ Nat.log 2 ⌊3*(D*B)⌋₊+1 :=
      Nat.add_le_add_right (Nat.log_mono_right (Nat.floor_mono (by nlinarith))) 1
    apply (Nat.cast_le.mpr (hc.trans hm)).trans
    apply (hcount (D*B) (one_le_mul_of_one_le_of_one_le hD hB₁)).trans
    rw [Real.log_mul hDp.ne' hBp.ne']
    have hdlog := Real.log_nonneg hD
    have hblog := Real.log_nonneg hB₁
    calc
      _ ≤ C₀*((1+Real.log D)*(1+Real.log B)) :=
        mul_le_mul_of_nonneg_left (by nlinarith [mul_nonneg hdlog hblog]) hC₀.le
      _ = _ := by ring
  simp_rw [he]
  apply (dyadicHeightMean_norm_sum_le I F (fun j _ => hfc j) hTp).trans
  apply (Finset.sum_le_sum hrow).trans
  simp only [Finset.sum_const,nsmul_eq_mul]
  calc
    _ ≤ (C₀*(1+Real.log D)*(1+Real.log B))*
        (K*(2*D)^(5/6:ℝ)*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^(k+1)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by dsimp [K₀]; rw [pow_succ]; field_simp

end CubicFirstMoment

end

end OAI
