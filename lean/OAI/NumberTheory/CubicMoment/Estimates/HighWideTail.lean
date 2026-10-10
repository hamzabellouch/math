import OAI.NumberTheory.CubicMoment.Estimates.UniformHighTail
import OAI.NumberTheory.CubicMoment.Estimates.TailDyads

namespace OAI

/-! Fixed-width support version of the uniform power-width tail. The same
positive exponent is chosen before all coefficient arities and energies. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem high_wide_envelope_tail_uniform
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (Mα Mβ D Q : ℝ),
      0 ≤ Mα → 0 ≤ Mβ → 1 ≤ D → 1 ≤ Q → ∀ (n dα dβ : ℕ)
      (W : ℝ → ℂ), HasCompactSupport W → tsupport W ⊆ Set.Ioi 0 →
      ContDiff ℝ ∞ W → ∃ K B₀ : ℝ, 0 < K ∧
      ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ) (B A X T H : ℝ),
      B₀ ≤ B → 4*(2*D*B)^(3/2:ℝ) ≤ A →
      Q*A ≤ B^(2+γ) → A ≤ B^3 → 0 < X →
      (2*D*B)^(1/50:ℝ) ≤ T → 1 ≤ H → H ≤ B^3 →
      (∀ x ∈ P, primary x ∧ A ≤ norm x ∧ norm x ≤ Q*A) →
      (∀ y ∈ S, primary y ∧ Squarefree y ∧ B ≤ norm y ∧ norm y ≤ D*B) →
      (∑ x ∈ P, ‖α x‖^2) ≤ Mα*A*(1+Real.log B)^dα →
      (∑ y ∈ S, ‖β y‖^2) ≤ Mβ*B*(1+Real.log B)^dβ →
      ‖envelopeCutoffBilinearTail P S α β W H T X‖ ≤
        K*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^n := by
  obtain ⟨γ,hγ,huniform⟩ := high_energy_envelope_cutoff_tail_uniform hMV hC hHuxley
  refine ⟨γ,hγ,?_⟩
  intro Mα Mβ D Q hMα hMβ hD hQ n dα dβ W hW hpos hsm
  obtain ⟨K,Z₀,hK,hbound⟩ := huniform (2*Mα) Mβ (by positivity) hMβ
    (n+2) dα dβ W hW hpos hsm
  obtain ⟨C₀,hC₀,hcount⟩ := stoppedNormDyad_count_power
  let KP := 3*C₀*(1+Real.log Q)
  let KS := 3*C₀*(1+Real.log D)
  let R := K*Q^(5/6:ℝ)*(2*D)^(5/6:ℝ)
  refine ⟨KP*KS*R,max Z₀ ((65536:ℝ)^2),
    by dsimp [KP,KS,R]; positivity [Real.log_nonneg hQ,Real.log_nonneg hD],?_⟩
  intro P S α β B A X T H hB hAlow hAup hA3 hX hT hH hHB hP hS hea heb
  have hBbig : (65536:ℝ)^2 ≤ B := (le_max_right _ _).trans hB
  have hB1 : 1 ≤ B := by nlinarith
  have hBp : 0 < B := zero_lt_one.trans_le hB1
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hQp : 0 < Q := zero_lt_one.trans_le hQ
  have hAB : B ≤ A := by
    have hb : B ≤ (2*D*B)^(3/2:ℝ) := by
      calc
        B ≤ 2*D*B := by nlinarith
        _ = (2*D*B)^(1:ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by nlinarith : (1:ℝ) ≤ 2*D*B) (by norm_num)
    have hp := Real.rpow_nonneg (by positivity : 0 ≤ 2*D*B) (3/2:ℝ)
    linarith
  have hA1 : 1 ≤ A := hB1.trans hAB
  have hAp : 0 < A := hBp.trans_le hAB
  have hL : 0 < 1+Real.log B := by linarith [Real.log_nonneg hB1]
  have hrow (r : ℕ) (hr : r ∈ P.image stoppedNormDyadIndex)
      (s : ℕ) (hs : s ∈ S.image stoppedNormDyadIndex) :
      ‖envelopeCutoffBilinearTail (stoppedNormDyad P r) (stoppedNormDyad S s)
        α β W H T X‖ ≤ R*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^(n+2) := by
    let A' := stoppedNormDyadLength r/2
    let Z := stoppedNormDyadLength s
    obtain ⟨x,hx,hxr⟩ := Finset.mem_image.mp hr
    obtain ⟨y,hy,hys⟩ := Finset.mem_image.mp hs
    have hxd := stoppedNormDyad_outer_bounds (Finset.mem_filter.mpr ⟨hx,hxr⟩) (hP x hx).1
    have hyd := stoppedNormDyad_outer_bounds (Finset.mem_filter.mpr ⟨hy,hys⟩) (hS y hy).1
    have hAr : A/2 ≤ A' := by dsimp [A']; linarith [(hP x hx).2.1]
    have hArup : A' ≤ Q*A := hxd.1.trans (hP x hx).2.2
    have hBZ : B ≤ Z := (hS y hy).2.2.1.trans hyd.2
    have hZB : Z ≤ 2*D*B := by dsimp [Z]; linarith [(hS y hy).2.2.2]
    have hZ1 : 1 ≤ Z := hB1.trans hBZ
    have hZp : 0 < Z := hBp.trans_le hBZ
    have hArp : 0 < A' := (div_pos hAp (by norm_num)).trans_le hAr
    have hlog : 1+Real.log B ≤ 1+Real.log Z := by linarith [Real.log_le_log hBp hBZ]
    have hAlow' : 2*Z^(3/2:ℝ) ≤ A' := by
      have hh := Real.rpow_le_rpow hZp.le hZB (by norm_num : (0:ℝ) ≤ 3/2)
      linarith
    have hAup' : A' ≤ Z^(2+γ) :=
      (hArup.trans hAup).trans (Real.rpow_le_rpow hBp.le hBZ (by linarith))
    have hT' : Z^(1/50:ℝ) ≤ T :=
      (Real.rpow_le_rpow hZp.le hZB (by norm_num)).trans hT
    have hPa : ∀ x ∈ stoppedNormDyad P r, primary x ∧ 1 ≤ norm x/A' ∧ norm x/A' ≤ 2 := by
      intro x hx
      have hpx := (hP x (Finset.mem_filter.mp hx).1).1
      have hd := stoppedNormDyad_outer_bounds hx hpx
      exact ⟨hpx,(le_div_iff₀ hArp).mpr (by simpa only [one_mul] using hd.1),
        (div_le_iff₀ hArp).mpr (by dsimp [A']; linarith)⟩
    have hSb : ∀ y ∈ stoppedNormDyad S s,
        primary y ∧ Squarefree y ∧ Z/2 ≤ norm y ∧ norm y ≤ Z := by
      intro y hy
      have hpy := hS y (Finset.mem_filter.mp hy).1
      have hd := stoppedNormDyad_outer_bounds hy hpy.1
      exact ⟨hpy.1,hpy.2.1,hd⟩
    have hea' : (∑ x ∈ stoppedNormDyad P r, ‖α x‖^2) ≤
        (2*Mα)*A'*(1+Real.log Z)^dα := by
      apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)).trans
      apply hea.trans
      have hh := mul_le_mul
        (mul_le_mul_of_nonneg_left (show A ≤ 2*A' by linarith) hMα)
        (pow_le_pow_left₀ hL.le hlog dα) (by positivity) (by positivity)
      convert hh using 1; ring
    have heb' : (∑ y ∈ stoppedNormDyad S s, ‖β y‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ := by
      apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => sq_nonneg _)).trans
      exact heb.trans (mul_le_mul (mul_le_mul_of_nonneg_left hBZ hMβ)
        (pow_le_pow_left₀ hL.le hlog dβ) (by positivity) (by positivity))
    have hh := hbound (stoppedNormDyad P r) (stoppedNormDyad S s) α β Z A' X T H
      (((le_max_left _ _).trans hB).trans hBZ) hAlow' hAup' hX hT' hH
      (hHB.trans (pow_le_pow_left₀ hBp.le hBZ 3)) hPa hSb
      hea' heb'
    apply hh.trans
    calc
      _ ≤ K*(Q*A)^(5/6:ℝ)*(2*D*B)^(5/6:ℝ)/(1+Real.log B)^(n+2) := by
        apply div_le_div₀ (by positivity)
          (mul_le_mul (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hArp.le hArup (by norm_num)) hK.le)
            (Real.rpow_le_rpow hZp.le hZB (by norm_num)) (by positivity) (by positivity))
          (pow_pos hL _) (pow_le_pow_left₀ hL.le hlog _)
      _ = _ := by
        rw [Real.mul_rpow hQp.le hAp.le,Real.mul_rpow (by positivity : 0 ≤ 2*D) hBp.le]
        dsimp [R]
        ring
  have hPc := hcount P Q A B hQ hA1 hB1 hA3 (fun x hx => (hP x hx).2.2)
  have hBc : B ≤ B^3 := le_self_pow₀ hB1 (by norm_num : 3 ≠ 0)
  have hSc := hcount S D B B hD hB1 hB1 hBc (fun y hy => (hS y hy).2.2.2)
  have hb := envelopeCutoffBilinearTail_dyads_bound P S α β W H T X _ hrow
  apply hb.trans
  calc
    _ ≤ (KP*(1+Real.log B))*(KS*(1+Real.log B))*
        (R*A^(5/6:ℝ)*B^(5/6:ℝ)/(1+Real.log B)^(n+2)) := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [R]; positivity)
      exact mul_le_mul hPc hSc (Nat.cast_nonneg _) (by dsimp [KP]; positivity [Real.log_nonneg hQ])
    _ = _ := by rw [pow_add]; norm_num; field_simp

end CubicFirstMoment

end

end OAI
