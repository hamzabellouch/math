import OAI.NumberTheory.CubicMoment.Estimates.LowCoprimeDispersion
import OAI.NumberTheory.CubicMoment.Estimates.LowNormScale
import OAI.NumberTheory.CubicMoment.Estimates.SmallBRealLength

namespace OAI
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment.ProfileControl

theorem low_coprime_height_real (hpnt : PrimaryPrimePNT) (k : ℕ)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (P : PoissonProfileBudget) (S : Finset Eisenstein) (v : Eisenstein → ℂ)
      (Z A T M u : ℝ), 65536 ≤ (⌊Z⌋₊:ℝ) → 16 ≤ (⌊Z⌋₊:ℝ)^(3/4:ℝ) → 0 ≤ M →
      (1+Real.log Z)^Ct ≤ T → Z^(3/2:ℝ) ≤ A →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖v b‖ ≤ M) →
      dyadicHeightMean (fun t =>
        ‖coprimeGramForm S (fun b => v b*star (normTwist (u+t) b)) P.V A‖) T ≤
        (K*P.cost)*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨K₀,Ct,hK₀,hbound₀⟩ := low_coprime_dispersion_height_log_saving hpnt k hMV hC hHuxley
  refine ⟨K₀*(2:ℝ)^k,Ct,by positivity,?_⟩
  intro P S v Z A T M u hZ hlarge hM hT hA hS hv
  let K := K₀*P.cost
  have hK : 0 < K := mul_pos hK₀ P.cost_pos
  have hbound := hbound₀ P
  have hZ₀ : 0 ≤ Z := by
    by_contra h
    have hf : ⌊Z⌋₊ = 0 := Nat.floor_of_nonpos (le_of_not_ge h)
    simp only [hf,Nat.cast_zero] at hZ
    linarith
  have hf : (⌊Z⌋₊:ℝ) ≤ Z := Nat.floor_le hZ₀
  have hA₀ : 0 ≤ A := (Real.rpow_nonneg hZ₀ _).trans hA
  have hS' : ∀ b ∈ S, primary b ∧ Squarefree b ∧
      (⌊Z⌋₊:ℝ)/2 ≤ norm b ∧ norm b ≤ (⌊Z⌋₊:ℝ) := by
    intro b hb
    refine ⟨(hS b hb).1,(hS b hb).2.1,?_,?_⟩
    · linarith [(hS b hb).2.2.1]
    · have hh : normNat b ≤ ⌊Z⌋₊ := Nat.le_floor (by
        rw [normNat_cast]
        exact (hS b hb).2.2.2)
      have hr : (normNat b : ℝ) ≤ (⌊Z⌋₊:ℝ) := by exact_mod_cast hh
      rwa [normNat_cast] at hr
  have hfloor1 : 1 ≤ (⌊Z⌋₊:ℝ) := by linarith
  have hZ1 : 1 ≤ Z := hfloor1.trans hf
  have hfloorp : 0 < (⌊Z⌋₊:ℝ) := by linarith
  have hLp : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hLfp : 0 < 1+Real.log (⌊Z⌋₊:ℝ) := by linarith [Real.log_nonneg hfloor1]
  have hTf : (1+Real.log (⌊Z⌋₊:ℝ))^Ct ≤ T := by
    apply le_trans _ hT
    apply pow_le_pow_left₀ (by linarith [Real.log_nonneg hfloor1])
    linarith [Real.log_le_log hfloorp hf]
  have hv' : ∀ b ∈ S, ‖gramUntwist v b‖ ≤ M := by
    intro b hb
    rw [gramUntwist_norm (hS b hb).1 (hS b hb).2.1]
    exact hv b hb
  have hh := hbound S (gramUntwist v) ⌊Z⌋₊ A T M u hZ hlarge hM hTf
    ((Real.rpow_le_rpow (by positivity) hf (by norm_num)).trans hA) hS' hv'
  have he (t : ℝ) := coprimeGramForm_height_eq S
    (fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩) v (u+t) P.V A
  simp_rw [← he] at hh
  have hratio : (⌊Z⌋₊:ℝ)^(5/3:ℝ)/(1+Real.log (⌊Z⌋₊:ℝ))^k ≤
      (2:ℝ)^k*Z^(5/3:ℝ)/(1+Real.log Z)^k := by
    apply (div_le_div_iff₀ (pow_pos hLfp _) (pow_pos hLp _)).mpr
    calc
      _ ≤ (⌊Z⌋₊:ℝ)^(5/3:ℝ)*((2:ℝ)^k*(1+Real.log (⌊Z⌋₊:ℝ))^k) :=
        mul_le_mul_of_nonneg_left (log_floor_power_comparison hfloor1 k) (by positivity)
      _ = (2:ℝ)^k*(⌊Z⌋₊:ℝ)^(5/3:ℝ)*(1+Real.log (⌊Z⌋₊:ℝ))^k := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow hfloorp.le hf (by norm_num)
  apply hh.trans
  have hb := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ K*M^2*A^(2/3:ℝ) by positivity)
  convert hb using 1 <;> dsimp [K] <;> ring


end CubicFirstMoment.ProfileControl

end

end OAI
