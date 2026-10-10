import OAI.NumberTheory.CubicMoment.Estimates.NormMellinMoments

namespace OAI

/-! A weighted Mellin tail from actual dyadic height means. -/
noncomputable section
open Set Filter MeasureTheory
namespace CubicFirstMoment

def mellinHeightDyad (T : ℝ) (n : ℕ) : Set ℝ := Ico ((2:ℝ)^n*T) ((2:ℝ)^(n+1)*T)

lemma mellinHeightDyad_union {T : ℝ} (hT : 0 < T) :
    (⋃ n : ℕ, mellinHeightDyad T n) = Ici T := by
  ext x
  constructor
  · intro hx
    obtain ⟨n,hn⟩ := mem_iUnion.mp hx
    exact (le_mul_of_one_le_left hT.le (one_le_pow₀ (by norm_num))).trans hn.1
  · intro hx
    obtain ⟨n,hn,hnext⟩ := exists_nat_pow_near ((le_div_iff₀ hT).mpr (by simpa using hx))
      (by norm_num : (1:ℝ) < 2)
    exact mem_iUnion.mpr ⟨n,⟨(le_div_iff₀ hT).mp hn,(div_lt_iff₀ hT).mp hnext⟩⟩

lemma mellinHeightDyad_disjoint {T : ℝ} (hT : 0 < T) :
    Pairwise (fun i j => Disjoint (mellinHeightDyad T i) (mellinHeightDyad T j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : i+1 ≤ j)) hT.le
    exact (not_lt_of_ge (hp.trans hj.1)) hi.2
  · have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega : j+1 ≤ i)) hT.le
    exact (not_lt_of_ge (hp.trans hi.1)) hj.2

theorem weighted_positive_mellin_tail {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hg0 : ∀ t, 0 ≤ g t) (hfg : Integrable (fun t => f t*g t))
    {T B C : ℝ} (hT : 0 < T) (_hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmean : ∀ S : ℝ, T ≤ S → (∫ t in S..2*S, g t) ≤ B*S)
    (hdecay : ∀ t : ℝ, T ≤ t → f t ≤ C/t^2) :
    (∫ t in Ici T, f t*g t) ≤ 2*B*C/T := by
  have hdyad (n : ℕ) : (∫ t in mellinHeightDyad T n, f t*g t) ≤
      (B*C/T)*((1/2:ℝ)^n) := by
    let S := (2:ℝ)^n*T
    have hS : 0 < S := mul_pos (pow_pos (by norm_num) _) hT
    have hTS : T ≤ S := le_mul_of_one_le_left hT.le (one_le_pow₀ (by norm_num))
    have hS2 : S ≤ 2*S := by linarith
    have he : (2:ℝ)^(n+1)*T = 2*S := by dsimp [S]; rw [pow_succ]; ring
    change (∫ t in Ico S ((2:ℝ)^(n+1)*T), f t*g t) ≤ _
    rw [he,integral_Ico_eq_integral_Ioc,← intervalIntegral.integral_of_le hS2]
    have hi := intervalIntegral.integral_mono_on (μ := volume) hS2
      ((hf.mul hg).intervalIntegrable _ _)
      ((continuous_const.mul hg).intervalIntegrable S (2*S))
      (show ∀ t ∈ Icc S (2*S), f t*g t ≤ (C/S^2)*g t from fun t ht => by
        apply mul_le_mul_of_nonneg_right _ (hg0 t)
        apply (hdecay t (hTS.trans ht.1)).trans
        exact div_le_div_of_nonneg_left hC (sq_pos_of_pos hS)
          (pow_le_pow_left₀ hS.le ht.1 2))
    calc
      _ ≤ ∫ t in S..2*S, (C/S^2)*g t := hi
      _ = (C/S^2)*(∫ t in S..2*S, g t) := intervalIntegral.integral_const_mul _ _
      _ ≤ (C/S^2)*(B*S) := mul_le_mul_of_nonneg_left (hmean S hTS) (by positivity)
      _ = (B*C/T)*((1/2:ℝ)^n) := by
        dsimp [S]
        rw [div_pow,one_pow]
        field_simp
  have hsum := hasSum_integral_iUnion (μ := volume)
    (s := mellinHeightDyad T) (f := fun t => f t*g t)
    (fun n : ℕ => (measurableSet_Ico : MeasurableSet (mellinHeightDyad T n))) (mellinHeightDyad_disjoint hT)
    hfg.integrableOn
  rw [mellinHeightDyad_union hT] at hsum
  calc
    _ = ∑' n : ℕ, ∫ t in mellinHeightDyad T n, f t*g t := hsum.tsum_eq.symm
    _ ≤ ∑' n : ℕ, (B*C/T)*((1/2:ℝ)^n) :=
      Summable.tsum_le_tsum hdyad hsum.summable (summable_geometric_two.mul_left _)
    _ = (B*C/T)*2 := (hasSum_geometric_two.mul_left _).tsum_eq
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
