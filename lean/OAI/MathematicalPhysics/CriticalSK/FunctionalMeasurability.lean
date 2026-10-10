import OAI.MathematicalPhysics.CriticalSK.EntropyBounds

namespace OAI

noncomputable section
open scoped BigOperators Topology NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
namespace CriticalSK

section FunctionalMeasurability
variable {n : ℕ} (W : Disorder n)

lemma variance_pos_iff_nonconstant (f : Spin n → ℝ) :
    0 < variance W f ↔ ∃ x y, f x ≠ f y := by
  constructor
  · intro hf
    by_contra! hconst
    have he : f = fun _ => f (fun _ => false) := funext (fun x => hconst x _)
    rw [he] at hf
    simp [variance] at hf
  · rintro ⟨x, y, hxy⟩
    by_contra h
    have hv : variance W f = 0 := le_antisymm (le_of_not_gt h) (variance_nonneg_full W f)
    have he (z : Spin n) : f z = mean W f := by
      have hh : gibbs W z * (f z - mean W f) ^ 2 ≤ variance W f :=
        Finset.single_le_sum
          (fun y _ => mul_nonneg (gibbs_nonneg W y) (sq_nonneg (f y - mean W f)))
          (Finset.mem_univ z)
      rw [hv] at hh
      have heq := le_antisymm hh (mul_nonneg (gibbs_nonneg W z) (sq_nonneg (f z - mean W f)))
      have hs := (mul_eq_zero.mp heq).resolve_left (gibbs_pos W z).ne'
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hs)
    exact hxy ((he x).trans (he y).symm)

lemma dirichlet_pos_of_nonconstant (hn : 0 < n) (f : Spin n → ℝ)
    (hf : ∃ x y, f x ≠ f y) : 0 < dirichlet W f := by
  have hv := (variance_pos_iff_nonconstant W f).mpr hf
  obtain ⟨C, hC, hgap⟩ := exists_finite_poincare W hn
  by_contra h
  have ht := mul_nonpos_of_nonneg_of_nonpos hC.le (le_of_not_gt h)
  have hh := hgap f
  linarith

lemma entropy_square_pos_iff_nonconstant (f : Spin n → ℝ) :
    0 < entropy W (fun x => f x ^ 2) ↔ ∃ x y, f x ^ 2 ≠ f y ^ 2 := by
  constructor
  · intro hf
    by_contra! hconst
    have he : (fun x => f x ^ 2) = fun _ => f (fun _ => false) ^ 2 :=
      funext (fun x => hconst x _)
    rw [he] at hf
    simp [entropy, mean_const] at hf
  · rintro ⟨x, y, hxy⟩
    have hxyabs : |f x| ≠ |f y| := by
      intro he
      apply hxy
      have hh : |f x| ^ 2 = |f y| ^ 2 := congrArg (fun a : ℝ => a ^ 2) he
      simpa only [sq_abs] using hh
    have hv := (variance_pos_iff_nonconstant W (fun x => |f x|)).mpr ⟨x, y, hxyabs⟩
    have hh := variance_le_entropy_square W (fun x => |f x|) (fun x => abs_nonneg _)
    simp only [sq_abs] at hh
    exact hv.trans_le hh

lemma relaxationTime_eq_iSup : relaxationTime W =
    ⨆ f : {f : Spin n → ℝ // ∃ x y, f x ≠ f y}, variance W f.val / dirichlet W f.val := by
  change sSup _ = sSup _
  congr 1
  ext r
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, (variance_pos_iff_nonconstant W f).mp hf⟩, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f.val, (variance_pos_iff_nonconstant W f.val).mpr f.property, rfl⟩

lemma logSobolevConstant_eq_iSup : logSobolevConstant W =
    ⨆ f : {f : Spin n → ℝ // ∃ x y, f x ^ 2 ≠ f y ^ 2},
      entropy W (fun x => f.val x ^ 2) / dirichlet W f.val := by
  change sSup _ = sSup _
  congr 1
  ext r
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, (entropy_square_pos_iff_nonconstant W f).mp hf⟩, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨f.val, (entropy_square_pos_iff_nonconstant W f.val).mpr f.property, rfl⟩

end FunctionalMeasurability

lemma entropy_continuous {n : ℕ} (g : Spin n → ℝ) :
    Continuous (fun W : Disorder n => entropy W g) :=
  (mean_continuous (fun x => g x * Real.log (g x))).sub
    (Real.continuous_mul_log.comp (mean_continuous g))

lemma relaxationTime_measurable {n : ℕ} (hn : 0 < n) :
    Measurable (relaxationTime (n := n)) := by
  apply LowerSemicontinuous.measurable
  change LowerSemicontinuous (fun W : Disorder n => relaxationTime W)
  simp_rw [relaxationTime_eq_iSup]
  apply lowerSemicontinuous_ciSup
  · intro W
    apply (full_ratios_bdd W hn).mono
    rintro r ⟨f, rfl⟩
    exact ⟨f.val, (variance_pos_iff_nonconstant W f.val).mpr f.property, rfl⟩
  · intro f
    exact ((variance_continuous f.val).div (dirichlet_continuous f.val)
      (fun W => (dirichlet_pos_of_nonconstant W hn f.val f.property).ne')).lowerSemicontinuous

lemma logSobolevConstant_measurable {n : ℕ} (hn : 0 < n) :
    Measurable (logSobolevConstant (n := n)) := by
  apply LowerSemicontinuous.measurable
  change LowerSemicontinuous (fun W : Disorder n => logSobolevConstant W)
  simp_rw [logSobolevConstant_eq_iSup]
  apply lowerSemicontinuous_ciSup
  · intro W
    apply (entropy_ratios_bdd W hn).mono
    rintro r ⟨f, rfl⟩
    exact ⟨f.val, (entropy_square_pos_iff_nonconstant W f.val).mpr f.property, rfl⟩
  · intro f
    have hf : ∃ x y, f.val x ≠ f.val y := by
      obtain ⟨x, y, hxy⟩ := f.property
      exact ⟨x, y, fun he => hxy (congrArg (fun a : ℝ => a ^ 2) he)⟩
    exact ((entropy_continuous (fun x => f.val x ^ 2)).div (dirichlet_continuous f.val)
      (fun W => (dirichlet_pos_of_nonconstant W hn f.val hf).ne')).lowerSemicontinuous

end CriticalSK
end

end OAI
