import OAI.NumberTheory.Ostmann.QuadraticCenter.AdaptiveArrayFamily

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

theorem adaptiveArray_error_le {Z : ℕ} (hZ : 1 ≤ Z)
    (hC : adaptiveArrayConstant ≤ (Z:ℝ)) :
    adaptiveArrayConstant*(Z:ℝ)^48/(Z^200:ℕ) ≤ (Z:ℝ)^(-(80:ℝ)) := by
  have hz : (0:ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  have hz1 : (1:ℝ) ≤ Z := by exact_mod_cast hZ
  rw [Real.rpow_neg (Nat.cast_nonneg Z),Real.rpow_ofNat,inv_eq_one_div,Nat.cast_pow]
  apply (div_le_div_iff₀ (pow_pos hz 200) (pow_pos hz 80)).mpr
  calc
    _ ≤ (Z:ℝ)*(Z:ℝ)^48*(Z:ℝ)^80 := by gcongr
    _ = (Z:ℝ)^129 := by ring
    _ ≤ (Z:ℝ)^200 := pow_le_pow_right₀ hz1 (by omega)
    _ = _ := by ring

theorem exists_near_adaptiveArrayFamily_canonical {L Z M h P : ℕ}
    (hL : Squarefree L) (hZ : 1 ≤ Z) (hLZ : L ≤ Z)
    (hC : adaptiveArrayConstant ≤ (Z:ℝ)) (hM : M < 4*L) (hh : h < L)
    (hP : 1 ≤ P) (hPZ : P ≤ Z^7) {lam : ℝ} (hlam : |lam| ≤ 1)
    (A : ∀ p : ℕ, Finset (ZMod p)) {θ R : ℝ}
    (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1) (hR1 : 1 ≤ R) (hRB : R ≤ (2*Z^13:ℕ)) :
    ∃ b ∈ adaptiveArrayFamily L Z lam A, ∀ s : ℕ,
      ‖adaptiveContinuousArray L Z M h P lam A θ R s-b s‖ ≤ (Z:ℝ)^(-(80:ℝ)) := by
  classical
  obtain ⟨a,ha,hMa,hha,hPa,hta,hRa⟩ := exists_near_adaptiveArrayParameters
    (by omega) hM hh hP hPZ ht0 ht1 hR1 hRB
  have haB := mem_adaptiveArrayParameters ha (by omega)
  refine ⟨adaptiveContinuousArray L Z a.modulusResidue a.phaseResidue a.multiple lam A a.theta a.radius,
    Finset.mem_image.mpr ⟨a,ha,rfl⟩,?_⟩
  intro s
  rw [hMa,hha,hPa]
  by_cases hs : s ∈ adaptiveArraySupport L Z
  · simp only [adaptiveContinuousArray,ite_eq_left hs]
    have hsI := Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1
    exact (positiveDivisorArray_grid_error hL hZ hLZ hsI.1 hsI.2 M P hlam A
      (adaptiveInverse M) hR1 haB.2.2.2.2.2.2.1 hRB haB.2.2.2.2.2.2.2 h hta hRa).trans
      (adaptiveArray_error_le hZ hC)
  · simp only [adaptiveContinuousArray,ite_eq_right hs,sub_self,norm_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg _) _

end Ostmann.QuadraticCenter

end

end OAI
