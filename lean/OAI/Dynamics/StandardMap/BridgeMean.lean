import OAI.Dynamics.StandardMap.BridgeAggregate

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma integral_torusShortfall (k : ℝ) (hk : 0≤ k) (a : ℤ) (m : ℕ) :
    (∫z,torusShortfall k z a m ∂area)=meanDeficit k m := by
  have hz (z : Torus) : torusShortfall k z a m=torusShortfall k (torusIter k a z) 0 m := by rw [torusShortfall_shift,zero_add]
  simp_rw [hz]
  rw [integral_torusIter k a (fun z => torusShortfall k z 0 m),←meanDeficit_eq_integral_shortfall k hk m]
lemma lipschitz_sum_nonneg {R : ℕ} (F : (Fin R → ℝ) → ℝ) (L : NNReal)
    (hF : LipschitzWith L F) (hFz : F 0=0) (x : Fin R → ℝ) (hx : ∀j,0≤ x j) :
    F x≤ L*∑j,x j := by
  have hh := hF.dist_le_mul x 0
  simp only [hFz,dist_zero_right] at hh
  have hb : ‖x‖≤∑j,x j := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => hx j))).mpr
    intro j
    rw [Real.norm_eq_abs,abs_of_nonneg (hx j)]
    exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ j)
  exact (le_abs_self _).trans (hh.trans (mul_le_mul_of_nonneg_left hb L.coe_nonneg))
lemma integral_observation_bound {R : ℕ} (k : ℝ) (hk : 0≤ k)
    (a : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀j,0< m j)
    (F : (Fin R → ℝ) → ℝ) (L : NNReal) (hF : LipschitzWith L F) (hFz : F 0=0) :
    (∫z,shortfallObservation k a m F z ∂area)≤ L*∑j,meanDeficit k (m j) := by
  have hi (j) : Integrable (fun z => torusShortfall k z (a j) (m j)) area :=
    (continuous_torusShortfall k hk _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have his := integrable_finsetSum Finset.univ (fun j _ => hi j)
  have hh : (∫z,shortfallObservation k a m F z ∂area)≤
      ∫z,(L:ℝ)*∑j,torusShortfall k z (a j) (m j) ∂area := by
    apply integral_mono ((continuous_shortfall_observation k hk a m F hF.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) (his.const_mul L)
    intro z
    exact lipschitz_sum_nonneg F L hF hFz _ (fun j => (torusShortfall_mem k hk z (a j) (m j) (hm j)).1)
  rw [integral_const_mul,integral_finsetSum _ (fun j _ => hi j)] at hh
  simpa only [integral_torusShortfall k hk] using hh
lemma deficit_fixed_scaled (k : ℝ) (hk : 0≤ k) (m p l H q : ℕ) (hm : 0< m)
    (hmp : m≤ 2^(p+H)) (hq : p+l≤ q) :
    meanDeficit k (m*2^l)≤ (2:ℝ)^(p+H)*meanDeficit k (2^(q+H)) := by
  have hn : m*2^l≤ 2^(p+l+H) := by
    calc
      _ ≤ 2^(p+H)*2^l := Nat.mul_le_mul_right _ hmp
      _ = _ := by rw [←pow_add]; congr 1; omega
  have hr : ((2^(p+l+H):ℕ):ℝ)/((m*2^l:ℕ):ℝ)≤ (2:ℝ)^(p+H) := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<((m*2^l:ℕ):ℝ))).mpr
    have hmR : (1:ℝ)≤ m := by exact_mod_cast hm
    push_cast
    rw [show p+l+H=(p+H)+l by omega,pow_add]
    nlinarith [mul_le_mul_of_nonneg_left hmR (show (0:ℝ)≤ 2^(p+H)*2^l by positivity)]
  exact (meanDeficit_ratio k hk _ _ (by positivity) hn).trans
    ((mul_le_mul_of_nonneg_right hr (meanDeficit_bounds k hk _ (by positivity)).1).trans
      (mul_le_mul_of_nonneg_left (meanDeficit_pow_mono k hk (Nat.add_le_add_right hq H)) (by positivity)))
namespace CriticalScaleSequence
lemma observation_scaled_bound (S : CriticalScaleSequence) {R : ℕ}
    (p : ℕ) (a : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀j,0< m j)
    (F : (Fin R → ℝ) → ℝ) (L : NNReal) (hF : LipschitzWith L F) (hFz : F 0=0) :
    ∃ C : ℝ,0≤ C ∧ ∀i l,p+l≤ S.exponent i →
      (∫z,shortfallObservation (S.parameter i) (fun j => a j*2^l) (fun j => m j*2^l) F z ∂area)≤ C*S.epsilon i := by
  obtain ⟨H,hH⟩ := exists_nat_gt (∑j,m j)
  have hmH (j) : m j≤ 2^(p+H) := by
    have hh : m j≤ ∑j,m j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ j)
    have hpow : H≤ 2^H := Nat.le_of_lt (Nat.lt_two_pow_self (n := H))
    exact hh.trans (hH.le.trans (hpow.trans (Nat.pow_le_pow_right (by omega) (by omega))))
  have hdc := doublingConstant_pos
  refine ⟨L*(R:ℝ)*((2:ℝ)^(p+H)*(2*(2*doublingConstant)^H)),by positivity,?_⟩
  intro i l hl
  apply (integral_observation_bound (S.parameter i) (S.positive i).le _ _
    (fun j => Nat.mul_pos (hm j) (by positivity)) F L hF hFz).trans
  have hb (j) : meanDeficit (S.parameter i) (m j*2^l)≤
      ((2:ℝ)^(p+H)*(2*(2*doublingConstant)^H))*S.epsilon i := by
    exact (deficit_fixed_scaled _ (S.positive i).le (m j) p l H (S.exponent i) (hm j) (hmH j) hl).trans
      ((mul_le_mul_of_nonneg_left (S.terminal i H) (by positivity)).trans_eq (by dsimp [epsilon]; ring))
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hb j)
  have hmul := mul_le_mul_of_nonneg_left hh L.coe_nonneg
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using hmul
end CriticalScaleSequence
end StandardMapEntropy

end OAI
