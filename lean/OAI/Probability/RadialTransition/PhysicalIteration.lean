import OAI.Probability.RadialTransition.UniformKac

namespace OAI

noncomputable section
open scoped BigOperators NNReal
open Set Filter
namespace RadialTransition

def iterationMass (b : ℝ) : ℕ → ℝ := prepend phaseMass (scaleTail b)
def iterationBudget : ℝ := phaseMass+1
lemma iterationBudget_pos : 0 < iterationBudget := by dsimp [iterationBudget]; linarith [phaseMass_pos]
lemma iterationMass_pos {b : ℝ} (hb : 0 < b) (n : ℕ) : 0 < iterationMass b n := by
  cases n with
  | zero => exact phaseMass_pos
  | succ n => exact scaleTail_pos hb n
lemma iterationMass_summable {b : ℝ} (hb : 2 ≤ b) : Summable (iterationMass b) :=
  summable_prepend _ (summable_scaleTail hb)
lemma iterationMass_tsum {b : ℝ} (hb : 2 ≤ b) : (∑' n, iterationMass b n) ≤ iterationBudget := by
  rw [iterationMass,tsum_prepend _ (summable_scaleTail hb)]
  have hh := tsum_scaleTail_le hb
  dsimp [iterationBudget]
  linarith [inv_fourth_le_half hb]
lemma iterationMass_le {b : ℝ} (hb : 2 ≤ b) (n : ℕ) : iterationMass b n ≤ iterationBudget := by
  exact ((iterationMass_summable hb).le_tsum n (fun j _ => (iterationMass_pos (by linarith) j).le)).trans (iterationMass_tsum hb)
lemma iterationMass_weight_summable {b : ℝ} (hb : 2 ≤ b) :
    Summable (fun n => iterationMass b n*(scaleRange b n)^(1/32:ℝ)) := by
  apply (summable_nat_add_iff 1).mp
  simpa only [iterationMass,prepend_succ] using summable_scaleTail_weight hb
lemma iteration_admissible {b : ℝ} (hb : 2 ≤ b) (t : ℝ) :
    AdmissibleFamily t iterationBudget (iterationMass b) (scaleRange b) :=
  ⟨fun n => (iterationMass_pos (by linarith) n).le,scaleRange_one_le (by linarith),
    iterationMass_summable hb,iterationMass_tsum hb⟩

def iterationQ (t b : ℝ) (n : ℕ) : Pressure :=
  grandPressure (familyPotential t (reversePrefix 0 (iterationMass b) (n+1))
    (reversePrefix 1 (scaleRange b) (n+1))) t
def iterationP (t b : ℝ) (n : ℕ) : Pressure :=
  idealAttraction (grandPressure (familyPotential t (reversePrefix 0 (iterationMass b) n)
    (reversePrefix 1 (scaleRange b) n)) t) (iterationMass b n)
lemma iterationP_zero (t b : ℝ) : iterationP t b 0=
    idealAttraction (grandPressure (corePotential t) t) phaseMass := by
  simp only [iterationP,reversePrefix_zero,iterationMass,prepend_zero,familyPotential_zero]
lemma iterationP_succ (t b : ℝ) (n : ℕ) : iterationP t b (n+1)=idealAttraction (iterationQ t b n) (scaleTail b n) := rfl

lemma iteration_kac {t C K b : ℝ} (ht : 1 ≤ t) (hC : 0 < C) (_hK : 1 ≤ K)
    (hb : 2 ≤ b) (hbK : 2*K ≤ b)
    (hrow : 2197*t*bumpIntegral⁻¹*iterationBudget ≤ (t^2/8)/8)
    (hkac : ∀ (a S : ℕ → ℝ) (m R₀ R β h : ℝ),
      (∀ n, 0 ≤ a n) → (∀ n, 1 ≤ S n) → Summable a →
      2 ≤ R₀ → (∀ n, S n ≤ R₀) → 0 ≤ m → m+∑' n, a n ≤ iterationBudget →
      2197*t*bumpIntegral⁻¹*(m+∑' n, a n) ≤ (t^2/8)/8 →
      K*R₀ ≤ R → β ∈ Icc (1/2:ℝ) (3/2) → h ∈ Icc (-2:ℝ) 2 →
      |grandPressure (familyPotential t (prepend m a) (prepend R S)) t β h-
        idealAttraction (grandPressure (familyPotential t a S) t) m β h| ≤ C*Real.sqrt (R₀/R)) :
    ∀ n x, x ∈ phaseWindow (1/4) →
      |onParameters (iterationQ t b n) x-onParameters (iterationP t b n) x| ≤ 2*C*(scaleTail b n)^2 := by
  have ha := iteration_admissible hb t
  have hbn : 1 ≤ b := by linarith
  intro n x hx
  have had := reversePrefix_admissible (t := t) ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 n
  have hadnext := reversePrefix_admissible (t := t) ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 (n+1)
  have hm : iterationMass b n+∑' j, reversePrefix 0 (iterationMass b) n j ≤ iterationBudget := by
    simpa only [reversePrefix_succ,tsum_prepend _ (summable_reversePrefix _ _)] using hadnext.2.2.2
  have hrow' : 2197*t*bumpIntegral⁻¹*(iterationMass b n+∑' j, reversePrefix 0 (iterationMass b) n j) ≤ (t^2/8)/8 := by
    apply le_trans (mul_le_mul_of_nonneg_left hm ?_) hrow
    have := bumpIntegral_pos
    positivity
  obtain ⟨hβ, hh⟩ := phaseWindow_quarter_bounds hx
  have hβ' : x 0 ∈ Icc (1/2:ℝ) (3/2) := ⟨by linarith [hβ.1],by linarith [hβ.2]⟩
  have hh' : x 1 ∈ Icc (-2:ℝ) 2 := abs_le.mp hh
  cases n with
  | zero =>
    have hh := hkac _ _ (iterationMass b 0) 2 (scaleRange b 0) (x 0) (x 1)
      had.1 had.2.1 had.2.2.1 (by norm_num) (fun _ => by norm_num [reversePrefix_zero])
      (ha.1 0) hm hrow' (by nlinarith [scaleRange_base_le hbn 0]) hβ' hh'
    change |onParameters (iterationQ t b 0) x-onParameters (iterationP t b 0) x| ≤ C*Real.sqrt (2/scaleRange b 0) at hh
    apply hh.trans
    nlinarith [mul_le_mul_of_nonneg_left (scale_kac_zero hb) hC.le]
  | succ n =>
    have hR₂ : 2 ≤ scaleRange b n := hb.trans (scaleRange_base_le hbn n)
    have hrange : ∀ j, reversePrefix 1 (scaleRange b) (n+1) j ≤ scaleRange b n :=
      reversePrefix_range_le (by linarith) (fun j hj => scaleRange_mono hbn (by omega))
    have hstep : K*scaleRange b n ≤ scaleRange b (n+1) := by
      rw [scaleRange_succ]
      have hKR : K ≤ scaleRange b n := (show K≤b by linarith).trans (scaleRange_base_le hbn n)
      nlinarith [mul_nonneg (scaleRange_pos (by linarith) n).le (sub_nonneg.mpr hKR)]
    have hh := hkac _ _ (iterationMass b (n+1)) (scaleRange b n) (scaleRange b (n+1)) (x 0) (x 1)
      had.1 had.2.1 had.2.2.1 hR₂ hrange (ha.1 (n+1)) hm hrow' hstep hβ' hh'
    change |onParameters (iterationQ t b (n+1)) x-onParameters (iterationP t b (n+1)) x| ≤ C*Real.sqrt (scaleRange b n/scaleRange b (n+1)) at hh
    rw [scale_kac_succ hbn] at hh
    nlinarith [sq_nonneg (scaleTail b (n+1))]

end RadialTransition
end

end OAI
