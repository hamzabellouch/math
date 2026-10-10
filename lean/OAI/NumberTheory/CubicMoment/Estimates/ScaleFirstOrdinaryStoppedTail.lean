import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailHeightPrefix
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstTailAggregation

namespace OAI

/-! The ordinary-height stopped contribution is an exact prefix of the
retained-envelope tail, bounded as a difference of two complete tails. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstStoppedWindow (i : ℕ) (ρ ξ H U X : ℝ) (h : ℕ) (early : Bool) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(69/200:ℝ) then
      scaleFirstTailStoppedRow i 0 ρ ξ H U X h early d else 0

def scaleFirstOrdinaryStoppedArity (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ) (early : Bool) : ℂ :=
  ∑ s ∈ Finset.range (heightWindowCount H T),
    if T*(3/2:ℝ)^s ≤ X^(1/100:ℝ) then
      scaleFirstStoppedWindow i ρ ξ H (T*(3/2:ℝ)^s) X h early else 0

lemma scaleFirstStoppedWindow_sum (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ) (early : Bool) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      scaleFirstStoppedWindow i ρ ξ H (T*(3/2:ℝ)^s) X h early) =
      scaleFirstStoppedEnvelopeTail i ρ ξ H T X h early := by
  unfold scaleFirstStoppedWindow scaleFirstStoppedEnvelopeTail
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : distinguishedScaleLength d < X^(69/200:ℝ)
  · simp only [hd,ite_true]
  · simp only [hd,ite_false,Finset.sum_const_zero]

lemma scaleFirstOrdinaryStoppedArity_prefix (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ)
    (early : Bool) (hH : 0 < H) (hT : 0 < T) :
    ∃ j ≤ heightWindowCount H T,
      scaleFirstOrdinaryStoppedArity i ρ ξ H T X h early =
        scaleFirstStoppedEnvelopeTail i ρ ξ H T X h early-
          scaleFirstStoppedEnvelopeTail i ρ ξ H (T*(3/2:ℝ)^j) X h early := by
  obtain ⟨j,hj,he⟩ := geometricHeight_filtered_prefix
    (fun U => scaleFirstStoppedWindow i ρ ξ H U X h early) hH hT (X^(1/100:ℝ))
  refine ⟨j,hj,?_⟩
  simpa only [scaleFirstOrdinaryStoppedArity,scaleFirstStoppedWindow_sum] using he

theorem scaleFirstOrdinaryStoppedArity_bound (i : ℕ)
    (hpnt : PrimaryPrimePNT) {C ξ ρ ε : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100) (n : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (H T : ℝ) (h : ℕ) (early : Bool),
      (1+Real.log X)^Ct ≤ T → 1 ≤ H → H ≤ X →
      ‖scaleFirstOrdinaryStoppedArity i ρ ξ H T X h early‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨K,Ct,hK,hbound⟩ := scaleFirstStoppedEnvelopeTail_bound i hpnt hMV hC hHuxley
    hξ hξz hρ hρ₂ hε hsmall hgap n
  refine ⟨2*K,Ct,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with X hb hX
  intro H T h early hT hH hHX
  have hL : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hTp : 0 < T := zero_lt_one.trans_le ((one_le_pow₀ hL).trans hT)
  obtain ⟨j,_hj,he⟩ := scaleFirstOrdinaryStoppedArity_prefix i ρ ξ H T X h early
    (zero_lt_one.trans_le hH) hTp
  have hT' : (1+Real.log X)^Ct ≤ T*(3/2:ℝ)^j := by
    apply hT.trans
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left
        (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 3/2) : 1 ≤ (3/2:ℝ)^j) hTp.le)
  rw [he]
  exact (norm_sub_le _ _).trans
    ((add_le_add (hb H T h early hT hH hHX)
      (hb H (T*(3/2:ℝ)^j) h early hT' hH hHX)).trans_eq (by ring))

theorem scaleFirstOrdinaryStoppedTail_isLittleO (m : ℕ)
    (hpnt : PrimaryPrimePNT) {C ξ ρ ε : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100) :
    ∃ Ct : ℕ, ∀ (H T : ℝ → ℝ) (h : ℝ → ℕ) (early : ℝ → Bool),
      (∀ᶠ X : ℝ in atTop, (1+Real.log X)^Ct ≤ T X) →
      (∀ᶠ X : ℝ in atTop, 1 ≤ H X) →
      (∀ᶠ X : ℝ in atTop, H X ≤ X) →
      (fun X => ∑ i ∈ Finset.range m,
        scaleFirstOrdinaryStoppedArity i ρ ξ (H X) (T X) X (h X) (early X))
        =o[atTop] firstMomentScale := by
  have hd (i : Fin m) := scaleFirstOrdinaryStoppedArity_bound i.val hpnt hMV hC hHuxley
    hξ hξz hρ hρ₂ hε hsmall hgap 3
  choose K Ct hK hb using hd
  let Ct₀ := ∑ i : Fin m, Ct i
  refine ⟨Ct₀,?_⟩
  intro H T h early hT hH hHX
  apply Asymptotics.IsLittleO.fun_sum
  intro i hi
  let ii : Fin m := ⟨i,Finset.mem_range.mp hi⟩
  have hCt : Ct ii ≤ Ct₀ :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (Ct j)) (Finset.mem_univ ii)
  apply Asymptotics.IsBigO.trans_isLittleO
    (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3) ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound (K ii)
  filter_upwards [hb ii,hT,hH,hHX,eventually_ge_atTop (1:ℝ)]
    with X hbound hT hH hHX hX
  have hL : 1 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hT' : (1+Real.log X)^(Ct ii) ≤ T X := (pow_le_pow_right₀ hL hCt).trans hT
  simpa only [Real.norm_of_nonneg (by positivity :
    0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3),mul_div_assoc] using
    hbound (H X) (T X) (h X) (early X) hT' hH hHX

end CubicFirstMoment

end

end OAI
