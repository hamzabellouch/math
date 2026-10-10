import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedTailBound
import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedAggregation
import OAI.NumberTheory.CubicMoment.Estimates.PrimeModelLogTail

namespace OAI

/-! Exact summation of retained-envelope height tails over the original
labels, sharp side dyads and low distinguished-scale pieces. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def scaleFirstStoppedEnvelopeTail (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ) (early : Bool) : ℂ :=
  ∑ d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)),
    if distinguishedScaleLength d < X^(69/200:ℝ) then
      ∑ s ∈ Finset.range (heightWindowCount H T),
        scaleFirstTailStoppedRow i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d
    else 0

lemma scaleFirstTailStoppedRow_height_dyads (i : ℕ) (ρ ξ H T X : ℝ) (h : ℕ)
    (early : Bool)
    (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X))) :
    (∑ s ∈ Finset.range (heightWindowCount H T),
      scaleFirstTailStoppedRow i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d) =
      ∑ q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
        (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)),
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹*
          ∑ j ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
            ∑ k ∈ (distinguishedStoppedSide X).image stoppedNormDyadIndex,
              ∑ s ∈ Finset.range (heightWindowCount H T),
                scaleFirstTailStoppedDyad i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d q j k := by
  simp_rw [scaleFirstTailStoppedRow_dyads]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [←Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]

theorem scaleFirstStoppedEnvelopeTail_aggregate (i : ℕ) {ρ : ℝ} (hρ : 1 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ξ H T X : ℝ), 1 ≤ X → ∀ (h : ℕ) (early : Bool)
      (M : ℝ), 0 ≤ M →
      (∀ (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
        (q : ℕ × ℕ × ℕ),
        q ∈ (if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
          (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)) →
        ∀ j k : ℕ, ‖∑ s ∈ Finset.range (heightWindowCount H T),
          scaleFirstTailStoppedDyad i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d q j k‖ ≤ M) →
      ‖scaleFirstStoppedEnvelopeTail i ρ ξ H T X h early‖ ≤
        K*(1+Real.log X)^(i+5)*M := by
  obtain ⟨D,hD,hcount⟩ := stoppedFactorSupport_log_count
  obtain ⟨C,hC,hlabels⟩ := stopping_label_weighted_sum_dilated hρ
    (Real.one_le_exp primeProductWeights.radius_nonneg)
  obtain ⟨E,hE,hparts⟩ := stopped_norm_partition_subset_count i
  refine ⟨E*(C*D^2),by positivity,?_⟩
  intro ξ H T X hX h early M hM hpiece
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  let I := if early then (stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)).filter
    (fun q => q.1 < h) else stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X)
  let J := (distinguishedStoppedSide X).image stoppedNormDyadIndex
  let S := (Finset.univ : Finset (Fin i → Fin (normPartitionCount
    (Real.exp primeProductWeights.radius*X))))
  have hI : I ⊆ stoppingLabelBox ρ (Real.exp primeProductWeights.radius*X) := by
    dsimp [I]
    split
    · exact Finset.filter_subset _ _
    · exact Finset.Subset.refl _
  have hJ : (J.card:ℝ) ≤ D*(1+Real.log X) := hcount X hX _
  have hrow (d) : ‖∑ s ∈ Finset.range (heightWindowCount H T),
      scaleFirstTailStoppedRow i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d‖ ≤
      (C*D^2)*(1+Real.log X)^5*M := by
    rw [scaleFirstTailStoppedRow_height_dyads]
    have hinner (q) (hq : q ∈ I) :
        ‖∑ j ∈ J, ∑ k ∈ J, ∑ s ∈ Finset.range (heightWindowCount H T),
          scaleFirstTailStoppedDyad i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d q j k‖ ≤
        D^2*(1+Real.log X)^2*M := by
      apply (norm_double_sum_le_card_sq J J _ (fun j _ k _ => hpiece d q hq j k)).trans
      have hs := mul_le_mul hJ hJ (Nat.cast_nonneg J.card)
        (by positivity : 0 ≤ D*(1+Real.log X))
      calc
        _ ≤ (D*(1+Real.log X))*(D*(1+Real.log X))*M := mul_le_mul_of_nonneg_right hs hM
        _ = _ := by ring
    exact ((hlabels X hX I hI).2 _ (D^2*(1+Real.log X)^2*M)
      (by positivity) hinner).trans_eq (by ring)
  have hb (d) : ‖(if distinguishedScaleLength d < X^(69/200:ℝ) then
      ∑ s ∈ Finset.range (heightWindowCount H T),
        scaleFirstTailStoppedRow i 0 ρ ξ H (T*(3/2:ℝ)^s) X h early d else 0)‖ ≤
      (C*D^2)*(1+Real.log X)^5*M := by
    split_ifs
    · exact hrow d
    · rw [norm_zero]; positivity
  calc
    _ ≤ ∑ d ∈ S, (C*D^2)*(1+Real.log X)^5*M := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun d _ => hb d)
    _ = (S.card:ℝ)*((C*D^2)*(1+Real.log X)^5*M) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ (E*(1+Real.log X)^i)*((C*D^2)*(1+Real.log X)^5*M) :=
      mul_le_mul_of_nonneg_right (hparts X hX S) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem scaleFirstStoppedEnvelopeTail_bound (i : ℕ)
    (hpnt : PrimaryPrimePNT) {C ξ ρ ε : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100) (n : ℕ) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (H T : ℝ) (h : ℕ) (early : Bool),
      (1+Real.log X)^Ct ≤ T → 1 ≤ H → H ≤ X →
      ‖scaleFirstStoppedEnvelopeTail i ρ ξ H T X h early‖ ≤
        K*X^(5/6:ℝ)/(1+Real.log X)^n := by
  obtain ⟨K,Ct,hK,hbound⟩ := distinguishedStoppedEnvelopeTail_bound i hpnt hMV hC hHuxley
    hξ hξz hρ hρ₂ hε hsmall hgap (i+5+n)
  obtain ⟨D,hD,hagg⟩ := scaleFirstStoppedEnvelopeTail_aggregate i hρ
  refine ⟨D*K,Ct,by positivity,?_⟩
  filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with X hb hX
  intro H T h early hT hH hHX
  have hL : 0 < 1+Real.log X := by linarith [Real.log_nonneg hX]
  have hs := hagg ξ H T X hX h early
    (K*X^(5/6:ℝ)/(1+Real.log X)^(i+5+n)) (by positivity)
    (fun d q hq j k => hb H T h early d q j k hT hH hHX (by
      cases early
      · exact (Finset.mem_filter.mp hq).2
      · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2))
  apply hs.trans_eq
  rw [pow_add]
  field_simp
  simp only [pow_add]
  ring


/-- A common logarithmic height cutoff works for every arity in a fixed
finite collection, without restrictions on the chosen boundary label. -/
theorem scaleFirstStoppedEnvelopeTail_isLittleO (m : ℕ)
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
        scaleFirstStoppedEnvelopeTail i ρ ξ (H X) (T X) X (h X) (early X))
        =o[atTop] firstMomentScale := by
  have hd (i : Fin m) := scaleFirstStoppedEnvelopeTail_bound i.val hpnt hMV hC hHuxley
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
  have hT' : (1+Real.log X)^(Ct ii) ≤ T X :=
    (pow_le_pow_right₀ hL hCt).trans hT
  simpa only [Real.norm_of_nonneg (by positivity :
    0 ≤ X^(5/6:ℝ)/(1+Real.log X)^3),mul_div_assoc] using
    hbound (H X) (T X) (h X) (early X) hT' hH hHX

end CubicFirstMoment

end

end OAI
