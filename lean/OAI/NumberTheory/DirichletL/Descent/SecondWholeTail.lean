import OAI.NumberTheory.DirichletL.Descent.SecondTailCost
import OAI.NumberTheory.DirichletL.Descent.ChildCutoff

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_second_supported_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H lengthScale : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ lengthScale →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
        (128*lengthScale)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+lengthScale^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_uniform_secondSourceTail_bound order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Hcol W B Y H lengthScale hB hY hH hL hcol hsupp K hK
  exact (htail p hp hg hinj hc F Ψ m c d Hcol W Y H hY hH K hK).trans
    (secondSourceTailCost_bounded_test p hp hg hinj F Ψ hΨ m c d Hcol B Y H lengthScale
      (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) order hB hY hH (by positivity) hL hcol hsupp)

def supportedSecondRadius (d : O) (lengthScale Y H : ℝ) : ℝ :=
  childOuterRadius Y (‖eisEmbedding d‖^2 * lengthScale) lengthScale lengthScale lengthScale H

lemma supportedSecondRadius_eq (d : O) (lengthScale Y H : ℝ) :
    supportedSecondRadius d lengthScale Y H = ‖eisEmbedding d‖^2 * lengthScale^4 * H / Y := by
  unfold supportedSecondRadius childOuterRadius
  ring

theorem full_second_child_supported_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H lengthScale R : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ lengthScale →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ lengthScale) →
      supportedSecondRadius d lengthScale Y H ≤ R →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun _ E => childFrequencyBall
          (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) R)‖ ≤
        (128*lengthScale)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+lengthScale^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_supported_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H lengthScale R hB hY hH hL hcol hsupp hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d Hcol W B Y H lengthScale hB hY hH hL hcol hsupp
  intro G hG E S hS T hT hST hw k hk
  obtain ⟨hGS,hGT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hGS' := hsupp (G ∪ S) hGS
  have hGT' := hsupp (G ∪ T) hGT
  have hGn := (primeProductNorm_mono p hp Finset.subset_union_left).trans hGS'
  have hEn := (primeProductNorm_mono p hp (Finset.mem_powerset.mp E.property)).trans hGn
  have hSn := (primeProductNorm_mono p hp Finset.subset_union_right).trans hGS'
  have hTn := (primeProductNorm_mono p hp Finset.subset_union_right).trans hGT'
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E.val
  have he : e ≠ 0 := primeSubsetGenerator_ne_zero _ _
  have hde : d*e ≠ 0 := mul_ne_zero hd he
  have hdN : 0 < ‖eisEmbedding d‖^2 := SecondPassIntegration.elementNorm_pos d hd
  have hL0 : 0 < lengthScale := lt_of_lt_of_le zero_lt_one hL
  have heN : ‖eisEmbedding e‖^2 ≤ lengthScale := by
    simpa only [e,primeSubsetGenerator_norm_eq_productNorm] using hEn
  have hdeN : ‖eisEmbedding (d*e)‖^2 ≤ ‖eisEmbedding d‖^2 * lengthScale := by
    simp only [map_mul,norm_mul,mul_pow]
    exact mul_le_mul_of_nonneg_left heN (sq_nonneg _)
  apply childFrequencyBall_raw_tail p hp Y (‖eisEmbedding d‖^2*lengthScale)
    lengthScale lengthScale lengthScale H hY (mul_pos hdN hL0) hL0 hL0 hL0 hH
    (d*e) e hde he hdeN heN S T hST hSn hTn k
  intro hsmall
  apply hk
  apply (mem_childFrequencyBall (d*e) hde R k).mpr
  exact ((mem_childFrequencyBall (d*e) hde _ k).mp hsmall).trans hR

end
end SevenEighths.InverseMoment

end OAI
