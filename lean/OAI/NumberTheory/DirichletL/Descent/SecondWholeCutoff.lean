import OAI.NumberTheory.DirichletL.Descent.SecondWholeTail

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstCauchyArithmetic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem second_whole_column_denominator {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal] (G E S T : Finset ι)
    (hEG : E ⊆ G) (hGS : Disjoint G S) (hGT : Disjoint G T)
    (L : ℝ) (hL : 0 ≤ L)
    (hS : primeProductNorm p (G ∪ S) ≤ L)
    (hT : primeProductNorm p (G ∪ T) ≤ L) :
    (primeProductNorm p E)^2 * (primeProductNorm p S * primeProductNorm p T) ≤ L^2 := by
  have hE := primeProductNorm_mono p hp hEG
  have hE0 := (primeProductNorm_pos p hp E).le
  have hS0 := (primeProductNorm_pos p hp S).le
  have hT0 := (primeProductNorm_pos p hp T).le
  rw [primeProductNorm_union p G S hGS] at hS
  rw [primeProductNorm_union p G T hGT] at hT
  calc
    _ ≤ (primeProductNorm p G)^2 * (primeProductNorm p S * primeProductNorm p T) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hE0 hE 2) (mul_nonneg hS0 hT0)
    _ = (primeProductNorm p G * primeProductNorm p S) *
      (primeProductNorm p G * primeProductNorm p T) := by ring
    _ ≤ L*L := mul_le_mul hS hT (mul_nonneg (primeProductNorm_pos p hp G).le hT0) hL
    _ = _ := by ring

def wholeSecondRadius (d : O) (L Y H : ℝ) : ℝ := ‖eisEmbedding d‖^2 * L^2 * H / Y

theorem full_second_whole_column_tail (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct : ℝ), 0 < Ct ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a, ‖Ψ a‖ ≤ 1)
      (m c d : O) (_hd : d ≠ 0) (Hcol : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ))
      (B Y H L R : ℝ), 0 ≤ B → 0 < Y → 0 ≤ H → 1 ≤ L →
      (∀ U, ‖Hcol U‖ ≤ B) →
      (∀ U, Hcol U ≠ 0 → primeProductNorm p U ≤ L) →
      wholeSecondRadius d L Y H ≤ R →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun _ E => childFrequencyBall
          (d*primeSubsetGenerator (fun i => Ideal.span {p i}) E) R)‖ ≤
        (128*L)^4 * (B^2 *
          (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
            (1+L^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_supported_tail order
  refine ⟨s,Ct,hCt,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W B Y H L R hB hY hH hL hcol hsupp hR
  apply htail p hp hg hinj hc F Ψ hΨ m c d Hcol W B Y H L hB hY hH hL hcol hsupp
  intro G hG E S hS T hT hST hw k hk
  obtain ⟨hGS,hGT⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
  have hdGS : Disjoint G S := Finset.disjoint_left.mpr (by
    intro i hiG hiS
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hiS)).2 hiG)
  have hdGT : Disjoint G T := Finset.disjoint_left.mpr (by
    intro i hiG hiT
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hT) hiT)).2 hiG)
  have hden := second_whole_column_denominator p hp G E.val S T
    (Finset.mem_powerset.mp E.property) hdGS hdGT L (zero_le_one.trans hL)
    (hsupp _ hGS) (hsupp _ hGT)
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E.val
  have he : e ≠ 0 := primeSubsetGenerator_ne_zero _ _
  have hde := mul_ne_zero hd he
  have hdN : 0 < ‖eisEmbedding d‖^2 := SecondPassIntegration.elementNorm_pos d hd
  have heN : 0 < ‖eisEmbedding e‖^2 := SecondPassIntegration.elementNorm_pos e he
  have henorm : ‖eisEmbedding e‖^2 = primeProductNorm p E.val :=
    primeSubsetGenerator_norm_eq_productNorm p E.val
  have hkR := (outside_childFrequencyBall (d*e) hde R k hk).le
  have hR' : ‖eisEmbedding d‖^2 * L^2 * H ≤
      Y * (‖eisEmbedding d‖^2 * ‖eisEmbedding e‖^2 * ‖eisEmbedding k‖^2) := by
    have hh := (div_le_iff₀ hY).mp hR
    have hh' := mul_le_mul_of_nonneg_right hkR hY.le
    simp only [map_mul,norm_mul,mul_pow] at hh'
    nlinarith
  have hbound : H * (‖eisEmbedding e‖^2 *
      (primeProductNorm p S * primeProductNorm p T)) ≤ Y*‖eisEmbedding k‖^2 := by
    apply (mul_le_mul_iff_right₀ (mul_pos hdN heN)).mp
    have hh := mul_le_mul_of_nonneg_left hden (mul_nonneg hdN.le hH)
    rw [←henorm] at hh
    nlinarith [hh,hR']
  rw [active_norm_sq_disjoint p S T hST,div_mul_eq_mul_div]
  apply (le_div_iff₀ (mul_pos heN (mul_pos (primeProductNorm_pos p hp S)
    (primeProductNorm_pos p hp T)))).mpr
  exact hbound

end
end SevenEighths.InverseMoment

end OAI
