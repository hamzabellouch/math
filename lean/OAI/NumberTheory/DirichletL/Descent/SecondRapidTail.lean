import OAI.NumberTheory.DirichletL.Descent.SecondTailAbsorption

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_second_rapid_correlated_tail (Lcap tau saving : ℝ)
    (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ), (∀ a,‖Ψ a‖≤1) →
      ∀ (m c d : O),d≠0 → ∀ (Hcol : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (Z B Y L : ℝ) (R : Finset ι→Finset ι→ℝ),
      1≤Z → 0≤B → 0<Y → 1≤L → Y≤Z^Lcap → Y⁻¹≤Z^Lcap → L≤Z^Lcap →
      (∀ U,‖Hcol U‖≤B) → (∀ U,Hcol U≠0 → primeProductNorm p U≤L) →
      (∀ G∈F.powerset,∀ E : G.powerset,correlatedSecondRadius p d G E.val L Y (Z^tau)≤R G E.val) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))‖≤
      C*B^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  obtain ⟨order,horder⟩ := choose_second_tail_order Lcap tau saving hLcap htau
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_correlated_tail order
  refine ⟨s,(4*128^4)*Ct,by positivity,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W Z B Y L R hZ hB hY hL hy hyi hl hcol hsupp hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have he := htail p hp hg hinj hc F Ψ hΨ m c d hd Hcol W B Y (Z^tau) L R
    hB hY (Real.rpow_pos_of_pos hz _).le hL hcol hsupp hR
  apply he.trans
  have hh := horder Z Y L B (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    hZ hY (zero_le_one.trans hL) hB (mul_nonneg hCt.le (apply_nonneg _ _)) hy hyi hl
  convert hh using 1 ; ring

end
end SevenEighths.InverseMoment

end OAI
