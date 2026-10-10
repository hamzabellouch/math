import OAI.NumberTheory.CubicMoment.Angular.AngularSquarefreeMomentTransfer
import OAI.NumberTheory.CubicMoment.Angular.AngularCommonPrimeIndicatorExponents

namespace OAI

/-! Weight-independent exponents for uniform smooth families. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem angular_first_common_squarefree_exponents (hpub : PrimitiveAngularHeckeInput)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y N : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → 1 ≤ Real.log Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) →
      (∀ i, (2*Y)^c < X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryAngularSquarefreePrimeTuple ℓ a 1 q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ₀,hκ₀,hκ₀hi,e,he,hfamily⟩ := angular_first_common_prime_exponents ℓ (γ := γ) (ι := ι)
    hpub hc hc₁ V hV hposV hsmV hVlo hVhi hVnorm hGI hGQ
  obtain ⟨C,hC,herr⟩ := first_angular_squarefreeCoordinateError_moment (ι := ι) hc hc₁
  let κ := min κ₀ (c/256)
  have hκ : 0 < κ := lt_min hκ₀ (by positivity)
  have hκle : κ ≤ κ₀ := min_le_left _ _
  have hκc : κ ≤ c/256 := min_le_right _ _
  refine ⟨κ,hκ,hκle.trans hκ₀hi,min e (c/4)/2,by positivity,?_⟩
  intro W hW hWlo
  obtain ⟨T₀,hnorm⟩ := hfamily W hW hWlo
  obtain ⟨K,hK,hbound⟩ := hW.norm_bound
  let M : ι → ℝ := fun _ => K
  have hM0 : ∀ i, 0 ≤ M i := fun _ => hK
  let E := C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2
  obtain ⟨T₁,hT₁,habs⟩ := absorb_prime_coordinate_error_explicit he
    (show 0 < c/4 by positivity) (show 0 ≤ E by dsimp [E]; positivity)
  refine ⟨max T₀ T₁,?_⟩
  intro r Y N X q η t P hYT hlog hNlo hNhi hXlo hXhi hq hη hqY ht hP
  have hM : ∀ i x, ‖W r i x‖ ≤ M i := fun i x => hbound (r,i) x
  have hYT₀ : T₀ ≤ Y := (le_max_left _ _).trans hYT
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans hYT
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hNlo₀ : Y^(1-κ₀) ≤ N :=
    (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)).trans hNlo
  have hNhi₀ : N ≤ Y^(1+κ₀) := hNhi.trans
    (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith))
  have hn := hnorm r Y N X q η t P hYT₀ hlog hNlo₀ hNhi₀ hXlo hXhi hq hη hqY ht hP
  have hd := herr ℓ q η t (W r) M X V Y hY1 hq hM0 hM (hWlo r) hXlo hVnorm P
    (fun a ha => first_squarefree_error_rows hY1 hc hκc hNhi a (hP a ha))
  have hm := angular_squarefreePrime_moment_transfer P ℓ (fun a => a) (fun _ => 1)
    (fun a ha => ⟨(hP a ha).1,by norm_num [primary]⟩) q η t (W r) X V hYp hVhi
  calc
    _ ≤ 2*(∑ a ∈ P, ‖primaryAngularPrimeIndicatorTuple ℓ a 1 q η t (W r) X V Y‖^2)+
        2*(∑ a ∈ P, ‖angularSquarefreeCoordinateError ℓ a 1 q η t (W r) X V Y‖^2) := hm
    _ ≤ 2*Y^(7/3-e)+2*E*(2*Y)^(7/3-c/4) := by dsimp [E]; linarith
    _ ≤ _ := habs Y hYT₁


 theorem angular_balanced_common_squarefree_exponents (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
      (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → 1 ≤ Real.log Y →
      (∀ i, (2*Y)^c < X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryAngularSquarefreePrimeTuple ℓ a.1 a.2 q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  obtain ⟨κ₀,hκ₀,hκ₀hi,e,he,hfamily⟩ := angular_balanced_common_prime_exponents ℓ (γ := γ) (ι := ι)
    hpub hHuxley hc hc₁ V hV hposV hsmV hVlo hVhi hVnorm hGI hGQ
  obtain ⟨C,hC,herr⟩ := balanced_angular_squarefreeCoordinateError_moment (ι := ι) hHuxley hc hc₁
  let κ := min κ₀ (c/256)
  have hκ : 0 < κ := lt_min hκ₀ (by positivity)
  have hκle : κ ≤ κ₀ := min_le_left _ _
  have hκc : κ ≤ c/256 := min_le_right _ _
  refine ⟨κ,hκ,hκle.trans hκ₀hi,min e (c/4)/2,by positivity,?_⟩
  intro W hW hWlo
  obtain ⟨T₀,hnorm⟩ := hfamily W hW hWlo
  obtain ⟨K,hK,hbound⟩ := hW.norm_bound
  let M : ι → ℝ := fun _ => K
  have hM0 : ∀ i, 0 ≤ M i := fun _ => hK
  let E := C*(((Fintype.card ι)^(Fintype.card ι):ℕ)*(∏ i, M i))^2
  obtain ⟨T₁,hT₁,habs⟩ := absorb_prime_coordinate_error_explicit he
    (show 0 < c/4 by positivity) (show 0 ≤ E by dsimp [E]; positivity)
  refine ⟨max T₀ T₁,?_⟩
  intro r Y X q η t P hYT hlog hXlo hXhi hq hη hqY ht hP
  have hM : ∀ i x, ‖W r i x‖ ≤ M i := fun i x => hbound (r,i) x
  have hYT₀ : T₀ ≤ Y := (le_max_left _ _).trans hYT
  have hYT₁ : T₁ ≤ Y := (le_max_right _ _).trans hYT
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hP₀ : ∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ₀) ∧
      norm a.2 ≤ Y^(1/3+κ₀) ∧ Y^(1/1000:ℝ) ≤ norm a.1 := by
    intro a ha
    have hp : Y^(1/3+κ) ≤ Y^(1/3+κ₀) :=
      Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    exact ⟨(hP a ha).1,(hP a ha).2.1.trans hp,(hP a ha).2.2.1.trans hp,(hP a ha).2.2.2⟩
  have hn := hnorm r Y X q η t P hYT₀ hlog hXlo hXhi hq hη hqY ht hP₀
  have hd := herr ℓ q η t (W r) M X V Y hY1 hq hM0 hM (hWlo r) hXlo hVnorm P
    (fun a ha => balanced_squarefree_error_rows hY1 hc hκc a (hP a ha))
  have hm := angular_squarefreePrime_moment_transfer P ℓ Prod.fst Prod.snd
    (fun a ha => ⟨(hP a ha).1.1,(hP a ha).1.2.1⟩) q η t (W r) X V hYp hVhi
  calc
    _ ≤ 2*(∑ a ∈ P, ‖primaryAngularPrimeIndicatorTuple ℓ a.1 a.2 q η t (W r) X V Y‖^2)+
        2*(∑ a ∈ P, ‖angularSquarefreeCoordinateError ℓ a.1 a.2 q η t (W r) X V Y‖^2) := hm
    _ ≤ 2*Y^(7/3-e)+2*E*(2*Y)^(7/3-c/4) := by dsimp [E]; linarith
    _ ≤ _ := habs Y hYT₁

end CubicFirstMoment

end

end OAI
