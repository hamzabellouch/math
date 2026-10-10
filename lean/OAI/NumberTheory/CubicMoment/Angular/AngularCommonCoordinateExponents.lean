import OAI.NumberTheory.CubicMoment.Estimates.DilatedMomentPowers
import OAI.NumberTheory.CubicMoment.Angular.AngularFirstUniformCoordinateNeighborhood
import OAI.NumberTheory.CubicMoment.Angular.AngularBalancedUniformCoordinateNeighborhood

namespace OAI

/-! The exceptional exponent is chosen before the smooth-weight family.
Only the threshold depends on its derivative constants. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem angular_first_common_coordinate_exponents (hpub : PrimitiveAngularHeckeInput)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      ∃ Y₀ : ℝ, ∀ (u : γ) (Y N : ℝ) (X : ι → ℝ)
      (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → (∀ i, 0 < X i) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt)
        a 1 q η t (W u) X V Y‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,e,he,T,hraw⟩ := angular_first_twisted_vonMangoldt_neighborhood ℓ (ι := ι)
    hpub V hV hposV hsmV hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,min e (1/3)/2,by positivity,?_⟩
  intro W hW
  obtain ⟨M,hM⟩ := hV.exists_bound_of_continuous hsmV.continuous
  have hM0 : 0 ≤ M := (_root_.norm_nonneg (V 0)).trans (hM 0)
  let k := Fintype.card ι
  let A := 1000*(2*k+7)
  let K : ℝ := M*72^k
  obtain ⟨L,J,hL,hJ,hMoments⟩ := hW.coordinate_moments A
  obtain ⟨T₁,hshift⟩ := eventual_dilated_shift_height_bound
  obtain ⟨T₂,hT₂,habs⟩ := absorb_short_mellin_bounds he (2*L^2) (2*K^2*J^2)
    (by positivity) (by positivity)
  refine ⟨max 36 (max T (max T₁ T₂)),?_⟩
  intro u Y N X q η t P hY hNlo hNhi hX hq hη hqY ht hP
  have hY36 : 36 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := by linarith
  have hYp : 0 < Y := by linarith
  have hYT : T ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hYT₂ : T₂ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hb (τ : ι → ℝ) (hτ : τ ∈ mellinHeightBox (Y^(1/1000:ℝ))) :
      (∑ a : P, ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt)
        a 1 q η (fun i => t i-τ i) V Y‖^2) ≤ Y^(7/3-e) := by
    have hh := hraw Y N q η (fun i => t i-τ i) P hYT hNlo hNhi hq hη hqY
      (fun i => hshift Y hYT₁ _ _ (ht i) (hτ i)) hP
    have heq (a : Eisenstein) (ha : a ∈ P) :=
      angularTwistedProductPolynomial_eq_unsplit ℓ (a := a) (b := 1) (fun _ : ι => idealVonMangoldt)
        (hP a ha).1 (by norm_num [primary]) q η hη (fun i => t i-τ i) V hYp hVhi
    have hh' : (∑ a ∈ P, ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt)
        a 1 q η (fun i => t i-τ i) V Y‖^2) ≤ Y^(7/3-e) := by
      calc
        _ = ∑ a ∈ P, ‖primaryComplexProductPolynomial
            (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i-τ i) idealVonMangoldt) (mixedCubic a 1) V Y‖^2 :=
          Finset.sum_congr rfl (fun a ha => by rw [heq a ha])
        _ ≤ _ := hh
    change (∑ a ∈ P.attach, ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt)
      a 1 q η (fun i => t i-τ i) V Y‖^2) ≤ _
    rw [Finset.sum_attach (f := fun a : Eisenstein =>
      ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt) a 1 q η (fun i => t i-τ i) V Y‖^2)]
    exact hh'
  have hm := angular_coordinate_vonMangoldt_moment_bound ℓ (fun a : P => ((a : Eisenstein),1))
    (fun a => ⟨(hP a a.property).1,by norm_num [primary]⟩) q η hq t (W u) X
    (fun i => hW.compact (u,i)) (fun i => hW.positive (u,i))
    (fun i => hW.smooth (u,i)) hX V hM0 hM hYp.le A (Real.rpow_pos_of_pos hYp _)
    (Real.rpow_nonneg hYp.le _) hb
  have hcard : (Fintype.card P:ℝ) ≤ Y^4 := by
    have hN : 1 ≤ N := (Real.one_le_rpow hY1 (by linarith : 0 ≤ 1-κ)).trans hNlo
    have hNY : N ≤ Y^2 := by
      simpa only [Real.rpow_two] using hNhi.trans
        (Real.rpow_le_rpow_of_exponent_le hY1 (by linarith : 1+κ ≤ 2))
    simpa only [Fintype.card_coe] using neighborhood_cubic_card P hY36 hN hNY hP
  have hm' : (∑ a ∈ P, ‖primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt)
      a 1 q η t (W u) X V Y‖^2) ≤ 2*L^2*Y^(7/3-e)+
        2*(Fintype.card P:ℝ)*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := by
    change (∑ a ∈ P.attach, _) ≤ _ at hm
    rw [Finset.sum_attach (f := fun a : Eisenstein =>
      ‖primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt) a 1 q η t (W u) X V Y‖^2)] at hm
    have hmass0 : 0 ≤ ∏ i, zeroLineMellinMass (W u i) :=
      Finset.prod_nonneg (fun i _ => zeroLineMellinMass_nonneg _)
    have hjoint0 := independentMellinMoment_nonneg (W u) A
    apply hm.trans
    gcongr
    · exact (hMoments u).1
    · exact (hMoments u).2
  calc
    _ ≤ 2*L^2*Y^(7/3-e)+2*(Fintype.card P:ℝ)*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := hm'
    _ ≤ 2*L^2*Y^(7/3-e)+2*Y^4*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := by gcongr
    _ ≤ 2*L^2*Y^(7/3-e)+(2*K^2*J^2)*Y^(-42/5:ℝ) := by
      exact add_le_add le_rfl (coordinate_neighborhood_tail_le_short_tail (K := K) (J := J) k hY1)
    _ ≤ _ := habs Y hYT₂


 theorem angular_balanced_common_coordinate_exponents (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      ∃ Y₀ : ℝ, ∀ (u : γ) (Y : ℝ) (X : ι → ℝ)
      (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → (∀ i, 0 < X i) → (∀ i, q i ≠ 0) →
      (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt)
        (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t (W u) X V Y‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,e,he,T,hraw⟩ := angular_balanced_twisted_vonMangoldt_neighborhood ℓ (ι := ι)
    hpub hHuxley V hV hposV hsmV hVlo hVhi hGI hGQ
  refine ⟨κ,hκ,hκhi,min e (1/3)/2,by positivity,?_⟩
  intro W hW
  obtain ⟨M,hM⟩ := hV.exists_bound_of_continuous hsmV.continuous
  have hM0 : 0 ≤ M := (_root_.norm_nonneg (V 0)).trans (hM 0)
  let k := Fintype.card ι
  let A := 1000*(2*k+7)
  let K : ℝ := M*72^k
  obtain ⟨L,J,hL,hJ,hMoments⟩ := hW.coordinate_moments A
  obtain ⟨T₁,hshift⟩ := eventual_dilated_shift_height_bound
  obtain ⟨T₂,hT₂,habs⟩ := absorb_short_mellin_bounds he (2*L^2) (2*K^2*J^2)
    (by positivity) (by positivity)
  refine ⟨max 324 (max T (max T₁ T₂)),?_⟩
  intro u Y X q η t P hY hX hq hη hqY ht hP
  have hY324 : 324 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := by linarith
  have hYp : 0 < Y := by linarith
  have hYT : T ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hYT₂ : T₂ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hb (τ : ι → ℝ) (hτ : τ ∈ mellinHeightBox (Y^(1/1000:ℝ))) :
      (∑ a : P, ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt)
        (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun i => t i-τ i) V Y‖^2) ≤ Y^(7/3-e) := by
    have hh := hraw Y q η (fun i => t i-τ i) P hYT hq hη hqY
      (fun i => hshift Y hYT₁ _ _ (ht i) (hτ i)) hP
    have heq (a : Eisenstein × Eisenstein) (ha : a ∈ P) :=
      angularTwistedProductPolynomial_eq_unsplit ℓ (fun _ : ι => idealVonMangoldt)
        (hP a ha).1.1 (hP a ha).1.2.1 q η hη (fun i => t i-τ i) V hYp hVhi
    have hh' : (∑ a ∈ P, ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt)
        (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun i => t i-τ i) V Y‖^2) ≤ Y^(7/3-e) := by
      calc
        _ = ∑ a ∈ P, ‖primaryComplexProductPolynomial
            (fun i => angularTwistArithmetic ℓ (q i) (η i) (t i-τ i) idealVonMangoldt) (mixedCubic (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2) V Y‖^2 :=
          Finset.sum_congr rfl (fun a ha => by rw [heq a ha])
        _ ≤ _ := hh
    change (∑ a ∈ P.attach, ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt)
      (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun i => t i-τ i) V Y‖^2) ≤ _
    rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
      ‖primaryAngularUnsplitTuple ℓ (fun _ : ι => idealVonMangoldt) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η (fun i => t i-τ i) V Y‖^2)]
    exact hh'
  have hm := angular_coordinate_vonMangoldt_moment_bound ℓ (fun a : P => (a : Eisenstein × Eisenstein))
    (fun a => ⟨(hP a a.property).1.1,(hP a a.property).1.2.1⟩) q η hq t (W u) X
    (fun i => hW.compact (u,i)) (fun i => hW.positive (u,i))
    (fun i => hW.smooth (u,i)) hX V hM0 hM hYp.le A (Real.rpow_pos_of_pos hYp _)
    (Real.rpow_nonneg hYp.le _) hb
  have hcard : (Fintype.card P:ℝ) ≤ Y^4 := by
    have hLY : Y^(1/3+κ) ≤ Y := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hY1
        (by linarith : 1/3+κ ≤ 1)
    simpa only [Fintype.card_coe] using neighborhood_balanced_card P hY324
      (Real.rpow_nonneg hYp.le _) hLY
      (fun a ha => ⟨(hP a ha).1,(hP a ha).2.1,(hP a ha).2.2.1⟩)
  have hm' : (∑ a ∈ P, ‖primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt)
      (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t (W u) X V Y‖^2) ≤ 2*L^2*Y^(7/3-e)+
        2*(Fintype.card P:ℝ)*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := by
    change (∑ a ∈ P.attach, _) ≤ _ at hm
    rw [Finset.sum_attach (f := fun a : Eisenstein × Eisenstein =>
      ‖primaryAngularCoordinateWeightedTuple ℓ (fun _ : ι => idealVonMangoldt) (a : Eisenstein × Eisenstein).1 (a : Eisenstein × Eisenstein).2 q η t (W u) X V Y‖^2)] at hm
    have hmass0 : 0 ≤ ∏ i, zeroLineMellinMass (W u i) :=
      Finset.prod_nonneg (fun i _ => zeroLineMellinMass_nonneg _)
    have hjoint0 := independentMellinMoment_nonneg (W u) A
    apply hm.trans
    gcongr
    · exact (hMoments u).1
    · exact (hMoments u).2
  calc
    _ ≤ 2*L^2*Y^(7/3-e)+2*(Fintype.card P:ℝ)*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := hm'
    _ ≤ 2*L^2*Y^(7/3-e)+2*Y^4*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := by gcongr
    _ ≤ 2*L^2*Y^(7/3-e)+(2*K^2*J^2)*Y^(-42/5:ℝ) := by
      exact add_le_add le_rfl (coordinate_neighborhood_tail_le_short_tail (K := K) (J := J) k hY1)
    _ ≤ _ := habs Y hYT₂

end CubicFirstMoment

end

end OAI
