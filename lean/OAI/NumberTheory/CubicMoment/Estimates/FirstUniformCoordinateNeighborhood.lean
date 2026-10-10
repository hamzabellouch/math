import OAI.NumberTheory.CubicMoment.Estimates.CoordinatePrimeMoment
import OAI.NumberTheory.CubicMoment.Estimates.UniformCoordinateWeights
import OAI.NumberTheory.CubicMoment.Estimates.TwistedPrimeNeighborhood
import OAI.NumberTheory.CubicMoment.Estimates.CoordinateNeighborhoodPowers

namespace OAI

/-! First exceptional moments with the original independent smooth weights
restored on the von Mangoldt factors. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem first_uniform_coordinate_vonMangoldt_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (W : γ → ι → ℝ → ℂ)
    (hW : UniformLogWeights (fun z : γ × ι => W z.1 z.2))
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (u : γ) (Y N : ℝ) (X : ι → ℝ)
      (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ)
      (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → (∀ i, 0 < X i) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(9/25:ℝ)) →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
        a 1 q η t (W u) X V Y‖^2) ≤ Y^(7/3-ε) := by
  obtain ⟨κ,hκ,hκhi,e,he,T,hraw⟩ := first_twisted_vonMangoldt_neighborhood (ι := ι)
    hpub V hV hposV hsmV hVlo hVhi hGI hGQ
  obtain ⟨M,hM⟩ := hV.exists_bound_of_continuous hsmV.continuous
  have hM0 : 0 ≤ M := (_root_.norm_nonneg (V 0)).trans (hM 0)
  let k := Fintype.card ι
  let A := 1000*(2*k+7)
  let K : ℝ := M*72^k
  obtain ⟨L,J,hL,hJ,hMoments⟩ := hW.coordinate_moments A
  obtain ⟨T₁,hshift⟩ := eventual_independent_shift_height_bound
  obtain ⟨T₂,hT₂,habs⟩ := absorb_short_mellin_bounds he (2*L^2) (2*K^2*J^2)
    (by positivity) (by positivity)
  refine ⟨κ,hκ,hκhi,min e (1/3)/2,by positivity,max 36 (max T (max T₁ T₂)),?_⟩
  intro u Y N X q η t P hY hNlo hNhi hX hq hη hqY ht hP
  have hY36 : 36 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := by linarith
  have hYp : 0 < Y := by linarith
  have hYT : T ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hYT₂ : T₂ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hY))
  have hb (τ : ι → ℝ) (hτ : τ ∈ mellinHeightBox (Y^(1/1000:ℝ))) :
      (∑ a : P, ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt)
        a 1 q η (fun i => t i-τ i) V Y‖^2) ≤ Y^(7/3-e) := by
    have hh := hraw Y N q η (fun i => t i-τ i) P hYT hNlo hNhi hq hη hqY
      (fun i => hshift Y hYT₁ _ _ (ht i) (hτ i)) hP
    have heq (a : Eisenstein) (ha : a ∈ P) :=
      twistedProductPolynomial_eq_unsplit (a := a) (b := 1) (fun _ : ι => idealVonMangoldt)
        (hP a ha).1 (by norm_num [primary]) q η hη (fun i => t i-τ i) V hYp hVhi
    have hh' : (∑ a ∈ P, ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt)
        a 1 q η (fun i => t i-τ i) V Y‖^2) ≤ Y^(7/3-e) := by
      calc
        _ = ∑ a ∈ P, ‖primaryComplexProductPolynomial
            (fun i => twistArithmetic (q i) (η i) (t i-τ i) idealVonMangoldt) (mixedCubic a 1) V Y‖^2 :=
          Finset.sum_congr rfl (fun a ha => by rw [heq a ha])
        _ ≤ _ := hh
    change (∑ a ∈ P.attach, ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt)
      a 1 q η (fun i => t i-τ i) V Y‖^2) ≤ _
    rw [Finset.sum_attach (f := fun a : Eisenstein =>
      ‖primaryUnsplitTuple (fun _ : ι => idealVonMangoldt) a 1 q η (fun i => t i-τ i) V Y‖^2)]
    exact hh'
  have hm := coordinate_vonMangoldt_moment_bound (fun a : P => ((a : Eisenstein),1))
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
  have hm' : (∑ a ∈ P, ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt)
      a 1 q η t (W u) X V Y‖^2) ≤ 2*L^2*Y^(7/3-e)+
        2*(Fintype.card P:ℝ)*((K*Y^(2*k)/(Y^(1/1000:ℝ))^A)*J)^2 := by
    change (∑ a ∈ P.attach, _) ≤ _ at hm
    rw [Finset.sum_attach (f := fun a : Eisenstein =>
      ‖primaryCoordinateWeightedTuple (fun _ : ι => idealVonMangoldt) a 1 q η t (W u) X V Y‖^2)] at hm
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
