import OAI.MeasureTheory.Falconer.Fourier.MaskJetSeed
import OAI.MeasureTheory.Falconer.Fourier.ComplexMaskJets
import OAI.MeasureTheory.Falconer.Fourier.InverseJetSupport
import OAI.MeasureTheory.Falconer.Fourier.MaskJetCount

namespace OAI

/-! # The inverse acting on already normalized individual jets

Only the additional derivative orders enter the extracted radius weight.
The formula also permits a complex angular multiplier as a separate label.
-/

namespace Falconer
open scoped ContDiff

namespace MaskJetIndex

theorem value_scaled_input {d : ℕ} (j : MaskJetIndex d) (k : ℕ)
    (hkj : k ≤ j.order) (r : ℝ) (hr : r ≠ 0) (f : Space d → ℂ)
    (hf : ContDiff ℝ ∞ f) (z : Space d) :
    j.value (fun w => r^k • f w) z =
      (((r⁻¹)^(j.order-k) : ℝ) : ℂ) * j.scaledValue r f z := by
  rw [j.value_real_smul (r^k) f hf z,j.value_eq_inv_radius_scaled r hr f z,
    Complex.real_smul,← mul_assoc,← Complex.ofReal_mul,
    MaskJetExpansion.radius_power_cancel hr hkj]

end MaskJetIndex

namespace MaskJetExpansion
variable {ι : Type} {X : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def seededRadiusWeight (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (a : ((seed k).inverse m j).index) : ℝ :=
  ∏ i, (r i)⁻¹^(((((seed k).inverse m j).term a).jet i).order-(k i).order)

theorem seededRadiusWeight_nonneg (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) (a : ((seed k).inverse m j).index) :
    0 ≤ seededRadiusWeight m j k r a :=
  Finset.prod_nonneg (fun i _ => pow_nonneg (inv_nonneg.mpr (hr i).le) _)

theorem seededRadiusWeight_le (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (hr : ∀ i, 0 < r i) {D : ℝ} (hD : 1 ≤ D)
    (hscale : ∀ i, (r i)⁻¹ ≤ D) (a : ((seed k).inverse m j).index) :
    seededRadiusWeight m j k r a ≤ D^(2*j) := by
  rw [seededRadiusWeight,← seed_inverse_radius_cancel m j k r (fun i => (hr i).ne') a]
  exact seed_inverse_radius_le m j k r hr hD hscale a

theorem inverse_seed_term_normalized (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (B : ι → X → Space (m+3) → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Sphere (m+3)) :
    let T := (seed k).inverse m j
    ∀ a : T.index,
      (T.term a).value (fun i x z => (r i)^(k i).order • B i x z) x e =
        (T.term a).coefficient e * (seededRadiusWeight m j k r a : ℂ) *
          ∏ i, ((T.term a).jet i).scaledValue (r i) (B i x) e := by
  intro T a
  by_cases he : stationaryPatchMask m e = 0
  · have hc : (T.term a).coefficient e = 0 := inverse_coefficient_eq_zero m j (seed k) a e he
    simp only [MaskJetTerm.value,hc,zero_mul]
  · have hnear : ‖(e : Space (m+3))-
        (gnomonicChart (0 : Space (m+2)) : Space (m+3))‖ ≤ 1/2 :=
      (poleCutoff_support _ _ he).le.trans (by norm_num)
    have hp : (T.term a).point e = (e : Space (m+3)) :=
      ((seed_hasPointAt k (e : Space (m+3))).inverse hnear j a)
    have hi (i : ι) :
        ((T.term a).jet i).value (fun z => (r i)^(k i).order • B i x z) e =
          (((r i)⁻¹^(((T.term a).jet i).order-(k i).order) : ℝ) : ℂ) *
            ((T.term a).jet i).scaledValue (r i) (B i x) e :=
      MaskJetIndex.value_scaled_input _ _ ((seed_ordersExtend k).inverse j a i)
        (r i) (hr i) (B i x) (hB i x) e
    unfold MaskJetTerm.value
    rw [hp]
    simp_rw [hi]
    have hw : (∏ i, (((r i)⁻¹^(((T.term a).jet i).order-(k i).order) : ℝ) : ℂ)) =
        (seededRadiusWeight m j k r a : ℂ) := by
      exact_mod_cast (rfl :
      (∏ i, (r i)⁻¹^(((T.term a).jet i).order-(k i).order)) =
        seededRadiusWeight m j k r a)
    rw [Finset.prod_mul_distrib,hw,mul_assoc]

/-- Exact global expansion with every old radius normalization cancelled. -/
theorem localInverseAmplitude_seeded_jets (m j : ℕ) (k : ι → MaskJetIndex (m+3))
    (r : ι → ℝ) (hr : ∀ i, r i ≠ 0) (B : ι → X → Space (m+3) → ℂ)
    (hB : ∀ i x, ContDiff ℝ ∞ (B i x)) (x : X) (e : Sphere (m+3)) :
    let T := (seed k).inverse m j
    localInverseAmplitude m (fun z => ∏ i, (k i).scaledValue (r i) (B i x) z) j e =
      ∑ a : T.index, (T.term a).coefficient e * (seededRadiusWeight m j k r a : ℂ) *
        ∏ i, ((T.term a).jet i).scaledValue (r i) (B i x) e := by
  intro T
  let C : ι → X → Space (m+3) → ℂ := fun i x z => (r i)^(k i).order • B i x z
  have hC (i : ι) (x : X) : ContDiff ℝ ∞ (C i x) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space (m+3) => (r i)^(k i).order)).smul (hB i x)
  have hseed : (seed k).value C x = fun z => ∏ i, (k i).scaledValue (r i) (B i x) z := by
    funext z
    rw [seed_value]
    apply Finset.prod_congr rfl
    intro i _
    exact (k i).value_real_smul _ _ (hB i x) z
  have hv := inverse_value m j (seed k) C hC x e
  rw [hseed] at hv
  rw [← hv]
  apply Finset.sum_congr rfl
  intro a _
  exact inverse_seed_term_normalized m j k r hr B hB x e a

/-- Term count is unchanged by the initial derivative orders. -/
theorem card_inverse_seed (m j : ℕ) (k : ι → MaskJetIndex (m+3)) :
    Fintype.card ((seed k).inverse m j).index =
      inverseMultiplicity (m+2) j * (1+Fintype.card ι*(m+3))^(2*j) := by
  rw [card_inverse]
  change Fintype.card Unit * _ * _ = _
  rw [Fintype.card_unique,one_mul]

/-- The smooth coefficients are drawn from a fixed finite geometric family,
independent of the number and previous orders of the masks. -/
theorem inverse_seed_geometryCoveredBy_unit (m j : ℕ) (k : ι → MaskJetIndex (m+3)) :
    ((seed k).inverse m j).GeometryCoveredBy
      ((product : MaskJetExpansion Unit (m+3) (Space (m+3))).inverse m j) :=
  (seed_geometryCoveredBy_unit k).inverse j

omit [Fintype ι] [DecidableEq ι] in
theorem inverse_seed_coefficient_derivatives (m j t : ℕ)
    {s : Set (Space (m+3))} (hs : IsCompact s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι],
      ∀ (k : ι → MaskJetIndex (m+3)) (a : ((seed k).inverse m j).index),
        ∀ z ∈ s, ‖iteratedFDeriv ℝ t (((seed k).inverse m j).term a).coefficient z‖ ≤ C := by
  obtain ⟨C,hC,hbound⟩ := coefficient_derivatives_bounded_on
    ((product : MaskJetExpansion Unit (m+3) (Space (m+3))).inverse m j) t hs
  refine ⟨C,hC,?_⟩
  intro ι _ _ k a z hz
  obtain ⟨b,hcoeff,_⟩ := inverse_seed_geometryCoveredBy_unit m j k a
  rw [hcoeff]
  exact hbound b z hz

end MaskJetExpansion
end Falconer

end OAI
