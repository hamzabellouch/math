import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.OriginalTFScale
import OAI.Analysis.CoulombIonization.RadialBounds.FiniteBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.MasterExteriorStatistic
import OAI.Analysis.CoulombIonization.RadialBounds.AnnularFirst
import OAI.Analysis.CoulombIonization.Variational.OwnStateResidual

namespace OAI

noncomputable section

namespace CoulombAtom

def exteriorGradientConstant : ℝ := 24*(Real.pi*smoothTransitionBound)^2
lemma exteriorGradientConstant_nonneg : 0 ≤ exteriorGradientConstant := by unfold exteriorGradientConstant; positivity

def actualScreenRadius : ℝ := max actualShellRadius (Real.sqrt (2*exteriorGradientConstant)+1)
lemma actualScreenRadius_ge : actualShellRadius ≤ actualScreenRadius := le_max_left _ _
lemma actualScreenRadius_ge16 : 16 ≤ actualScreenRadius := actualShellRadius_ge.trans actualScreenRadius_ge
lemma actualScreenRadius_pos : 0 < actualScreenRadius := lt_of_lt_of_le (by norm_num) actualScreenRadius_ge16
lemma actualScreenRadius_square : 2*exteriorGradientConstant ≤ actualScreenRadius^2 := by
  have hh := le_max_right actualShellRadius (Real.sqrt (2*exteriorGradientConstant)+1)
  change Real.sqrt (2*exteriorGradientConstant)+1 ≤ actualScreenRadius at hh
  have hn := Real.sqrt_nonneg (2*exteriorGradientConstant)
  have hs := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) exteriorGradientConstant_nonneg)
  nlinarith only [hh,hn,hs,sq_nonneg (actualScreenRadius-Real.sqrt (2*exteriorGradientConstant))]

lemma exterior_price_gradient_absorb {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    2*(exteriorGradientConstant/(actualScreenRadius*s)^2) ≤ 1/s^4 := by
  rw [←mul_div_assoc]
  apply (div_le_div_iff₀ (sq_pos_of_pos (mul_pos actualScreenRadius_pos hs)) (pow_pos hs 4)).2
  have hh := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs.le hs1 (by omega : 2 ≤ 4))
    (mul_nonneg (by norm_num : (0:ℝ)≤2) exteriorGradientConstant_nonneg)
  have hb := mul_le_mul_of_nonneg_right actualScreenRadius_square (sq_nonneg s)
  nlinarith only [hh,hb]

lemma annularOffsetMass_one_small_two {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    annularOffsetMass 1 r ≤ 2/r^3 := by
  have hi : 1 ≤ 1/r^3 := (le_div_iff₀ (pow_pos hr 3)).2 (by simpa using pow_le_one₀ hr.le hr1 (n := 3))
  have hs : Real.sqrt r ≤ 1 := by simpa using Real.sqrt_le_sqrt hr1
  unfold annularOffsetMass
  rw [one_mul,max_eq_left hi]
  have he : 2/r^3 = 2*(1/r^3) := by ring
  rw [he]
  linarith only [hi,hs]

lemma exterior_bound_scale {R L C s v : ℝ} (hR : 0 < R) (hs : 0 < s) (hs1 : s ≤ 1)
    (hv : (1/s^4)*v ≤ 2*(L/(R*s)^2)*(C*(2/(R*s)^3))+4) :
    v ≤ (4*L*C/R^5+4)/s := by
  have hh := mul_le_mul_of_nonneg_left hv (pow_nonneg hs.le 4)
  have he : s^4*((1/s^4)*v) = v := by field_simp
  have he' : s^4*(2*(L/(R*s)^2)*(C*(2/(R*s)^3))+4) = (4*L*C/R^5)/s+4*s^4 := by field_simp; ring
  rw [he,he'] at hh
  have hpow : s^4 ≤ 1/s := (le_div_iff₀ hs).2 (by simpa [←pow_succ] using pow_le_one₀ hs.le hs1 (n := 5))
  calc v ≤ (4*L*C/R^5)/s+4*s^4 := hh
       _ ≤ (4*L*C/R^5)/s+4*(1/s) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ)≤4))
       _ = _ := by ring

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
open CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator graphRawLaw

def actualScreenConstant : ℝ :=
  4*exteriorGradientConstant*(Classical.choose
    (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one))/actualScreenRadius^5+4
lemma actualScreenConstant_nonneg : 0 ≤ actualScreenConstant := by
  have hC := (Classical.choose_spec (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one)).1
  have hn := exteriorGradientConstant_nonneg
  have hr := actualScreenRadius_pos
  unfold actualScreenConstant
  positivity

lemma exists_own_state_exterior_number_succ {Z s r : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hs : 0 < s) (hs1 : s ≤ 1) (hRs : actualScreenRadius*s ≤ 1) (hr : 0 < r)
    (hN : PriceMinimizes (energy Z) (1/s^4) (N+1))
    (K : ℕ) (p₀ : Fin (K+1) → ℝ) (h₀ : ∀ j, 0 < p₀ j) :
    ∃ F : fermionGraph (N+1), OwnProbabilityTailTiltState Z (1/s^4) r K p₀ 1 F ∧
      (∫ x, rawExteriorCount (2*(actualScreenRadius*s)) x ∂graphRawLaw F) ≤ actualScreenConstant/s := by
  have hv : 0 < actualScreenRadius*s := mul_pos actualScreenRadius_pos hs
  obtain ⟨F,η,hF,hη,hsmall,hres⟩ := exists_own_state_shell_residual hZ hr hv hN K p₀ h₀
  refine ⟨F,hF,?_⟩
  have hbound := actual_exterior_number_absorbed hZ hs hs1 hv
    (mul_le_mul_of_nonneg_right actualScreenRadius_ge hs.le) hN hη zero_le_one F hsmall.1 hsmall.2 hres
    (exterior_price_gradient_absorb hs hs1)
  have hann := actual_annular_first_bound hZ (by positivity : 0 < 1/s^4) zero_le_one hv hN F hF.1 hF.2.1
  have hC := (Classical.choose_spec (exists_priced_annular_count_constant (alpha := 1) (beta := 2) zero_lt_one)).1
  have hmoment := hann.trans (mul_le_mul_of_nonneg_left (annularOffsetMass_one_small_two hv hRs) (le_trans zero_le_one hC))
  apply exterior_bound_scale actualScreenRadius_pos hs hs1
  apply hbound.trans
  exact add_le_add (mul_le_mul_of_nonneg_left hmoment (by
    change 0 ≤ 2*(exteriorGradientConstant/(actualScreenRadius*s)^2)
    exact mul_nonneg (by norm_num) (div_nonneg exteriorGradientConstant_nonneg (sq_nonneg _)))) (by norm_num)

lemma exists_own_state_exterior_number {Z s r : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hs : 0 < s) (hs1 : s ≤ 1) (hRs : actualScreenRadius*s ≤ 1) (hr : 0 < r)
    (hN : PriceMinimizes (energy Z) (1/s^4) N)
    (K : ℕ) (p₀ : Fin (K+1) → ℝ) (h₀ : ∀ j, 0 < p₀ j) :
    ∃ F : fermionGraph N, OwnProbabilityTailTiltState Z (1/s^4) r K p₀ 1 F ∧
      (∫ x, rawExteriorCount (2*(actualScreenRadius*s)) x ∂graphRawLaw F) ≤ actualScreenConstant/s := by
  cases N with
  | zero =>
    obtain ⟨F,hF⟩ := exists_actual_own_probability_tail_tilt_state hZ hr hN K p₀ h₀ zero_lt_one
    refine ⟨F,hF,?_⟩
    have hc (x : Configuration 0) : rawExteriorCount (2*(actualScreenRadius*s)) x = 0 := by simp [rawExteriorCount]
    simp_rw [hc,integral_zero]
    exact div_nonneg actualScreenConstant_nonneg hs.le
  | succ N => exact exists_own_state_exterior_number_succ hZ hs hs1 hRs hr hN K p₀ h₀
end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology
namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability
attribute [local irreducible] graphRawLaw physicalObservationLaw jointMasterPosterior

def selectedTailRadius : ℝ := 4*actualScreenRadius

theorem selected_data_of_events {Z s r c l B C T η δ : ℝ} {N K : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hr : 0 < r) (hrs : r ≤ s)
    (hc : 0 < c) (hc1 : c ≤ 1/2) (_ : 1 ≤ l) (hδ : 0 < δ)
    (F : fermionGraph N) (hFn : ‖fermionGraphValue N F‖^2 = 1) (j : ℕ)
    {u : ℝ} (hu : 0 < u) (hul : 1/(2*l) ≤ u/s) (huh : u/s ≤ l⁻¹)
    (hcover : s*l ≤ (2*l^2)*u)
    (htail : (∫ x, rawExteriorCount (2*(actualScreenRadius*s)) x ∂graphRawLaw F) ≤ actualScreenConstant/s)
    {a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ}
    (hbar : IsNuclearBarrier (physicalObservationLaw (graphRawLaw F) K)
      (originalQueryDensity F r j c r s) Z tfDensityCoefficient B C u T η a p)
    {G : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hG : MeasurableSet G)
    (hcomp : ∀ q ∈ G, ∀ y, u ≤ ‖y‖ → ‖y‖ ≤ (2*l^2)*u →
      (‖y‖^4*originalQueryField F Z (1/s^4) r j c r s q y ≤ actualInverseCap) ∧
      |originalQueryDensity F r j c r s q y-tfDensityCoefficient*
        (max (originalQueryField F Z (1/s^4) r j c r s q y) 0)^(3/2:ℝ)| < l⁻¹^8/‖y‖^6)
    (hbudget : η+(actualScreenConstant*s^2)/δ+(physicalObservationLaw (graphRawLaw F) K).real Gᶜ < 1) :
    Nonempty (SelectedQuantumData Z N s l δ B C selectedTailRadius) := by
  let := graphRawLaw_probability F hFn
  let ell : Fin K → ℝ := fun k => dyadicObservationWidth r k
  let μ := originalQueryDensity (K := K) F r j c r s
  let g : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → ℝ :=
    fun q => s^3*(∫ y in {y : TFSpace | s*selectedTailRadius < ‖y‖}, μ q y)
  have hgi : Integrable g (physicalObservationLaw (graphRawLaw F) K) :=
    (original_master_tail_integrable F ell j hc hr hs (s*selectedTailRadius)
      canonicalRealPacket_smooth.continuous canonicalRealPacket_normalized).const_mul _
  have hμn : ∀ q x, 0 ≤ μ q x := fun q x => jointMasterPosterior_nonneg _ _ _ _ _ _ _ _ _
  have hgn : ∀ q, 0 ≤ g q := fun q => mul_nonneg (pow_nonneg hs.le 3) (integral_nonneg (hμn q))
  have hrR : r ≤ 2*(actualScreenRadius*s) := by
    have hR := actualScreenRadius_ge16
    nlinarith only [hrs,hs,hR]
  have htailmean := (original_master_tail_mean_le F ell j hc hc1 hr hs hs1 hrR
    canonicalRealPacket_smooth.continuous canonicalRealPacket_support canonicalRealPacket_normalized).trans htail
  have hgm : (∫ q, g q ∂physicalObservationLaw (graphRawLaw F) K) ≤ actualScreenConstant*s^2 := by
    rw [show (∫ q, g q ∂physicalObservationLaw (graphRawLaw F) K) =
      s^3*(∫ q, (∫ y in {y : TFSpace | s*selectedTailRadius < ‖y‖}, μ q y)
        ∂physicalObservationLaw (graphRawLaw F) K) from integral_const_mul _ _]
    have hrad : s*selectedTailRadius = 2*(2*(actualScreenRadius*s)) := by unfold selectedTailRadius; ring
    change s^3*(∫ q, (∫ y in {y : TFSpace | s*selectedTailRadius < ‖y‖}, μ q y)
      ∂physicalObservationLaw (graphRawLaw F) K) ≤ _
    rw [hrad]
    convert mul_le_mul_of_nonneg_left htailmean (pow_nonneg hs.le 3) using 1 <;>
      try rfl
    field_simp
  obtain ⟨q,hq,hw,hpint,hgq⟩ := hbar.select_data hgi hgn hG hδ hgm hbudget
  obtain ⟨M,hM,hMb⟩ := jointMasterPosterior_global_bound (graphRawLaw F) ell j hc hr hs hrs
    canonicalRealPacket_smooth.continuous canonicalRealPacket_compact
  have hμm : Measurable (μ q) :=
    (jointMasterPosterior_measurable (graphRawLaw F) ell j hc hr hs canonicalRealPacket_smooth.continuous).comp
      (measurable_const.prodMk measurable_id)
  have hμi : Integrable (μ q) := jointMasterPosterior_integrable (graphRawLaw F) ell j hc hr hs
    canonicalRealPacket_smooth.continuous canonicalRealPacket_normalized _
  have hpm : Measurable (p q) := hbar.measurable_error.comp (measurable_const.prodMk measurable_id)
  obtain ⟨L,hL⟩ := hbar.bounded_error
  have hpb : ∀ x, p q x ≤ max L 0 := fun x => (hL _ _).trans (le_max_left _ _)
  have hpi : Integrable (p q) := (bounded_compact_mass_le hpm (le_max_right L 0)
    (hbar.nonneg_error q) hpb (hbar.support_error q)).1
  have scaled (x : TFSpace) (hxl : u/s ≤ ‖x‖) (hxh : ‖x‖ ≤ l) := by
    have hx : x ≠ 0 := norm_pos_iff.mp ((div_pos hu hs).trans_le hxl)
    have hnorm : ‖s • x‖ = s*‖x‖ := by rw [norm_smul,Real.norm_of_nonneg hs.le]
    have hyl : u ≤ ‖s • x‖ := by rw [hnorm]; nlinarith [(div_le_iff₀ hs).mp hxl]
    have hyh : ‖s • x‖ ≤ (2*l^2)*u := by rw [hnorm]; exact (mul_le_mul_of_nonneg_left hxh hs.le).trans hcover
    have hh := hcomp q hq (s • x) hyl hyh
    exact original_TF_scale hs hx hh.1 hh.2.le
  refine ⟨⟨u,a q,μ q,p q,hu,hul,huh,(hbar.locallyLipschitz_offset q).continuous,
    hμm,hμi,hμn q,⟨M,hM,?_⟩,?_,hpm,hpi,hbar.nonneg_error q,⟨max L 0,le_max_right _ _,hpb⟩,
    hbar.support_error q,hpint.le,hw,hbar.lower q,hbar.upper q,?_,?_,?_⟩⟩
  · intro x
    exact (le_abs_self _).trans (by simpa only [μ,originalQueryDensity,ell,Real.norm_eq_abs] using hMb _ x)
  · exact jointMasterPosterior_mass (graphRawLaw F) ell j hc hr hs
      canonicalRealPacket_smooth.continuous canonicalRealPacket_normalized _
  · intro x hxl hxh; exact (scaled x hxl hxh).2
  · intro x hxl hxh; exact (scaled x hxl hxh).1
  · rw [tfDilation_exterior_mass hs]
    exact hgq.le
end CoulombBarrier

end

end OAI
