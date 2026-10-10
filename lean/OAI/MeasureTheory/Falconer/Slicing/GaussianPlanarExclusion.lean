import OAI.MeasureTheory.Falconer.Estimates.PlanarSelectedGain
import OAI.MeasureTheory.Falconer.Slicing.GaussianFrostmanTransfer
import OAI.MeasureTheory.Falconer.Geometry.PolynomialNormalization
import OAI.MeasureTheory.Falconer.Slicing.GaussianBandRestriction
import OAI.MeasureTheory.Falconer.Slicing.GaussianPrunedMass

namespace OAI

/-! # Excluding a large actual Gaussian slice using the published planar input -/

namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem gaussian_planar_slice_exclusion
    (hpublished : PublishedPlanarFurstenberg) {b f : ℝ}
    (hb : 0 < b) (hb' : b ≤ 1/2) (hbf : b < f) (hf : f < 1) (C : ℝ) :
    ∃ η δ₀ : ℝ, 0 < η ∧ 0 < δ₀ ∧
    ∀ (N d h : ℕ) (κ : Type) [Fintype κ] [DecidableEq κ]
      (A : Fin h → Space d) (z : Space h) (e : (gaussianRowMap A).ker ≃ₗᵢ[ℝ] Space 2)
      (μ : Measure (Space d)) (ν : Measure (Sphere d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
      (E : Set (Space d × Sphere d)) (J : Sphere d → Finset κ) (a : κ → Space d)
      (K V M T a₀ : ℝ),
    1/(2:ℝ)^N < δ₀ → 0 < K → 0 < V → 0 ≤ M → 0 ≤ T →
    T ≤ (1/(2:ℝ)^N)^(-b-η) →
    1 ≤ a₀ → 1 ≤ 4*K^10*V → 4+8*(h:ℝ) ≤ a₀ →
    (4*K^10*V)*(4*a₀)^f ≤ (1/(2:ℝ)^N)^(-η) →
    (4*K^10*V)*(8*a₀)^b ≤ (1/(2:ℝ)^N)^(-η) →
    (1/(2:ℝ)^N)^η < 1/(4*K^10*V) →
    MeasurableSet E → (∀ i, MeasurableSet {w | i ∈ J w}) →
    (∀ i, ‖A i‖ ≤ M) →
    (∀ x : Space d, ‖(gaussianRowMap A).kerᗮ.starProjection x‖ ≤ 2*‖gaussianRowMap A x‖) →
    2*((h:ℝ)*(1/(2:ℝ)^N)) < 1 →
    (∀ u ∈ E, ‖u.1‖ ≤ 1/4) → (∀ w, ∀ i ∈ J w, ‖a i‖ ≤ 1/4) →
    (∀ u ∈ E, ∃ i ∈ J u.2, ‖perpendicularPart (u.2:Space d) (u.1-a i)‖ ≤ C*(1/(2:ℝ)^N)) →
    (∀ᵐ x ∂μ, ‖x‖ ≤ 1/4) →
    (∀ᵐ w : Sphere d ∂ν, w ∈ gaussianDirectionBand A (1/(2:ℝ)^N) →
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) →
    gaussianPrunedPairMass μ ν (1/(2:ℝ)^N)
      (fun g : Fin (N+1) => (1/(2:ℝ)^g.val)/2)
      (fun g => ENNReal.ofReal (K^6*(1/(2:ℝ)^g.val)^f))
      (fun g => ENNReal.ofReal (K^3*(1/(2:ℝ)^g.val)^b)) (ENNReal.ofReal (K^3))
      (gaussianActiveRelation E J a
        ((1/(2:ℝ)^N)+(2*(1/4))*(1/(2:ℝ)^N)+(C*(1/(2:ℝ)^N))*M)
        (ENNReal.ofReal T) true) (A,z) ≤ ENNReal.ofReal (1/(4*K*V)) := by
  classical
  obtain ⟨η,δ₀,hη,hδ₀,hgain⟩ := planar_selected_slice_gain hpublished hb hb' hbf hf C
  refine ⟨η,δ₀,hη,hδ₀,?_⟩
  intro N d h κ _ _ A z e μ ν _ _ E J a K V M T a₀ hδsmall hK hV hM hT hTbound
    ha₀ hH haK hpcoef hqcoef hlow hE hJ hA hbound hsmall hEb hanchors hcover hμ hν
  let δ : ℝ := 1/(2:ℝ)^N
  let r : Fin (N+1) → ℝ := fun g => (1/(2:ℝ)^g.val)/2
  let TP : Fin (N+1) → ℝ≥0∞ := fun g => ENNReal.ofReal (K^6*(1/(2:ℝ)^g.val)^f)
  let TD : Fin (N+1) → ℝ≥0∞ := fun g => ENNReal.ofReal (K^3*(1/(2:ℝ)^g.val)^b)
  let α := (gaussianPointSliceMeasure μ A z δ).restrict (gaussianPointGood μ δ r TP (A,z))
  let β := (gaussianDirectionSliceMeasure ν A δ).restrict
    (gaussianDirectionGood ν δ r TD (ENNReal.ofReal (K^3)) A)
  let R := δ+(2*(1/4))*δ+(C*δ)*M
  let F := selectedActiveRelation A z δ E J a R T
  have hδ : 0 < δ := by dsimp [δ]; positivity
  by_contra hnot
  have hmass : ENNReal.ofReal (1/(4*K*V)) ≤ (α.prod β) F := by
    have hi := (lt_of_not_ge hnot).le
    change _ ≤ gaussianPrunedIncidence μ ν δ r TP TD (ENNReal.ofReal (K^3)) F (A,z)
    rw [show F = {u | ((A,z),u) ∈ gaussianActiveRelation E J a R (ENNReal.ofReal T) true} ∩
      (gaussianPointBand A z δ ×ˢ gaussianDirectionBand A δ) from rfl,
      gaussian_pruned_incidence_inter_bands μ ν δ r TP TD (ENNReal.ofReal (K^3))
        {u | ((A,z),u) ∈ gaussianActiveRelation E J a R (ENNReal.ofReal T) true} (A,z)]
    exact hi
  have hαmass : α univ ≤ ENNReal.ofReal (K^6) := by
    have hm := gaussianPointGood_mass μ δ r TP (A,z) hμ 0 (by norm_num [r])
    simpa only [TP,Fin.val_zero,pow_zero,div_one,Real.one_rpow,mul_one] using hm
  have hβmass : β univ ≤ ENNReal.ofReal (K^3) := gaussianDirectionGood_mass ν δ r TD _ A
  obtain ⟨hα,hβ,hαratio,hβratio,_,_,hinc⟩ :=
    polynomial_slice_normalization α β F hK hV hαmass hβmass hmass
  let α' := normalizedSliceLaw α hα
  let β' := normalizedSliceLaw β hβ
  have hpball (c : Space 2) (s : ℝ) (hs : δ ≤ s) :
      (α' : Measure (Space d)).real {x | dist (e ((gaussianRowMap A).ker.orthogonalProjectionOnto x)) c ≤ s}
        ≤ δ^(-η)*s^f := by
    have hh := gaussian_point_normalized_frostman μ A z e N r TP (fun _ => rfl)
      (by norm_num) (by norm_num : (0:ℝ) < 1) ha₀ hH (pow_nonneg hK.le 6)
      (hb.le.trans hbf.le) hbound (by linarith) (fun _ => le_rfl) hα hαratio c s hs
    simp only [inv_one,one_smul] at hh
    have hs0 : 0 ≤ s := hδ.le.trans hs
    have hc : (4*K^10*V)*(4*a₀*s)^f ≤ δ^(-η)*s^f := by
      rw [Real.mul_rpow (by positivity) hs0]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hpcoef (Real.rpow_nonneg hs0 f)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans (by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (4*K^10*V)*(4*a₀*s)^f)] using hc)
  have hqball (c : Space 2) (s : ℝ) (hs : δ ≤ s) :
      (β' : Measure (Sphere d)).real
        {w | dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))) c ≤ 2*s}
        ≤ δ^(-η)*s^b := by
    have hs0 : 0 ≤ s := hδ.le.trans hs
    have hh := gaussian_direction_normalized_frostman ν A e N r TD (ENNReal.ofReal (K^3))
      (fun _ => rfl) (by norm_num) ha₀ hH (pow_nonneg hK.le 3) hb.le hbound hsmall
      (by linarith) (fun _ => le_rfl) hβ hβratio c (2*s) (by linarith)
    have hc : (4*K^10*V)*(4*a₀*(2*s))^b ≤ δ^(-η)*s^b := by
      rw [show 4*a₀*(2*s) = (8*a₀)*s by ring,Real.mul_rpow (by positivity) hs0]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hqcoef (Real.rpow_nonneg hs0 b)
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans (by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ (4*K^10*V)*(4*a₀*(2*s))^b)] using hc)
  have hαsupport : ∀ᵐ x ∂(α' : Measure (Space d)), ‖x‖ ≤ 1/4 :=
    normalizedSliceLaw_ae α hα (ae_restrict_of_ae (gaussianPointSliceMeasure_ae_of_ae μ A z δ hμ))
  have hβsupport : ∀ᵐ (w : Sphere d) ∂(β' : Measure (Sphere d)),
      ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
      dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 := by
    apply normalizedSliceLaw_ae β hβ
    have hc : ∀ᵐ (w : Sphere d) ∂β, w ∈ gaussianDirectionBand A δ →
        ‖normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d)))‖ = 1 ∧
        dist (normalize (e ((gaussianRowMap A).ker.orthogonalProjectionOnto (w:Space d))))
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4 :=
      ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_of_ae hν) _)
    have hbnd : ∀ᵐ (w : Sphere d) ∂β, w ∈ gaussianDirectionBand A δ :=
      ae_restrict_of_ae (Measure.ae_smul_measure (ae_restrict_mem (gaussianDirectionBand_measurable A δ)) _)
    filter_upwards [hc,hbnd] with w hw hbnd
    exact hw hbnd
  have hu := hgain δ hδ hδsmall d h κ A z e α' β' E J a M 2 T hE hJ hM (by norm_num)
    hT hTbound hA hbound hsmall hEb hanchors hcover hαsupport hβsupport hpball hqball
  have hl : 1/(4*K^10*V) ≤ ((α' : Measure (Space d)).prod (β' : Measure (Sphere d))).real F := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) hinc
    simpa only [α',β',Measure.real,ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/(4*K^10*V))] using hh
  exact (not_lt_of_ge (hl.trans hu)) hlow

end Falconer

end OAI
