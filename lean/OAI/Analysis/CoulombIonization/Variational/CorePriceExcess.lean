import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.CoreSliceMassIntegrable
import OAI.Analysis.CoulombIonization.ThomasFermi.PacketFieldConstant

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace ENNReal
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open Set Filter Topology InnerProductSpace Laplacian
open MeasureTheory Filter
open scoped Topology
open MeasureTheory Filter
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter
open scoped Topology BigOperators Pointwise
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open scoped Convolution
open scoped RealInnerProductSpace
open MeasureTheory Filter Set Metric
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Set Filter Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology InnerProductSpace Laplacian
open Filter Set Metric Topology InnerProductSpace Laplacian
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open Filter
open scoped Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Filter Set Metric Topology
open MeasureTheory Complex Filter
open scoped Topology InnerProductSpace ContDiff BigOperators
open MeasureTheory Filter Set
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators InnerProductSpace
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

def corePriceExcess {N : ℕ} (Z lam : ℝ) (ψ : FormVector N) : ℝ :=
  formEnergy Z ψ+lam*N*formMass ψ-priceEnergy (energy Z) lam*formMass ψ

def normalizedCoreField {N : ℕ} (Z lam : ℝ) (ψ : FormVector N) (y : Space) : ℝ :=
  (Z*formMass ψ/‖y‖-coreCoulombAt ψ y)/formMass ψ-lam

lemma corePriceExcess_nonneg {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) : 0 ≤ corePriceExcess Z lam ψ :=
  sub_nonneg.mpr (hψ.priced_lower_bound hZ hlam)

theorem vacant_core_field_cap {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (hm : 0 < formMass ψ) (y : Space) {B : ℝ} (hB : 0 < B) (hnuc : B ≤ ‖y‖)
    (hc : FormAvoids ψ (ball y B)) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    normalizedCoreField Z lam ψ y ≤ packetFieldConstant *
      (1/B^4+1/B+Real.sqrt (corePriceExcess Z lam ψ/(formMass ψ*B))) := by
  have hδ := corePriceExcess_nonneg hψ hZ hlam
  have hgrid (n : ℕ) (hn : 0 < n) :
      (n:ℝ)^3*normalizedCoreField Z lam ψ y ≤ corePriceExcess Z lam ψ/formMass ψ+
        packetKineticConstant*(n:ℝ)^5/B^2+packetRepulsionConstant*(n:ℝ)^6/B := by
    have hh := grid_packet_screening hψ y hB hnuc hc hn hZ hlam
    have he :
        (corePriceExcess Z lam ψ + formMass ψ*(packetKineticConstant*(n:ℝ)^5/B^2+
          packetRepulsionConstant*(n:ℝ)^6/B))/formMass ψ =
        corePriceExcess Z lam ψ/formMass ψ+
          packetKineticConstant*(n:ℝ)^5/B^2+packetRepulsionConstant*(n:ℝ)^6/B := by
      field_simp
      ring
    rw [← he]
    apply (le_div_iff₀ hm).mpr
    unfold normalizedCoreField
    have he' :
        ((n:ℝ)^3*((Z*formMass ψ/‖y‖-coreCoulombAt ψ y)/formMass ψ-lam))*formMass ψ =
        (n:ℝ)^3*(Z*formMass ψ/‖y‖-coreCoulombAt ψ y-lam*formMass ψ) := by field_simp
    rw [he']
    exact hh
  have hh := field_cap_of_grid_bounds hB (div_nonneg hδ hm.le)
    packetKineticConstant_nonneg packetRepulsionConstant_nonneg hgrid
  simpa only [packetFieldConstant,div_div] using hh

lemma vacant_core_field_cap_normalized {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) (y : Space) {B : ℝ}
    (hB : 0 < B) (hnuc : B ≤ ‖y‖) (hc : FormAvoids ψ (ball y B))
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    Z/‖y‖-coreCoulombAt ψ y-lam ≤ packetFieldConstant*
      (1/B^4+1/B+Real.sqrt (corePriceExcess Z lam ψ/B)) := by
  have hh := vacant_core_field_cap hψ (by rw [hm]; norm_num) y hB hnuc hc hZ hlam
  simpa only [normalizedCoreField,hm,mul_one,one_mul,div_one] using hh

theorem vacant_core_quadratic_cap {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : 0 < formMass ψ) (y : Space) {B : ℝ}
    (hB : 0 < B) (hnuc : B ≤ ‖y‖) (hc : FormAvoids ψ (ball y B))
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    formMass ψ*(max (normalizedCoreField Z lam ψ y -
      packetFieldConstant*(1/B^4+1/B)) 0)^2 ≤
        packetFieldConstant^2*corePriceExcess Z lam ψ/B := by
  let s := Real.sqrt (corePriceExcess Z lam ψ/(formMass ψ*B))
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hδ := corePriceExcess_nonneg hψ hZ hlam
  have hh := vacant_core_field_cap hψ hm y hB hnuc hc hZ hlam
  have hmax : max (normalizedCoreField Z lam ψ y-packetFieldConstant*(1/B^4+1/B)) 0 ≤
      packetFieldConstant*s := max_le (by dsimp [s]; nlinarith) (mul_nonneg packetFieldConstant_pos.le hs)
  have hh2 := (sq_le_sq₀ (le_max_right _ _) (mul_nonneg packetFieldConstant_pos.le hs)).mpr hmax
  have hh3 := mul_le_mul_of_nonneg_left hh2 hm.le
  have hs2 : s^2 = corePriceExcess Z lam ψ/(formMass ψ*B) :=
    Real.sq_sqrt (div_nonneg hδ (mul_nonneg hm.le hB.le))
  have he : formMass ψ*(packetFieldConstant*s)^2 = packetFieldConstant^2*corePriceExcess Z lam ψ/B := by
    rw [mul_pow,hs2]
    field_simp
  rwa [he] at hh3


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators


def coreCapEnvelope {N : ℕ} (Z lam B : ℝ) (ψ : FormVector N) : ℝ :=
  packetFieldConstant*(1/B^4+1/B+
    Real.sqrt (corePriceExcess Z lam ψ/(formMass ψ*B)))

lemma coreCapEnvelope_nonneg {N : ℕ} (Z lam : ℝ) {B : ℝ} (hB : 0 < B)
    (ψ : FormVector N) : 0 ≤ coreCapEnvelope Z lam B ψ := by
  unfold coreCapEnvelope
  have := packetFieldConstant_pos
  positivity

lemma vacant_core_field_cap_all_mass {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {B : ℝ} (hB : 0 < B) (hnuc : B ≤ ‖y‖)
    (hc : FormAvoids ψ (ball y B)) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    normalizedCoreField Z lam ψ y ≤ coreCapEnvelope Z lam B ψ := by
  by_cases hm : 0 < formMass ψ
  · exact vacant_core_field_cap hψ hm y hB hnuc hc hZ hlam
  · have hm0 : formMass ψ = 0 := le_antisymm (not_lt.mp hm) (formMass_nonneg ψ)
    have hh := coreCapEnvelope_nonneg Z lam hB ψ
    simp only [normalizedCoreField,hm0,div_zero,zero_sub]
    linarith

theorem vacant_core_uniform_field_cap {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (y : Space) {B : ℝ} (hB : 0 < B) (hnuc : 2*B ≤ ‖y‖)
    (hc : FormAvoids ψ (ball y (2*B))) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    ∀ z ∈ closedBall y B, normalizedCoreField Z lam ψ z ≤ coreCapEnvelope Z lam B ψ := by
  intro z hz
  have hzy : ‖z-y‖ ≤ B := mem_closedBall.mp hz
  have hnorm : B ≤ ‖z‖ := by
    have hh := norm_add_le (y-z) z
    rw [sub_add_cancel, norm_sub_rev y z] at hh
    linarith
  apply vacant_core_field_cap_all_mass hψ z hB hnorm _ hZ hlam
  apply hc.mono
  intro x hx
  apply mem_ball.mpr
  change ‖x-y‖ < 2*B
  have hh := norm_add_le (x-z) (z-y)
  rw [sub_add_sub_cancel] at hh
  have hx' : ‖x-z‖ < B := mem_ball.mp hx
  linarith

lemma coreCapEnvelope_weighted_square {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) {Z lam B : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) :
    formMass ψ*(coreCapEnvelope Z lam B ψ)^2 ≤
      2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass ψ+corePriceExcess Z lam ψ/B) := by
  have hm := formMass_nonneg ψ
  have hδ := corePriceExcess_nonneg hψ hZ hlam
  by_cases hm0 : formMass ψ = 0
  · rw [hm0,zero_mul,mul_zero,zero_add]
    positivity
  have hmp : 0 < formMass ψ := lt_of_le_of_ne hm (Ne.symm hm0)
  let a := 1/B^4+1/B
  let s := Real.sqrt (corePriceExcess Z lam ψ/(formMass ψ*B))
  have hs2 : s^2 = corePriceExcess Z lam ψ/(formMass ψ*B) :=
    Real.sq_sqrt (div_nonneg hδ (mul_nonneg hm hB.le))
  have hbound : (a+s)^2 ≤ 2*(a^2+s^2) := by nlinarith [sq_nonneg (a-s)]
  have hh := mul_le_mul_of_nonneg_left hbound (mul_nonneg hm (sq_nonneg packetFieldConstant))
  have he : formMass ψ*packetFieldConstant^2*(2*(a^2+s^2)) =
      2*packetFieldConstant^2*(a^2*formMass ψ+corePriceExcess Z lam ψ/B) := by
    rw [hs2]
    field_simp
  rw [he] at hh
  dsimp only [coreCapEnvelope]
  dsimp only [a,s] at hh
  nlinarith only [hh]

lemma SobolevVector.coreSlice_excess_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (t : Spins M) :
    Integrable (fun y => corePriceExcess Z lam (coreSlice ψ t y)) :=
  ((hψ.coreSlice_energy_integrable Z t).add
    ((hψ.coreSlice_mass_integrable t).const_mul _)).sub
      ((hψ.coreSlice_mass_integrable t).const_mul _)

lemma SobolevVector.coreSlice_envelope_measurable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (Z lam B : ℝ) (t : Spins M) :
    AEStronglyMeasurable (fun y => coreCapEnvelope Z lam B (coreSlice ψ t y)) := by
  have hm := (hψ.coreSlice_mass_integrable t).aestronglyMeasurable
  have hδ := (hψ.coreSlice_excess_integrable Z lam t).aestronglyMeasurable
  exact ((aestronglyMeasurable_const.add aestronglyMeasurable_const).add
    ((hδ.aemeasurable.div (hm.aemeasurable.mul_const B)).sqrt.aestronglyMeasurable)).const_mul _

lemma coreSlice_envelope_square_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) {Z lam B : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) (t : Spins M) :
    Integrable (fun y => formMass (coreSlice ψ t y)*
      (coreCapEnvelope Z lam B (coreSlice ψ t y))^2) := by
  have hi := (((hψ.coreSlice_mass_integrable t).const_mul ((1/B^4+1/B)^2)).add
    ((hψ.coreSlice_excess_integrable Z lam t).div_const B)).const_mul (2*packetFieldConstant^2)
  apply hi.mono' ((hψ.coreSlice_mass_integrable t).aestronglyMeasurable.mul
    ((hψ.coreSlice_envelope_measurable Z lam B t).pow 2))
  apply (ha.ae_coreSlice hψ t).mono
  intro y hy
  simp only [Pi.mul_apply,Pi.pow_apply,Pi.add_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (formMass_nonneg _) (sq_nonneg _))]
  exact coreCapEnvelope_weighted_square hy hZ hlam hB

theorem integrated_core_envelope_square {N M : ℕ} {ψ : FormVector (N+M)}
    (ha : CoreAntisymmetric ψ) (hψ : SobolevVector ψ) {Z lam B : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hB : 0 < B) :
    (∑ t : Spins M, ∫ y, formMass (coreSlice ψ t y)*
      (coreCapEnvelope Z lam B (coreSlice ψ t y))^2) ≤
      2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass ψ+
        ((∑ t : Spins M, ∫ y, formEnergy Z (coreSlice ψ t y))+
          lam*N*formMass ψ-priceEnergy (energy Z) lam*formMass ψ)/B) := by
  have hti (t : Spins M) := coreSlice_envelope_square_integrable ha hψ hZ hlam hB t
  have hbound (t : Spins M) :
      (∫ y, formMass (coreSlice ψ t y)*(coreCapEnvelope Z lam B (coreSlice ψ t y))^2) ≤
      ∫ y, 2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass (coreSlice ψ t y)+
        corePriceExcess Z lam (coreSlice ψ t y)/B) := by
    apply integral_mono_ae (hti t)
      ((((hψ.coreSlice_mass_integrable t).const_mul _).add
        ((hψ.coreSlice_excess_integrable Z lam t).div_const B)).const_mul _)
    exact (ha.ae_coreSlice hψ t).mono fun _ hy => coreCapEnvelope_weighted_square hy hZ hlam hB
  have hh := Finset.sum_le_sum (fun t (_ : t ∈ (Finset.univ : Finset (Spins M))) => hbound t)
  have he (t : Spins M) : (∫ y, corePriceExcess Z lam (coreSlice ψ t y)) =
      (∫ y, formEnergy Z (coreSlice ψ t y))+lam*N*(∫ y, formMass (coreSlice ψ t y))-
        priceEnergy (energy Z) lam*(∫ y, formMass (coreSlice ψ t y)) := by
    simp only [corePriceExcess]
    rw [integral_sub,integral_add,integral_const_mul,integral_const_mul]
    · exact hψ.coreSlice_energy_integrable Z t
    · exact (hψ.coreSlice_mass_integrable t).const_mul (lam*N)
    · exact (hψ.coreSlice_energy_integrable Z t).add
        ((hψ.coreSlice_mass_integrable t).const_mul (lam*N))
    · exact (hψ.coreSlice_mass_integrable t).const_mul (priceEnergy (energy Z) lam)
  have he' (t : Spins M) :
      (∫ y, 2*packetFieldConstant^2*((1/B^4+1/B)^2*formMass (coreSlice ψ t y)+
        corePriceExcess Z lam (coreSlice ψ t y)/B)) =
      2*packetFieldConstant^2*((1/B^4+1/B)^2*(∫ y, formMass (coreSlice ψ t y))+
        ((∫ y, formEnergy Z (coreSlice ψ t y))+lam*N*(∫ y, formMass (coreSlice ψ t y))-
          priceEnergy (energy Z) lam*(∫ y, formMass (coreSlice ψ t y)))/B) := by
    rw [integral_const_mul,integral_add ((hψ.coreSlice_mass_integrable t).const_mul _)
      ((hψ.coreSlice_excess_integrable Z lam t).div_const B),integral_const_mul,integral_div,he]
  simp_rw [he'] at hh
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_div,← Finset.mul_sum,
    hψ.integral_coreSlice_mass] at hh
  exact hh


open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

end CoulombAtom

end

end OAI
