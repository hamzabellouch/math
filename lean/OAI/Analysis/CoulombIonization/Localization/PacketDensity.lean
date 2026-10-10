import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.Radial
import OAI.Analysis.CoulombIonization.Ionization.InsertionTermsDisjointSet
import OAI.Analysis.CoulombIonization.Localization.RadialPacketBase

namespace OAI

noncomputable section

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
namespace CoulombAtom

lemma integral_one_position (f : Space → ℝ) :
    (∫ x : Configuration 1, f (x 0)) = ∫ y, f y := by
  exact (volume_preserving_funUnique (Fin 1) Space).integral_comp
    (MeasurableEquiv.funUnique (Fin 1) Space).measurableEmbedding f

lemma integral_one_configuration (f : Configuration 1 → ℝ) :
    (∫ y : Space, f (fun _ => y)) = ∫ x, f x := by
  exact ((volume_preserving_funUnique (Fin 1) Space).symm
    (MeasurableEquiv.funUnique (Fin 1) Space)).integral_comp
    (MeasurableEquiv.funUnique (Fin 1) Space).symm.measurableEmbedding f

def packetDensity (y : Space) (R : ℝ) (x : Space) : ℝ :=
  ∑ s : Spins 1, ‖(radialLocalOrbital y R).value s (fun _ => x)‖^2

lemma packetDensity_formula (y : Space) (R : ℝ) (x : Space) :
    packetDensity y R x = (Fintype.card (Spins 1) : ℝ) *
      (Real.sqrt (formMass (radialScaledRaw R)))⁻¹ ^ 2 *
      ‖radialPacketBase (R⁻¹ • (x-y))‖^2 := by
  simp only [packetDensity,radialLocalOrbital,scaleForm,norm_real_mul_sq,radialLocalRaw_mass]
  simp only [radialLocalRaw,smoothForm,radialLocalSeed,radialScaledSeed,
    radialPacketSeed,radialCenterShift,Pi.smul_apply,Pi.add_apply,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,sub_eq_add_neg,mul_assoc]

lemma packetDensity_continuous (y : Space) (R : ℝ) : Continuous (packetDensity y R) := by
  change Continuous (fun x => packetDensity y R x)
  simp_rw [packetDensity_formula]
  have hc : Continuous (fun x : Space => R⁻¹ • (x-y)) :=
    (continuous_id.sub continuous_const).const_smul R⁻¹
  have hn : Continuous (fun x : Space => ‖radialPacketBase (R⁻¹ • (x-y))‖^2) :=
    (radialPacketBase_smooth.continuous.comp hc).norm.pow 2
  exact continuous_const.mul hn

lemma packetDensity_support (y : Space) {R : ℝ} (hR : 0 < R) {x : Space}
    (hx : packetDensity y R x ≠ 0) : ‖x-y‖ ≤ R := by
  by_contra hh
  have hz := radialLocalOrbital_zero y hR (x := fun _ => x) (not_le.mp hh)
  apply hx
  unfold packetDensity
  apply Finset.sum_eq_zero
  intro s _
  rw [(hz s).1,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)]

lemma packetDensity_compact (y : Space) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (packetDensity y R) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall y R)
  intro x hx
  exact (Metric.mem_closedBall).mpr (packetDensity_support y hR hx)

lemma packetDensity_integrable (y : Space) {R : ℝ} (hR : 0 < R) :
    Integrable (packetDensity y R) :=
  (packetDensity_continuous y R).integrable_of_hasCompactSupport (packetDensity_compact y hR)

lemma packetDensity_memLp (y : Space) {R : ℝ} (hR : 0 < R) :
    MemLp (packetDensity y R) (5/3) :=
  (packetDensity_continuous y R).memLp_of_hasCompactSupport (packetDensity_compact y hR)

lemma packetDensity_mass (y : Space) {R : ℝ} (hR : 0 < R) :
    (∫ x, packetDensity y R x) = 1 := by
  have hm := (radialLocalOrbital_admissible y hR).2.2.2.2.1
  change formMass (radialLocalOrbital y R) = 1 at hm
  rw [← hm]
  unfold packetDensity formMass
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    exact integral_one_configuration (fun x => ‖(radialLocalOrbital y R).value s x‖^2)
  · intro s _
    have hh := ((radialLocalOrbital_admissible y hR).1 s).integrable_norm_pow (by norm_num)
    exact ((volume_preserving_funUnique (Fin 1) Space).symm
        (MeasurableEquiv.funUnique (Fin 1) Space)).integrable_comp_of_integrable hh

lemma packetDensity_translate (y : Space) (R : ℝ) (x : Space) :
    packetDensity y R x = packetDensity 0 R (x-y) := by
  simp only [packetDensity_formula,sub_zero]

lemma packetDensity_radial (R : ℝ) : CoulombAnalysis.IsRadial (packetDensity 0 R) := by
  intro x y hxy
  simp only [packetDensity_formula,sub_zero,radialPacketBase,norm_smul,hxy]

theorem packetDensity_potential (y : Space) {R : ℝ} (hR : 0 < R)
    {z : Space} (hz : R < ‖z-y‖) :
    (∫ x, packetDensity y R x / ‖z-x‖) = 1 / ‖z-y‖ := by
  have ht := integral_add_right_eq_self (μ := volume)
    (fun x : Space => packetDensity y R x / ‖z-x‖) y
  rw [← ht]
  have he : (fun x => packetDensity y R (x+y) / ‖z-(x+y)‖) =
      (fun x => packetDensity 0 R x / ‖(z-y)-x‖) := by
    funext x
    rw [packetDensity_translate,add_sub_cancel_right]
    congr 2
    abel
  rw [he]
  have hn := CoulombAnalysis.tfPotential_newton_exterior
    (packetDensity_integrable 0 hR) (packetDensity_memLp 0 hR) (packetDensity_radial R)
    hR.le (fun x hx => by simpa only [sub_zero] using packetDensity_support 0 hR hx) hz
  rw [packetDensity_mass 0 hR] at hn
  exact hn

lemma packetDensity_eq_two (y : Space) (R : ℝ) (x : Space) (s : Spins 1) :
    packetDensity y R x = 2 * ‖(radialLocalOrbital y R).value s (fun _ => x)‖^2 := by
  simp only [packetDensity,radialLocalOrbital,scaleForm,radialLocalRaw,smoothForm,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1

lemma radialLocalOrbital_value_config (y : Space) (R : ℝ) (s : Spins 1)
    (x : Configuration 1) :
    (radialLocalOrbital y R).value s x =
      (radialLocalOrbital y R).value s (fun _ => x 0) := by
  congr 1
  funext i
  exact congrArg x (Subsingleton.elim i 0)

lemma radialLocalOrbital_potential (y : Space) {R : ℝ} (hR : 0 < R)
    {z : Space} (hz : R < ‖z-y‖) (s : Spins 1) :
    (∫ x : Configuration 1, ‖(radialLocalOrbital y R).value s x‖^2 / ‖z-x 0‖) =
      (1/2 : ℝ) / ‖z-y‖ := by
  have ht := packetDensity_potential y hR hz
  simp_rw [packetDensity_eq_two y R _ s,mul_div_assoc] at ht
  rw [integral_const_mul] at ht
  have he : (∫ x : Configuration 1, ‖(radialLocalOrbital y R).value s x‖^2 / ‖z-x 0‖) =
      ∫ v : Space, ‖(radialLocalOrbital y R).value s (fun _ => v)‖^2 / ‖z-v‖ := by
    rw [← integral_one_configuration]
  rw [he]
  calc
    _ = (1 / ‖z-y‖) / 2 := by linarith
    _ = _ := by ring

lemma radialLocalOrbital_nuclear (y : Space) {R : ℝ} (hR : 0 < R)
    (hy : R < ‖y‖) : formNuclear (radialLocalOrbital y R) = 1 / ‖y‖ := by
  have hh (s : Spins 1) := radialLocalOrbital_potential y hR
    (z := 0) (by simpa only [zero_sub,norm_neg] using hy) s
  simp only [zero_sub,norm_neg] at hh
  unfold formNuclear
  simp only [Fin.sum_univ_one,hh,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  norm_num [Spins]
  ring

lemma integral_join_left {N M : ℕ} {f : Configuration (N+M) → ℝ}
    (hf : Integrable f) :
    (∫ x : Configuration N, ∫ y : Configuration M, f (joinLists x y)) = ∫ z, f z := by
  have hj := integrable_join (N := N) (M := M) hf
  have he := (configurationJoin_preserving N M).integral_comp
    (configurationJoin N M).toHomeomorph.measurableEmbedding f
  simp only [configurationJoin_apply_prod] at he
  rw [Measure.volume_eq_prod] at hj he
  exact (integral_prod _ hj).symm.trans he

def coreCoulombAt {N : ℕ} (ψ : FormVector N) (y : Space) : ℝ :=
  ∑ s : Spins N, ∑ i : Fin N, ∫ x, ‖ψ.value s x‖^2 / ‖x i-y‖

lemma tensor_packet_pair {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {R B : ℝ} (hR : 0 < R) (hRB : R < B)
    (hc : ∀ x i, ‖x i-y‖ < B → FormZeroAt ψ x)
    (s : Spins N) (t : Spins 1) (i : Fin N) :
    (∫ z, ‖(tensorForm ψ (radialLocalOrbital y R)).value (joinLists s t) z‖^2 /
      ‖z i.castSucc-z (Fin.last N)‖) =
      (1/2 : ℝ) * ∫ x, ‖ψ.value s x‖^2 / ‖x i-y‖ := by
  have hφ := (radialLocalOrbital_admissible y hR).sobolevFermion.sobolevVector
  have hT := hψ.tensor hφ
  have hi := pair_integrable i.castSucc (Fin.last N) (Fin.castSucc_ne_last i)
    (hT.1 (joinLists s t)) (hT.2.1 (joinLists s t) _) (hT.2.2 (joinLists s t) _)
  rw [← integral_join_left hi]
  change (∫ x : Configuration N, ∫ v : Configuration 1,
    ‖(tensorForm ψ (radialLocalOrbital y R)).value (joinLists s t) (joinLists x v)‖^2 /
    ‖joinLists x v (finSumFinEquiv (Sum.inl i)) -
      joinLists x v (finSumFinEquiv (Sum.inr (0 : Fin 1)))‖) = _
  simp only [tensorForm_value_join,joinLists_left,joinLists_right,norm_mul,mul_pow,
    mul_div_assoc,integral_const_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  by_cases hz : ψ.value s x = 0
  · simp only [hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),zero_mul,zero_div,mul_zero]
  · have hd : R < ‖x i-y‖ := hRB.trans_le (le_of_not_gt fun hh => hz ((hc x i hh s).1))
    dsimp only
    rw [radialLocalOrbital_potential y hR hd]
    ring

lemma tensorCross_packet {N : ℕ} {ψ : FormVector N} (hψ : SobolevVector ψ)
    (y : Space) {R B : ℝ} (hR : 0 < R) (hRB : R < B)
    (hc : ∀ x i, ‖x i-y‖ < B → FormZeroAt ψ x) :
    tensorCross ψ (radialLocalOrbital y R) = coreCoulombAt ψ y := by
  unfold tensorCross coreCoulombAt
  simp_rw [tensor_packet_pair hψ y hR hRB hc,← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  norm_num [Spins]
  simp only [← Finset.mul_sum]
  ring

theorem local_point_field {N : ℕ} {ψ : FormVector N} (hψ : SobolevFermion ψ)
    (y : Space) {R B : ℝ} (hR : 0 < R) (hRB : R < B) (hy : R < ‖y‖)
    (hc : ∀ x i, ‖x i-y‖ < B → FormZeroAt ψ x)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam) :
    Z * formMass ψ / ‖y‖ - coreCoulombAt ψ y ≤
      (formEnergy Z ψ + lam*N*formMass ψ - priceEnergy (energy Z) lam * formMass ψ) +
      formMass ψ * (radialPacketKinetic / R^2 + lam) := by
  have hh := local_screened_insertion hψ (radialLocalOrbital_admissible y hR)
    (Metric.ball y B) (fun x i hi => hc x i (Metric.mem_ball.mp hi))
    (fun x hx => radialLocalOrbital_zero y hR (hRB.trans_le (le_of_not_gt
      (fun hh => hx (Metric.mem_ball.mpr hh))))) hZ hlam
  rw [radialLocalOrbital_nuclear y hR hy,tensorCross_packet hψ.sobolevVector y hR hRB hc,
    radialLocalOrbital_kinetic y hR] at hh
  simpa only [mul_one_div] using hh

end CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators

end

end OAI
