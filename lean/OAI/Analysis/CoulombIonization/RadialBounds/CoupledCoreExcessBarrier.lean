import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.DeletedFieldBudget
import OAI.Analysis.CoulombIonization.RadialBounds.RootMomentCauchyBarrier
import OAI.Analysis.CoulombIonization.Localization.CoreHistoryOutMaximumBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_CoupledCoreExcess_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators

lemma outKinetic_nonneg {N M : ℕ} (ψ : FormVector (N+M)) : 0 ≤ outKinetic ψ := by
  unfold outKinetic
  positivity

lemma outRepulsion_nonneg {N M : ℕ} (ψ : FormVector (N+M)) : 0 ≤ outRepulsion ψ := by
  apply Finset.sum_nonneg; intro s _
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  split_ifs
  · exact integral_nonneg (fun _ => by positivity)
  · exact le_rfl

lemma cutExteriorPrice_eq_field_work {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevVector ψ) (Z lam : ℝ) (c : Fin L → Fin 2) :
    cutExteriorPrice p hp Z lam ψ c =
      outKinetic (orderedCutForm p hp ψ c)-
        (∑ s : Spins (cutOutNumber c), ∫ u,
          conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u)+
        outRepulsion (orderedCutForm p hp ψ c) := by
  have hχ := orderedCutForm_sobolev p hp hψ c
  rw [integral_conditionalFieldSum hχ Z lam]
  unfold cutExteriorPrice cutCoreEnergy
  rw [integrated_core_parts hχ Z,formEnergy_core_out_cross]
  ring

lemma cutCoreExcess_le_field_work {L : ℕ}
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) {ψ : FormVector L}
    (hψ : SobolevVector ψ) (Z lam : ℝ) :
    (∑ c : Fin L → Fin 2, cutCoreExcess p hp Z lam ψ c) ≤
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p)+
        (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
          conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u) := by
  have hid := fock_cut_excess_identity p hp hψ Z lam
  simp_rw [cutExteriorPrice_eq_field_work p hp hψ Z lam] at hid
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib] at hid
  have hk : 0 ≤ ∑ c : Fin L → Fin 2, outKinetic (orderedCutForm p hp ψ c) :=
    Finset.sum_nonneg (fun c _ => outKinetic_nonneg _)
  have hr : 0 ≤ ∑ c : Fin L → Fin 2, outRepulsion (orderedCutForm p hp ψ c) :=
    Finset.sum_nonneg (fun c _ => outRepulsion_nonneg _)
  linarith

lemma conditionalFieldSum_le_max {N M : ℕ} (ψ : FormVector (N+M))
    (s : Spins M) (u : Configuration M) (Z lam : ℝ) :
    conditionalFieldSum Z lam ψ s u ≤
      conditionalOutMaximum Z lam ψ s u*M*formMass (coreSlice ψ s u) := by
  have hh := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => conditionalField_le_outMaximum Z lam ψ s u i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  unfold conditionalFieldSum
  nlinarith [mul_le_mul_of_nonneg_left hh (formMass_nonneg (coreSlice ψ s u))]

lemma radial_max_out_product_integrable {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t)
    (hb : 0 < b) (hy : t+2*b ≤ ‖y‖) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    Integrable (fun u => conditionalOutMaximum Z lam (orderedCutForm p hp ψ c) s u*
      (cutOutNumber c:ℝ)*formMass (coreSlice (orderedCutForm p hp ψ c) s u)) := by
  dsimp only
  have hχ := orderedCutForm_sobolev (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) hψ c
  have hh : Integrable (fun u => conditionalOutMaximum Z lam
      (orderedCutForm (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c) s u*
        formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
          (coreFirstRadialCut_partition y ht hb) ψ c) s u)) := by
    apply (hχ.coreSlice_mass_integrable s).bdd_mul
      (conditionalOutMaximum_aemeasurable hχ s Z lam).aestronglyMeasurable
    apply ae_of_all; intro u
    rw [Real.norm_of_nonneg (conditionalOutMaximum_nonneg _ _ _ _ _)]
    exact radial_conditionalOutMaximum_bound ψ y ht hb hy hZ hlam c s u
  simpa only [mul_right_comm] using hh.mul_const (cutOutNumber c:ℝ)

theorem radial_full_field_work_budget {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t)
    (hb : 0 < b) (hy : t+2*b ≤ ‖y‖) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∑ c : Fin L → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
      conditionalFieldSum Z lam (orderedCutForm p hp ψ c) s u) ≤
      Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*
        Real.sqrt (∑ c : Fin L → Fin 2, (cutOutNumber c:ℝ)^2*
          formMass (orderedCutForm p hp ψ c)) := by
  let p := coreFirstRadialCut y ht hb
  let hp := coreFirstRadialCut_partition y ht hb
  dsimp only
  have hc := weighted_sum_integral_cauchy
    (ι := Σ c : Fin L → Fin 2, Spins (cutOutNumber c))
    (X := fun cs => Configuration (cutOutNumber cs.1)) (fun _ => volume)
    (fun cs u => formMass (coreSlice (orderedCutForm p hp ψ cs.1) cs.2 u))
    (fun cs u => conditionalOutMaximum Z lam (orderedCutForm p hp ψ cs.1) cs.2 u)
    (fun cs _ => (cutOutNumber cs.1:ℝ)) (fun _ _ => formMass_nonneg _)
    (fun cs => radial_outMaximum_square_integrable hψ y ht hb hy hZ hlam cs.1 cs.2)
    (fun cs => ((orderedCutForm_sobolev p hp hψ cs.1).coreSlice_mass_integrable cs.2).const_mul _)
    (fun cs => radial_max_out_product_integrable hψ y ht hb hy hZ hlam cs.1 cs.2)
  simp only [Fintype.sum_sigma,integral_const_mul,←Finset.mul_sum,
    SobolevVector.integral_coreSlice_mass (orderedCutForm_sobolev p hp hψ _)] at hc
  apply le_trans _ hc
  apply Finset.sum_le_sum; intro c _
  apply Finset.sum_le_sum; intro s _
  apply integral_mono
    (conditionalFieldSum_integrable (orderedCutForm_sobolev p hp hψ c) Z lam s)
    (radial_max_out_product_integrable hψ y ht hb hy hZ hlam c s)
  intro u
  exact conditionalFieldSum_le_max _ s u Z lam

theorem radial_core_excess_coupling {L : ℕ} {ψ : FormVector L}
    (hψ : SobolevVector ψ) (y : Space) {t b R : ℝ} (ht : 0 ≤ t)
    (hb : 0 < b) (hy : t+2*b ≤ ‖y‖) (hR : t+b ≤ R) {Z lam : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    let p := coreFirstRadialCut y ht hb
    let hp := coreFirstRadialCut_partition y ht hb
    (∑ c : Fin L → Fin 2, cutCoreExcess p hp Z lam ψ c) ≤
      corePriceExcess Z lam ψ+(1/2:ℝ)*weightedParticleCount ψ (spatialErrorWeight p)+
        Real.sqrt (freshOutMaximumSecondMoment p hp ψ Z lam)*
          Real.sqrt (∫ x, rawBallCount y R x^2 ∂formRawLaw ψ) := by
  dsimp only
  refine (cutCoreExcess_le_field_work _ _ hψ Z lam).trans (add_le_add le_rfl
    ((radial_full_field_work_budget hψ y ht hb hy hZ hlam).trans ?_))
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (radialCut_out_second_moment hψ y ht hb hR))
    (Real.sqrt_nonneg _)

end Work_CoupledCoreExcess_barrier_scope

open MeasureTheory Filter
open scoped BigOperators

lemma radial_freshMaximum_statistic_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) {r b : ℝ} (hr : 0 ≤ r) (hb : 0 < b)
    (hy : r+2*b ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (s : Spins M) :
    Integrable (fun v => freshOutMaximumSecondMoment (coreFirstRadialCut y hr hb)
      (coreFirstRadialCut_partition y hr hb) (coreSlice ψ s v) Z lam) := by
  apply integrable_finsetSum
  intro c _
  exact nextBlockMaximum_square_statistic_integrable ψ _ _ c Z lam
    (fun t => radial_nextBlockMaximum_square_integrable hψ y hr hb hy hZ hlam c t) s

namespace CoreObservationGraph

lemma outMoment_eq_average (G : CoreObservationGraph) (y : Space) {r b : ℝ}
    (hr : 0 ≤ r) (hb : 0 < b) (hy : r+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    G.outMoment y hr hb Z lam = coreLawAverage G.vector (fun φ =>
      freshOutMaximumSecondMoment (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) φ Z lam) := by
  unfold outMoment
  change (∑ c : Fin G.coreSize → Fin 2, ∑ s : Spins (cutOutNumber c+G.outSize), ∫ u,
    conditionalBlockMaximum (K := cutOutNumber c) Z lam
      (nextCoreObservation (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) G.vector c) s u^2*
      formMass (coreSlice
        (nextCoreObservation (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) G.vector c) s u)) = _
  have he (c : Fin G.coreSize → Fin 2) := nextBlockMaximum_square_fubini G.vector
    (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) c Z lam
    (fun s => radial_nextBlockMaximum_square_integrable G.sobolev y hr hb hy hZ hlam c s)
  simp_rw [he]
  rw [Finset.sum_comm]
  unfold coreLawAverage freshOutMaximumSecondMoment
  apply Finset.sum_congr rfl
  intro s _
  apply (integral_finsetSum _ _).symm
  intro c _
  exact nextBlockMaximum_square_statistic_integrable G.vector _ _ c Z lam
    (fun t => radial_nextBlockMaximum_square_integrable G.sobolev y hr hb hy hZ hlam c t) s

theorem observe_excess_budget (G : CoreObservationGraph) (y : Space) {r b R : ℝ}
    (hr : 0 ≤ r) (hb : 0 < b) (hy : r+2*b ≤ ‖y‖) (hR : r+b < R)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    (∑ c : Fin G.coreSize → Fin 2,
      (G.observe (coreFirstRadialCut y hr hb) (coreFirstRadialCut_partition y hr hb) c).excess Z lam) ≤
      G.excess Z lam+((3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2)*
        (Real.sqrt (G.countMoment y R)*Real.sqrt G.mass)+
        Real.sqrt (G.outMoment y hr hb Z lam)*Real.sqrt (G.countMoment y R) := by
  let p := coreFirstRadialCut y hr hb
  let hp := coreFirstRadialCut_partition y hr hb
  let K := (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2
  let C (s : Spins G.outSize) (v : Configuration G.outSize) := rawCountMoment (coreSlice G.vector s v) y R
  let F (s : Spins G.outSize) (v : Configuration G.outSize) :=
    freshOutMaximumSecondMoment p hp (coreSlice G.vector s v) Z lam
  let W (s : Spins G.outSize) (v : Configuration G.outSize) := formMass (coreSlice G.vector s v)
  have hC (s : Spins G.outSize) : Integrable (C s) := rawCountMoment_coreSlice_integrable G.sobolev y R s
  have hF (s : Spins G.outSize) : Integrable (F s) := radial_freshMaximum_statistic_integrable G.sobolev y hr hb hy hZ hlam s
  have hW (s : Spins G.outSize) : Integrable (W s) := G.sobolev.coreSlice_mass_integrable s
  have hCn (s : Spins G.outSize) (v : Configuration G.outSize) : 0 ≤ C s v := rawCountMoment_nonneg _ _ _
  have hFn (s : Spins G.outSize) (v : Configuration G.outSize) : 0 ≤ F s v := freshOutMaximumSecondMoment_nonneg _ _ _ _ _
  have hWn (s : Spins G.outSize) (v : Configuration G.outSize) : 0 ≤ W s v := formMass_nonneg _
  have hCW (s : Spins G.outSize) := integrable_sqrt_mul_sqrt (hC s) (hW s) (hCn s) (hWn s)
  have hFC (s : Spins G.outSize) := integrable_sqrt_mul_sqrt (hF s) (hC s) (hFn s) (hCn s)
  have hcW := sum_integral_sqrt_mul_sqrt_le (fun _ : Spins G.outSize => volume) C W hC hW hCn hWn
  have hcF := sum_integral_sqrt_mul_sqrt_le (fun _ : Spins G.outSize => volume) F C hF hC hFn hCn
  have hstep (s : Spins G.outSize) :
      (∫ v, ∑ c : Fin G.coreSize → Fin 2, cutCoreExcess p hp Z lam (coreSlice G.vector s v) c) ≤
        ∫ v, corePriceExcess Z lam (coreSlice G.vector s v)+
          K*(Real.sqrt (C s v)*Real.sqrt (W s v))+Real.sqrt (F s v)*Real.sqrt (C s v) := by
    apply integral_mono_ae
      (integrable_finsetSum _ (fun c _ => nextCoreObservation_excess_statistic_integrable G.sobolev p hp c s Z lam))
      (((G.sobolev.coreSlice_excess_integrable Z lam s).add ((hCW s).const_mul K)).add (hFC s))
    filter_upwards [G.sobolev.ae_coreSlice s] with v hv
    have hh := radial_core_excess_coupling hv y hr hb hy hR.le hZ hlam
    dsimp only at hh
    rw [←rawCountMoment_eq_integral hv y R] at hh
    have hi := radial_ims_le_sqrt_count hv y hr hb hR
    exact hh.trans (add_le_add (add_le_add le_rfl hi) le_rfl)
  have he (s : Spins G.outSize) :
      (∫ v, corePriceExcess Z lam (coreSlice G.vector s v)+
          K*(Real.sqrt (C s v)*Real.sqrt (W s v))+Real.sqrt (F s v)*Real.sqrt (C s v)) =
      (∫ v, corePriceExcess Z lam (coreSlice G.vector s v))+
        K*(∫ v, Real.sqrt (C s v)*Real.sqrt (W s v))+
        (∫ v, Real.sqrt (F s v)*Real.sqrt (C s v)) := by
    have hA : Integrable (fun v => corePriceExcess Z lam (coreSlice G.vector s v)+
        K*(Real.sqrt (C s v)*Real.sqrt (W s v))) :=
      (G.sobolev.coreSlice_excess_integrable Z lam s).add ((hCW s).const_mul K)
    rw [integral_add hA (hFC s),
      integral_add (G.sobolev.coreSlice_excess_integrable Z lam s) ((hCW s).const_mul K),integral_const_mul]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hstep s)
  simp_rw [he] at hh
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hh
  have hend := hh.trans (add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hcW (by positivity : 0 ≤ K))) hcF)
  change (∑ c : Fin G.coreSize → Fin 2, coreLawAverage (nextCoreObservation p hp G.vector c) (corePriceExcess Z lam)) ≤ _
  rw [sum_nextCoreObservation_excess G.sobolev p hp Z lam]
  have hwe : (∑ s : Spins G.outSize, ∫ v, W s v) = G.mass := G.sobolev.integral_coreSlice_mass
  have hfe : (∑ s : Spins G.outSize, ∫ v, F s v) = G.outMoment y hr hb Z lam :=
    (G.outMoment_eq_average y hr hb hy hZ hlam).symm
  rw [hwe,hfe] at hend
  exact hend

end CoreObservationGraph

end CoulombAtom

end

end OAI
