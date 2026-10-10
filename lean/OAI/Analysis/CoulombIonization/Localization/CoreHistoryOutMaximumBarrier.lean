import Mathlib
import OAI.Analysis.CoulombIonization.Ionization.CoreHistoryFieldFubiniBarrier
import OAI.Analysis.CoulombIonization.FieldAnalysis.OutMaximumSubmeanBarrier

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators

def conditionalBlockMaximum {N K M : ℕ} (Z lam : ℝ) (ψ : FormVector (N+(K+M)))
    (s : Spins (K+M)) (u : Configuration (K+M)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun o : Option (Fin K) =>
    o.elim 0 (fun i => normalizedCoreField Z lam (coreSlice ψ s u) (leftList u i)))

lemma conditionalBlockMaximum_nonneg {N K M : ℕ} (Z lam : ℝ)
    (ψ : FormVector (N+(K+M))) (s : Spins (K+M)) (u : Configuration (K+M)) :
    0 ≤ conditionalBlockMaximum (K := K) Z lam ψ s u :=
  Finset.le_sup' (fun o : Option (Fin K) =>
    o.elim 0 (fun i => normalizedCoreField Z lam (coreSlice ψ s u) (leftList u i)))
    (Finset.mem_univ none)

lemma conditionalBlockMaximum_aemeasurable {N K M : ℕ} {ψ : FormVector (N+(K+M))}
    (hψ : SobolevVector ψ) (s : Spins (K+M)) (Z lam : ℝ) :
    AEMeasurable (conditionalBlockMaximum (K := K) Z lam ψ s) := by
  obtain ⟨F,hF,he⟩ := coreSlice_field_measurable_rep hψ s Z lam
  let f : Option (Fin K) → Configuration (K+M) → ℝ :=
    fun o u => o.elim 0 (fun i => F (u,leftList u i))
  have hf (o : Option (Fin K)) : Measurable (f o) := by
    cases o with
    | none => exact measurable_const
    | some i => exact hF.comp (measurable_id.prodMk (measurable_pi_apply _))
  have hh := Finset.measurable_sup' Finset.univ_nonempty (fun i (_ : i ∈ Finset.univ) => hf i)
  apply hh.aemeasurable.congr
  filter_upwards [he] with u hu
  simp only [Finset.sup'_apply]
  unfold conditionalBlockMaximum
  congr 1
  funext o
  cases o with
  | none => rfl
  | some i => exact hu _

lemma conditionalBlockMaximum_next_join {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2)
    (s : Spins (cutOutNumber c)) (t : Spins M)
    (u : Configuration (cutOutNumber c)) (v : Configuration M) (Z lam : ℝ) :
    conditionalBlockMaximum (K := cutOutNumber c) Z lam (nextCoreObservation p hp ψ c)
      (joinLists s t) (joinLists u v) =
      conditionalOutMaximum Z lam (orderedCutForm p hp (coreSlice ψ t v) c) s u := by
  simp only [conditionalBlockMaximum,conditionalOutMaximum,nextCoreObservation_slice,leftList_join]

lemma radial_nextBlockMaximum_bound {N M : ℕ} (ψ : FormVector (N+M))
    (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hy : t+2*b ≤ ‖y‖)
    {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) (c : Fin N → Fin 2)
    (s : Spins (cutOutNumber c+M)) (u : Configuration (cutOutNumber c+M)) :
    conditionalBlockMaximum (K := cutOutNumber c) Z lam
      (nextCoreObservation (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c) s u ≤ Z/b := by
  conv_lhs => rw [←join_list_parts s,←join_list_parts u]
  rw [conditionalBlockMaximum_next_join]
  exact radial_conditionalOutMaximum_bound _ y ht hb hy hZ hlam c _ _

lemma radial_nextBlockMaximum_square_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (hy : t+2*b ≤ ‖y‖) {Z lam : ℝ} (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    (c : Fin N → Fin 2) (s : Spins (cutOutNumber c+M)) :
    let χ := nextCoreObservation (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c
    Integrable (fun u => conditionalBlockMaximum (K := cutOutNumber c) Z lam χ s u^2*
      formMass (coreSlice χ s u)) := by
  dsimp only
  have hχ := nextCoreObservation_sobolev hψ (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) c
  exact (hχ.coreSlice_mass_integrable s).bdd_mul
    ((conditionalBlockMaximum_aemeasurable hχ s Z lam).pow_const 2).aestronglyMeasurable
    (ae_of_all _ (fun u => norm_sq_le_of_nonneg (conditionalBlockMaximum_nonneg _ _ _ _ _)
      (radial_nextBlockMaximum_bound ψ y ht hb hy hZ hlam c s u)))

lemma nextBlockMaximum_square_fubini {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) (Z lam : ℝ)
    (hi : ∀ s, Integrable (fun u => conditionalBlockMaximum (K := cutOutNumber c) Z lam
      (nextCoreObservation p hp ψ c) s u^2*formMass (coreSlice (nextCoreObservation p hp ψ c) s u))) :
    (∑ s : Spins (cutOutNumber c+M), ∫ u,
      conditionalBlockMaximum (K := cutOutNumber c) Z lam (nextCoreObservation p hp ψ c) s u^2*
        formMass (coreSlice (nextCoreObservation p hp ψ c) s u)) =
      ∑ t : Spins M, ∫ v, ∑ s : Spins (cutOutNumber c), ∫ u,
        conditionalOutMaximum Z lam (orderedCutForm p hp (coreSlice ψ t v) c) s u^2*
          formMass (coreSlice (orderedCutForm p hp (coreSlice ψ t v) c) s u) := by
  rw [←sum_spin_join]
  apply Finset.sum_congr rfl
  intro t _
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro s _
    rw [←integral_join (hi (joinLists s t))]
    simp only [conditionalBlockMaximum_next_join,nextCoreObservation_slice]
  · intro s _
    have hh := (integrable_join (hi (joinLists s t))).integral_prod_right
    simpa only [conditionalBlockMaximum_next_join,nextCoreObservation_slice] using hh

lemma nextBlockMaximum_square_statistic_integrable {N M : ℕ} (ψ : FormVector (N+M))
    (p : Fin 2 → SmoothMultiplier spaceDirections)
    (hp : ∀ x, ∑ a, (p a).value x^2 = 1) (c : Fin N → Fin 2) (Z lam : ℝ)
    (hi : ∀ s, Integrable (fun u => conditionalBlockMaximum (K := cutOutNumber c) Z lam
      (nextCoreObservation p hp ψ c) s u^2*formMass (coreSlice (nextCoreObservation p hp ψ c) s u)))
    (t : Spins M) : Integrable (fun v => ∑ s : Spins (cutOutNumber c), ∫ u,
        conditionalOutMaximum Z lam (orderedCutForm p hp (coreSlice ψ t v) c) s u^2*
          formMass (coreSlice (orderedCutForm p hp (coreSlice ψ t v) c) s u)) := by
  apply integrable_finsetSum
  intro s _
  have hh := (integrable_join (hi (joinLists s t))).integral_prod_right
  simpa only [conditionalBlockMaximum_next_join,nextCoreObservation_slice] using hh

open MeasureTheory Filter Set Metric
open scoped BigOperators

open CoulombAnalysis

lemma ball_one_integrable (y : Space) (A : ℝ) :
    Integrable ((closedBall y A).indicator (fun _ => (1:ℝ))) := by
  apply bounded_compact_integrable (measurable_const.indicator isClosed_closedBall.measurableSet)
    (isCompact_closedBall y A) (B := 1)
  · exact support_indicator_subset
  · intro z
    by_cases hz : z ∈ closedBall y A <;> simp [hz]

lemma ball_indicator_nuclear_separation (y : Space) {A d : ℝ}
    (hsep : A+d ≤ ‖y‖) (z : Space)
    (hz : (closedBall y A).indicator (fun _ => (1:ℝ)) z ≠ 0) : d ≤ ‖z‖ := by
  have hm : z ∈ closedBall y A := by
    by_contra hm
    exact hz (by simp [hm])
  have hzd : ‖z-y‖ ≤ A := by simpa only [mem_closedBall,dist_eq_norm] using hm
  have hh := norm_le_norm_sub_add y z
  rw [norm_sub_rev y z] at hh
  linarith

lemma fieldSquare_ball_weight_eq {N : ℕ} (ψ : FormVector N) (Z lam : ℝ)
    (y : Space) (A : ℝ) :
    (∫ z, coreFieldSquare Z lam z ψ*(closedBall y A).indicator (fun _ => (1:ℝ)) z) =
      ∫ z in closedBall y A, coreFieldSquare Z lam z ψ := by
  rw [←integral_indicator isClosed_closedBall.measurableSet]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  by_cases hz : z ∈ closedBall y A <;> simp [hz]

lemma coreFieldSquare_ball_statistic_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (t : Spins M) (y : Space) {A d Z lam : ℝ}
    (hd : 0 < d) (hsep : A+d ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    Integrable (fun u => ∫ z in closedBall y A, coreFieldSquare Z lam z (coreSlice ψ t u)) := by
  have hi := (coreFieldSquare_weighted_prod_integrable hψ t hZ hlam hd
    (ball_one_integrable y A)
    (fun z => indicator_nonneg (fun _ _ => zero_le_one) z)
    (ball_indicator_nuclear_separation y hsep)).integral_prod_left
  simpa only [fieldSquare_ball_weight_eq] using hi

lemma coreFieldSquare_ball_fubini {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) {A d Z lam : ℝ}
    (hd : 0 < d) (hsep : A+d ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    coreLawAverage ψ (fun φ => ∫ z in closedBall y A, coreFieldSquare Z lam z φ) =
      ∫ z in closedBall y A, coreLawAverage ψ (coreFieldSquare Z lam z) := by
  have hh := coreFieldSquare_weighted_fubini hψ Z lam hZ hlam hd (ball_one_integrable y A)
    (fun z => indicator_nonneg (fun _ _ => zero_le_one) z)
    (ball_indicator_nuclear_separation y hsep)
  simp only [fieldSquare_ball_weight_eq] at hh
  rw [hh,←integral_indicator isClosed_closedBall.measurableSet]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  by_cases hz : z ∈ closedBall y A <;> simp [hz]

lemma coreLawAverage_fieldSquare_ball_integrable {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) {A d Z lam : ℝ}
    (hd : 0 < d) (hsep : A+d ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) :
    IntegrableOn (fun z => coreLawAverage ψ (coreFieldSquare Z lam z)) (closedBall y A) := by
  have hi : Integrable (fun z => coreLawAverage ψ (coreFieldSquare Z lam z)*
      (closedBall y A).indicator (fun _ => (1:ℝ)) z) := by
    unfold coreLawAverage
    simp only [Finset.sum_mul]
    apply integrable_finsetSum
    intro t _
    have hj := (coreFieldSquare_weighted_prod_integrable hψ t hZ hlam hd
      (ball_one_integrable y A) (fun z => indicator_nonneg (fun _ _ => zero_le_one) z)
      (ball_indicator_nuclear_separation y hsep)).integral_prod_right
    simpa only [integral_mul_const] using hj
  rw [←integrable_indicator_iff isClosed_closedBall.measurableSet]
  apply hi.congr
  exact ae_of_all _ (fun z => by by_cases hz : z ∈ closedBall y A <;> simp [hz])

lemma radial_out_position_distance {L : ℕ} (ψ : FormVector L) (y : Space)
    {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (c : Fin L → Fin 2)
    (s : Spins (cutOutNumber c)) (u : Configuration (cutOutNumber c))
    (hm : formMass (coreSlice (orderedCutForm (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u) ≠ 0) (i : Fin (cutOutNumber c)) :
    ‖u i-y‖ < t+b := by
  by_contra! h
  exact hm (orderedCutForm_slice_mass_zero _ _ ψ c s u i (coreFirstRadialCut_out_zero y ht hb _ h))

theorem radial_nextBlockMaximum_sq_spatial {N M : ℕ} (ψ : FormVector (N+M))
    (y : Space) {t b R B Z lam : ℝ} (ht : 0 ≤ t) (hb : 0 < b) (hR : 0 < R)
    (hsep : t+b+2*R ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    (c : Fin N → Fin 2) (s : Spins (cutOutNumber c+M)) (u : Configuration (cutOutNumber c+M))
    (hcore : SobolevVector (coreSlice (nextCoreObservation (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u)) {η : Space → ℝ}
    (hm : Measurable η) (hn : ∀ z, 0 ≤ η z) (hs : ∀ z, η z ≠ 0 → ‖z‖ ≤ R)
    (hbound : ∀ z, |η z| ≤ B) (hr : IsRadial η) (h1 : ∫ z, η z = 1) :
    let χ := nextCoreObservation (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c
    conditionalBlockMaximum (K := cutOutNumber c) Z lam χ s u^2*formMass (coreSlice χ s u) ≤
      B*∫ z in closedBall y (t+b+R), coreFieldSquare Z lam z (coreSlice χ s u) := by
  dsimp only
  have hc0 : coreSlice (nextCoreObservation (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u =
      coreSlice (orderedCutForm (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb)
        (coreSlice ψ (rightList s) (rightList u)) c) (leftList s) (leftList u) := by
    conv_lhs => rw [←join_list_parts s,←join_list_parts u]
    exact nextCoreObservation_slice _ _ _ _ _ _ _ _
  have hb0 : 0 ≤ B := (abs_nonneg (η 0)).trans (hbound 0)
  by_cases hmass : formMass (coreSlice (nextCoreObservation (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u) = 0
  · simp only [hmass,mul_zero,coreFieldSquare,integral_zero,le_refl]
  have hpos := radial_out_position_distance (coreSlice ψ (rightList s) (rightList u)) y ht hb c
    (leftList s) (leftList u) (by rwa [←hc0])
  have hh := conditional_out_maximum_sq_le_ball_average
    (orderedCutForm (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb)
      (coreSlice ψ (rightList s) (rightList u)) c) (leftList s) (leftList u)
      (by rwa [←hc0]) y (by positivity : 0 ≤ t+b) hR hsep
      (fun i => (hpos i).le) hZ hlam hm hn hs hbound hr h1
  have hend := mul_le_mul_of_nonneg_right hh
    (formMass_nonneg (coreSlice (nextCoreObservation (coreFirstRadialCut y ht hb)
      (coreFirstRadialCut_partition y ht hb) ψ c) s u))
  rw [←hc0] at hend
  have hemax : conditionalBlockMaximum (K := cutOutNumber c) Z lam
      (nextCoreObservation (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c) s u =
      conditionalOutMaximum Z lam (orderedCutForm (coreFirstRadialCut y ht hb)
        (coreFirstRadialCut_partition y ht hb) (coreSlice ψ (rightList s) (rightList u)) c)
        (leftList s) (leftList u) := by
    conv_lhs => rw [←join_list_parts s,←join_list_parts u]
    exact conditionalBlockMaximum_next_join _ _ _ _ _ _ _ _ _ _
  rw [hemax]
  simpa only [coreFieldSquare,integral_mul_const,mul_assoc] using hend

theorem radial_nextBlockMaximum_moment_spatial {N M : ℕ} {ψ : FormVector (N+M)}
    (hψ : SobolevVector ψ) (y : Space) {t b R B Z lam : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hR : 0 < R) (hsep : t+b+2*R ≤ ‖y‖)
    (hnear : t+2*b ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam)
    (c : Fin N → Fin 2) {η : Space → ℝ}
    (hm : Measurable η) (hn : ∀ z, 0 ≤ η z) (hs : ∀ z, η z ≠ 0 → ‖z‖ ≤ R)
    (hbound : ∀ z, |η z| ≤ B) (hr : IsRadial η) (h1 : ∫ z, η z = 1) :
    let χ := nextCoreObservation (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c
    (∑ s : Spins (cutOutNumber c+M), ∫ u,
      conditionalBlockMaximum (K := cutOutNumber c) Z lam χ s u^2*formMass (coreSlice χ s u)) ≤
      B*∫ z in closedBall y (t+b+R), coreLawAverage χ (coreFieldSquare Z lam z) := by
  let χ := nextCoreObservation (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) ψ c
  have hχ := nextCoreObservation_sobolev hψ (coreFirstRadialCut y ht hb)
    (coreFirstRadialCut_partition y ht hb) c
  change _ ≤ B*∫ z in closedBall y (t+b+R), coreLawAverage χ (coreFieldSquare Z lam z)
  rw [←coreFieldSquare_ball_fubini hχ y hR (by linarith : t+b+R+R ≤ ‖y‖) hZ hlam]
  unfold coreLawAverage
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  rw [←integral_const_mul]
  apply integral_mono_ae
    (radial_nextBlockMaximum_square_integrable hψ y ht hb hnear hZ hlam c s)
    ((coreFieldSquare_ball_statistic_integrable hχ s y hR (by linarith) hZ hlam).const_mul B)
  filter_upwards [hχ.ae_coreSlice s] with u hu
  exact radial_nextBlockMaximum_sq_spatial ψ y ht hb hR hsep hZ hlam c s u hu hm hn hs hbound hr h1

namespace CoreObservationGraph

def outMoment (G : CoreObservationGraph) (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (Z lam : ℝ) : ℝ :=
  ∑ c : Fin G.coreSize → Fin 2, ∑ s : Spins (cutOutNumber c+G.outSize), ∫ u,
    conditionalBlockMaximum (K := cutOutNumber c) Z lam
      (G.observe (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) c).vector s u^2*
      formMass (coreSlice
        (G.observe (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) c).vector s u)

lemma outMoment_nonneg (G : CoreObservationGraph) (y : Space) {t b : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (Z lam : ℝ) : 0 ≤ G.outMoment y ht hb Z lam :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ =>
    mul_nonneg (sq_nonneg _) (formMass_nonneg _))))

lemma outMoment_spatial (G : CoreObservationGraph) (y : Space) {t b R B Z lam : ℝ}
    (ht : 0 ≤ t) (hb : 0 < b) (hR : 0 < R) (hsep : t+b+2*R ≤ ‖y‖)
    (hnear : t+2*b ≤ ‖y‖) (hZ : 0 ≤ Z) (hlam : 0 ≤ lam) {η : Space → ℝ}
    (hm : Measurable η) (hn : ∀ z, 0 ≤ η z) (hs : ∀ z, η z ≠ 0 → ‖z‖ ≤ R)
    (hbound : ∀ z, |η z| ≤ B) (hr : IsRadial η) (h1 : ∫ z, η z = 1) :
    G.outMoment y ht hb Z lam ≤ B*∫ z in closedBall y (t+b+R),
      ∑ c : Fin G.coreSize → Fin 2,
        (G.observe (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) c).fieldMoment Z lam z := by
  unfold outMoment
  rw [integral_finsetSum,Finset.mul_sum]
  · apply Finset.sum_le_sum
    intro c _
    exact radial_nextBlockMaximum_moment_spatial G.sobolev y ht hb hR hsep hnear hZ hlam c
      hm hn hs hbound hr h1
  · intro c _
    exact coreLawAverage_fieldSquare_ball_integrable
      (G.observe (coreFirstRadialCut y ht hb) (coreFirstRadialCut_partition y ht hb) c).sobolev y
      hR (by linarith) hZ hlam

end CoreObservationGraph

end CoulombAtom

end

end OAI
