import Mathlib
import OAI.Analysis.CoulombRadii.Packets.PatchKernelDuality
import OAI.Analysis.CoulombRadii.RandomFields.RecordedStatistic

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace Coulomb

lemma localCount_ball_matching {n : ℕ} (x z : Configuration n) (y : Space)
    {r d : ℝ} (hmatch : ∀ i, ‖position z i-position x i‖≤d) :
    localCount (Metric.closedBall y r) x≤localCount (Metric.closedBall y (r+d)) z := by
  unfold localCount
  apply Finset.sum_le_sum
  intro i hi
  by_cases hx : position x i∈Metric.closedBall y r
  · have hz : position z i∈Metric.closedBall y (r+d) := by
      rw [Metric.mem_closedBall,dist_eq_norm] at hx ⊢
      have ht := norm_sub_le_norm_sub_add_norm_sub (position z i) (position x i) y
      linarith [hmatch i]
    simp only [indicator_of_mem hx,indicator_of_mem hz,le_refl]
  · rw [indicator_of_notMem hx]
    exact indicator_nonneg (fun _ _ => zero_le_one) _

lemma arrayStatistic_matching_observed_count {n : ℕ} (χ : Space → ℝ) (x z : Configuration n)
    (y : Space) {r d L : ℝ} (hd : 0≤d) (hL : 0≤L)
    (hs : ∀ v, χ v≠0 → ‖v-y‖≤r) (hLip : ∀ v w, |χ v-χ w|≤L*‖v-w‖)
    (hmatch : ∀ i, ‖position z i-position x i‖≤d) :
    |arrayStatistic χ z-arrayStatistic χ x|≤
      (L*d)*localCount (Metric.closedBall y (r+2*d)) z := by
  have H := arrayStatistic_local_matching χ x z y hd hL hs hLip hmatch
  apply H.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hL hd)
  convert localCount_ball_matching x z y (r:=r+d) hmatch using 1
  congr 2
  ring
end Coulomb
namespace NeutralAtom

theorem arrayEvent_fresh_statistic_lower {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : H)
    {E : Set ((H × (Fin n × Fin 3)) → ℝ)} (hE : MeasurableSet E)
    (ψ : Wavefunction n) (u : Coulomb.H1Vector n)
    (hbayes : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ E))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*F (flattenConfiguration n x)))
    (T : Coulomb.RecordedEnsemble n) (hT : T.Conserves u)
    (χ : Position → ℝ) (hχm : Measurable χ) {A : Set Position}
    (hχ : ∀ z∈A, χ z=0) (hcs : T.CoreSupported A)
    (y : Position) {r L M Q : ℝ} (hL : 0≤L)
    (hs : ∀ v, χ v≠0 → ‖v-y‖≤r) (hLip : ∀ v w, |χ v-χ w|≤L*‖v-w‖)
    (hhigh : ∀ z∈E, Q≤∑ i, χ (observationArrayPositions h z i))
    (hcount : ∀ z∈E, rawCount (Metric.closedBall y (r+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) :
    ∀ p s, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice s x)≠0 →
      Q-L*(Real.sqrt 3*ℓ h)*M≤Coulomb.arrayStatistic χ x := by
  apply arrayEvent_fresh_statistic_ae ℓ (fun h => (hℓ h).ne') hE ψ u hbayes T hT hχm hχ hcs
    measurableSet_Ici
  intro x z hz he
  let w := fun ia : H × (Fin n × Fin 3) => x ia.2.1 ia.2.2+ℓ ia.1*z ia
  let X := flattenConfiguration n x
  let Y := flattenConfiguration n (observationArrayPositions h w)
  have hd : 0≤Real.sqrt 3*ℓ h := mul_nonneg (Real.sqrt_nonneg _) (hℓ h).le
  have hd' (i : Fin n) : ‖Coulomb.position Y i-Coulomb.position X i‖≤Real.sqrt 3*ℓ h := by
    simpa only [X,Y,position_flattenConfiguration] using observationArrayPositions_displacement ℓ hℓ x hz h i
  have Hmatch := Coulomb.arrayStatistic_matching_observed_count χ X Y y hd hL hs hLip hd'
  have Hcount : Coulomb.localCount (Metric.closedBall y (r+2*(Real.sqrt 3*ℓ h))) Y≤M := by
    simpa only [Y,Coulomb.localCount,position_flattenConfiguration,rawCount] using hcount w he
  have Hhigh : Q≤Coulomb.arrayStatistic χ Y := by
    simpa only [Y,Coulomb.arrayStatistic,position_flattenConfiguration] using hhigh w he
  have Herror := Hmatch.trans (mul_le_mul_of_nonneg_left Hcount (mul_nonneg hL hd))
  change Q-L*(Real.sqrt 3*ℓ h)*M≤Coulomb.arrayStatistic χ X
  linarith [(abs_le.mp Herror).2]

end NeutralAtom

end
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

theorem arrayEvent_fresh_count_upper {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : H)
    {E : Set ((H × (Fin n × Fin 3)) → ℝ)} (hE : MeasurableSet E)
    (ψ : Wavefunction n) (u : Coulomb.H1Vector n)
    (hbayes : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ E))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*F (flattenConfiguration n x)))
    (T : Coulomb.RecordedEnsemble n) (hT : T.Conserves u)
    {A : Set Position} (hcs : T.CoreSupported A) (y : Position) {R M : ℝ}
    (hfar : ∀ z∈A, R<‖z-y‖)
    (hcount : ∀ z∈E, rawCount (Metric.closedBall y (R+Real.sqrt 3*ℓ h))
      (observationArrayPositions h z)≤M) :
    ∀ p s, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice s x)≠0 →
      Coulomb.localCount (Metric.closedBall y R) x≤M := by
  let χ : Position → ℝ := (Metric.closedBall y R).indicator (fun _ => 1)
  have hχm : Measurable χ := measurable_const.indicator measurableSet_closedBall
  have hχ (z) (hz : z∈A) : χ z=0 := by
    apply indicator_of_notMem
    simpa only [Metric.mem_closedBall,dist_eq_norm,not_le] using hfar z hz
  apply arrayEvent_fresh_statistic_ae ℓ (fun h => (hℓ h).ne') hE ψ u hbayes T hT hχm hχ hcs
    (B := Set.Iic M) measurableSet_Iic
  intro x z hz he
  let w := fun ia : H × (Fin n × Fin 3) => x ia.2.1 ia.2.2+ℓ ia.1*z ia
  let X := flattenConfiguration n x
  let Y := flattenConfiguration n (observationArrayPositions h w)
  have hd (i : Fin n) : ‖Coulomb.position Y i-Coulomb.position X i‖≤Real.sqrt 3*ℓ h := by
    simpa only [X,Y,position_flattenConfiguration] using observationArrayPositions_displacement ℓ hℓ x hz h i
  have HH := Coulomb.localCount_ball_matching X Y y (r:=R) hd
  have HC : Coulomb.localCount (Metric.closedBall y (R+Real.sqrt 3*ℓ h)) Y≤M := by
    simpa only [Y,Coulomb.localCount,position_flattenConfiguration,rawCount] using hcount w he
  exact HH.trans HC

theorem arrayEvent_fresh_fine_lower {H : Type*} [Fintype H] {n : ℕ}
    (ℓ : H → ℝ) (hℓ : ∀ h, 0<ℓ h) (h : H)
    {E : Set ((H × (Fin n × Fin 3)) → ℝ)} (hE : MeasurableSet E)
    (ψ : Wavefunction n) (u : Coulomb.H1Vector n)
    (hbayes : ∀ F : Coulomb.Configuration n → ℝ, Coulomb.potentialForm F u=
      (stateWeightedIntegral ψ (arrayEventLikelihood ℓ E))⁻¹*
        stateWeightedIntegral ψ (fun x => arrayEventLikelihood ℓ E x*F (flattenConfiguration n x)))
    (T : Coulomb.RecordedEnsemble n) (hT : T.Conserves u)
    (χ : Position → ℝ) (hχm : Measurable χ) (y : Position) {r b t L M Q K : ℝ}
    (hb : 0<b) (hL : 0≤L) (hretain : r+2*b<t-7*b)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) (hK : ∀ z, |χ z|≤K)
    (hs : ∀ v, χ v≠0 → ‖v-y‖≤r) (hLip : ∀ v w, |χ v-χ w|≤L*‖v-w‖)
    (hhigh : ∀ z∈E, Q≤∑ i, χ (observationArrayPositions h z i))
    (hcount : ∀ z∈E, rawCount (Metric.closedBall y (r+2*b+2*(Real.sqrt 3*ℓ h)))
      (observationArrayPositions h z)≤M) :
    ∀ p s, ∀ᵐ x, Coulomb.mass ((T.vector p).coreSlice s x)≠0 →
      Q-L*(Real.sqrt 3*ℓ h+2*b)*M≤
        ∫ z, Coulomb.retainedFineDensity b (Coulomb.patchRetained y t b x) (Coulomb.position x) z*χ z := by
  have hd : 0≤Real.sqrt 3*ℓ h := mul_nonneg (Real.sqrt_nonneg _) (hℓ h).le
  have hχ (z) (hz : t≤‖z-y‖) : χ z=0 := by
    by_contra hn
    have hh := hs z hn
    linarith
  have hrawcount (z) (hz : z∈E) {R : ℝ} (hR : R≤r+2*b+2*(Real.sqrt 3*ℓ h)) :
      rawCount (Metric.closedBall y R) (observationArrayPositions h z)≤M := by
    have HH := Coulomb.localCount_mono (Metric.closedBall_subset_closedBall (x:=y) hR)
      (flattenConfiguration n (observationArrayPositions h z))
    simp only [Coulomb.localCount,position_flattenConfiguration] at HH
    exact HH.trans (hcount z hz)
  have Hhigh := arrayEvent_fresh_statistic_lower ℓ hℓ h hE ψ u hbayes T hT χ hχm
    hχ hcs y hL hs hLip hhigh (fun z hz => hrawcount z hz (by linarith))
  have Hcount := arrayEvent_fresh_count_upper ℓ hℓ h hE ψ u hbayes T hT hcs y
    (R:=r+2*b) (fun z hz => by change t≤‖z-y‖ at hz; linarith)
    (fun z hz => hrawcount z hz (by linarith))
  intro p s
  filter_upwards [Hhigh p s,Hcount p s] with x hx hc
  intro hm
  have hh := hx hm
  have hcx := hc hm
  have Hfine := Coulomb.patchFine_kernel_matching hb hL hretain χ hχm hK y
    (fun z hz => by by_contra hn; linarith [hs z hn]) hLip x
  have HE := Hfine.trans (mul_le_mul_of_nonneg_left hcx (by positivity : 0≤L*(2*b)))
  change Q-L*(Real.sqrt 3*ℓ h)*M≤∑ i,χ (Coulomb.position x i) at hh
  linarith [(abs_le.mp HE).1]

end NeutralAtom

end

end OAI
