import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.AtomicThinScreening
import OAI.Analysis.CoulombRadii.ThomasFermi.PhysicalCount
import OAI.Analysis.CoulombRadii.FormDomain.PatchErrors
import OAI.Analysis.CoulombRadii.RandomFields.ExactRecordedCount

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma PartlyAntisymmetric.outer_symmetry {m k : ℕ} {u : H1Vector (m+k)}
    (hu : PartlyAntisymmetric u (outIndexSet m k))
    (s : Spins k) (p : Equiv.Perm (Fin m)) (t : Spins m) :
    ∀ᵐ z, u.value (outerAppend s t ∘ outerPerm k p) (permute (outerPerm k p) z) =
      (((outerPerm k p).sign:ℤ):ℂ)*u.value (outerAppend s t) z := by
  apply hu
  intro i
  refine Fin.addCases (fun j hi => ?_) (fun j _ => ?_) i
  · exact False.elim (hi ⟨j,rfl⟩)
  · exact outerPerm_right k p j

lemma patch_packet_expected_bound {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (ht : t≤6*a) (y : Space)
    (hn : ∀ j, 20*a≤‖S.position j-y‖) (F : Spins m → Configuration m → ℝ)
    (hFm : ∀ s, AEStronglyMeasurable (F s) volume)
    (hF0 : ∀ s, ∀ᵐ x, 0≤F s x)
    (hFi : ∀ s, Integrable (fun x => mass (u.coreSlice s x)*(F s x)^2))
    (hcap : ∀ s, ∀ᵐ x, ∀ w∈Metric.ball y (t-4*b), coreScreenedField S (u.coreSlice s x).normalized w≤F s x) :
    sliceExpectation u (fun s x => packetKineticError (scaledWindow unitWindow b hb.ne')
      (localTFDensity measurableSet_ball (coreTFField S (u.coreSlice s x).normalized measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht y hn))))≤
      (12*a*unitWindowKinetic/b^2)*sliceExpectation u F := by
  unfold sliceExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  have hTF := coreTF_conditional_integrable measurableSet_ball S u s ha
    (patch_nucleus_separation S ha hb ht y hn) (show 0<12*a by positivity)
    (patch_diameter ha hb ht y) (F s) (hF0 s) (hFi s) (hcap s)
  have hi : Integrable (fun x => mass (u.coreSlice s x)*packetKineticError (scaledWindow unitWindow b hb.ne')
      (localTFDensity measurableSet_ball (coreTFField S (u.coreSlice s x).normalized measurableSet_ball ha
        (patch_nucleus_separation S ha hb ht y hn)))) := by
    unfold packetKineticError
    convert hTF.1.mul_const ((1/2:ℝ)*(∑ j : Fin 3, ∫ z : Space,
      (fderiv ℝ (scaledWindow unitWindow b hb.ne') z (EuclideanSpace.single j 1))^2)) using 1
    funext x
    ring
  rw [←integral_const_mul]
  apply integral_mono_ae hi ((weighted_cap_integrable (mass_coreSlice_integrable u s)
    (Eventually.of_forall (fun _ => mass_nonneg _)) (hFm s) (hF0 s) (hFi s)).const_mul _)
  filter_upwards [hF0 s,hcap s] with x hf hc
  simpa only [mul_left_comm (mass _) (12*a*unitWindowKinetic/b^2)] using
    mul_le_mul_of_nonneg_left (patch_packet_bound S _ ha hb ht y hn hf hc) (mass_nonneg _)

lemma ensemble_fineLocalizationError {P : Type*} [Fintype P] (n : P → ℕ) (w : P → ℝ)
    (hw : ∀ p, 0≤w p) (hm : ∑ p, w p=1) {b : ℝ} (hb : 0<b) :
    (∑ p, fineLocalizationError (n p) b*w p)≤
      (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(∑ p, (n p:ℝ)^2*w p)^(2/3:ℝ)+
      ((2*Real.pi+1)/(2*b))*Real.sqrt (∑ p, (n p:ℝ)^2*w p) := by
  simp only [fineLocalizationError,add_mul,Finset.sum_add_distrib]
  simp_rw [show ∀ p, (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(n p:ℝ)^(4/3:ℝ)*w p =
    ((b⁻¹)^2*((Real.pi^2/2)*neumannBoundary))*((n p:ℝ)^(4/3:ℝ)*w p) by intro p; ring,
    show ∀ p, ((2*Real.pi+1)/(2*b))*(n p:ℝ)*w p=((2*Real.pi+1)/(2*b))*((n p:ℝ)*w p) by intro p; ring]
  rw [←Finset.mul_sum,←Finset.mul_sum]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (ensemble_number_rpow n w hw hm) (by positivity [neumannBoundary_nonneg]))
    (mul_le_mul_of_nonneg_left (ensemble_number_mean n w hw hm) (by positivity [Real.pi_pos]))

theorem physical_ensemble_count {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n)
    (T : RecordedEnsemble n) (hC : T.Conserves ψ) (hc : T.CoreFermionic) (ho : T.OutFermionic)
    (hm : T.totalMass=1) {E B : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S)
    (henergy : T.totalForm S≤E+B)
    {a b t : ℝ} (ha : 0<a) (hb : 0<b) (hsmall : 18*b≤a) (ht : t∈Set.Icc (5*a) (6*a))
    (y : Space) (hn : ∀ j, 20*a≤‖S.position j-y‖)
    (hcs : T.CoreSupported {z | t≤‖z-y‖}) (hos : T.OutSupported (Metric.closedBall y (t+b)))
    (F : (p : T.index) → Spins (T.out p) → Configuration (T.out p) → ℝ)
    (hFm : ∀ p s, AEStronglyMeasurable (F p s) volume)
    (hF0 : ∀ p s, ∀ᵐ x, 0≤F p s x)
    (hFi : ∀ p s, Integrable (fun x => mass ((T.vector p).coreSlice s x)*(F p s x)^2))
    (hcap : ∀ p s, ∀ᵐ x, ∀ w∈Metric.closedBall y (t+b), coreScreenedField S ((T.vector p).coreSlice s x).normalized w≤F p s x) :
    let Q := ∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2)
    let N := ∑ p, (T.out p:ℝ)^2*mass (T.vector p)
    localCountSecondMoment ψ (Metric.closedBall y a)≤2*(tfInteriorCountConstant/a^3)^2+
      6*a*(max countTestEnergy 0)*(B+12*a*unitWindowKinetic/b^2*Real.sqrt Q+
        Real.sqrt (Q*T.deletedSquare y t b)+
        (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*N^(2/3:ℝ)+
        ((2*Real.pi+1)/(2*b))*Real.sqrt N) := by
  dsimp only
  let ρ := fun p s x => localTFDensity measurableSet_ball
    (coreTFField S ((T.vector p).coreSlice s x).normalized measurableSet_ball ha
      (patch_nucleus_separation S ha hb ht.2 y hn))
  let G := fun p s x => rawThomasFermiEnergy (coreScreenedField S ((T.vector p).coreSlice s x).normalized)
    (retainedFineDensity b (patchRetained y t b x) (position x))-
    rawThomasFermiEnergy (coreScreenedField S ((T.vector p).coreSlice s x).normalized) (ρ p s x)
  have hcs' (p : T.index) (s) : ∀ᵐ x, SpatiallySupported ((T.vector p).coreSlice s x).normalized {z | t≤‖z-y‖} := by
    filter_upwards [(hcs p).coreSlice s] with x hx
    exact hx.normalized
  have hcap' (p : T.index) (s) : ∀ᵐ x, ∀ w∈Metric.ball y (t-4*b), coreScreenedField S ((T.vector p).coreSlice s x).normalized w≤F p s x := by
    filter_upwards [hcap p s] with x hx
    exact fun w hw => hx w (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith)) hw)
  have hgap (p : T.index) := physical_patch_comparison S (T.vector p) (ho p).outer_symmetry
    (fun s => (hc p).coreSlice s) ha hb hsmall ht y hn (hcs' p) (fun s => (hos p).recorded_positions s)
    (F p) (hFm p) (hF0 p) (hFi p) (hcap p) hE
  have hpacket (p : T.index) := patch_packet_expected_bound S (T.vector p) ha hb ht.2 y hn
    (F p) (hFm p) (hF0 p) (hFi p) (hcap' p)
  have hmean := slice_ensemble_mean_le_sqrt T.out T.core T.vector F hFm hF0 hFi hm
  have hdel := slice_ensemble_mul_le_sqrt T.out T.core T.vector F
    (fun _ _ x => localCount {z | t-7*b≤‖z-y‖} x) hFi
    (fun p s => sliceCount_weight_integrable (T.vector p) (isClosed_le continuous_const (by fun_prop)).measurableSet s 2)
    (fun p s => weighted_cap_count_integrable (mass_coreSlice_integrable (T.vector p) s)
      (Eventually.of_forall (fun _ => mass_nonneg _)) (hFm p s) (hF0 p s) (hFi p s)
      (localCount_measurable (isClosed_le continuous_const (by fun_prop)).measurableSet).aestronglyMeasurable
      (Nat.cast_nonneg (T.out p)) (Eventually.of_forall (fun x => ⟨localCount_nonneg _ x,localCount_le _ x⟩)))
  have hfine := ensemble_fineLocalizationError T.out (fun p => mass (T.vector p)) (fun p => mass_nonneg _) hm hb
  have hsumgap := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hgap p)
  have hsumpacket := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => hpacket p)
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum] at hsumgap hsumpacket
  change (∑ p, sliceExpectation (T.vector p) (G p))≤_ at hsumgap
  have hGapBound : (∑ p, sliceExpectation (T.vector p) (G p))≤B+
      12*a*unitWindowKinetic/b^2*Real.sqrt (∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2))+
      Real.sqrt ((∑ p, sliceExpectation (T.vector p) (fun s x => (F p s x)^2))*T.deletedSquare y t b)+
      (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(∑ p, (T.out p:ℝ)^2*mass (T.vector p))^(2/3:ℝ)+
      ((2*Real.pi+1)/(2*b))*Real.sqrt (∑ p, (T.out p:ℝ)^2*mass (T.vector p)) := by
    have hp := mul_le_mul_of_nonneg_left hmean (show 0≤12*a*unitWindowKinetic/b^2 by exact div_nonneg (mul_nonneg (by positivity) unitWindowKinetic_nonneg) (sq_nonneg _))
    change (∑ p, mass (T.vector p))=1 at hm
    rw [hm,mul_one] at hsumgap
    change (∑ p, form S (T.vector p))≤E+B at henergy
    unfold RecordedEnsemble.deletedSquare
    linarith
  have hAB : Disjoint {z : Space | t≤‖z-y‖} (Metric.closedBall y a) := by
    apply Set.disjoint_left.mpr
    intro z hz hz'
    have hh : ‖z-y‖≤a := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz'
    have hz : t≤‖z-y‖ := hz
    linarith [ht.1]
  rw [←hC.recorded_secondMoment_eq measurableSet_closedBall hAB hcs]
  have hcounts := Finset.sum_le_sum (fun p (_ : p∈Finset.univ) => physical_patch_averaged_count S (T.vector p)
    ha hb hsmall ht y hn (hcs' p) (F p) (hF0 p) (hFi p) (hcap p))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at hcounts
  change (∑ p, mass (T.vector p))=1 at hm
  rw [hm,mul_one] at hcounts
  have hcoef : 0≤6*a*max countTestEnergy 0 := mul_nonneg (mul_nonneg (by norm_num) ha.le) (le_max_right _ _)
  exact hcounts.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hGapBound hcoef))

end Coulomb
end

end
end

end OAI
