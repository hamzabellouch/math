import Mathlib
import OAI.Analysis.CoulombRadii.Screening.AtomicPatchCap
import OAI.Analysis.CoulombRadii.FormDomain.PhysicalEnsemble

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

theorem thin_localization_history_sharp {J n : ℕ} (S : Nuclei J) (ψ : H1Vector n) (hψ : Antisymmetric ψ)
    {y : Space} (hy : y≠0) {t b : ℝ} (ht : 0≤t) (hb : 0<b)
    (hwidth : t+b≤80*atomicCellScale y) :
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1,
      (∀ i, T.target i=y) ∧ T.ensemble.OutFermionic ∧
      T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+b)) ∧
      T.ensemble.totalForm S≤form S ψ+thinIMS ψ y t b := by
  obtain ⟨U,hC,hc,ho,hcs,hos,hm,hf⟩ := thin_localization S ψ hψ y ht hb
  let T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1 := {
    ensemble := U
    target := fun _ => y
    nonzero := fun _ => hy
    law := hC
    fermionic := hc
    support := by
      intro p
      apply (hos p).mono_space
      intro z hz
      apply Set.mem_iUnion.mpr
      refine ⟨0,?_⟩
      exact Metric.closedBall_subset_closedBall hwidth hz
    mass_eq := hm
    energy := by
      apply hf.trans
      apply le_add_of_nonneg_right
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (expectedPopulation_nonneg _ _)) }
  exact ⟨T,fun _ => rfl,ho,hcs,hos,hf⟩

theorem exists_atomic_thin_screened_sharp {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) (hstate : form S ψ≤E+δ)
    (hδ : 0≤δ) {y : Space} (hy : y≠0) {b : ℝ} (hb : 0<b)
    (hsmall : 18*b≤atomicCellScale y)
    (hcond : atomicCellScale y≤b^2*Real.sqrt (screenCountParameter ψ δ)*screenMass δ (atomicCellScale y)) :
    ∃ t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1,
      T.ensemble.totalForm S≤form S ψ+thinIMS ψ y t b ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+b)) ∧
      T.ensemble.deletedSquare y t b≤
        18*atomicPatchCountFactor*(b/atomicCellScale y)*screenCountParameter ψ δ*(screenMass δ (atomicCellScale y))^2 ∧
      (∑ p, (T.ensemble.out p:ℝ)^2*mass (T.ensemble.vector p))≤
        atomicPatchCountFactor*screenCountParameter ψ δ*(screenMass δ (atomicCellScale y))^2 ∧
      (∀ v, AtomicScaleWindow (atomicCellScale y) 4 v →
        Real.sqrt (T.ensemble.rawSquare S v (atomicCellScale v))≤
          2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*
            screenFieldUnit δ (screenCountParameter ψ δ) (atomicCellScale y)) := by
  let P := screenCountParameter ψ δ
  have hP : 1≤P := screenCountParameter_ge_one ψ δ
  have hP0 : 0≤P := le_trans zero_le_one hP
  have hc := fun z hz => screenCountParameter_controls ψ hm δ (y:=z) hz
  obtain ⟨t,ht,hdel⟩ := exists_atomic_deletedShell ψ hm hδ hy hb hsmall
  have ht0 : 0≤t := by nlinarith [ht.1,atomicCellScale_nonneg y]
  have hwidth : t+b≤80*atomicCellScale y := by linarith [ht.2,atomicCellScale_nonneg y]
  obtain ⟨T,hTr,ho,hcs,hos,hEt⟩ := thin_localization_history_sharp S ψ hψ hy ht0 hb hwidth
  have hbudget := thinIMS_budget ψ hm hδ hP hc hy hb hwidth hcond
  have hP' : 1≤thinReserveFactor*P := by nlinarith [thinReserveFactor_ge_one]
  have hc' (z : Space) (hz : z≠0) : localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z))≤
      (thinReserveFactor*P)*(screenMass δ (atomicCellScale z))^2 :=
    (hc z hz).trans (mul_le_mul_of_nonneg_right
      (le_mul_of_one_le_left hP0 thinReserveFactor_ge_one) (sq_nonneg _))
  refine ⟨t,ht,T,hEt,ho,hcs,hos,(RecordedEnsemble.deletedSquare_le T.law hos).trans hdel,?_,?_⟩
  · exact (RecordedEnsemble.out_square_le T.law measurableSet_closedBall hos).trans
      ((localCountSecondMoment_mono ψ measurableSet_closedBall (Metric.closedBall_subset_closedBall hwidth)).trans
        (atomicPatch_secondMoment ψ hδ hP0 hc hy))
  · intro v hv
    have H := T.positive_field S hatom ψ hm hE hstate hbudget hδ hP' (atomicCellScale_pos hy) hc'
      (fun i => by rw [hTr i]; constructor <;> norm_num <;> linarith [atomicCellScale_nonneg y])
      v (by simpa only [pow_one] using hv)
    convert H using 1
    simp only [screenFieldUnit,Real.sqrt_mul thinReserveFactor_nonneg]
    ring

lemma thinIMS_sharp_budget {n : ℕ} (ψ : H1Vector n) (hm : mass ψ=1)
    {δ P : ℝ} (hδ : 0≤δ) (hP : 0≤P)
    (hc : ∀ z : Space, z≠0 → localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z))≤
      P*(screenMass δ (atomicCellScale z))^2)
    {y : Space} (hy : y≠0) {t b : ℝ} (hb : 0<b) (hwidth : t+b≤80*atomicCellScale y) :
    thinIMS ψ y t b≤thinReserveFactor*(Real.sqrt P*screenMass δ (atomicCellScale y)/b^2) := by
  have H := (expectedPopulation_mono ψ measurableSet_closedBall measurableSet_closedBall
    (Metric.closedBall_subset_closedBall hwidth)).trans (atomicPatch_population ψ hm hδ hP hc hy)
  have Hims := mul_le_mul_of_nonneg_left H (show 0≤3*(thinCutCoefficient/b)^2 by positivity)
  apply Hims.trans
  calc
    _=(3*thinCutCoefficient^2*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*8)*
        (Real.sqrt P*screenMass δ (atomicCellScale y)/b^2) := by rw [div_pow]; ring
    _≤_ := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (screenMass_pos _ _).le) (sq_pos_of_pos hb).le)

end Coulomb

end
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
namespace Coulomb

def atomicPhysicalCapConstant : ℝ :=
  16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*
    (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor)^2+8*atomicPatchCountFactor/9

lemma atomicPhysicalCapConstant_nonneg : 0≤atomicPhysicalCapConstant := by
  unfold atomicPhysicalCapConstant
  positivity [atomicPatchCountFactor_nonneg]

def atomicComparisonExpression (δ P a b : ℝ) : ℝ :=
  2*(tfInteriorCountConstant/a^3)^2+6*a*max countTestEnergy 0*
    ((δ+thinReserveFactor*(Real.sqrt P*screenMass δ a/b^2))+
      12*a*unitWindowKinetic/b^2*Real.sqrt (atomicPhysicalCapConstant*P*(screenMass δ a)^2/a^2)+
      Real.sqrt ((atomicPhysicalCapConstant*P*(screenMass δ a)^2/a^2)*
        (18*atomicPatchCountFactor*(b/a)*P*(screenMass δ a)^2))+
      (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(atomicPatchCountFactor*P*(screenMass δ a)^2)^(2/3:ℝ)+
      ((2*Real.pi+1)/(2*b))*Real.sqrt (atomicPatchCountFactor*P*(screenMass δ a)^2))

theorem atomic_physical_count_comparison {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) (hstate : form S ψ≤E+δ)
    (hδ : 0≤δ) {y : Space} (hy : y≠0) {b : ℝ} (hb : 0<b)
    (hsmall : 18*b≤atomicCellScale y)
    (hcond : atomicCellScale y≤b^2*Real.sqrt (screenCountParameter ψ δ)*screenMass δ (atomicCellScale y)) :
    localCountSecondMoment ψ (Metric.closedBall y (atomicCellScale y))≤
      atomicComparisonExpression δ (screenCountParameter ψ δ) (atomicCellScale y) b := by
  let a := atomicCellScale y
  let P := screenCountParameter ψ δ
  let m := screenMass δ a
  have ha : 0<a := atomicCellScale_pos hy
  have hP1 : 1≤P := screenCountParameter_ge_one ψ δ
  have hP : 0≤P := le_trans zero_le_one hP1
  have hm0 : 0 < m := screenMass_pos δ a
  have hc := fun z hz => screenCountParameter_controls ψ hm δ (y:=z) hz
  obtain ⟨t,ht,T,hEt,ho,hcs,hos,hD,hN,hraw⟩ :=
    exists_atomic_thin_screened_sharp S hatom ψ hψ hm hE hstate hδ hy hb hsmall hcond
  let F := fun p s x => atomicPatchCap S ((T.ensemble.vector p).coreSlice s x).normalized x y
  let Q := ∑ p, sliceExpectation (T.ensemble.vector p) (fun s x => (F p s x)^2)
  let N := ∑ p, (T.ensemble.out p:ℝ)^2*mass (T.ensemble.vector p)
  have hN0 : 0≤N := Finset.sum_nonneg (fun p _ => mul_nonneg (sq_nonneg _) (mass_nonneg _))
  have hD0 : 0≤T.ensemble.deletedSquare y t b := Finset.sum_nonneg (fun p _ =>
    Finset.sum_nonneg (fun s _ => integral_nonneg (fun x => mul_nonneg (mass_nonneg _) (sq_nonneg _))))
  have hwidth : t+b≤80*a := by dsimp only [a] at *; linarith [ht.2]
  have hgap : T.ensemble.totalForm S≤E+(δ+thinIMS ψ y t b) := by linarith
  have hQ : Q≤atomicPhysicalCapConstant*P*m^2/a^2 := by
    have HQ := atomicPatchCap_ensemble_square S hatom T.ensemble hy
      (H := (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2)
      (fun v hv => (Real.sqrt_le_iff.mp (hraw v hv)).2)
    change Q≤_ at HQ
    calc
      Q≤16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*
        (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2+8*N/(9*a^2) := HQ
      _≤16*(Fintype.card {z : Space // z∈atomicPatchMesh}:ℝ)*
        (2*atomicBudgetRecursionC^3*Real.sqrt thinReserveFactor*screenFieldUnit δ P a)^2+
        8*(atomicPatchCountFactor*P*m^2)/(9*a^2) := add_le_add le_rfl
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num)) (by positivity))
      _=atomicPhysicalCapConstant*P*m^2/a^2 := by
        dsimp only [atomicPhysicalCapConstant,screenFieldUnit,m]
        simp only [mul_pow,div_pow,Real.sq_sqrt hP]
        ring
  have hQ0 : 0≤atomicPhysicalCapConstant*P*m^2/a^2 := by positivity [atomicPhysicalCapConstant_nonneg]
  have hn (j) : 20*a≤‖S.position j-y‖ := by
    rw [hatom j,zero_sub,norm_neg]
    dsimp only [a,atomicCellScale]
    nlinarith [norm_nonneg y]
  have hH := physical_ensemble_count S ψ T.ensemble T.law T.fermionic ho
    (T.mass_eq.trans hm) hE hgap ha hb hsmall ht y hn hcs hos F
    (fun p s => atomicPatchCap_slice_aestronglyMeasurable S (T.ensemble.vector p) s y)
    (fun p s => Eventually.of_forall (fun x => atomicPatchCap_nonneg S _ x hy))
    (fun p s => atomicPatchCap_weight_integrable S hatom (T.ensemble.vector p) s hy)
    (fun p s => Eventually.of_forall (fun x w hw => coreField_le_atomicPatchCap S hatom _ x hy
      ((show ‖w-y‖≤t+b from by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw).trans hwidth)))
  change localCountSecondMoment ψ (Metric.closedBall y a)≤_ at hH
  apply hH.trans
  unfold atomicComparisonExpression
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (by norm_num) ha.le) (le_max_right _ _))
  have hB := thinIMS_sharp_budget ψ hm hδ hP hc hy hb hwidth
  have hp := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hQ)
    (show 0≤12*a*unitWindowKinetic/b^2 from div_nonneg (mul_nonneg (by positivity) unitWindowKinetic_nonneg) (sq_nonneg _))
  have hd := Real.sqrt_le_sqrt (mul_le_mul hQ hD hD0 hQ0)
  have hf := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hN0 hN (by norm_num : (0:ℝ)≤2/3))
    (show 0≤(b⁻¹)^2*((Real.pi^2/2)*neumannBoundary) by positivity [neumannBoundary_nonneg])
  have hn' := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hN)
    (show 0≤(2*Real.pi+1)/(2*b) by positivity [Real.pi_pos])
  dsimp only [Q,N,m,a,P] at hp hd hf hn' hB ⊢
  linarith

end Coulomb

end

end OAI
