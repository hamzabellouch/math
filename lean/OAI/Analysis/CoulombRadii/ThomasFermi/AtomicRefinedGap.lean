import Mathlib
import OAI.Analysis.CoulombRadii.Screening.SharpThinScreening
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalEnsembleGap

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace Coulomb

lemma atomic_patch_nucleus_distance {J : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (y : Space) (j : Fin J) :
    20*atomicCellScale y ≤ ‖S.position j-y‖ := by
  rw [hatom j,zero_sub,norm_neg]
  unfold atomicCellScale
  nlinarith [norm_nonneg y]

def atomicPatchTFGap {J n : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0)
    (T : RecordedEnsemble n) (y : Space) (hy : y≠0) (b : ℝ) (hb : 0<b)
    (t : ℝ) (ht : t≤6*atomicCellScale y) : ℝ :=
  ∑ p, sliceExpectation (T.vector p) (fun s x =>
    let Φ := coreScreenedField S ((T.vector p).coreSlice s x).normalized
    let ρ := localTFDensity measurableSet_ball
      (coreTFField S ((T.vector p).coreSlice s x).normalized measurableSet_ball
        (atomicCellScale_pos hy)
        (patch_nucleus_separation S (atomicCellScale_pos hy) hb ht y
          (atomic_patch_nucleus_distance S hatom y)))
    rawThomasFermiEnergy Φ (retainedFineDensity b (patchRetained y t b x) (position x))-
    rawThomasFermiEnergy Φ ρ)

def atomicRefinedError (δ P a b : ℝ) : ℝ :=
(δ+thinReserveFactor*(Real.sqrt P*screenMass δ a/b^2))+
      12*a*unitWindowKinetic/b^2*Real.sqrt (atomicPhysicalCapConstant*P*(screenMass δ a)^2/a^2)+
      Real.sqrt ((atomicPhysicalCapConstant*P*(screenMass δ a)^2/a^2)*
        (18*atomicPatchCountFactor*(b/a)*P*(screenMass δ a)^2))+
      (b⁻¹)^2*((Real.pi^2/2)*neumannBoundary)*(atomicPatchCountFactor*P*(screenMass δ a)^2)^(2/3:ℝ)+
      ((2*Real.pi+1)/(2*b))*Real.sqrt (atomicPatchCountFactor*P*(screenMass δ a)^2)

theorem exists_atomic_physical_gap {J n : ℕ} (S : Nuclei J)
    (hatom : ∀ i, S.position i=0) (ψ : H1Vector n) (hψ : Antisymmetric ψ) (hm : mass ψ=1)
    {E δ : ℝ} (hE : (E:EReal)≤unrestrictedFormBottom S) (hstate : form S ψ≤E+δ)
    (hδ : 0≤δ) {y : Space} (hy : y≠0) {b : ℝ} (hb : 0<b)
    (hsmall : 18*b≤atomicCellScale y)
    (hcond : atomicCellScale y≤b^2*Real.sqrt (screenCountParameter ψ δ)*screenMass δ (atomicCellScale y)) :
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t b) 1,
      T.ensemble.totalForm S≤form S ψ+thinIMS ψ y t b ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+b)) ∧
      atomicPatchTFGap S hatom T.ensemble y hy b hb t ht.2 ≤
        atomicRefinedError δ (screenCountParameter ψ δ) (atomicCellScale y) b := by
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
  have hH := physical_ensemble_gap S ψ T.ensemble T.law T.fermionic ho
    (T.mass_eq.trans hm) hE hgap ha hb hsmall ht y hn hcs hos F
    (fun p s => atomicPatchCap_slice_aestronglyMeasurable S (T.ensemble.vector p) s y)
    (fun p s => Eventually.of_forall (fun x => atomicPatchCap_nonneg S _ x hy))
    (fun p s => atomicPatchCap_weight_integrable S hatom (T.ensemble.vector p) s hy)
    (fun p s => Eventually.of_forall (fun x w hw => coreField_le_atomicPatchCap S hatom _ x hy
      ((show ‖w-y‖≤t+b from by simpa only [Metric.mem_closedBall,dist_eq_norm] using hw).trans hwidth)))
  refine ⟨t,ht,T,hEt,ho,hcs,hos,?_⟩
  change atomicPatchTFGap S hatom T.ensemble y hy b hb t ht.2≤_ at hH
  apply hH.trans
  unfold atomicRefinedError
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

end
end

end OAI
