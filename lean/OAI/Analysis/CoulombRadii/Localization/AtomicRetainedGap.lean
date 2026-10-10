import Mathlib
import OAI.Analysis.CoulombRadii.Packets.AtomicSmallPatch

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

theorem exists_atomic_physical_gap_with_deleted {J n : ℕ} (S : Nuclei J)
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
        atomicRefinedError δ (screenCountParameter ψ δ) (atomicCellScale y) b ∧
      T.ensemble.deletedSquare y t b ≤
        18*atomicPatchCountFactor*(b/atomicCellScale y)*(screenCountParameter ψ δ)*(screenMass δ (atomicCellScale y))^2 := by
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
  refine ⟨t,ht,T,hEt,ho,hcs,hos,?_,hD⟩
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
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma atomic_deleted_small_bound {δ P a : ℝ} (hδ : 0≤δ) (hP : 0≤P)
    (hPP : P≤atomicCountConstant) (ha : 0<a) (ha1 : a≤1) (hd : δ≤a^(-349/50:ℝ)) :
    18*atomicPatchCountFactor*(a^(6/5:ℝ)/a)*P*(screenMass δ a)^2 ≤
      (72*atomicPatchCountFactor*atomicCountConstant)*a^(-29/5:ℝ) := by
  have hsmall : δ*a^7≤1 := by
    calc
      δ*a^7≤a^(-349/50:ℝ)*a^7 := mul_le_mul_of_nonneg_right hd (pow_nonneg ha.le _)
      _=a^(1/50:ℝ) := by rw [←Real.rpow_natCast a 7,←Real.rpow_add ha]; norm_num
      _≤1 := Real.rpow_le_one ha.le ha1 (by norm_num)
  have hm := NeutralAtom.screenMass_small_offset ha ha1 hδ hsmall
  have hm' : screenMass δ a≤2*a^(-3:ℝ) := by
    simpa only [Real.rpow_neg ha.le,Real.rpow_ofNat,div_eq_mul_inv] using hm
  have hA := atomicPatchCountFactor_nonneg
  have hC : 0≤atomicCountConstant := hP.trans hPP
  calc
    _≤18*atomicPatchCountFactor*(a^(6/5:ℝ)/a)*atomicCountConstant*(2*a^(-3:ℝ))^2 := by
      gcongr
      exact (screenMass_pos _ _).le
    _=(72*atomicPatchCountFactor*atomicCountConstant)*a^(-29/5:ℝ) := by
      have hm2 : (2*a^(-3:ℝ))^2=4*a^(-6:ℝ) := by
        rw [mul_pow,←Real.rpow_mul_natCast ha.le]
        norm_num
      rw [hm2]
      calc
        _=((72*atomicPatchCountFactor*atomicCountConstant)*(a^(6/5:ℝ)*a^(-6:ℝ)))/a^1 := by ring
        _=_ := by rw [←Real.rpow_add ha,←Real.rpow_natCast a 1,div_rpow_monomial ha]; norm_num

theorem exists_atomic_small_gap_with_deleted : ∃ s : ℝ, 0<s ∧ s≤1 ∧
    ∀ {J n : ℕ} (S : Nuclei J) (hatom : ∀ i, S.position i=0)
    (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E+δ → 0≤δ →
    ∀ (y : Space) (hy : y≠0), atomicCellScale y<s → δ≤(atomicCellScale y)^(-349/50:ℝ) →
    ∃ t : ℝ, ∃ ht : t∈Set.Icc (5*atomicCellScale y) (6*atomicCellScale y),
    ∃ T : AtomicBudgetHistory S ψ (thinIMS ψ y t ((atomicCellScale y)^(6/5:ℝ))) 1,
      T.ensemble.totalForm S≤form S ψ+thinIMS ψ y t ((atomicCellScale y)^(6/5:ℝ)) ∧
      T.ensemble.OutFermionic ∧ T.ensemble.CoreSupported {z | t≤‖z-y‖} ∧
      T.ensemble.OutSupported (Metric.closedBall y (t+(atomicCellScale y)^(6/5:ℝ))) ∧
      atomicPatchTFGap S hatom T.ensemble y hy ((atomicCellScale y)^(6/5:ℝ))
        (Real.rpow_pos_of_pos (atomicCellScale_pos hy) _) t ht.2≤2*(atomicCellScale y)^(-349/50:ℝ) ∧
      T.ensemble.deletedSquare y t ((atomicCellScale y)^(6/5:ℝ))≤
        (72*atomicPatchCountFactor*atomicCountConstant)*(atomicCellScale y)^(-29/5:ℝ) := by
  obtain ⟨s,hs,hs1,hbound⟩ := exists_atomic_refined_small_scale
  refine ⟨s,hs,hs1,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ y hy hys hd
  let a := atomicCellScale y
  have ha : 0<a := atomicCellScale_pos hy
  have ha1 : a≤1 := hys.le.trans hs1
  obtain ⟨hsmall,herror⟩ := hbound a ha hys
  obtain ⟨t,ht,T,hT,ho,hcs,hos,hgap,hD⟩ := exists_atomic_physical_gap_with_deleted S hatom ψ hψ hm hE hstate hδ
    hy (Real.rpow_pos_of_pos ha (6/5:ℝ)) hsmall
    (source_patch_scale_condition ha ha1 (screenCountParameter_ge_one ψ δ))
  have hPP := screenCountParameter_le_atomicCountConstant S hatom ψ hψ hm hE hstate hδ
  have hP := le_trans zero_le_one (screenCountParameter_ge_one ψ δ)
  refine ⟨t,ht,T,hT,ho,hcs,hos,?_,?_⟩
  · exact hgap.trans ((atomicRefinedError_small_bound hδ hP hPP ha ha1 hd).trans herror)
  · exact hD.trans (atomic_deleted_small_bound hδ hP hPP ha ha1 hd)
end Coulomb

end

end OAI
