import Mathlib
import OAI.Analysis.CoulombRadii.Screening.UniformCountConsequences

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology
noncomputable section
namespace Coulomb

lemma atomicIMS_nonneg {n : ℕ} (ψ : H1Vector n) (y : Space) : 0 ≤ atomicIMS ψ y :=
  mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (expectedPopulation_nonneg _ _)

lemma exists_annular_history_targets : ∃ j : ℕ, 1 ≤ j ∧
    ∀ {u : ℝ}, 0<u → ∃ y : Fin j → Space,
      (∀ i, y i≠0) ∧
      (∀ i, AtomicScaleWindow (u/100000) (4^j) (y i)) ∧
      {x : Space | u/2<‖x‖ ∧ ‖x‖<4*u} ⊆ atomicPatchRegion y := by
  obtain ⟨t,ht,hcover⟩ := exists_atomic_annular_mesh (α:=(1/2:ℝ)) (β:=4) (by norm_num)
  let M := Fintype.card {z : Space // z∈t}
  let e := Fintype.equivFin {z : Space // z∈t}
  let v : Space := EuclideanSpace.single 0 1
  have hv : ‖v‖=1 := by simp [v]
  refine ⟨M+1,by omega,?_⟩
  intro u hu
  let y : Fin (M+1) → Space := Fin.snoc (fun i => u • (e.symm i).val) (u • v)
  have hybounds (i : Fin (M+1)) : u/2 ≤ ‖y i‖ ∧ ‖y i‖ ≤ 4*u := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [y,Fin.snoc_last,norm_smul,Real.norm_eq_abs,abs_of_pos hu,hv,mul_one]
      constructor <;> linarith
    · simp only [y,Fin.snoc_castSucc,norm_smul,Real.norm_eq_abs,abs_of_pos hu]
      have H := ht (e.symm i).val (e.symm i).property
      constructor <;> nlinarith [H.1,H.2]
  have hq : (4:ℝ) ≤ 4^(M+1) := by
    simpa only [pow_one] using pow_le_pow_right₀ (show (1:ℝ)≤4 by norm_num) (show 1≤M+1 by omega)
  refine ⟨y,(fun i => norm_pos_iff.mp (by linarith [(hybounds i).1])),?_,?_⟩
  · intro i
    apply AtomicScaleWindow.enlarge (q:=4) _ (by positivity) hq
    dsimp only [AtomicScaleWindow,atomicCellScale]
    constructor <;> linarith [(hybounds i).1,(hybounds i).2]
  · intro x hx
    have hn : ‖u⁻¹ • x‖=‖x‖/u := by simp [norm_smul,abs_of_pos hu,div_eq_mul_inv,mul_comm]
    have hlow : (1/2:ℝ) ≤ ‖u⁻¹ • x‖ := by rw [hn]; apply (le_div_iff₀ hu).mpr; linarith [hx.1]
    have hhigh : ‖u⁻¹ • x‖ ≤ 4 := by rw [hn]; exact (div_le_iff₀ hu).mpr hx.2.le
    obtain ⟨z,hz,hxz⟩ := hcover (u⁻¹ • x) hlow hhigh
    apply Set.mem_iUnion.mpr
    refine ⟨(e ⟨z,hz⟩).castSucc,?_⟩
    simp only [y,Fin.snoc_castSucc,Equiv.symm_apply_apply,Metric.mem_closedBall,dist_eq_norm]
    rw [atomicCellScale_smul hu.le]
    have hid : x-u • z=u • (u⁻¹ • x-z) := by simp [smul_sub,smul_smul,hu.ne']
    rw [hid,norm_smul,Real.norm_eq_abs,abs_of_pos hu]
    have H := mul_le_mul_of_nonneg_left hxz.le hu.le
    nlinarith [atomicCellScale_nonneg z]

lemma annularIMSCost_reserve {δ u C : ℝ} (hδ : 0≤δ) (hu : 0<u) (hC : 0≤C) :
    C*screenMass δ u/u^2 ≤ (C*(100000:ℝ)^3)*screenEnergy δ (u/100000) := by
  have ha : 0<u/100000 := by positivity
  have H : screenMass δ u ≤ (100000:ℝ)^3*screenMass δ (u/100000) :=
    screenMass_comparable hδ ha (by norm_num) (by linarith) (by linarith)
  have hm := screenMass_pos δ (u/100000)
  have hs := screenMass_scale δ ha
  have hnum : screenMass δ u ≤ (100000:ℝ)^3*(u*screenMass δ (u/100000)^2)*100000 := by
    have H1 := mul_le_mul_of_nonneg_right hs hm.le
    nlinarith
  rw [div_le_iff₀ (sq_pos_of_pos hu)]
  unfold screenEnergy
  have he : (C*(100000:ℝ)^3)*(screenMass δ (u/100000)^2/(u/100000))*u^2 =
      C*((100000:ℝ)^3*(u*screenMass δ (u/100000)^2)*100000) := by field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hnum hC

theorem annular_ensemble_positive_field : ∀ C₀ : ℝ, 0≤C₀ → ∃ C : ℝ, 0≤C ∧
    ∀ {J n : ℕ} (S : Nuclei J), (∀ i, S.position i=0) →
    ∀ (ψ : H1Vector n), Antisymmetric ψ → mass ψ=1 →
    ∀ {E δ : ℝ}, (E:EReal)≤unrestrictedFormBottom S → form S ψ≤E+δ → 0≤δ →
    ∀ {u : ℝ}, 0<u → ∀ T : RecordedEnsemble n,
      T.Conserves ψ → T.CoreFermionic →
      T.OutSupported {x : Space | u/2<‖x‖ ∧ ‖x‖<4*u} →
      T.totalMass=mass ψ → T.totalForm S≤form S ψ+C₀*screenMass δ u/u^2 →
      ∀ y : Space, u/2≤‖y‖ → ‖y‖≤4*u →
      Real.sqrt (T.rawSquare S y (atomicCellScale y)) ≤ C*screenMass δ u/u := by
  intro C₀ hC₀
  obtain ⟨j,hj,Htargets⟩ := exists_annular_history_targets
  let P : ℝ := max 1 (max atomicCountConstant (C₀*(100000:ℝ)^3))
  have hP : 1≤P := le_max_left _ _
  have hPcount : atomicCountConstant≤P := (le_max_left _ _).trans (le_max_right _ _)
  have hPcost : C₀*(100000:ℝ)^3≤P := (le_max_right _ _).trans (le_max_right _ _)
  have hCrec : 0 ≤ atomicBudgetRecursionC := le_trans (by norm_num) atomicBudgetRecursionC_ge_four
  let C : ℝ := 2*atomicBudgetRecursionC^(j+2)*Real.sqrt P*(100000:ℝ)^4
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro J n S hatom ψ hψ hm E δ hE hstate hδ u hu T hlaw hf hsupp hmass hform y hylo hyhi
  obtain ⟨ys,hys0,hys,hcover⟩ := Htargets hu
  let B := C₀*screenMass δ u/u^2
  let U : AtomicBudgetHistory S ψ B j := {
    ensemble := T
    target := ys
    nonzero := hys0
    law := hlaw
    fermionic := hf
    support := fun p => (hsupp p).mono_space hcover
    mass_eq := hmass
    energy := hform.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => atomicIMS_nonneg ψ (ys i)))) }
  have hB : B≤P*screenEnergy δ (u/100000) :=
    (annularIMSCost_reserve hδ hu hC₀).trans (mul_le_mul_of_nonneg_right hPcost (screenEnergy_pos δ (by positivity)).le)
  have hc (z : Space) (hz : z≠0) : localCountSecondMoment ψ (Metric.closedBall z (atomicCellScale z)) ≤
      P*(screenMass δ (atomicCellScale z))^2 := by
    exact (screenCountParameter_controls ψ hm δ hz).trans (mul_le_mul_of_nonneg_right
      ((screenCountParameter_le_atomicCountConstant S hatom ψ hψ hm hE hstate hδ).trans hPcount) (sq_nonneg _))
  have hy : AtomicScaleWindow (u/100000) (4^j) y := by
    apply AtomicScaleWindow.enlarge (q:=4) _ (by positivity)
      (by simpa only [pow_one] using pow_le_pow_right₀ (show (1:ℝ)≤4 by norm_num) hj)
    dsimp only [AtomicScaleWindow,atomicCellScale]
    constructor <;> linarith
  have H := U.positive_field S hatom ψ hm hE hstate hB hδ hP (by positivity) hc hys y hy
  have Hm : screenMass δ (u/100000) ≤ (100000:ℝ)^3*screenMass δ u :=
    screenMass_comparable hδ hu (by norm_num) le_rfl (by linarith)
  have Hu : screenFieldUnit δ P (u/100000) ≤ Real.sqrt P*(100000:ℝ)^4*screenMass δ u/u := by
    unfold screenFieldUnit
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left Hm (Real.sqrt_nonneg _)) (by positivity)).trans_eq (by ring)
  exact H.trans ((mul_le_mul_of_nonneg_left Hu (by positivity)).trans_eq (by dsimp [C]; ring))

end Coulomb
end

end

end OAI
