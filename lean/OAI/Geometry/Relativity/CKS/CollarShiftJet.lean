import OAI.Geometry.Relativity.CKS.MatrixThreeJets

namespace OAI

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

abbrev ShiftInput := MatrixThreeJet × (I → ScalarThreeJet)
def raisedMixedJet (j : ShiftInput) (a : I) : ScalarThreeJet :=
  ∑ b, productThreeJet (inverseMatrixThreeJet j.1 a b) (j.2 b)
def shiftRegion : Set ShiftInput := {j | determinant (fun i k => (j.1 i k).1.1) ≠ 0}

lemma productThreeJet_zero_right (f : ScalarThreeJet) : productThreeJet f 0 = 0 := by
  apply Prod.ext
  · exact productJet_zero_right _
  · funext a
    simp [productThreeJet,productJet_zero_right,productJet_zero_left]

lemma raisedMixedJet_zero (q : MatrixThreeJet) : raisedMixedJet (q,0) = 0 := by
  funext a
  simp [raisedMixedJet,productThreeJet_zero_right]

lemma raisedMixedJet_smooth {j : ShiftInput} (hj : j ∈ shiftRegion) :
    ContDiffAt ℝ ∞ raisedMixedJet j := by
  apply contDiffAt_pi.mpr
  intro a
  apply ContDiffAt.sum
  intro b hb
  exact productThreeJet_smooth.contDiffAt.comp j
    (((inverseMatrixThreeJet_smooth hj a b).comp j
      (by fun_prop : ContDiffAt ℝ ∞ (fun j : ShiftInput => j.1) j)).prodMk (by fun_prop))

lemma shiftRegion_open : IsOpen shiftRegion := by
  exact isOpen_ne_fun (determinant_smooth.continuous.comp
    (by fun_prop : Continuous (fun j : ShiftInput => fun i k => (j.1 i k).1.1))) continuous_const

theorem shift_uniform_lipschitz {K : Set ShiftInput} (hK : IsCompact K)
    (hreg : K ⊆ shiftRegion) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0,
      LipschitzOnWith C raisedMixedJet (Metric.cthickening δ K) := by
  let : FiniteDimensional ℝ ScalarThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixThreeJet := inferInstance
  let : FiniteDimensional ℝ (I → ScalarThreeJet) := inferInstance
  let : ProperSpace ShiftInput := FiniteDimensional.proper ℝ ShiftInput
  obtain ⟨δ,hδ,hsub⟩ := hK.exists_cthickening_subset_open shiftRegion_open hreg
  refine ⟨δ,hδ,?_⟩
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (hK.cthickening (r := δ))
  intro j hj
  obtain ⟨C,t,ht,hC⟩ := ((raisedMixedJet_smooth (hsub hj)).of_le
    (by simp : (1:ℕ∞ω) ≤ ∞)).exists_lipschitzOnWith
  exact ⟨C,t,mem_nhdsWithin_of_mem_nhds ht,hC⟩

theorem normalized_shift_bound {K : Set ShiftInput} (hK : IsCompact K)
    (hreg : K ⊆ shiftRegion) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q qref : MatrixThreeJet) (b : I → ScalarThreeJet) (r A B : ℝ),
      (qref,0) ∈ K → 0 < r → 0 ≤ A → 0 ≤ B →
      ‖q-qref‖ ≤ B/r^3 → ‖b‖ ≤ A/r^3 → max A B/r^3 ≤ δ →
      ‖(1/r) • raisedMixedJet (q,b)‖ ≤ C*A/r^4 := by
  obtain ⟨δ,hδ,C,hC⟩ := shift_uniform_lipschitz hK hreg
  refine ⟨δ,hδ,C,C.coe_nonneg,?_⟩
  intro q qref b r A B href hr hA hB hq hb hδ'
  have hAd : A/r^3 ≤ δ := (div_le_div_of_nonneg_right (le_max_left A B)
    (pow_nonneg hr.le _)).trans hδ'
  have hBd : B/r^3 ≤ δ := (div_le_div_of_nonneg_right (le_max_right A B)
    (pow_nonneg hr.le _)).trans hδ'
  have hmem : (q,b) ∈ Metric.cthickening δ K := by
    apply Metric.mem_cthickening_of_dist_le (q,b) (qref,0) δ K href
    rw [dist_eq_norm]
    apply norm_prod_le_iff.mpr
    exact ⟨hq.trans hBd,by simpa using hb.trans hAd⟩
  have hzero : (q,(0:I → ScalarThreeJet)) ∈ Metric.cthickening δ K := by
    apply Metric.mem_cthickening_of_dist_le (q,0) (qref,0) δ K href
    rw [dist_eq_norm]
    apply norm_prod_le_iff.mpr
    exact ⟨hq.trans hBd,by simp [hδ.le]⟩
  have hnorm : ‖raisedMixedJet (q,b)‖ ≤ (C:ℝ)*(A/r^3) := by
    have hh := hC.norm_sub_le hmem hzero
    simpa [raisedMixedJet_zero] using hh.trans
      (mul_le_mul_of_nonneg_left (by simpa using hb) C.coe_nonneg)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hr)]
  exact (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans_eq (by field_simp)

lemma actual_raisedMixedJet {q : Point → Mat} {b : Point → Point} {x : Point}
    (hq : ContDiffAt ℝ 3 q x) (hb : ContDiffAt ℝ 3 b x) (h0 : determinant (q x) ≠ 0) :
    (fun a => actualThreeJet (fun y => ∑ i, inverse (q y) a i*b y i) x) =
      raisedMixedJet (matrixThreeJets q x,fun a => actualThreeJet (fun y => b y a) x) := by
  funext a
  have hi (i : I) : ContDiffAt ℝ 3 (fun y => inverse (q y) a i) x := by
    unfold inverse
    apply ContDiffAt.div
    · fin_cases a <;> fin_cases i <;> dsimp <;> first | exact component_three hq _ _ | exact (component_three hq _ _).neg
    · exact (determinant_smooth.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3)).contDiffAt.comp x hq
    · exact h0
  have hb' (i : I) := contDiffAt_pi.mp hb i
  rw [actualThreeJet_sum Finset.univ (fun i _ => (hi i).mul (hb' i))]
  unfold raisedMixedJet
  apply Finset.sum_congr rfl
  intro i hi'
  rw [actualThreeJet_mul (hi i) (hb' i),actual_inverseMatrixThreeJet hq h0]

end
end CKSAngularGeometry

end

end OAI
