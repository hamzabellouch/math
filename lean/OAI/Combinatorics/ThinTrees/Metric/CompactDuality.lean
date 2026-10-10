import Mathlib
import OAI.Combinatorics.ThinTrees.Metric.ConicDuality

namespace OAI

/-! Metric compact duality. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n : ℕ} {E T : Type*}

lemma average_antitone (b : E → Fin n → ℝ) (O : T → Finset E) (t : T)
    {D F : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) (hF : F.PosDef) (hDF : D ≤ F) :
    ShortcutDual.boundaryAverage b O t F ≤ ShortcutDual.boundaryAverage b O t D := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact sum_le_sum (fun e _ => resistance_antitone hF hD (Matrix.le_iff.mp hDF) (b e))

lemma average_smul (b : E → Fin n → ℝ) (O : T → Finset E) (t : T)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) {c : ℝ} (hc : 0 < c) :
    ShortcutDual.boundaryAverage b O t (c • D)=c⁻¹*ShortcutDual.boundaryAverage b O t D := by
  let : Invertible c := invertibleOfNonzero hc.ne'
  simp only [ShortcutDual.boundaryAverage,Matrix.inv_smul D c ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit),
    invOf_eq_inv,smul_mulVec,dotProduct_smul,smul_eq_mul,←mul_sum]
  ring

lemma average_continuousAt (b : E → Fin n → ℝ) (O : T → Finset E) (t : T)
    {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosDef) :
    ContinuousAt (ShortcutDual.boundaryAverage b O t) D := by
  have hc : Continuous (fun X : Matrix (Fin n) (Fin n) ℝ =>
      ((O t).card : ℝ)⁻¹ * ∑e ∈ O t, qform X (b e)) :=
    (continuous_finsetSum _ (fun e _ => qform_continuous (b e))).const_mul _
  apply hc.continuousAt.comp
  apply continuousAt_matrix_inv
  simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hD.det_pos.ne'

def pdBox (B : Matrix (Fin n) (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {D | (1/4:ℝ) • B ≤ D ∧ D.trace ≤ B.trace}

lemma pdBox_pd {B D : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) (hD : D ∈ pdBox B) : D.PosDef :=
  posDef_of_le (hB.smul (by norm_num : (0:ℝ)<1/4)) hD.1

lemma pdBox_closed (B : Matrix (Fin n) (Fin n) ℝ) : IsClosed (pdBox B) :=
  (isClosed_matrixAbove _).inter (isClosed_le
    (by simpa only [mul_one] using trace_pairing_continuous (1 : Matrix (Fin n) (Fin n) ℝ)) continuous_const)

lemma pdBox_bounded {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) : Bornology.IsBounded (pdBox B) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨B.trace,fun D hD => ?_⟩
  have hC : 0 ≤ B.trace := hB.posSemidef.trace_nonneg
  have hDp := (pdBox_pd hB hD).posSemidef
  have hdiag : ∀i, D i i ≤ B.trace := by
    intro i
    exact (single_le_sum (fun j _ => hDp.diag_nonneg (i := j)) (mem_univ i)).trans hD.2
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  intro j
  simpa only [Real.norm_eq_abs] using psd_entry_bound hDp hC hdiag i j

lemma pdBox_compact {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) : IsCompact (pdBox B) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨pdBox_closed B,pdBox_bounded hB⟩

lemma pdBox_objective_closed (b : E → Fin n → ℝ) (O : T → Finset E)
    {B : Matrix (Fin n) (Fin n) ℝ} (hB : B.PosDef) (K : ℝ) :
    IsClosed {D | D ∈ pdBox B ∧ ∀t, ShortcutDual.boundaryAverage b O t D ≤ K} := by
  have ht (t : T) : IsClosed {D | D ∈ pdBox B ∧ ShortcutDual.boundaryAverage b O t D ≤ K} :=
    (pdBox_closed B).isClosed_le (fun D hD => (average_continuousAt b O t (pdBox_pd hB hD)).continuousWithinAt)
      continuousOn_const
  have heq : {D | D ∈ pdBox B ∧ ∀t, ShortcutDual.boundaryAverage b O t D ≤ K}=
      pdBox B ∩ ⋂t, {D | D ∈ pdBox B ∧ ShortcutDual.boundaryAverage b O t D ≤ K} := by
    ext D
    simp only [Set.mem_ofPred_eq,Set.mem_inter_iff,Set.mem_iInter]
    constructor
    · exact fun h => ⟨h.1,fun t => ⟨h.1,h.2 t⟩⟩
    · exact fun h => ⟨h.1,fun t => (h.2 t).2⟩
  rw [heq]
  exact (pdBox_closed B).inter (isClosed_iInter ht)

section Cone
variable [Fintype T]

theorem metric_shortcut_of_trace_bound (hn : 0 < n)
    (b : E → Fin n → ℝ) (O : T → Finset E)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.PosDef) {K : ℝ} (hK : 0 < K)
    (hbound : ∀Z : Matrix (Fin n) (Fin n) ℝ, Test Z →
      ∀lam : T → ℝ, (∀t, 0 ≤ lam t) → (∑t, lam t)=1 →
      (CFC.sqrt (CFC.sqrt Z*ShortcutDual.objectiveMatrix b O lam*CFC.sqrt Z)).trace^2 ≤ K*(B*Z).trace) :
    ∃D : Matrix (Fin n) (Fin n) ℝ, D.PosDef ∧
      (∀t, ShortcutDual.boundaryAverage b O t D ≤ 2*K) ∧
      (∀Z : Matrix (Fin n) (Fin n) ℝ, Test Z → (D*Z).trace ≤ (B*Z).trace) := by
  let C := {D | D ∈ pdBox B ∧ ∀t, ShortcutDual.boundaryAverage b O t D ≤ 2*K}
  have hC : IsCompact C := (pdBox_compact hB).of_isClosed_subset
    (pdBox_objective_closed b O hB (2*K)) (fun _ h => h.1)
  let I := {Z : Matrix (Fin n) (Fin n) ℝ // Test Z}
  let A : I → Set (Matrix (Fin n) (Fin n) ℝ) := fun Z => {D | (D*Z.val).trace ≤ (B*Z.val).trace}
  have hA : ∀Z, IsClosed (A Z) := fun Z => isClosed_le (trace_pairing_continuous Z.val) continuous_const
  have hfinite : ∀s : Finset I, (C ∩ ⋂Z ∈ s, A Z).Nonempty := by
    intro s
    have h1 : (1 : Matrix (Fin n) (Fin n) ℝ) ≠ 0 := by
      intro he
      have hh := congrFun (congrFun he ⟨0,hn⟩) ⟨0,hn⟩
      norm_num at hh
    let s' : Finset I := (insert ⟨1,test_one⟩ s).filter fun Z => Z.val ≠ 0
    have hbnd : ∀lam : T → ℝ, ∀y : s' → ℝ,
        (∀t, 0 ≤ lam t) → (∑t, lam t)=1 → (∀j, 0 ≤ y j) →
        (CFC.sqrt (CFC.sqrt (∑j, y j • j.val.val)*ShortcutDual.objectiveMatrix b O lam*
          CFC.sqrt (∑j, y j • j.val.val))).trace^2 ≤ K*∑j, y j*(B*j.val.val).trace := by
      intro lam y hlam hsum hy
      have ht : Test (∑j : s', y j • j.val.val) := test_sum univ _
        (fun j _ => test_smul j.val.property (hy j))
      simpa only [mul_sum,mul_smul_comm,trace_sum,trace_smul,smul_eq_mul] using hbound _ ht lam hlam hsum
    obtain ⟨D,hD,hobj,htr⟩ := finite_shortcut_of_trace_bound b O (fun j : s' => j.val.val)
      (fun j => j.val.property.1) (fun j => (B*j.val.val).trace)
      (fun j => trace_pairing_pos hB j.val.property.1 ((mem_filter.mp j.property).2))
      hK.le hbnd (eta := K/2) (by positivity)
    let F : Matrix (Fin n) (Fin n) ℝ := (3/4:ℝ) • D+(1/4:ℝ) • B
    have hF : F.PosDef := (hD.smul (by norm_num : (0:ℝ)<3/4)).add_posSemidef
      (hB.posSemidef.smul (by norm_num : (0:ℝ)≤1/4))
    have hFB : (1/4:ℝ) • B ≤ F := by
      apply Matrix.le_iff.mpr
      simpa only [F,add_sub_cancel_right] using hD.posSemidef.smul (show (0:ℝ)≤3/4 by norm_num)
    have hFD : (3/4:ℝ) • D ≤ F := by
      apply Matrix.le_iff.mpr
      simpa only [F,add_sub_cancel_left] using hB.posSemidef.smul (show (0:ℝ)≤1/4 by norm_num)
    have hfbound (t : T) : ShortcutDual.boundaryAverage b O t F ≤ 2*K := by
      have hh := average_antitone b O t (hD.smul (show (0:ℝ)<3/4 by norm_num)) hF hFD
      rw [average_smul b O t hD (by norm_num : (0:ℝ)<3/4)] at hh
      norm_num at hh
      linarith only [hh,hobj t]
    have hFtr (Z : I) (hZ : Z ∈ insert ⟨1,test_one⟩ s) : (F*Z.val).trace ≤ (B*Z.val).trace := by
      by_cases hZ0 : Z.val=0
      · simp [hZ0]
      have hh := htr ⟨Z,mem_filter.mpr ⟨hZ,hZ0⟩⟩
      dsimp [F]
      simp only [add_mul,smul_mul_assoc,trace_add,trace_smul,smul_eq_mul]
      linarith only [hh]
    have hFt : F.trace ≤ B.trace := by
      simpa only [mul_one] using hFtr ⟨1,test_one⟩ (mem_insert_self _ _)
    refine ⟨F,⟨⟨hFB,hFt⟩,hfbound⟩,?_⟩
    simp only [Set.mem_iInter]
    intro Z hZ
    exact hFtr Z (mem_insert_of_mem hZ)
  obtain ⟨D,hDC,hDA⟩ := hC.inter_iInter_nonempty A hA hfinite
  refine ⟨D,pdBox_pd hB hDC.1,hDC.2,?_⟩
  intro Z hZ
  exact Set.mem_iInter.mp hDA ⟨Z,hZ⟩

end Cone
end
end AlgorithmicThinTrees.MetricTests
end

end OAI
