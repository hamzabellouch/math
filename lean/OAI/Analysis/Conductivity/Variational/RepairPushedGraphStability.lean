import Mathlib
import OAI.Analysis.Conductivity.Variational.ContDiffClmDet
import OAI.Analysis.Conductivity.Variational.GramRankDetNe
import OAI.Analysis.Conductivity.Variational.UniformNormBound

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

section
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma repairPushed_graph_stability
    {P m : Type*} [TopologicalSpace P] [Fintype m] [DecidableEq m]
    {K : Set P} (hK : IsCompact K)
    (A : P → Symmetric3) (J : P → Mat3) (E F : P → Matrix (Fin 3) m ℝ)
    (hA : ∀ p ∈ K, ContinuousAt A p) (hJ : ∀ p ∈ K, ContinuousAt J p)
    (hE : ∀ p ∈ K, ContinuousAt E p) (hF : ∀ p ∈ K, ContinuousAt F p)
    (hdet : ∀ p ∈ K, 0 < (J p).det) (hrank : ∀ p ∈ K, LinearIndependent ℝ (E p).col)
    {U : Set (P × Symmetric3)} (hU : IsOpen U)
    (hmem : ∀ p ∈ K, (p, repairPushed (A p) (J p) (E p) (F p)) ∈ U) :
    ∃ O : Set P, IsOpen O ∧ K ⊆ O ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ p ∈ O, ∀ (dJ : Mat3) (dE dF : Matrix (Fin 3) m ℝ),
        ‖(dJ, dE, dF)‖ < ε →
          0 < (J p + dJ).det ∧ LinearIndependent ℝ (E p + dE).col ∧
          (p, repairPushed (A p) (J p + dJ) (E p + dE) (F p + dF)) ∈ U := by
  let V := Mat3 × Matrix (Fin 3) m ℝ × Matrix (Fin 3) m ℝ
  let a : P × V → Symmetric3 := fun q => A q.1
  let j : P × V → Mat3 := fun q => J q.1 + q.2.1
  let e : P × V → Matrix (Fin 3) m ℝ := fun q => E q.1 + q.2.2.1
  let f : P × V → Matrix (Fin 3) m ℝ := fun q => F q.1 + q.2.2.2
  let T : P × V → (P × Symmetric3) × ℝ × ℝ := fun q =>
    ((q.1, repairPushed (a q) (j q) (e q) (f q)), (j q).det, ((e q)ᵀ * e q).det)
  have hT : ∀ p ∈ K, ContinuousAt T (p, 0) := by
    intro p hp
    have ha : ContinuousAt a (p, 0) := (hA p hp).comp continuousAt_fst
    have hj : ContinuousAt j (p, 0) := ((hJ p hp).comp continuousAt_fst).add
      (continuousAt_fst.comp continuousAt_snd)
    have he : ContinuousAt e (p, 0) := ((hE p hp).comp continuousAt_fst).add
      (continuousAt_fst.comp (continuousAt_snd.comp continuousAt_snd))
    have hf : ContinuousAt f (p, 0) := ((hF p hp).comp continuousAt_fst).add
      (continuousAt_snd.comp (continuousAt_snd.comp continuousAt_snd))
    have hj0 : j (p, 0) = J p := by simp [j]
    have he0 : e (p, 0) = E p := by simp [e]
    have hc : Continuous (fun M : Mat3 => M.det) := continuous_id.matrix_det
    have hg : Continuous (fun M : Matrix m m ℝ => M.det) := continuous_id.matrix_det
    exact (continuousAt_fst.prodMk (continuousAt_repairPushed a j e f ha hj he hf
      (hj0 ▸ (hdet p hp).ne') (he0 ▸ hrank p hp))).prodMk
        ((hc.continuousAt.comp hj).prodMk
          (hg.continuousAt.comp (matrix_mul_contAt (matrix_transpose_contAt he) he)))
  let W : Set ((P × Symmetric3) × ℝ × ℝ) := U ×ˢ Ioi 0 ×ˢ ({0} : Set ℝ)ᶜ
  have hW : IsOpen W := hU.prod (isOpen_Ioi.prod isClosed_singleton.isOpen_compl)
  have hTW : ∀ p ∈ K, T (p, 0) ∈ W := by
    intro p hp
    simpa [T, W, a, j, e, f] using
      And.intro (hmem p hp) (And.intro (hdet p hp) (gram_det_ne_zero (E p) (hrank p hp)))
  obtain ⟨O, hO, hKO, ε, hε, heps⟩ := compact_zero_stability hK T hT hW hTW
  refine ⟨O, hO, hKO, ε, hε, ?_⟩
  intro p hp dJ dE dF hd
  have ht := heps p hp (dJ, dE, dF) hd
  exact ⟨ht.2.1, gram_rank_of_det_ne_zero _ ht.2.2, ht.1⟩

end

section
open Set MeasureTheory

lemma exists_det_bound_of_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (R : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ D : E →L[ℝ] E, ‖D‖ ≤ R → |D.det| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : E →L[ℝ] E) R).exists_bound_of_continuousOn
    (contDiff_clm_det (E := E) 1).continuous.continuousOn
  refine ⟨max C 0 + 1, by positivity, ?_⟩
  intro D hD
  have hb := hC D (by simpa only [Metric.mem_closedBall, dist_zero_right] using hD)
  rw [Real.norm_eq_abs] at hb
  exact hb.trans (by linarith only [le_max_left C (0 : ℝ)])

lemma exists_bounded_chart_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X : OpenPartialHomeomorph E E) (hX : Continuous X)
    (hXi : ContDiffOn ℝ (↑(⊤ : ℕ∞)) X.symm X.target)
    {V : Set E} (hV : IsOpen V) (hVX : V ⊆ X.source) {p : E} (hp : p ∈ V) :
    ∃ W : Set E, IsOpen W ∧ p ∈ W ∧ closure W ⊆ V ∧ IsCompact (closure W) ∧
      Bornology.IsBounded (X '' W) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ y ∈ X '' W, |(fderiv ℝ X.symm y).det| ≤ C := by
  obtain ⟨K, hpK, hKV, hK⟩ := local_compact_nhds (hV.mem_nhds hp)
  have hXK : IsCompact (X '' K) := hK.image hX
  have hKt : X '' K ⊆ X.target := by
    rintro y ⟨x, hx, rfl⟩
    exact X.map_source (hVX (hKV hx))
  have hc : ContinuousOn (fun y => (fderiv ℝ X.symm y).det) X.target :=
    (contDiff_clm_det (E := E) 1).continuous.comp_continuousOn
      (hXi.continuousOn_fderiv_of_isOpen X.open_target (by simp))
  obtain ⟨C, hC⟩ := hXK.exists_bound_of_continuousOn (hc.mono hKt)
  have hcl : closure (interior K) ⊆ K := hK.isClosed.closure_subset_iff.mpr interior_subset
  refine ⟨interior K, isOpen_interior, mem_interior_iff_mem_nhds.mpr hpK,
    hcl.trans hKV, hK.of_isClosed_subset isClosed_closure hcl,
    hXK.isBounded.subset (image_mono interior_subset), max C 0 + 1, by positivity, ?_⟩
  intro y hy
  have hb := hC y (image_mono interior_subset hy)
  rw [Real.norm_eq_abs] at hb
  exact hb.trans (by linarith only [le_max_left C (0 : ℝ)])

end

lemma synchronized_det_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (d : E) (c : ℝ) (L : E →L[ℝ] ℝ) (ε : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : E →L[ℝ] E) (z : ℝ), |z| ≤ 1 →
      ‖D - (ContinuousLinearMap.id ℝ E + lineShiftGradientOperator d c (z • L))‖ ≤ ε →
      |D.det| ≤ C := by
  let T := lineShiftGradientOperator d c
  obtain ⟨C, hC, hb⟩ := exists_det_bound_of_norm (E := E)
    (ε + ‖ContinuousLinearMap.id ℝ E‖ + ‖T‖ * ‖L‖)
  refine ⟨C, hC, ?_⟩
  intro D z hz he
  apply hb D
  have hnorm : ‖T (z • L)‖ ≤ ‖T‖ * ‖L‖ := by
    apply (T.le_opNorm _).trans
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_right hz (norm_nonneg L)).trans_eq (one_mul _)) (norm_nonneg T)
  have hj := norm_add_le (ContinuousLinearMap.id ℝ E) (T (z • L))
  have ht : ‖D‖ ≤ ‖D - (ContinuousLinearMap.id ℝ E + T (z • L))‖ +
      ‖ContinuousLinearMap.id ℝ E + T (z • L)‖ := by
    simpa only [sub_add_cancel] using norm_add_le
      (D - (ContinuousLinearMap.id ℝ E + T (z • L)))
      (ContinuousLinearMap.id ℝ E + T (z • L))
  linarith only [hnorm, hj, ht, he]
end ScalarConductivity

end

end OAI
