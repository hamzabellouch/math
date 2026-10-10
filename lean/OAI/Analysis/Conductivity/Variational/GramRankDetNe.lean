import Mathlib
import OAI.Analysis.Conductivity.Variational.CrossingHxx

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
open Matrix Set Filter Topology
open scoped Matrix.Norms.Elementwise

lemma gram_rank_of_det_ne_zero {m : Type*} [Fintype m] [DecidableEq m]
    (E : Matrix (Fin 3) m ℝ) (h : (Eᵀ * E).det ≠ 0) : LinearIndependent ℝ E.col := by
  apply Matrix.mulVec_injective_iff.mp
  intro v w hvw
  apply Matrix.mulVec_injective_iff.mpr (Matrix.linearIndependent_cols_of_det_ne_zero h)
  simpa only [Matrix.mulVec_mulVec] using congrArg Eᵀ.mulVec hvw

lemma repairPushed_path_stability
    {P m : Type*} [TopologicalSpace P] [Fintype m] [DecidableEq m]
    {K : Set P} (hK : IsCompact K)
    (A : P → Symmetric3) (J : P → Mat3) (E F : P → Matrix (Fin 3) m ℝ)
    (hA : ∀ p ∈ K, ContinuousAt A p) (hJ : ∀ p ∈ K, ContinuousAt J p)
    (hE : ∀ p ∈ K, ContinuousAt E p) (hF : ∀ p ∈ K, ContinuousAt F p)
    (hdet : ∀ p ∈ K, 0 < (J p).det) (hrank : ∀ p ∈ K, LinearIndependent ℝ (E p).col)
    {U : Set Symmetric3} (hU : IsOpen U)
    (hmem : ∀ p ∈ K, repairPushed (A p) (J p) (E p) (F p) ∈ U) :
    ∃ O : Set P, IsOpen O ∧ K ⊆ O ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ p ∈ O, ∀ (dJ : Mat3) (dE dF : Matrix (Fin 3) m ℝ),
        ‖(dJ, dE, dF)‖ < ε →
          0 < (J p + dJ).det ∧ LinearIndependent ℝ (E p + dE).col ∧
          repairPushed (A p) (J p + dJ) (E p + dE) (F p + dF) ∈ U := by
  let V := Mat3 × Matrix (Fin 3) m ℝ × Matrix (Fin 3) m ℝ
  let a : P × V → Symmetric3 := fun q => A q.1
  let j : P × V → Mat3 := fun q => J q.1 + q.2.1
  let e : P × V → Matrix (Fin 3) m ℝ := fun q => E q.1 + q.2.2.1
  let f : P × V → Matrix (Fin 3) m ℝ := fun q => F q.1 + q.2.2.2
  let T : P × V → Symmetric3 × ℝ × ℝ := fun q =>
    (repairPushed (a q) (j q) (e q) (f q), (j q).det, ((e q)ᵀ * e q).det)
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
    exact (continuousAt_repairPushed a j e f ha hj he hf
      (hj0 ▸ (hdet p hp).ne') (he0 ▸ hrank p hp)).prodMk
        ((hc.continuousAt.comp hj).prodMk
          (hg.continuousAt.comp (matrix_mul_contAt (matrix_transpose_contAt he) he)))
  let W : Set (Symmetric3 × ℝ × ℝ) := U ×ˢ Ioi 0 ×ˢ ({0} : Set ℝ)ᶜ
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

end ScalarConductivity

end

end OAI
