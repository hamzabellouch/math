import Mathlib
import OAI.Analysis.Conductivity.Variational.MatrixFiniteLaminate
import OAI.Analysis.Conductivity.Variational.QuantitativeLocalTwoFieldSplit

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

def conjugateDiagonal (Q : Mat3) (α : DiagonalTriple) : Symmetric3 :=
  ⟨Q * Matrix.diagonal α * Qᵀ, by
    rw [Matrix.isHermitian_iff_isSymm]
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, Matrix.mul_assoc]⟩

lemma conjugateDiagonal_continuous (Q : Mat3) : Continuous (conjugateDiagonal Q) := by
  apply Continuous.subtype_mk
  exact continuous_const.matrix_mul (continuous_pi (fun i => continuous_pi (fun j => by
    by_cases hij : i = j
    · subst j; simpa only [Matrix.diagonal_apply_eq] using continuous_apply i
    · simpa only [Matrix.diagonal_apply_ne _ hij] using
        (continuous_const : Continuous (fun _ : DiagonalTriple => (0:ℝ)))))) |>.matrix_mul continuous_const

lemma conjugateDiagonal_spectral {Q : Mat3} (hQ : Q ∈ orthogonalFrames)
    {α : DiagonalTriple} {T : Set DiagonalTriple} (hα : α ∈ T) :
    conjugateDiagonal Q α ∈ spectralExtension T := ⟨Q, hQ, α, hα, rfl⟩

lemma stretched_preliminary (i : Fin 3) {A α : DiagonalTriple}
    (hq : preliminaryQ i A α ≠ 0) (hA : A i ≠ 0) :
    stretchedDiagonal i (preliminaryQ i A α) (preliminaryB i A α) = α := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [stretchedDiagonal, preliminaryB, preliminaryQ, hA]
  · simp [stretchedDiagonal, preliminaryB, hj, hq]

lemma continuousAt_stretchedDiagonal {i : Fin 3} {q : ℝ → ℝ} {D : ℝ → DiagonalTriple}
    {z : ℝ} (hq : ContinuousAt q z) (hD : ContinuousAt D z) (hn : q z ≠ 0) :
    ContinuousAt (fun t => stretchedDiagonal i (q t) (D t)) z := by
  apply continuousAt_pi.mpr; intro j
  have hj := continuousAt_pi.mp hD j
  by_cases hji : j = i
  · change ContinuousAt (fun y => if j = i then q y * D y j else D y j / q y) z
    simp only [ite_eq_left hji]
    exact hq.mul hj
  · change ContinuousAt (fun y => if j = i then q y * D y j else D y j / q y) z
    simp only [ite_eq_right hji]
    exact hj.div hq hn

lemma contDiffAt_stretchedDiagonal {i : Fin 3} {q : ℝ → ℝ} {D : ℝ → DiagonalTriple}
    {z : ℝ} {k : WithTop ℕ∞} (hq : ContDiffAt ℝ k q z) (hD : ContDiffAt ℝ k D z)
    (hn : q z ≠ 0) : ContDiffAt ℝ k (fun t => stretchedDiagonal i (q t) (D t)) z := by
  apply contDiffAt_pi.mpr; intro j
  have hj := contDiffAt_pi.mp hD j
  by_cases hji : j = i
  · change ContDiffAt ℝ k (fun y => if j = i then q y * D y j else D y j / q y) z
    simp only [ite_eq_left hji]
    exact hq.mul hj
  · change ContDiffAt ℝ k (fun y => if j = i then q y * D y j else D y j / q y) z
    simp only [ite_eq_right hji]
    exact hj.div hq hn

lemma conjugateDiagonal_contDiff (Q : Mat3) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun α : DiagonalTriple => (conjugateDiagonal Q α).val) := by
  rw [contDiff_iff_contDiffAt]; intro α
  apply contDiffAt_matrix_mul _ contDiffAt_const
  apply contDiffAt_matrix_mul contDiffAt_const
  apply contDiffAt_pi.mpr; intro i
  apply contDiffAt_pi.mpr; intro j
  by_cases hij : i = j
  · subst j; simpa only [Matrix.diagonal_apply_eq, id_eq] using
      (contDiffAt_pi.mp (contDiffAt_id (x := α)) i)
  · simpa only [Matrix.diagonal_apply_ne _ hij] using
      (contDiffAt_const : ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun _ : DiagonalTriple => (0:ℝ)) α)

theorem spectral_join_plan {a b : ℝ} (ha : 0 < a) {T : Set DiagonalTriple}
    (hT : ∀ α ∈ T, IsFiniteLaminate a b α)
    (i : Fin 3) {α β : DiagonalTriple} (hα : α ∈ T) (hβ : β ∈ T)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    {Q : Mat3} (hQ : Q ∈ orthogonalFrames) :
    let A := conjugateDiagonal Q (coordinateJoin i θ α β)
    ∃ (d : Coord3) (L : Coord3 →L[ℝ] ℝ) (B : Mat3) (η c m : ℝ)
      (C : ℝ → Symmetric3),
      L d = 1 ∧ B.IsSymm ∧ (∀ v, L (B *ᵥ v) = 0) ∧
      0 < η ∧ η < 1 ∧ 0 < m ∧
      (∀ z ∈ Icc (-η) (1-η), m ≤ 1+c*z) ∧
      (∀ z ∈ Icc (-η) (1-η), ContinuousAt C z) ∧
      (∀ z ∈ Icc (-η) (1-η), ContDiffAt ℝ (↑(⊤ : ℕ∞)) (fun t => (C t).val) z) ∧
      (∀ z ∈ Icc (-η) (1-η), 0 < (splitJacobian d L c z).det) ∧
      (∀ z ∈ Icc (-η) (1-η), (C z).val =
        (splitJacobian d L c z).det⁻¹ •
          (splitJacobian d L c z * (A.val + z • B) * (splitJacobian d L c z)ᵀ)) ∧
      (∀ z ∈ Icc (-η) (1-η), C z ∈ matrixFiniteLaminate a b) ∧
      C (-η) ∈ spectralExtension T ∧ C (1-η) ∈ spectralExtension T := by
  let A := coordinateJoin i θ α β
  let P := preliminaryB i A α
  let N := preliminaryB i A β
  let qp := preliminaryQ i A α
  let qm := preliminaryQ i A β
  let η := θ/qp
  have hαi : 0 < α i := ha.trans ((hT α hα).bounds ha i).1
  have hβi : 0 < β i := ha.trans ((hT β hβ).bounds ha i).1
  have hf : 0 < qp ∧ 0 < qm ∧ 0 < η ∧ 0 < (1-θ)/qm ∧
    η+(1-θ)/qm=1 ∧ η*qp+((1-θ)/qm)*qm=1 := by
    simpa [qp, qm, η, A, preliminaryQ, coordinateJoin] using
      preliminary_fractions hαi hβi hθ hθ1
  have hη1 : η < 1 := by linarith [hf.2.2.2.1, hf.2.2.2.2.1]
  let c := qp-qm
  let q : ℝ → ℝ := fun z => 1+c*z
  let D : ℝ → DiagonalTriple := fun z => A + z • (P-N)
  let C : ℝ → Symmetric3 := fun z => conjugateDiagonal Q (stretchedDiagonal i (q z) (D z))
  have hs (z : ℝ) :
      q z = (z+η)*qp+(1-(z+η))*qm ∧
      D z = (z+η) • P + (1-(z+η)) • N := by
    have hh := preliminary_segment i hαi hβi hθ hθ1 z
    refine ⟨?_, hh.1⟩
    change 1 + (qp-qm)*z = _
    have heq : 1+z*(qp-qm)=(z+η)*qp+(1-(z+η))*qm := hh.2.1
    linarith only [heq]
  have hq (z : ℝ) (hz : z ∈ Icc (-η) (1-η)) : min qp qm ≤ q z := by
    rw [(hs z).1]
    have ht : 0 ≤ z+η := by linarith [hz.1]
    have ht' : 0 ≤ 1-(z+η) := by linarith [hz.2]
    have h1 := mul_le_mul_of_nonneg_left (min_le_left qp qm) ht
    have h2 := mul_le_mul_of_nonneg_left (min_le_right qp qm) ht'
    nlinarith
  have hm : 0 < min qp qm := lt_min hf.1 hf.2.1
  have hqpos (z : ℝ) (hz : z ∈ Icc (-η) (1-η)) : 0 < q z := hm.trans_le (hq z hz)
  have hP : P i = N i := by simp [P, N, preliminaryB]
  refine ⟨rotatedDirection Q i, rotatedPhase Q i, Q * Matrix.diagonal (P-N) * Qᵀ,
    η, c, min qp qm, C, rotated_normalization hQ i, ?_,
    rotated_increment_annihilates hQ i hP, hf.2.2.1, hη1, hm, hq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.isHermitian_iff_isSymm.mp (conjugateDiagonal Q (P-N)).property
  · intro z hz
    exact (conjugateDiagonal_continuous Q).continuousAt.comp
      (continuousAt_stretchedDiagonal (continuous_const.add
        (continuous_const.mul continuous_id)).continuousAt
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt (hqpos z hz).ne')
  · intro z hz
    exact (conjugateDiagonal_contDiff Q).contDiffAt.comp z
      (contDiffAt_stretchedDiagonal (contDiffAt_const.add
        (contDiffAt_const.mul contDiffAt_id))
        (contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)) (hqpos z hz).ne')
  · intro z hz
    rw [splitJacobian_det _ _ (rotated_normalization hQ i)]
    exact hqpos z hz
  · intro z hz
    rw [splitJacobian_rotated hQ]
    change Q * Matrix.diagonal (stretchedDiagonal i (q z) (D z)) * Qᵀ = _
    have he : (conjugateDiagonal Q A).val + z • (Q * Matrix.diagonal (P-N) * Qᵀ) =
        Q * Matrix.diagonal (D z) * Qᵀ := by
      change Q * Matrix.diagonal A * Qᵀ + z • (Q * Matrix.diagonal (P-N) * Qᵀ) =
        Q * Matrix.diagonal (A + z • (P-N)) * Qᵀ
      have hd : Matrix.diagonal (A+z • (P-N)) =
          Matrix.diagonal A + z • Matrix.diagonal (P-N) := by
        ext j k
        by_cases hjk : j = k
        · subst k; simp
        · simp [hjk]
      rw [hd, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [he, conjugated_push hQ, normalStretch_push i (hqpos z hz).ne']
  · intro z hz
    have hz' : z ∈ Icc (-η) ((1-θ)/qm) := by
      constructor; exact hz.1; linarith [hz.2, hf.2.2.2.2.1]
    obtain ⟨_, w, hw, he⟩ := affine_synchronized_path i hαi hβi hθ hθ1 z hz'
    have hd : stretchedDiagonal i (q z) (D z) = coordinateJoin i w α β := by
      simpa only [q, c, mul_comm] using he
    change conjugateDiagonal Q _ ∈ spectralExtension _
    rw [hd]
    exact conjugateDiagonal_spectral hQ (.join i w hw.1 hw.2 (hT α hα) (hT β hβ))
  · have he := hs (-η)
    have eq : q (-η) = qm := by simpa using he.1
    have ed : D (-η) = N := by simpa using he.2
    change conjugateDiagonal Q (stretchedDiagonal i (q (-η)) (D (-η))) ∈ _
    rw [eq, ed, stretched_preliminary i hf.2.1.ne']
    · exact conjugateDiagonal_spectral hQ hβ
    · simpa [A, coordinateJoin] using (harmonic_parent_pos hαi hβi hθ hθ1).ne'
  · have he := hs (1-η)
    have eq : q (1-η) = qp := by simpa using he.1
    have ed : D (1-η) = P := by simpa using he.2
    change conjugateDiagonal Q (stretchedDiagonal i (q (1-η)) (D (1-η))) ∈ _
    rw [eq, ed, stretched_preliminary i hf.1.ne']
    · exact conjugateDiagonal_spectral hQ hα
    · simpa [A, coordinateJoin] using (harmonic_parent_pos hαi hβi hθ hθ1).ne'

end ScalarConductivity

end

end OAI
