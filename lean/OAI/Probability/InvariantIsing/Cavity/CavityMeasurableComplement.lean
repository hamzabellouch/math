import OAI.Probability.InvariantIsing.Cavity.CavityCompletion
import OAI.Probability.InvariantIsing.Cavity.CavityComplement
import OAI.Probability.InvariantIsing.Cavity.CavityFrameMeasurable

namespace OAI

/-! A global measurable completion of the cavity columns. The rule first
tries the prescribed limiting frame and otherwise uses a fixed dense
sequence. Near the limit it agrees with the continuous local rule. -/

noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped Matrix Topology MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

def cavityComplementCandidate {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) : ℕ → Matrix (Fin (d + n)) (Fin d) ℝ
  | 0 => B₀
  | k + 1 => denseSeq (Fin (d + n) → Fin d → ℝ) k

def cavityGoodCandidate {d n : ℕ} (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (k : ℕ) : Prop :=
  0 < ((cavityRawComplement E (cavityComplementCandidate B₀ k)).transpose *
    cavityRawComplement E (cavityComplementCandidate B₀ k)).det

lemma continuous_cavityRawComplement {r d n : ℕ}
    (B : Matrix (Fin r) (Fin d) ℝ) :
    Continuous (fun E : Matrix (Fin r) (Fin n) ℝ => cavityRawComplement E B) :=
  (continuous_const.sub (continuous_id.matrix_mul continuous_id.matrix_transpose)).matrix_mul
    continuous_const

lemma measurableSet_cavityGoodCandidate {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (k : ℕ) :
    MeasurableSet {E | cavityGoodCandidate B₀ E k} := by
  have h := continuous_cavityRawComplement (n := n) (cavityComplementCandidate B₀ k)
  exact isOpen_lt continuous_const ((h.matrix_transpose.matrix_mul h).matrix_det) |>.measurableSet

lemma cavityGoodCandidate_exists {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hE : E.transpose * E = 1) :
    ∃ k, cavityGoodCandidate B₀ E k := by
  obtain ⟨B, hB, hEB⟩ := cavity_frame_completion E hE
  let s : Set (Matrix (Fin (d + n)) (Fin d) ℝ) :=
    {A | 0 < ((cavityRawComplement E A).transpose * cavityRawComplement E A).det}
  have hraw : Continuous (fun A : Matrix (Fin (d + n)) (Fin d) ℝ => cavityRawComplement E A) :=
    continuous_const.matrix_mul continuous_id
  have hs : IsOpen s := isOpen_lt continuous_const ((hraw.matrix_transpose.matrix_mul hraw).matrix_det)
  have hBmem : B ∈ s := by
    change 0 < ((cavityRawComplement E B).transpose * cavityRawComplement E B).det
    rw [cavityRawComplement_eq E B hEB, hB, Matrix.det_one]
    norm_num
  obtain ⟨k, hk⟩ := (denseRange_denseSeq (Fin (d + n) → Fin d → ℝ)).exists_mem_open hs ⟨B, hBmem⟩
  exact ⟨k + 1, hk⟩

def cavityComplementChoicePredicate {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (k : ℕ) : Prop :=
  if k = 0 then ¬∃ j, cavityGoodCandidate B₀ E j else cavityGoodCandidate B₀ E (k - 1)

lemma cavityComplementChoice_exists {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) :
    ∃ k, cavityComplementChoicePredicate B₀ E k := by
  classical
  by_cases h : ∃ j, cavityGoodCandidate B₀ E j
  · obtain ⟨j, hj⟩ := h
    exact ⟨j + 1, by simpa [cavityComplementChoicePredicate] using hj⟩
  · exact ⟨0, by simpa [cavityComplementChoicePredicate] using h⟩

def cavitySelectedComplement {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) : Matrix (Fin (d + n)) (Fin d) ℝ :=
  by classical exact cavityComplement E (cavityComplementCandidate B₀
    (Nat.find (cavityComplementChoice_exists B₀ E) - 1))

lemma measurable_cavitySelectedComplement {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) : Measurable (cavitySelectedComplement B₀) := by
  classical
  refine Measurable.find (p := fun k E => cavityComplementChoicePredicate B₀ E k)
    (f := fun k E => cavityComplement E (cavityComplementCandidate B₀ (k - 1)))
    ?_ ?_ (cavityComplementChoice_exists B₀)
  · intro k
    exact (measurable_cavityNormalizeFrame _ _).comp
      (continuous_cavityRawComplement (cavityComplementCandidate B₀ (k - 1))).measurable
  · intro k
    by_cases hk : k = 0
    · subst k
      have he : {E | cavityComplementChoicePredicate B₀ E 0} =
          (⋃ j, {E | cavityGoodCandidate B₀ E j})ᶜ := by
        ext E
        simp [cavityComplementChoicePredicate]
      rw [he]
      exact (MeasurableSet.iUnion (fun j => measurableSet_cavityGoodCandidate B₀ j)).compl
    · simpa only [cavityComplementChoicePredicate, ite_eq_right hk] using
        measurableSet_cavityGoodCandidate B₀ (k - 1)

lemma cavitySelectedComplement_gram {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hE : E.transpose * E = 1) :
    (cavitySelectedComplement B₀ E).transpose * cavitySelectedComplement B₀ E = 1 := by
  classical
  have he := cavityGoodCandidate_exists B₀ E hE
  have hs := Nat.find_spec (cavityComplementChoice_exists B₀ E)
  have hn : Nat.find (cavityComplementChoice_exists B₀ E) ≠ 0 := by
    intro h
    simp only [cavityComplementChoicePredicate, h, ite_true] at hs
    exact hs he
  have hg : cavityGoodCandidate B₀ E (Nat.find (cavityComplementChoice_exists B₀ E) - 1) := by
    simpa only [cavityComplementChoicePredicate, ite_eq_right hn] using hs
  apply cavityComplement_gram
  apply cavity_posDef_of_posSemidef_det_ne_zero
  · simpa using Matrix.posSemidef_conjTranspose_mul_self
      (cavityRawComplement E (cavityComplementCandidate B₀
        (Nat.find (cavityComplementChoice_exists B₀ E) - 1)))
  · exact hg.ne'

lemma cavitySelectedComplement_orthogonal {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hE : E.transpose * E = 1) :
    E.transpose * cavitySelectedComplement B₀ E = 0 :=
  cavityComplement_orthogonal E _ hE

lemma cavitySelectedComplement_eq_local {d n : ℕ}
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ)
    (E : Matrix (Fin (d + n)) (Fin n) ℝ) (hg : cavityGoodCandidate B₀ E 0) :
    cavitySelectedComplement B₀ E = cavityComplement E B₀ := by
  classical
  have hp : cavityComplementChoicePredicate B₀ E 1 := by
    simpa only [cavityComplementChoicePredicate, one_ne_zero, ite_false, Nat.sub_self] using hg
  have hs := Nat.find_spec (cavityComplementChoice_exists B₀ E)
  have hle := Nat.find_le (h := cavityComplementChoice_exists B₀ E) hp
  have hn : Nat.find (cavityComplementChoice_exists B₀ E) ≠ 0 := by
    intro h
    simp only [cavityComplementChoicePredicate, h, ite_true] at hs
    exact hs ⟨0, hg⟩
  have heq : Nat.find (cavityComplementChoice_exists B₀ E) = 1 := by omega
  simp only [cavitySelectedComplement, heq, Nat.sub_self, cavityComplementCandidate]

theorem cavitySelectedComplement_tendsto {d n : ℕ}
    (E : ℕ → Matrix (Fin (d + n)) (Fin n) ℝ)
    (E₀ : Matrix (Fin (d + n)) (Fin n) ℝ)
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (hEB : E₀.transpose * B₀ = 0) (hE : Tendsto E atTop (𝓝 E₀)) :
    Tendsto (fun k => cavitySelectedComplement B₀ (E k)) atTop (𝓝 B₀) := by
  have hraw := continuous_cavityRawComplement (n := n) B₀
  have hdet := ((hraw.matrix_transpose.matrix_mul hraw).matrix_det).tendsto E₀ |>.comp hE
  have hdet₀ : ((cavityRawComplement E₀ B₀).transpose *
      cavityRawComplement E₀ B₀).det = 1 := by
    rw [cavityRawComplement_eq E₀ B₀ hEB, hB₀, Matrix.det_one]
  rw [hdet₀] at hdet
  have hevent : ∀ᶠ k in atTop, cavityGoodCandidate B₀ (E k) 0 :=
    hdet.eventually (Ioi_mem_nhds zero_lt_one)
  apply (cavityComplement_tendsto E E₀ B₀ hB₀ hEB hE).congr'
  filter_upwards [hevent] with k hk
  exact (cavitySelectedComplement_eq_local B₀ (E k) hk).symm

lemma cavitySelectedComplement_at_limit {d n : ℕ}
    (E₀ : Matrix (Fin (d + n)) (Fin n) ℝ)
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (hEB : E₀.transpose * B₀ = 0) : cavitySelectedComplement B₀ E₀ = B₀ := by
  have hg : cavityGoodCandidate B₀ E₀ 0 := by
    change 0 < ((cavityRawComplement E₀ B₀).transpose * cavityRawComplement E₀ B₀).det
    rw [cavityRawComplement_eq E₀ B₀ hEB, hB₀, Matrix.det_one]
    norm_num
  rw [cavitySelectedComplement_eq_local B₀ E₀ hg, cavityComplement,
    cavityRawComplement_eq E₀ B₀ hEB, cavityNormalizeFrame, hB₀,
    CFC.sqrt_one, inv_one, Matrix.mul_one]

lemma cavitySelectedComplement_continuousAt {d n : ℕ}
    (E₀ : Matrix (Fin (d + n)) (Fin n) ℝ)
    (B₀ : Matrix (Fin (d + n)) (Fin d) ℝ) (hB₀ : B₀.transpose * B₀ = 1)
    (hEB : E₀.transpose * B₀ = 0) : ContinuousAt (cavitySelectedComplement B₀) E₀ := by
  let : FirstCountableTopology (Matrix (Fin (d + n)) (Fin n) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin (d + n) → Fin n → ℝ))
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro E hE
  rw [cavitySelectedComplement_at_limit E₀ B₀ hB₀ hEB]
  exact cavitySelectedComplement_tendsto E E₀ B₀ hB₀ hEB hE

end InvariantIsing

end

end OAI
