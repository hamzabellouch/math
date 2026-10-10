import Mathlib
import OAI.Analysis.Conductivity.Variational.VariationalDN

namespace OAI

noncomputable section

namespace ScalarConductivity

open MeasureTheory
open scoped ENNReal
section
def preliminaryQ (i : Fin 3) (A α : DiagonalTriple) : ℝ := α i / A i

def preliminaryB (i : Fin 3) (A α : DiagonalTriple) : DiagonalTriple :=
  fun j => if j = i then A i else preliminaryQ i A α * α j

lemma harmonic_parent_pos {x y θ : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hθ : 0 < θ) (hθ' : θ < 1) : 0 < (θ / x + (1 - θ) / y)⁻¹ := by
  exact inv_pos.mpr (add_pos (div_pos hθ hx) (div_pos (sub_pos.mpr hθ') hy))

theorem preliminary_fractions {x y θ : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hθ : 0 < θ) (hθ' : θ < 1) :
    let A := (θ / x + (1 - θ) / y)⁻¹
    let q_plus := x / A
    let q_minus := y / A
    let η_plus := θ / q_plus
    let η_minus := (1 - θ) / q_minus
    0 < q_plus ∧ 0 < q_minus ∧ 0 < η_plus ∧ 0 < η_minus ∧
      η_plus + η_minus = 1 ∧ η_plus * q_plus + η_minus * q_minus = 1 := by
  dsimp only
  have hA := harmonic_parent_pos hx hy hθ hθ'
  have hq_plus := div_pos hx hA
  have hq_minus := div_pos hy hA
  refine ⟨hq_plus, hq_minus, div_pos hθ hq_plus, div_pos (sub_pos.mpr hθ') hq_minus, ?_, ?_⟩
  · have hd : θ / x + (1 - θ) / y ≠ 0 := (inv_pos.mp hA).ne'
    rw [div_div_eq_mul_div, div_div_eq_mul_div]
    calc
      θ * (θ / x + (1 - θ) / y)⁻¹ / x +
          (1 - θ) * (θ / x + (1 - θ) / y)⁻¹ / y =
          (θ / x + (1 - θ) / y)⁻¹ * (θ / x + (1 - θ) / y) := by ring
      _ = 1 := inv_mul_cancel₀ hd
  · rw [div_mul_cancel₀ _ hq_plus.ne', div_mul_cancel₀ _ hq_minus.ne']
    ring

theorem preliminary_matrix_mean (i : Fin 3) {α β : DiagonalTriple} {θ : ℝ}
    (hα : 0 < α i) (hβ : 0 < β i) (hθ : 0 < θ) (hθ' : θ < 1) :
    let A := coordinateJoin i θ α β
    let η_plus := θ / preliminaryQ i A α
    let η_minus := (1 - θ) / preliminaryQ i A β
    η_plus • preliminaryB i A α + η_minus • preliminaryB i A β = A := by
  dsimp only
  let A := coordinateJoin i θ α β
  have hAi : 0 < A i := by simpa [A, coordinateJoin] using harmonic_parent_pos hα hβ hθ hθ'
  have hqα : preliminaryQ i A α ≠ 0 := (div_pos hα hAi).ne'
  have hqβ : preliminaryQ i A β ≠ 0 := (div_pos hβ hAi).ne'
  have hm : θ / preliminaryQ i A α + (1 - θ) / preliminaryQ i A β = 1 := by
    simpa [preliminaryQ, A, coordinateJoin] using
      (preliminary_fractions hα hβ hθ hθ').2.2.2.2.1
  ext j
  change (θ / preliminaryQ i A α) * preliminaryB i A α j +
    ((1 - θ) / preliminaryQ i A β) * preliminaryB i A β j = A j
  by_cases hj : j = i
  · simp only [preliminaryB, ite_eq_left hj]
    rw [← add_mul, hm, one_mul, hj]
  · simp only [preliminaryB, ite_eq_right hj]
    rw [← mul_assoc, div_mul_cancel₀ _ hqα, ← mul_assoc, div_mul_cancel₀ _ hqβ]
    exact (ite_eq_right hj).symm

def stretchedDiagonal (i : Fin 3) (q : ℝ) (B : DiagonalTriple) : DiagonalTriple :=
  fun j => if j = i then q * B j else B j / q

theorem synchronized_path_is_join (i : Fin 3) {α β : DiagonalTriple} {θ τ : ℝ}
    (hα : 0 < α i) (hβ : 0 < β i) (hθ : 0 < θ) (hθ' : θ < 1)
    (hτ : 0 ≤ τ) (hτ' : τ ≤ 1) :
    let A := coordinateJoin i θ α β
    let q_plus := preliminaryQ i A α
    let q_minus := preliminaryQ i A β
    let q := τ * q_plus + (1 - τ) * q_minus
    let B := τ • preliminaryB i A α + (1 - τ) • preliminaryB i A β
    let w := τ * q_plus / q
    0 < q ∧ 0 ≤ w ∧ w ≤ 1 ∧
      stretchedDiagonal i q B = coordinateJoin i w α β := by
  dsimp only
  let A := coordinateJoin i θ α β
  let q_plus := preliminaryQ i A α
  let q_minus := preliminaryQ i A β
  let q := τ * q_plus + (1 - τ) * q_minus
  let w := τ * q_plus / q
  have hAi : 0 < A i := by simpa [A, coordinateJoin] using harmonic_parent_pos hα hβ hθ hθ'
  have hqp : 0 < q_plus := div_pos hα hAi
  have hqm : 0 < q_minus := div_pos hβ hAi
  have hq : 0 < q := by
    rcases eq_or_lt_of_le hτ with rfl | hτ
    · simpa [q] using hqm
    · exact add_pos_of_pos_of_nonneg (mul_pos hτ hqp)
        (mul_nonneg (sub_nonneg.mpr hτ') hqm.le)
  have hwp : 0 ≤ w := div_nonneg (mul_nonneg hτ hqp.le) hq.le
  have hwm : w ≤ 1 := (div_le_one hq).mpr (by dsimp [q]; nlinarith)
  refine ⟨hq, hwp, hwm, ?_⟩
  have hw : 1 - w = (1 - τ) * q_minus / q := by dsimp [w]; field_simp; dsimp [q]; ring
  ext j
  change stretchedDiagonal i q (τ • preliminaryB i A α +
    (1 - τ) • preliminaryB i A β) j = coordinateJoin i w α β j
  by_cases hj : j = i
  · subst j
    simp only [stretchedDiagonal, coordinateJoin, preliminaryB, ite_true, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [hw]
    have he : w / α i + ((1 - τ) * q_minus / q) / β i = (q * A i)⁻¹ := by
      dsimp [w, q_plus, q_minus, preliminaryQ]
      field_simp
      ring
    rw [he, inv_inv]
    ring
  · simp only [stretchedDiagonal, coordinateJoin, preliminaryB, ite_eq_right hj,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hw]
    dsimp [w, q_plus, q_minus]
    ring

end
open Matrix Filter Topology
abbrev Mat3 := Matrix (Fin 3) (Fin 3) ℝ

def orthogonalFrames : Set Mat3 := {Q | Qᵀ * Q = 1 ∧ Q * Qᵀ = 1}

lemma isClosed_orthogonalFrames : IsClosed orthogonalFrames := by
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq (by fun_prop) continuous_const

lemma orthogonalFrames_entry_bound {Q : Mat3} (hQ : Q ∈ orthogonalFrames) (i j : Fin 3) :
    |Q i j| ≤ 1 := by
  have hsum : ∑ k, Q i k ^ 2 = 1 := by
    have hh := congrArg (fun A : Mat3 => A i i) hQ.2
    simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hh
  have hh : Q i j ^ 2 ≤ ∑ k, Q i k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (Q i k)) (Finset.mem_univ j)
  rw [hsum] at hh
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

lemma isCompact_orthogonalFrames : IsCompact orthogonalFrames := by
  apply (isCompact_Icc : IsCompact (Set.Icc (-1 : ℝ) 1)).matrix.of_isClosed_subset
    isClosed_orthogonalFrames
  intro Q hQ i j
  exact abs_le.mp (orthogonalFrames_entry_bound hQ i j)

lemma roots_charpoly_diagonal (α : Fin 3 → ℝ) :
    (diagonal α).charpoly.roots = Finset.univ.val.map α := by
  rw [Matrix.charpoly_diagonal]
  simpa only [Multiset.map_map, Function.comp_def, Finset.prod] using
    (Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map α))

lemma same_multiset_permutation {α β : Fin 3 → ℝ}
    (h : Finset.univ.val.map α = Finset.univ.val.map β) :
    ∃ e : Equiv.Perm (Fin 3), ∀ i, β (e i) = α i := by
  classical
  have hc (c : ℝ) : Fintype.card { i // α i = c } = Fintype.card { i // β i = c } := by
    have hd := congrArg (Multiset.count c) h
    simp only [Multiset.count_map] at hd
    simpa only [Fintype.card_subtype, Finset.card, Finset.filter_val, eq_comm] using hd
  let ef (c : ℝ) := Fintype.equivOfCardEq (hc c)
  exact ⟨Equiv.ofFiberEquiv ef, Equiv.ofFiberEquiv_map ef⟩

lemma diagonalizations_permute {A : Mat3} {α β : Fin 3 → ℝ} {Q R : Mat3}
    (hQ : Q ∈ orthogonalFrames) (hR : R ∈ orthogonalFrames)
    (hA : A = Q * diagonal α * Qᵀ) (hB : A = R * diagonal β * Rᵀ) :
    ∃ e : Equiv.Perm (Fin 3), ∀ i, β (e i) = α i := by
  have ha : A.charpoly = (diagonal α).charpoly := by
    rw [hA, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hQ.1, Matrix.one_mul]
  have hb : A.charpoly = (diagonal β).charpoly := by
    rw [hB, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hR.1, Matrix.one_mul]
  apply same_multiset_permutation
  rw [← roots_charpoly_diagonal, ← roots_charpoly_diagonal, ← ha, ← hb]

lemma exists_orthogonal_diagonalization {A : Mat3} (hA : A.IsHermitian) :
    ∃ Q ∈ orthogonalFrames, ∃ α : Fin 3 → ℝ, A = Q * diagonal α * Qᵀ := by
  refine ⟨hA.eigenvectorUnitary, ⟨?_, ?_⟩, hA.eigenvalues, ?_⟩
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Unitary.coe_star_mul_self hA.eigenvectorUnitary
  · simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Unitary.coe_star] using Unitary.coe_mul_star_self hA.eigenvectorUnitary
  · simpa only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id,
      Function.id_comp] using hA.spectral_theorem

lemma diagonalization_pullback {A Q : Mat3} {α : Fin 3 → ℝ}
    (hQ : Q ∈ orthogonalFrames) (hA : A = Q * diagonal α * Qᵀ) :
    Qᵀ * A * Q = diagonal α := by
  rw [hA]
  calc
    Qᵀ * (Q * diagonal α * Qᵀ) * Q = (Qᵀ * Q) * diagonal α * (Qᵀ * Q) := by
      noncomm_ring
    _ = diagonal α := by rw [hQ.1, Matrix.one_mul, Matrix.mul_one]

abbrev Symmetric3 := { A : Mat3 // A.IsHermitian }

def spectralExtension (U : Set (Fin 3 → ℝ)) : Set Symmetric3 :=
  { A | ∃ Q ∈ orthogonalFrames, ∃ α ∈ U, A.val = Q * diagonal α * Qᵀ }

lemma spectralExtension_rep_mem {U : Set (Fin 3 → ℝ)}
    (hperm : ∀ α ∈ U, ∀ e : Equiv.Perm (Fin 3), α ∘ e ∈ U)
    {A : Symmetric3} (hA : A ∈ spectralExtension U) {Q : Mat3} {α : Fin 3 → ℝ}
    (hQ : Q ∈ orthogonalFrames) (hrep : A.val = Q * diagonal α * Qᵀ) : α ∈ U := by
  obtain ⟨R, hR, β, hβ, hβrep⟩ := hA
  obtain ⟨e, he⟩ := diagonalizations_permute hR hQ hβrep hrep
  have h := hperm β hβ e.symm
  convert h using 1
  ext i
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using (he (e.symm i))

lemma continuous_diagonal_pullback :
    Continuous (fun p : Mat3 × Mat3 => Matrix.diag (p.1ᵀ * p.2 * p.1)) :=
  ((continuous_fst.matrix_transpose.matrix_mul continuous_snd).matrix_mul
    continuous_fst).matrix_diag

lemma continuous_diagonal_pushforward :
    Continuous (fun p : Mat3 × (Fin 3 → ℝ) => p.1 * diagonal p.2 * p.1ᵀ) :=
  (continuous_fst.matrix_mul continuous_snd.matrix_diagonal).matrix_mul
    continuous_fst.matrix_transpose

lemma tendsto_diagonal_pullback {Qn An : ℕ → Mat3} {Q A : Mat3}
    {αn : ℕ → Fin 3 → ℝ} (hQn : ∀ n, Qn n ∈ orthogonalFrames)
    (hrepn : ∀ n, An n = Qn n * diagonal (αn n) * (Qn n)ᵀ)
    (hQ : Tendsto Qn atTop (𝓝 Q)) (hA : Tendsto An atTop (𝓝 A)) :
    Tendsto αn atTop (𝓝 (Matrix.diag (Qᵀ * A * Q))) := by
  have hh := continuous_diagonal_pullback.continuousAt.tendsto.comp (hQ.prodMk_nhds hA)
  change Tendsto (fun n => Matrix.diag ((Qn n)ᵀ * An n * Qn n)) atTop
    (𝓝 (Matrix.diag (Qᵀ * A * Q))) at hh
  simpa only [diagonalization_pullback (hQn _) (hrepn _), Matrix.diag_diagonal] using hh

lemma limit_diagonal_rep {Qn An : ℕ → Mat3} {Q A : Mat3}
    {αn : ℕ → Fin 3 → ℝ} {α : Fin 3 → ℝ}
    (hrepn : ∀ n, An n = Qn n * diagonal (αn n) * (Qn n)ᵀ)
    (hQ : Tendsto Qn atTop (𝓝 Q)) (hA : Tendsto An atTop (𝓝 A))
    (hα : Tendsto αn atTop (𝓝 α)) : A = Q * diagonal α * Qᵀ := by
  have hh := continuous_diagonal_pushforward.continuousAt.tendsto.comp (hQ.prodMk_nhds hα)
  change Tendsto (fun n => Qn n * diagonal (αn n) * (Qn n)ᵀ) atTop
    (𝓝 (Q * diagonal α * Qᵀ)) at hh
  simp only [← hrepn] at hh
  exact tendsto_nhds_unique hA hh

theorem isOpen_spectralExtension {U : Set (Fin 3 → ℝ)} (hU : IsOpen U)
    (hperm : ∀ α ∈ U, ∀ e : Equiv.Perm (Fin 3), α ∘ e ∈ U) :
    IsOpen (spectralExtension U) := by
  let : FirstCountableTopology Mat3 := inferInstanceAs
    (FirstCountableTopology (Fin 3 → Fin 3 → ℝ))
  suffices hc : IsClosed (spectralExtension U)ᶜ by
    simpa only [compl_compl] using hc.isOpen_compl
  apply IsSeqClosed.isClosed
  intro An A hAn hlim hA
  choose Qn hQn αn hrepn using fun n => exists_orthogonal_diagonalization (An n).property
  obtain ⟨Q, hQ, φ, hφ, hQlim⟩ := isCompact_orthogonalFrames.tendsto_subseq hQn
  have hAlim : Tendsto (fun n => (An (φ n)).val) atTop (𝓝 A.val) :=
    (continuous_subtype_val.tendsto A).comp (hlim.comp hφ.tendsto_atTop)
  let α := Matrix.diag (Qᵀ * A.val * Q)
  have hαlim : Tendsto (fun n => αn (φ n)) atTop (𝓝 α) :=
    tendsto_diagonal_pullback (fun n => hQn (φ n)) (fun n => hrepn (φ n)) hQlim hAlim
  have hrep : A.val = Q * diagonal α * Qᵀ :=
    limit_diagonal_rep (fun n => hrepn (φ n)) hQlim hAlim hαlim
  have hα : α ∈ U := spectralExtension_rep_mem hperm hA hQ hrep
  have hev : ∀ᶠ n in atTop, αn (φ n) ∈ U := hαlim (hU.mem_nhds hα)
  obtain ⟨n, hn⟩ := hev.exists
  exact hAn (φ n) ⟨Qn (φ n), hQn (φ n), αn (φ n), hn, hrepn (φ n)⟩

end ScalarConductivity

end

end OAI
