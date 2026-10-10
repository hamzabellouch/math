import OAI.Analysis.KadisonKastler.RegularTensorGap
import OAI.Analysis.KadisonKastler.GraphRowApproximation
import OAI.Analysis.KadisonKastler.CompleteConjugation
import OAI.Analysis.KadisonKastler.AmenableEmbedding

namespace OAI

/-! # Matrix unit-ball proximity and graph row estimates

The cb distance supplies a separate approximant at each matrix level.
No linear selection of those approximants is assumed.
-/

namespace KadisonKastler

open scoped WithCStarModule InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- One direction of matrix unit-ball proximity, uniformly in the matrix size. -/
def MatrixNearInclusion (M N : VonNeumannAlgebra H) (γ : ℝ) : Prop :=
  ∀ (n : ℕ) (X : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H)),
    (∀ i j, X i j ∈ M) → ‖X‖ ≤ 1 →
    ∃ Y : CStarMatrix (Fin n) (Fin n) (H →L[ℂ] H),
      (∀ i j, Y i j ∈ N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ γ

namespace MatrixNearInclusion

variable {M N : VonNeumannAlgebra H} {γ η : ℝ}

protected theorem mono (h : MatrixNearInclusion M N γ) (hγη : γ ≤ η) :
    MatrixNearInclusion M N η := by
  intro n X hX hn
  obtain ⟨Y, hY, hYn, hclose⟩ := h n X hX hn
  exact ⟨Y, hY, hYn, hclose.trans hγη⟩

local instance matrixNearOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance matrixNearStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The choice of finite index set does not affect the proximity bound. -/
theorem square (h : MatrixNearInclusion M N γ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (X : CStarMatrix ι ι (H →L[ℂ] H))
    (hX : ∀ i j, X i j ∈ M) (hn : ‖X‖ ≤ 1) :
    ∃ Y : CStarMatrix ι ι (H →L[ℂ] H),
      (∀ i j, Y i j ∈ N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ γ := by
  let e := CStarMatrix.reindexₐ ℂ (H →L[ℂ] H) (Fintype.equivFin ι)
  have he (T : CStarMatrix ι ι (H →L[ℂ] H)) : ‖e T‖ = ‖T‖ :=
    NonUnitalStarAlgHom.norm_map e.toStarAlgHom e.injective T
  have hes (T : CStarMatrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι))
      (H →L[ℂ] H)) : ‖e.symm T‖ = ‖T‖ :=
    NonUnitalStarAlgHom.norm_map e.symm.toStarAlgHom e.symm.injective T
  obtain ⟨Y, hY, hYn, hc⟩ := h _ (e X) (fun i j => hX _ _) (by rwa [he])
  refine ⟨e.symm Y, (fun i j => hY _ _), (hes Y).le.trans hYn, ?_⟩
  have hx : X = e.symm (e X) := (e.symm_apply_apply X).symm
  rw [hx, ← map_sub, hes]
  exact hc

private def rectangularCut {m n : Type*} [Fintype m] [Fintype n]
    (Y : CStarMatrix (m ⊕ n) (m ⊕ n) (H →L[ℂ] H)) :
    CStarMatrix m n (H →L[ℂ] H) := fun i j => Y (Sum.inl i) (Sum.inr j)

private def moduleRestrictRight {A : Type*} {m n : Type*} [CStarAlgebra A]
    [Fintype m] [Fintype n] (x : C⋆ᵐᵒᵈ(A, (m ⊕ n) → A)) : C⋆ᵐᵒᵈ(A, n → A) :=
  (WithCStarModule.equiv _ _).symm (fun j => x (Sum.inr j))

private theorem norm_moduleRestrictRight_le {m n : Type*} [Fintype m] [Fintype n]
    (x : C⋆ᵐᵒᵈ((H →L[ℂ] H), (m ⊕ n) → (H →L[ℂ] H))) :
    ‖moduleRestrictRight x‖ ≤ ‖x‖ := by
  simp only [WithCStarModule.pi_norm, moduleRestrictRight,
    WithCStarModule.equiv_symm_pi_apply, Fintype.sum_sum_type]
  apply Real.sqrt_le_sqrt
  apply CStarAlgebra.norm_le_norm_of_le_of_nonneg
  · exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ =>
      CStarModule.inner_self_nonneg)
  · exact Finset.sum_nonneg fun i _ => CStarModule.inner_self_nonneg

private theorem norm_rectangularCut_le {m n : Type*} [Fintype m] [Fintype n]
    (Y : CStarMatrix (m ⊕ n) (m ⊕ n) (H →L[ℂ] H)) :
    ‖rectangularCut Y‖ ≤ ‖Y‖ := by
  change ‖CStarMatrix.toCLM (rectangularCut Y)‖ ≤ ‖Y‖
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  have he : CStarMatrix.toCLM (rectangularCut Y) x =
      moduleRestrictRight (CStarMatrix.toCLM Y (moduleExtendLeft (n := n) x)) := by
    ext j
    simp [CStarMatrix.toCLM_apply_eq_sum, rectangularCut, moduleRestrictRight,
      moduleExtendLeft, Fintype.sum_sum_type, Sum.elim]
  rw [he]
  exact (norm_moduleRestrictRight_le _).trans (by
    simpa only [norm_moduleExtendLeft, ← CStarMatrix.norm_def] using
      ContinuousLinearMap.le_opNorm (CStarMatrix.toCLM Y) (moduleExtendLeft (n := n) x))

/-- Compression of the square approximant gives rectangular unit-ball proximity. -/
theorem rectangular (h : MatrixNearInclusion M N γ) {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (X : CStarMatrix m n (H →L[ℂ] H)) (hX : ∀ i j, X i j ∈ M) (hn : ‖X‖ ≤ 1) :
    ∃ Y : CStarMatrix m n (H →L[ℂ] H),
      (∀ i j, Y i j ∈ N) ∧ ‖Y‖ ≤ 1 ∧ ‖X - Y‖ ≤ γ := by
  obtain ⟨Y, hY, hYn, hc⟩ := h.square (rectangularCorner X)
    (by intro i j; cases i <;> cases j <;> simp_all [rectangularCorner])
    (by rwa [norm_rectangularCorner])
  refine ⟨rectangularCut Y, (fun i j => hY _ _), (norm_rectangularCut_le Y).trans hYn, ?_⟩
  have he : X - rectangularCut Y = rectangularCut (rectangularCorner X - Y) := rfl
  rw [he]
  exact (norm_rectangularCut_le _).trans hc

/-- Rescaling gives a row approximant with error proportional to the row norm. -/
theorem graphRow_approx (h : MatrixNearInclusion M N γ)
    (k : ℕ) (X : Fin k → H →L[ℂ] H) (hX : ∀ i, X i ∈ M) :
    ∃ Z : Fin k → H →L[ℂ] H, (∀ i, Z i ∈ N) ∧
      ‖operatorRow X - operatorRow Z‖ ≤ γ * ‖operatorRow X‖ := by
  let A := operatorRow X
  by_cases hz : ‖A‖ = 0
  · refine ⟨fun _ => 0, (fun _ => N.zero_mem), ?_⟩
    have hA : A = 0 := norm_eq_zero.mp hz
    have hZ : operatorRow (fun _ : Fin k => (0 : H →L[ℂ] H)) = 0 := rfl
    change ‖A - _‖ ≤ γ * ‖A‖
    rw [hA, hZ, sub_zero, norm_zero, mul_zero]
  have hp : 0 < ‖A‖ := lt_of_le_of_ne (norm_nonneg A) (Ne.symm hz)
  let c : ℂ := ((‖A‖⁻¹ : ℝ) : ℂ)
  have hc : ‖c‖ = ‖A‖⁻¹ := by simp [c]
  obtain ⟨Y, hY, hYn, hclose⟩ := h.rectangular (c • A)
    (fun _ i => M.smul_mem (hX i) c)
    (by rw [norm_smul, hc, inv_mul_cancel₀ hz])
  let Z : Fin k → H →L[ℂ] H := fun i => (‖A‖ : ℂ) • Y () i
  refine ⟨Z, (fun i => N.smul_mem (hY () i) _), ?_⟩
  have he : A - operatorRow Z = (‖A‖ : ℂ) • (c • A - Y) := by
    rw [smul_sub, smul_smul]
    have hsc : (‖A‖ : ℂ) * c = 1 := by
      simp only [c, ← Complex.ofReal_mul, mul_inv_cancel₀ hz, Complex.ofReal_one]
    rw [hsc, one_smul]
    rfl
  change ‖A - operatorRow Z‖ ≤ γ * ‖A‖
  rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp.le]
  nlinarith

/-- Moving the target algebra changes every matrix bound by at most the
complete displacement of the conjugation. -/
theorem conjugate_right (h : MatrixNearInclusion M N γ)
    (u : unitary (H →L[ℂ] H)) :
    MatrixNearInclusion M (unitaryConjugateAlgebra u N)
      (γ + 2 * ‖(u : H →L[ℂ] H) - 1‖) := by
  intro n X hX hn
  obtain ⟨Y, hY, hYn, hc⟩ := h n X hX hn
  let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u
  let Z := CStarMatrix.mapₗ e.toAlgEquiv.toLinearMap Y
  refine ⟨Z, ?_, ?_, ?_⟩
  · intro i j
    exact ⟨Y i j, hY i j, rfl⟩
  · exact (injective_starAlgHom_matrix_norm e.toStarAlgHom e.injective Y).le.trans hYn
  · have hd := complete_unitaryConjugation_sub_id u n n Y
    have he : CStarMatrix.mapₗ (unitaryConjugationLinear u - LinearMap.id) Y = Z - Y := by
      ext i j
      rfl
    rw [he] at hd
    have hZY : ‖Y - Z‖ ≤ 2 * ‖(u : H →L[ℂ] H) - 1‖ := by
      rw [norm_sub_rev]
      exact hd.trans (mul_le_of_le_one_right (by positivity) hYn)
    exact (norm_sub_le_norm_sub_add_norm_sub X Y Z).trans (add_le_add hc hZY)

/-- Moving the source algebra has the same matrix displacement bound. -/
theorem conjugate_left (h : MatrixNearInclusion M N γ)
    (u : unitary (H →L[ℂ] H)) :
    MatrixNearInclusion (unitaryConjugateAlgebra u M) N
      (γ + 2 * ‖(u : H →L[ℂ] H) - 1‖) := by
  intro n X hX hn
  let e := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u
  let X₀ := CStarMatrix.mapₗ e.symm.toAlgEquiv.toLinearMap X
  have hX₀ : ∀ i j, X₀ i j ∈ M := by
    intro i j
    obtain ⟨a, ha, he⟩ := hX i j
    change e a = X i j at he
    change e.symm (X i j) ∈ M
    rw [← he, e.symm_apply_apply]
    exact ha
  have hX₀n : ‖X₀‖ ≤ 1 :=
    (injective_starAlgHom_matrix_norm e.symm.toStarAlgHom e.symm.injective X).le.trans hn
  obtain ⟨Y, hY, hYn, hc⟩ := h n X₀ hX₀ hX₀n
  refine ⟨Y, hY, hYn, ?_⟩
  have hd := complete_unitaryConjugation_sub_id u n n X₀
  have he : CStarMatrix.mapₗ (unitaryConjugationLinear u - LinearMap.id) X₀ = X - X₀ := by
    apply Matrix.ext
    intro i j
    change e (e.symm (X i j)) - e.symm (X i j) = X i j - e.symm (X i j)
    rw [e.apply_symm_apply]
  rw [he] at hd
  have hXX₀ : ‖X - X₀‖ ≤ 2 * ‖(u : H →L[ℂ] H) - 1‖ :=
    hd.trans (mul_le_of_le_one_right (by positivity) hX₀n)
  exact (norm_sub_le_norm_sub_add_norm_sub X X₀ Y).trans (by linarith)

/-- A common countable matrix algebra supplies proximity from the ordinary gap. -/
theorem of_common_matrix_units (M N : VonNeumannAlgebra H)
    (D : Submodule ℂ H) [CompleteSpace D] (F : FullMatrixCorner D)
    (hM : ∀ i j, F.entry i j ∈ M) (hN : ∀ i j, F.entry i j ∈ N)
    {r : ℝ} (hr : kkDistance M N < r) : MatrixNearInclusion M N r := by
  intro n X hX hn
  cases n with
  | zero =>
    refine ⟨0, (fun i => Fin.elim0 i), ?_, ?_⟩
    · simp
    · have he : X = 0 := by ext i; exact Fin.elim0 i
      simp only [he, sub_self, norm_zero]
      exact (kkDistance_nonneg M N).trans hr.le
  | succ n =>
    obtain ⟨Y, hY, hYn, hc⟩ := (F.finiteCuntz (n + 1)).exists_matrix_unitBall_approx
      M N (F.finiteCuntz_mem _ M hM) (F.finiteCuntz_mem _ N hN) hr X hX hn
    exact ⟨Y, hY, hYn, hc.le⟩

/-- Matrix proximity in both directions controls the regular tensor product. -/
theorem regularTensor_gap (hMN : MatrixNearInclusion M N γ)
    (hNM : MatrixNearInclusion N M γ) (hγ : 0 ≤ γ) :
    kkDistance (regularTensorAlgebra M) (regularTensorAlgebra N) ≤ γ :=
  kkDistance_regularTensorAlgebra_le_of_matrix_approx M N hγ hMN hNM

end MatrixNearInclusion

end

end KadisonKastler

end OAI
