import OAI.Analysis.Cuntz.Cutoff
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Topology.Semicontinuity.Defs

namespace OAI

noncomputable section

/-! Regularized dimensions, cutoff calculus, and topological regularization. -/

open scoped Matrix CStarAlgebra Topology

namespace Kaplansky
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
namespace CuntzDimensionState

/-- Cutoff regularization of the constructed dimension state, as a finite real supremum. -/
def regularized (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) : ℝ :=
  sSup ((fun ε : ℝ => d.value (a.cutoff ε)) '' Set.Ioi 0)

theorem cutoff_values_nonempty (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    ((fun ε : ℝ => d.value (a.cutoff ε)) '' Set.Ioi 0).Nonempty :=
  ⟨_, ⟨1, by norm_num, rfl⟩⟩

theorem cutoff_values_bddAbove (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    BddAbove ((fun ε : ℝ => d.value (a.cutoff ε)) '' Set.Ioi 0) := by
  refine ⟨d.value a, ?_⟩
  rintro _ ⟨ε, hε, rfl⟩
  exact d.cutoff_value_le a hε.le

theorem cutoff_value_le_regularized (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {ε : ℝ} (hε : 0 < ε) : d.value (a.cutoff ε) ≤ d.regularized a :=
  le_csSup (d.cutoff_values_bddAbove a) ⟨ε, hε, rfl⟩

theorem regularized_le (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {r : ℝ} (h : ∀ ε : ℝ, 0 < ε → d.value (a.cutoff ε) ≤ r) : d.regularized a ≤ r := by
  apply csSup_le (d.cutoff_values_nonempty a)
  rintro _ ⟨ε, hε, rfl⟩
  exact h ε hε

theorem regularized_le_value (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    d.regularized a ≤ d.value a := d.regularized_le a fun _ hε => d.cutoff_value_le a hε.le

theorem regularized_nonneg (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    0 ≤ d.regularized a :=
  (d.value_nonneg (a.cutoff 1)).trans (d.cutoff_value_le_regularized a (by norm_num))

theorem regularized_le_size (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A) :
    d.regularized a ≤ a.size := (d.regularized_le_value a).trans (d.value_le_size a)

/-- Cuntz monotonicity is proved using the two-cutoff comparison theorem. -/
theorem regularized_mono (d : CuntzDimensionState A) {a b : CuntzPositiveMatrix A}
    (h : CuntzLE a.matrix b.matrix) : d.regularized a ≤ d.regularized b := by
  apply d.regularized_le a
  intro ε hε
  obtain ⟨δ, hδ, hc⟩ := (cuntzLE_iff_cutoff_comparison a b).mp h ε hε
  exact (d.value_mono (a := a.cutoff ε) (b := b.cutoff δ) hc).trans
    (d.cutoff_value_le_regularized b hδ)

theorem regularized_eq (d : CuntzDimensionState A) {a b : CuntzPositiveMatrix A}
    (h : CuntzEquivalent a.matrix b.matrix) : d.regularized a = d.regularized b :=
  le_antisymm (d.regularized_mono h.1) (d.regularized_mono h.2)

theorem regularized_zero (d : CuntzDimensionState A) : d.regularized .zero = 0 :=
  le_antisymm ((d.regularized_le_value .zero).trans_eq d.value_zero) (d.regularized_nonneg .zero)

/-- Every number strictly below the supremum is exceeded by one actual cutoff value. -/
theorem exists_lt_cutoff_value (d : CuntzDimensionState A) (a : CuntzPositiveMatrix A)
    {r : ℝ} (h : r < d.regularized a) : ∃ ε : ℝ, 0 < ε ∧ r < d.value (a.cutoff ε) := by
  by_contra! hn
  exact (not_le_of_gt h) (d.regularized_le a hn)

end CuntzDimensionState

/-- Iterated cutoffs add their thresholds. -/
theorem cuntzCutoff_cutoff {a : A} (ha : 0 ≤ a) (ε : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    cuntzCutoff (cuntzCutoff a ε) δ = cuntzCutoff a (ε+δ) := by
  unfold cuntzCutoff
  rw [← cfc_comp' (fun t : ℝ => max (t-δ) 0) (fun t : ℝ => max (t-ε) 0) a]
  apply cfc_congr
  intro t ht
  dsimp only
  rcases le_total t ε with h | h
  · rw [max_eq_right (sub_nonpos.mpr h), zero_sub, max_eq_right (neg_nonpos.mpr hδ),
      max_eq_right (by linarith : t-(ε+δ) ≤ 0)]
  · rw [max_eq_left (sub_nonneg.mpr h)]
    congr 1
    ring

theorem CuntzPositiveMatrix.cutoff_cutoff (a : CuntzPositiveMatrix A) (ε : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) : (a.cutoff ε).cutoff δ = a.cutoff (ε+δ) := by
  cases a with
  | mk n a ha =>
    simp only [CuntzPositiveMatrix.cutoff]
    congr 1
    change CStarMatrix.ofMatrix.symm (cuntzCutoff (cuntzCutoff (CStarMatrix.ofMatrix a) ε) δ) =
      CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix a) (ε + δ))
    rw [cuntzCutoff_cutoff ha ε hδ]

theorem cuntzCutoff_one_half : cuntzCutoff (1 : A) (1/2) = (1/2 : ℝ) • (1 : A) := by
  unfold cuntzCutoff
  have he := cfc_algebraMap (A := A) (1 : ℝ) (fun t : ℝ => max (t-1/2) 0)
  norm_num [Algebra.algebraMap_eq_smul_one] at he ⊢

/-- Regularization preserves the value of every finite identity matrix. -/
theorem CuntzDimensionState.regularized_unit (d : CuntzDimensionState A) (n : ℕ) :
    d.regularized (.unit n) = (n : ℝ) := by
  apply le_antisymm ((d.regularized_le_value _).trans_eq (d.value_unit n))
  have he : d.value ((CuntzPositiveMatrix.unit (A := A) n).cutoff (1/2)) = d.value (.unit n) := by
    apply d.value_eq
    change CuntzEquivalent (CStarMatrix.ofMatrix.symm
      (cuntzCutoff (1 : CStarMatrix (Fin n) (Fin n) A) (1/2))) (1 : Matrix (Fin n) (Fin n) A)
    rw [cuntzCutoff_one_half]
    exact cuntzEquivalent_pos_smul 1 (by norm_num)
  rw [← d.value_unit n, ← he]
  exact d.cutoff_value_le_regularized _ (by norm_num)

/-- Applying the cutoff supremum a second time does not change its value. -/
theorem CuntzDimensionState.regularized_idempotent (d : CuntzDimensionState A)
    (a : CuntzPositiveMatrix A) :
    sSup ((fun ε : ℝ => d.regularized (a.cutoff ε)) '' Set.Ioi 0) = d.regularized a := by
  have hne : ((fun ε : ℝ => d.regularized (a.cutoff ε)) '' Set.Ioi 0).Nonempty :=
    ⟨_, ⟨1, by norm_num, rfl⟩⟩
  have hb : BddAbove ((fun ε : ℝ => d.regularized (a.cutoff ε)) '' Set.Ioi 0) := by
    refine ⟨d.regularized a, ?_⟩
    rintro _ ⟨ε, hε, rfl⟩
    exact (d.regularized_le_value _).trans (d.cutoff_value_le_regularized a hε)
  apply le_antisymm
  · apply csSup_le hne
    rintro _ ⟨ε, hε, rfl⟩
    exact (d.regularized_le_value _).trans (d.cutoff_value_le_regularized a hε)
  apply d.regularized_le a
  intro ε hε
  have he : d.value (a.cutoff ε) ≤ d.regularized (a.cutoff (ε/2)) := by
    have hc := d.cutoff_value_le_regularized (a.cutoff (ε/2)) (half_pos hε)
    rw [CuntzPositiveMatrix.cutoff_cutoff a _ (half_pos hε).le] at hc
    simpa only [add_halves] using hc
  exact he.trans (le_csSup hb ⟨ε/2, half_pos hε, rfl⟩)


/-- A norm neighborhood controls one fixed cutoff by the regularized value. -/
theorem CuntzDimensionState.cutoff_value_le_regularized_of_norm {n : ℕ}
    (d : CuntzDimensionState A) {a b : CStarMatrix (Fin n) (Fin n) A}
    (ha : 0 ≤ a) (hb : 0 ≤ b) {ε : ℝ} (hε : 0 < ε) (hab : ‖a-b‖ < ε/2) :
    d.value ((⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ : CuntzPositiveMatrix A).cutoff ε) ≤
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ := by
  have hn : ‖a - cuntzCutoff b (ε/2)‖ < ε := by
    have ht : ‖a - cuntzCutoff b (ε/2)‖ ≤ ‖a-b‖ + ‖b - cuntzCutoff b (ε/2)‖ := by
      simpa only [dist_eq_norm] using dist_triangle a b (cuntzCutoff b (ε/2))
    have he := norm_sub_cuntzCutoff_le hb (half_pos hε).le
    linarith
  have hc := cuntzLE_cutoff_of_norm_sub_lt ha (cuntzCutoff_nonneg b (ε/2)).isSelfAdjoint hn
  exact (d.value_mono (a := (⟨n, CStarMatrix.ofMatrix.symm a, ha⟩ : CuntzPositiveMatrix A).cutoff ε)
    (b := (⟨n, CStarMatrix.ofMatrix.symm b, hb⟩ : CuntzPositiveMatrix A).cutoff (ε/2)) hc).trans
    (d.cutoff_value_le_regularized _ (half_pos hε))

/-- Lower semicontinuity on the full positive cone in each actual matrix norm. -/
theorem CuntzDimensionState.regularized_lowerSemicontinuous (d : CuntzDimensionState A)
    (n : ℕ) : LowerSemicontinuous (fun a : {a : CStarMatrix (Fin n) (Fin n) A // 0 ≤ a} =>
      d.regularized ⟨n, CStarMatrix.ofMatrix.symm a.val, a.property⟩) := by
  intro a r hr
  obtain ⟨ε, hε, he⟩ := d.exists_lt_cutoff_value _ hr
  apply Metric.mem_nhds_iff.mpr
  refine ⟨ε/2, half_pos hε, ?_⟩
  intro b hb
  have hdist : ‖a.val-b.val‖ < ε/2 := by
    simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using hb
  exact he.trans_le (d.cutoff_value_le_regularized_of_norm a.property b.property hε hdist)

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

local instance matrixRealFunctionalCalculus {ν : Type*} [Fintype ν] [DecidableEq ν] :
    ContinuousFunctionalCalculus ℝ (CStarMatrix ν ν A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

local instance productMatrixRealFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ (CStarMatrix ι ι A × CStarMatrix κ κ A) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- The genuine block-diagonal unital star homomorphism. -/
def cuntzBlockHom : (CStarMatrix ι ι A × CStarMatrix κ κ A) →⋆ₐ[ℂ]
    CStarMatrix (ι ⊕ κ) (ι ⊕ κ) A where
  toFun p := CStarMatrix.ofMatrix (cuntzBlock p.1 p.2)
  map_zero' := by ext i j; cases i <;> cases j <;> rfl
  map_one' := by exact Matrix.fromBlocks_one
  map_add' p q := by
    ext i j
    cases i <;> cases j <;> first | rfl | exact (zero_add (0 : A)).symm
  map_mul' p q := by
    change cuntzBlock (CStarMatrix.ofMatrix.symm p.1 * CStarMatrix.ofMatrix.symm q.1)
      (CStarMatrix.ofMatrix.symm p.2 * CStarMatrix.ofMatrix.symm q.2) =
      cuntzBlock (CStarMatrix.ofMatrix.symm p.1) (CStarMatrix.ofMatrix.symm p.2) *
        cuntzBlock (CStarMatrix.ofMatrix.symm q.1) (CStarMatrix.ofMatrix.symm q.2)
    simp only [cuntzBlock, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
  map_star' p := by
    ext i j
    cases i <;> cases j <;> first | rfl | exact (star_zero A).symm
  commutes' c := by
    classical
    simp only [Algebra.algebraMap_eq_smul_one]
    change Matrix.fromBlocks (c • (1 : Matrix ι ι A)) 0 0 (c • (1 : Matrix κ κ A)) = c • (1 : Matrix (ι ⊕ κ) (ι ⊕ κ) A)
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
    simp only [smul_zero]

theorem cuntzCutoff_block (a : CStarMatrix ι ι A) (b : CStarMatrix κ κ A)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (ε : ℝ) :
    cuntzCutoff (CStarMatrix.ofMatrix (cuntzBlock a b)) ε =
      CStarMatrix.ofMatrix (cuntzBlock (CStarMatrix.ofMatrix.symm (cuntzCutoff a ε)) (CStarMatrix.ofMatrix.symm (cuntzCutoff b ε))) := by
  let φ := cuntzBlockHom (A := A) (ι := ι) (κ := κ)
  have h := φ.map_cfc (fun t : ℝ => max (t-ε) 0) (a,b)
    (ha := by exact Prod.ext ha.isSelfAdjoint hb.isSelfAdjoint)
    (hφa := (cuntzBlock_nonneg _ _ ha hb).isSelfAdjoint)
  rw [cfc_map_prod (S := ℂ) (fun t : ℝ => max (t-ε) 0) a b
    (ha := ha.isSelfAdjoint) (hb := hb.isSelfAdjoint)
    (hab := by exact Prod.ext ha.isSelfAdjoint hb.isSelfAdjoint)] at h
  exact h.symm

theorem cuntzCutoff_reindex (a : CStarMatrix ι ι A) (ha : 0 ≤ a) (e : κ ≃ ι) (ε : ℝ) :
    cuntzCutoff (CStarMatrix.ofMatrix ((CStarMatrix.ofMatrix.symm a).submatrix e e)) ε =
      CStarMatrix.ofMatrix ((CStarMatrix.ofMatrix.symm (cuntzCutoff a ε)).submatrix e e) := by
  let φ := (CStarMatrix.reindexₐ ℂ A e.symm).toStarAlgHom
  exact (φ.map_cfc (fun t : ℝ => max (t-ε) 0) a
    (ha := ha.isSelfAdjoint) (hφa := (cuntzSubmatrix_nonneg _ e ha).isSelfAdjoint)).symm

theorem CuntzPositiveMatrix.cutoff_add (a b : CuntzPositiveMatrix A) (ε : ℝ) :
    (a.add b).cutoff ε = (a.cutoff ε).add (b.cutoff ε) := by
  cases a with
  | mk n a ha =>
    cases b with
    | mk m b hb =>
      simp only [CuntzPositiveMatrix.add, CuntzPositiveMatrix.cutoff]
      congr 1
      have he := cuntzCutoff_reindex (CStarMatrix.ofMatrix (cuntzBlock a b))
        (cuntzBlock_nonneg _ _ ha hb) finSumFinEquiv.symm ε
      have hh : cuntzCutoff (CStarMatrix.ofMatrix (cuntzBlock a b)) ε =
          CStarMatrix.ofMatrix (cuntzBlock
            (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix a) ε))
            (CStarMatrix.ofMatrix.symm (cuntzCutoff (CStarMatrix.ofMatrix b) ε))) :=
        cuntzCutoff_block (CStarMatrix.ofMatrix a) (CStarMatrix.ofMatrix b) ha hb ε
      rw [hh] at he
      exact congrArg CStarMatrix.ofMatrix.symm he

end Kaplansky

end

end OAI
