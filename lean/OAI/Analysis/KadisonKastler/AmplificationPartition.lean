import OAI.Analysis.KadisonKastler.ConcreteClippedDrift
import OAI.Analysis.KadisonKastler.MatrixUnitsExistence
import OAI.Analysis.KadisonKastler.ThroughLabelBounds
import OAI.Analysis.KadisonKastler.FreeWordConstants
import OAI.Analysis.KadisonKastler.PhaseCoefficients

namespace OAI

/-! # The actual diagonal partition in a matrix amplification

Outer row indices and inner matrix-unit indices give `n*k` mutually
orthogonal diagonal projections. Relabeling by `finProdFinEquiv` matches
the phase multiset supports with the concrete support projections used
in the clipped-column estimate.
-/

namespace KadisonKastler

open scoped BigOperators

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {n k : ℕ}

local instance amplificationPartitionOrder : PartialOrder (Algebra M) :=
  CStarAlgebra.spectralOrder _
local instance amplificationPartitionStarOrder : StarOrderedRing (Algebra M) :=
  CStarAlgebra.spectralOrderedRing _
local instance amplificationPartitionOperatorOrder : PartialOrder (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrder _
local instance amplificationPartitionOperatorStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

/-- The diagonal partition indexed by a single finite label set. -/
def amplificationPartition (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (a : Fin (n * k)) : Algebra (matrixVonNeumann (ι := Fin n) M) :=
  matrixAlgebraHom M (supportAtom E (finProdFinEquiv.symm a))

theorem amplificationPartition_projection
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M)) (a : Fin (n * k)) :
    IsStarProjection (amplificationPartition E a) :=
  (supportAtom_projection E (finProdFinEquiv.symm a)).map (matrixAlgebraHom M)

theorem amplificationPartition_orthogonal
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (a b : Fin (n * k)) (hab : a ≠ b) :
    amplificationPartition E a * amplificationPartition E b = 0 := by
  change matrixAlgebraHom M _ * matrixAlgebraHom M _ = 0
  rw [← map_mul, supportAtom_orthogonal E _ _ (finProdFinEquiv.symm.injective.ne hab), map_zero]

theorem amplificationPartition_total
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M)) :
    ∑ a : Fin (n * k), amplificationPartition E a = 1 := by
  have he : (∑ a : Fin (n * k), supportAtom E (finProdFinEquiv.symm a)) =
      ∑ p : Fin n × Fin k, supportAtom E p :=
    Fintype.sum_equiv finProdFinEquiv.symm _ _ (fun _ => rfl)
  change ∑ a : Fin (n * k), matrixAlgebraHom M _ = 1
  rw [← map_sum, he, supportAtom_total, map_one]

/-- Every atom has normalized trace `1/(n*k)`. -/
theorem amplificationPartition_trace [NeZero n]
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (τ : FaithfulTracialState (Algebra M)) (a : Fin (n * k)) :
    (matrixVonNeumannTrace (ι := Fin n) M τ).toLinearMap (amplificationPartition E a) =
      ((n * k : ℕ) : ℂ)⁻¹ := by
  let p : Fin n × Fin k := finProdFinEquiv.symm a
  have hs : (∑ i : Fin n, τ.toLinearMap (supportAtom E p i i)) =
      τ.toLinearMap (E.entry p.2 p.2) := by
    simp [supportAtom, matrixEntry, Matrix.single_apply, apply_ite]
  change (matrixVonNeumannTrace (ι := Fin n) M τ).toLinearMap
    (matrixAlgebraHom M (supportAtom E p)) = _
  rw [matrixVonNeumannTrace_map, matrixTrace_apply, hs, matrixUnits_trace_diagonal]
  simp only [Fintype.card_fin, Complex.ofReal_inv, Complex.ofReal_natCast, Nat.cast_mul,
    mul_inv_rev]
  exact mul_comm _ _

/-- A multiset of phase labels names the corresponding outer/inner support atoms. -/
def amplificationSupport (s : Multiset (Fin (n * k))) : Finset (Fin n × Fin k) :=
  s.toFinset.map finProdFinEquiv.symm.toEmbedding

@[simp]
theorem mem_amplificationSupport (s : Multiset (Fin (n * k))) (p : Fin n × Fin k) :
    p ∈ amplificationSupport s ↔ finProdFinEquiv p ∈ s := by
  simp only [amplificationSupport, Finset.mem_map, Equiv.toEmbedding_apply,
    Multiset.mem_toFinset]
  constructor
  · rintro ⟨a, ha, he⟩
    have he' : a = finProdFinEquiv p := by
      simpa only [Equiv.apply_symm_apply] using congrArg finProdFinEquiv he
    exact he' ▸ ha
  · intro hp
    exact ⟨finProdFinEquiv p, hp, finProdFinEquiv.symm_apply_apply p⟩

theorem amplificationSupport_card_le (s : Multiset (Fin (n * k))) :
    (amplificationSupport s).card ≤ s.card := by
  rw [amplificationSupport, Finset.card_map]
  exact s.toFinset_card_le

theorem amplificationSupport_sym_card_le {r : ℕ} (s : Sym (Fin (n * k)) r) :
    (amplificationSupport (s : Multiset (Fin (n * k)))).card ≤ r :=
  (amplificationSupport_card_le s.val).trans s.property.le

theorem amplificationSupport_small {r : ℕ} (s : Sym (Fin (n * k)) r) (hr : r ≤ k) :
    (amplificationSupport (s : Multiset (Fin (n * k)))).card ≤ k :=
  (amplificationSupport_sym_card_le s).trans hr

/-- Matrix entries of one relabeled atom are exactly the original operator atom. -/
theorem concreteMatrixEntries_amplificationPartition
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M)) (a : Fin (n * k)) :
    concreteMatrixEntries (M := M) (n := n) (amplificationPartition E a) =
      supportAtom (E.map M.toStarSubalgebra.subtype) (finProdFinEquiv.symm a) := by
  change coefficientMatrixMap M.toStarSubalgebra.subtype
      ((matrixAlgebraEquiv (ι := Fin n) M).symm
        ((matrixAlgebraEquiv (ι := Fin n) M) (supportAtom E (finProdFinEquiv.symm a)))) = _
  rw [StarAlgEquiv.symm_apply_apply]
  apply CStarMatrix.ext
  intro i j
  simp only [coefficientMatrixMap_apply, supportAtom, matrixEntry,
    Matrix.single_apply, CStarMatrix.ofMatrix_apply, Generator.MatrixUnitSystem.map_entry]
  split_ifs <;> rfl

/-- Phase supports coincide with the support projections in the small-column lemma. -/
theorem concreteMatrixEntries_phaseSupport
    (E : Generator.MatrixUnitSystem (Fin k) (Algebra M))
    (s : Multiset (Fin (n * k))) :
    concreteMatrixEntries (M := M) (n := n) (phaseSupport (amplificationPartition E) s) =
      supportProjection (E.map M.toStarSubalgebra.subtype) (amplificationSupport s) := by
  rw [phaseSupport, map_sum]
  simp_rw [concreteMatrixEntries_amplificationPartition]
  rw [supportProjection_eq_sum]
  simp only [amplificationSupport, Finset.sum_map, Equiv.toEmbedding_apply]

/-- Reindexing the support budget gives exactly the through-label sum. -/
theorem amplificationSupport_weight_sum_eq {r : ℕ} (C : ℝ) (p : Fin n × Fin k) :
    (∑ s : Sym (Fin (n * k)) r,
      if p ∈ amplificationSupport (s : Multiset (Fin (n * k)))
      then projectionWordWeight C s ^ 2 else 0) =
      ∑ s : ThroughLabel (finProdFinEquiv p) r, projectionWordWeight C s.val ^ 2 := by
  simp only [mem_amplificationSupport]
  symm
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun s : Sym (Fin (n * k)) r => finProdFinEquiv p ∈ s)
    (by simp) (fun s : Sym (Fin (n * k)) r => projectionWordWeight C s ^ 2),
    Finset.sum_filter]
  rfl

theorem amplificationSupport_weight_sum_le {r : ℕ} (C : ℝ)
    (h : ∀ a : Fin (n * k),
      (∑ s : ThroughLabel a r, projectionWordWeight C s.val ^ 2) ≤ 64)
    (p : Fin n × Fin k) :
    (∑ s : Sym (Fin (n * k)) r,
      if p ∈ amplificationSupport (s : Multiset (Fin (n * k)))
      then projectionWordWeight C s ^ 2 else 0) ≤ 64 := by
  rw [amplificationSupport_weight_sum_eq]
  exact h (finProdFinEquiv p)

/-- The actual clipping thresholds are strictly positive. -/
theorem amplificationProjectionWordWeight_pos [NeZero n] [NeZero k]
    {r : ℕ} (s : Sym (Fin (n * k)) r) :
    0 < projectionWordWeight (freeWordC r) s := by
  have hd : (0 : ℝ) < n * k := by
    exact_mod_cast Nat.mul_pos (NeZero.pos n) (NeZero.pos k)
  have hf : (0 : ℝ) < (r - 1).factorial := by exact_mod_cast Nat.factorial_pos (r - 1)
  unfold projectionWordWeight
  simp only [Fintype.card_fin, Nat.cast_mul]
  apply div_pos
  · split_ifs
    · exact mul_pos (by norm_num) (Real.sqrt_pos.mpr hf)
    · exact freeWordC_pos r
  · exact Real.sqrt_pos.mpr (pow_pos hd _)

/-- One inner matrix size suffices for every degree up to `N`, including
both the free-word norm bounds and the through-label square-sum budget. -/
theorem exists_amplification_partition_size (n N : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, 0 < k ∧ N ≤ k ∧
      (∀ r ≤ N, freeWordThreshold r ≤ n * k) ∧
      ∀ r : ℕ, 1 ≤ r → r ≤ N → ∀ a : Fin (n * k),
        (∑ s : ThroughLabel a r, projectionWordWeight (freeWordC r) s.val ^ 2) ≤ 64 := by
  obtain ⟨D, hD, hDall⟩ := exists_uniform_freeWordThreshold N
  obtain ⟨F, hF, hFall⟩ := exists_uniform_projectionWordWeight_threshold N freeWordC
  let k := max 1 (max N (max D F))
  have hk : 0 < k := lt_of_lt_of_le (by omega : 0 < 1) (le_max_left _ _)
  have hNk : N ≤ k := (le_max_left _ _).trans (le_max_right _ _)
  have hDk : D ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hFk : F ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hkn : k ≤ n * k := Nat.le_mul_of_pos_left k hn
  exact ⟨k, hk, hNk, fun r hr => (hDall r hr).trans (hDk.trans hkn),
    fun r hr hrN a => hFall (n * k) (hFk.trans hkn) r hr hrN a⟩

/-- A factor supplies the chosen inner matrix units at the same uniform size. -/
theorem exists_amplification_partition_matrixUnits
    (hM : Generator.IsII1Factor M.toStarSubalgebra) (n N : ℕ) (hn : 0 < n) :
    ∃ k : ℕ, 0 < k ∧ N ≤ k ∧
      Nonempty (Generator.MatrixUnitSystem (Fin k) (Algebra M)) ∧
      (∀ r ≤ N, freeWordThreshold r ≤ n * k) ∧
      ∀ r : ℕ, 1 ≤ r → r ≤ N → ∀ a : Fin (n * k),
        (∑ s : ThroughLabel a r, projectionWordWeight (freeWordC r) s.val ^ 2) ≤ 64 := by
  obtain ⟨k, hk, hNk, hword, hsum⟩ := exists_amplification_partition_size n N hn
  exact ⟨k, hk, hNk, exists_matrixUnits_of_size hM k hk, hword, hsum⟩

end

end KadisonKastler

end OAI
