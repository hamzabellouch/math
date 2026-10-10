import OAI.Analysis.KadisonKastler.TypeIIIProjectionComparison
import OAI.Analysis.KadisonKastler.MatrixOrbitAverage
import OAI.Analysis.FactorGeneration.SpectralApproximation
import OAI.Analysis.FactorGeneration.MatrixRefinement

namespace OAI

/-! # Finite spectral partitions in a type III factor are matrix diagonals -/

namespace KadisonKastler

open Generator Generator.Tracial
open scoped BigOperators

noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  [Fintype ι] [DecidableEq ι] {M : VonNeumannAlgebra H}

/-- Nonzero orthogonal spectral pieces summing to one are the diagonal of
an actual full matrix system in the original type III factor. -/
theorem TypeIIIFactor.exists_matrixUnits_of_partition (hM : TypeIIIFactor M)
    (q : ι → AlgebraProjection M) (hne : ∀ i, (q i).val ≠ 0)
    (horth : ∀ i j, i ≠ j → (q i).val * (q j).val = 0)
    (htotal : ∑ i, (q i).val = 1) :
    ∃ E : MatrixUnitSystem ι (Algebra M), ∀ i, E.entry i i = (q i).val := by
  choose v hv hq using fun i => hM.exists_isometry_onto_projection
    (q i).val (q i).property (hne i)
  have hright (i : ι) : (q i).val * v i = v i := by
    rw [← hq i, mul_assoc, hv i, mul_one]
  have hleft (i : ι) : star (v i) * (q i).val = star (v i) := by
    have h := congrArg star (hright i)
    simpa only [star_mul, (q i).property.isSelfAdjoint.star_eq] using h
  have hcross (i j : ι) : star (v i) * v j = if i = j then 1 else 0 := by
    split_ifs with hij
    · subst j
      exact hv i
    · calc
        star (v i) * v j = (star (v i) * (q i).val) * ((q j).val * v j) := by
          rw [hleft, hright]
        _ = star (v i) * ((q i).val * (q j).val) * v j := by simp only [mul_assoc]
        _ = 0 := by rw [horth i j hij, mul_zero, zero_mul]
  let E : MatrixUnitSystem ι (Algebra M) := {
    entry := fun i j => v i * star (v j)
    star_entry := by intro i j; simp only [star_mul, star_star]
    mul_entry := by
      intro i j k l
      rw [show (v i * star (v j)) * (v k * star (v l)) =
        v i * (star (v j) * v k) * star (v l) by simp only [mul_assoc], hcross]
      split_ifs <;> simp
    total := by simpa only [hq] using htotal }
  exact ⟨E, hq⟩



/-- Discard the zero spectral pieces without changing the spectral sum. -/
abbrev spectralPartitionNonzeroIndex {p : AlgebraProjection M} (Q : CornerPartition p) :=
  {i : Fin Q.size // (Q.piece i).val ≠ 0}

instance spectralPartitionNonzeroIndexFintype {p : AlgebraProjection M} (Q : CornerPartition p) :
    Fintype (spectralPartitionNonzeroIndex Q) := by
  classical
  exact Subtype.fintype _

instance spectralPartitionNonzeroIndexDecidableEq {p : AlgebraProjection M} (Q : CornerPartition p) :
    DecidableEq (spectralPartitionNonzeroIndex Q) := Classical.decEq _

omit [TopologicalSpace.SeparableSpace H] in
theorem spectralPartitionSum_nonzero {p : AlgebraProjection M} (Q : CornerPartition p)
    (c : Fin Q.size → ℂ) :
    (∑ i : spectralPartitionNonzeroIndex Q, c i.val • (Q.piece i.val).val) =
      ∑ i, c i • (Q.piece i).val := by
  classical
  have h := Fintype.sum_subtype_add_sum_subtype (fun i : Fin Q.size => (Q.piece i).val ≠ 0)
    (fun i => c i • (Q.piece i).val)
  have hz : (∑ i : {i : Fin Q.size // ¬ (Q.piece i).val ≠ 0},
      c i.val • (Q.piece i.val).val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [not_ne_iff.mp i.property, smul_zero]
  rw [hz, add_zero] at h
  exact h

omit [TopologicalSpace.SeparableSpace H] in
/-- A nonzero partition of the identity has a nonzero piece. -/
theorem spectralPartition_nonempty_nonzeroIndex [Nontrivial H] (Q : CornerPartition (identityProjection M)) :
    Nonempty (spectralPartitionNonzeroIndex Q) := by
  classical
  by_contra h
  have hz (i : Fin Q.size) : (Q.piece i).val = 0 := by
    by_contra hi
    exact h ⟨⟨i, hi⟩⟩
  have hs := Q.total
  simp only [hz, Finset.sum_const_zero, identityProjection] at hs
  exact zero_ne_one hs


/-- Every finite spectral partition in the type III factor is contained
in one finite full matrix algebra, after dropping its zero pieces. -/
theorem TypeIIIFactor.exists_spectral_matrixUnits (hM : TypeIIIFactor M)
    (Q : CornerPartition (identityProjection M)) :
    ∃ E : MatrixUnitSystem (spectralPartitionNonzeroIndex Q) (Algebra M),
      ∀ i, E.entry i i = (Q.piece i.val).val := by
  classical
  apply hM.exists_matrixUnits_of_partition (fun i : spectralPartitionNonzeroIndex Q => Q.piece i.val)
    (fun i => i.property)
    (fun i j hij => Q.orthogonal i.val j.val (fun h => hij (Subtype.ext h)))
  have hs := spectralPartitionSum_nonzero Q (fun _ => (1 : ℂ))
  simpa only [one_smul, Q.total, identityProjection] using hs


omit [Fintype ι] [DecidableEq ι] in
/-- A self-adjoint element of a type III factor is approximated in norm by
an element of a finite full matrix algebra in the same representation. -/
theorem TypeIIIFactor.exists_selfAdjoint_matrix_approx [Nontrivial H]
    (hM : TypeIIIFactor M) (x : Algebra M) (hx : IsSelfAdjoint x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (E : MatrixUnitSystem (Fin n) (H →L[ℂ] H)), 0 < n ∧
      E.algebra ≤ M.toStarSubalgebra ∧
      ∃ y ∈ E.algebra, ‖x.val - y‖ < ε := by
  classical
  obtain ⟨Q, c, _, hc⟩ := exists_finite_spectral_approximation
    (identityProjection M) x hx ε hε
  let I := spectralPartitionNonzeroIndex Q
  let : Nonempty I := spectralPartition_nonempty_nonzeroIndex Q
  obtain ⟨E₀, hE₀⟩ := hM.exists_spectral_matrixUnits Q
  let E₁ := E₀.map M.toStarSubalgebra.subtype
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let E := E₁.reindex e
  have hE : E.algebra = E₁.algebra := E₁.reindex_algebra e
  have hEM : E.algebra ≤ M.toStarSubalgebra := by
    rw [hE]
    apply (E₁.algebra_le_iff _).mpr
    intro i j
    exact (E₀.entry i j).property
  let y : Algebra M := ∑ i : I, (c i.val : ℂ) • (Q.piece i.val).val
  have hyval : y.val = ∑ i : I, (c i.val : ℂ) •
      ((Q.piece i.val).val : H →L[ℂ] H) := by simp [y]
  have hy : y.val ∈ E.algebra := by
    rw [hE, hyval]
    apply E₁.algebra.sum_mem
    intro i _
    apply E₁.algebra.smul_mem
    have hm := E₁.entry_mem i i
    change ((E₀.entry i i : Algebra M) : H →L[ℂ] H) ∈ E₁.algebra at hm
    rwa [hE₀ i] at hm
  refine ⟨Fintype.card I, E, Fintype.card_pos, hEM, y.val, hy, ?_⟩
  have hyfull : y = ∑ i, (c i : ℂ) • (Q.piece i).val :=
    spectralPartitionSum_nonzero Q (fun i => (c i : ℂ))
  have hc' : ‖(x - ∑ i, (c i : ℂ) • (Q.piece i).val : Algebra M)‖ < ε := by
    simpa only [identityProjection, one_mul, mul_one] using hc
  exact (congrArg (fun z : Algebra M => ‖x - z‖) hyfull).trans_lt hc'


end

end KadisonKastler

end OAI
