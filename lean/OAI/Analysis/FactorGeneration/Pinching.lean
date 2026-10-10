import OAI.Analysis.FactorGeneration.CornerTrace

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite pinching in the actual ambient algebra. The squared L2 energy
is a sum of the energies of the mutually orthogonal compression blocks.
These identities do not postulate a local-quantizing partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- A finite projection partition of a corner, allowing zero pieces. -/
structure CornerPartition (p : AlgebraProjection M) where
  size : ℕ
  piece : Fin size → AlgebraProjection M
  orthogonal : ∀ i j, i ≠ j → (piece i).val * (piece j).val = 0
  total : ∑ i, (piece i).val = p.val

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem piece_le (i : Fin Q.size) : Q.piece i ≤ p := by
  change p.val * (Q.piece i).val = (Q.piece i).val
  rw [← Q.total, Finset.sum_mul]
  simpa only [(Q.piece i).property.isIdempotentElem.eq] using
    (Finset.sum_eq_single i (fun j _ hji => Q.orthogonal j i hji)
      (fun h => (h (Finset.mem_univ i)).elim))

def pinch (x : M.toStarSubalgebra) : M.toStarSubalgebra :=
  ∑ i, (Q.piece i).val * x * (Q.piece i).val

theorem pinch_add (x y : M.toStarSubalgebra) :
    Q.pinch (x+y) = Q.pinch x + Q.pinch y := by
  simp [pinch, mul_add, add_mul, Finset.sum_add_distrib]

theorem pinch_sub (x y : M.toStarSubalgebra) :
    Q.pinch (x-y) = Q.pinch x - Q.pinch y := by
  simp [pinch, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem pinch_smul (c : ℂ) (x : M.toStarSubalgebra) :
    Q.pinch (c • x) = c • Q.pinch x := by
  simp [pinch, Finset.smul_sum]

theorem pinch_support (x : M.toStarSubalgebra) :
    p.val * Q.pinch x = Q.pinch x ∧ Q.pinch x * p.val = Q.pinch x := by
  constructor
  · have h (i : Fin Q.size) : p.val * (Q.piece i).val = (Q.piece i).val := Q.piece_le i
    simp only [pinch, Finset.mul_sum, ← mul_assoc, h]
  · simp only [pinch, Finset.sum_mul, mul_assoc, projection_mul_of_le (Q.piece_le _)]

theorem pinch_left (i : Fin Q.size) (x : M.toStarSubalgebra) :
    (Q.piece i).val * Q.pinch x = (Q.piece i).val * x * (Q.piece i).val := by
  rw [pinch, Finset.mul_sum]
  rw [Finset.sum_eq_single i]
  · simp only [← mul_assoc, (Q.piece i).property.isIdempotentElem.eq]
  · intro j _ hji
    simp only [← mul_assoc, Q.orthogonal i j hji.symm, zero_mul]
  · simp

theorem pinch_right (i : Fin Q.size) (x : M.toStarSubalgebra) :
    Q.pinch x * (Q.piece i).val = (Q.piece i).val * x * (Q.piece i).val := by
  rw [pinch, Finset.sum_mul]
  rw [Finset.sum_eq_single i]
  · simp only [mul_assoc, (Q.piece i).property.isIdempotentElem.eq]
  · intro j _ hji
    simp only [mul_assoc, Q.orthogonal j i hji, mul_zero]
  · simp

theorem pinch_idempotent (x : M.toStarSubalgebra) : Q.pinch (Q.pinch x) = Q.pinch x := by
  unfold pinch
  apply Finset.sum_congr rfl
  intro i _
  change (Q.piece i).val * Q.pinch x * (Q.piece i).val = _
  rw [Q.pinch_left]
  simp only [mul_assoc, (Q.piece i).property.isIdempotentElem.eq]

theorem pinch_trace (x : M.toStarSubalgebra) :
    τ.trace (Q.pinch x) = τ.trace (p.val*x*p.val) := by
  have hq (i : Fin Q.size) :
      τ.trace ((Q.piece i).val*x*(Q.piece i).val) = τ.trace (x*(Q.piece i).val) := by
    rw [τ.trace_mul_comm, ← mul_assoc, (Q.piece i).property.isIdempotentElem.eq,
      τ.trace_mul_comm]
  change coordinateTraceLinear τ (∑ i, (Q.piece i).val*x*(Q.piece i).val) = _
  rw [map_sum]
  change (∑ i, τ.trace ((Q.piece i).val*x*(Q.piece i).val)) = _
  simp only [hq]
  change (∑ i, coordinateTraceLinear τ (x*(Q.piece i).val)) = _
  rw [← map_sum (coordinateTraceLinear τ), ← Finset.mul_sum, Q.total]
  change τ.trace (x*p.val) = _
  rw [τ.trace_mul_comm (p.val*x) p.val, ← mul_assoc, p.property.isIdempotentElem.eq,
    τ.trace_mul_comm p.val x]

end CornerPartition

/-! Actual compression energies and the energy lost by finite pinching.
No existence statement about small-energy partitions is assumed here. -/

theorem norm₂_sq_trace (x : M.toStarSubalgebra) :
    τ.norm₂ x ^ 2 = (τ.trace (star x*x)).re := by
  rw [τ.trace_star_mul, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem trace_compression_pairing (q : AlgebraProjection M) (x y : M.toStarSubalgebra) :
    τ.trace (star (q.val*x*q.val)*y) = τ.trace (star x*(q.val*y*q.val)) := by
  simp only [star_mul, q.property.isSelfAdjoint.star_eq]
  rw [mul_assoc q.val (star x*q.val), τ.trace_mul_comm q.val]
  simp only [mul_assoc]

theorem baseVector_inner_trace (x y : M.toStarSubalgebra) :
    inner ℂ (baseVector τ x) (baseVector τ y) = τ.trace (star x*y) := by
  change inner ℂ ((x : H →L[ℂ] H) τ.vector) ((y : H →L[ℂ] H) τ.vector) = _
  rw [← ContinuousLinearMap.adjoint_inner_right]
  rfl

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem pinch_pairing (x y : M.toStarSubalgebra) :
    τ.trace (star (Q.pinch x)*y) = τ.trace (star x*Q.pinch y) := by
  simp only [pinch, star_sum, Finset.sum_mul, Finset.mul_sum]
  change coordinateTraceLinear τ _ = coordinateTraceLinear τ _
  simp only [map_sum]
  exact Finset.sum_congr rfl (fun i _ => trace_compression_pairing τ (Q.piece i) x y)

theorem pinch_residual_orthogonal (x : M.toStarSubalgebra) :
    inner ℂ (baseVector τ (Q.pinch x)) (baseVector τ (x-Q.pinch x)) = 0 := by
  rw [baseVector_inner_trace]
  rw [Q.pinch_pairing τ, Q.pinch_sub, Q.pinch_idempotent, sub_self, mul_zero]
  exact inner_zero_right _

theorem pinch_pythagoras (x : M.toStarSubalgebra) :
    τ.norm₂ (Q.pinch x)^2 + τ.norm₂ (x-Q.pinch x)^2 = τ.norm₂ x^2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (baseVector τ (Q.pinch x)) (baseVector τ (x-Q.pinch x))
    (Q.pinch_residual_orthogonal τ x)
  rw [← map_add, add_sub_cancel] at h
  change τ.norm₂ x * τ.norm₂ x = τ.norm₂ (Q.pinch x)*τ.norm₂ (Q.pinch x) +
    τ.norm₂ (x-Q.pinch x)*τ.norm₂ (x-Q.pinch x) at h
  simpa only [pow_two] using h.symm

theorem pinch_norm₂_le (x : M.toStarSubalgebra) : τ.norm₂ (Q.pinch x) ≤ τ.norm₂ x := by
  have h := Q.pinch_pythagoras τ x
  nlinarith [sq_nonneg (τ.norm₂ (x-Q.pinch x)), show 0 ≤ τ.norm₂ x from norm_nonneg _,
    show 0 ≤ τ.norm₂ (Q.pinch x) from norm_nonneg _]

theorem pinch_block_orthogonal (x : M.toStarSubalgebra) (i j : Fin Q.size) (hij : i ≠ j) :
    star ((Q.piece i).val*x*(Q.piece i).val) * ((Q.piece j).val*x*(Q.piece j).val) = 0 := by
  simp only [star_mul, (Q.piece i).property.isSelfAdjoint.star_eq]
  calc (Q.piece i).val*star x*(Q.piece i).val*((Q.piece j).val*x*(Q.piece j).val) =
      ((Q.piece i).val*star x)*((Q.piece i).val*(Q.piece j).val)*x*(Q.piece j).val := by
        simp only [mul_assoc]
    _ = 0 := by rw [Q.orthogonal i j hij, mul_zero, zero_mul, zero_mul]

theorem pinch_energy (x : M.toStarSubalgebra) :
    τ.norm₂ (Q.pinch x)^2 = ∑ i, τ.norm₂ ((Q.piece i).val*x*(Q.piece i).val)^2 := by
  have h : star (Q.pinch x)*Q.pinch x =
      ∑ i, star ((Q.piece i).val*x*(Q.piece i).val)*((Q.piece i).val*x*(Q.piece i).val) := by
    simp only [pinch, star_sum, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_eq_single i (fun j _ hji => Q.pinch_block_orthogonal x j i hji)
      (by simp)
  rw [norm₂_sq_trace τ, h]
  change (coordinateTraceLinear τ _).re = _
  rw [map_sum, Complex.re_sum]
  exact Finset.sum_congr rfl (fun i _ => (norm₂_sq_trace τ _).symm)

/-- The precise finite energy input is the squared norm of the pinched
corner-centered family; orthogonality proves this equality. -/
theorem pinch_family_energy (F : Finset M.toStarSubalgebra) :
    (∑ i, ∑ x ∈ F, τ.norm₂ ((Q.piece i).val*cornerCentered τ p x*(Q.piece i).val)^2) =
      ∑ x ∈ F, τ.norm₂ (Q.pinch (cornerCentered τ p x))^2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  exact (Q.pinch_energy τ _).symm

/-! Partition refinement decreases the actual compression energy. The final
selection theorem retains membership in the prescribed subalgebra. -/

theorem pinch_corner : Q.pinch p.val = p.val := by
  unfold pinch
  calc (∑ i, (Q.piece i).val*p.val*(Q.piece i).val) = ∑ i, (Q.piece i).val := by
         apply Finset.sum_congr rfl
         intro i _
         rw [projection_mul_of_le (Q.piece_le i), (Q.piece i).property.isIdempotentElem.eq]
    _ = p.val := Q.total

theorem pinch_corner_compression (x : M.toStarSubalgebra) :
    Q.pinch (p.val*x*p.val) = Q.pinch x := by
  unfold pinch
  apply Finset.sum_congr rfl
  intro i _
  have hl : p.val*(Q.piece i).val = (Q.piece i).val := Q.piece_le i
  have hr := projection_mul_of_le (Q.piece_le i)
  simp only [← mul_assoc, hr]
  simp only [mul_assoc, hl]

theorem pinch_cornerCentered (x : M.toStarSubalgebra) :
    Q.pinch (cornerCentered τ p x) = Q.pinch x - cornerScalar τ p x • p.val := by
  rw [cornerCentered, Q.pinch_sub, Q.pinch_smul, Q.pinch_corner, Q.pinch_corner_compression]

theorem pinch_compress_of_le (r : AlgebraProjection M) (i : Fin Q.size)
    (hr : r ≤ Q.piece i) (x : M.toStarSubalgebra) :
    r.val*Q.pinch x*r.val = r.val*x*r.val := by
  have hl : (Q.piece i).val*r.val = r.val := hr
  have hright := projection_mul_of_le hr
  calc r.val*Q.pinch x*r.val = (r.val*(Q.piece i).val)*Q.pinch x*r.val := by rw [hright]
    _ = r.val*((Q.piece i).val*Q.pinch x)*r.val := by rw [mul_assoc r.val]
    _ = r.val*((Q.piece i).val*x*(Q.piece i).val)*r.val := by rw [Q.pinch_left]
    _ = r.val*x*r.val := by
      simp only [← mul_assoc, hright]
      simp only [mul_assoc, hl]

def Refines (R : CornerPartition p) : Prop := ∀ i, ∃ j, R.piece i ≤ Q.piece j

theorem pinch_refinement (R : CornerPartition p) (h : Q.Refines R) (x : M.toStarSubalgebra) :
    R.pinch (Q.pinch x) = R.pinch x := by
  unfold pinch
  apply Finset.sum_congr rfl
  intro i _
  obtain ⟨j,hj⟩ := h i
  exact Q.pinch_compress_of_le (R.piece i) j hj x

theorem refinement_energy_le (R : CornerPartition p) (h : Q.Refines R)
    (x : M.toStarSubalgebra) :
    (∑ i, τ.norm₂ ((R.piece i).val*x*(R.piece i).val)^2) ≤
      ∑ i, τ.norm₂ ((Q.piece i).val*x*(Q.piece i).val)^2 := by
  rw [← R.pinch_energy τ, ← Q.pinch_energy τ, ← Q.pinch_refinement R h x]
  exact pow_le_pow_left₀ (norm_nonneg _) (R.pinch_norm₂_le τ (Q.pinch x)) 2

theorem trace_total : (∑ i, (τ.trace (Q.piece i).val).re) = (τ.trace p.val).re := by
  rw [← Complex.re_sum]
  change (∑ i, coordinateTraceLinear τ (Q.piece i).val).re = _
  rw [← map_sum, Q.total]
  rfl

/-- Converting a genuine pinching budget into the requested nonzero local
piece. The budget is explicit; this theorem does not claim to construct it. -/
theorem exists_local_piece_of_pinching_energy
    (P : StarSubalgebra ℂ M.toStarSubalgebra) (hP : ∀ i, (Q.piece i).val ∈ P)
    (F : Finset M.toStarSubalgebra) (ε : ℝ) (hε : 0 < ε)
    (henergy : (∑ x ∈ F, τ.norm₂ (Q.pinch (cornerCentered τ p x))^2) <
      ε^2 * (τ.trace p.val).re) :
    ∃ q : AlgebraProjection M, q ≤ p ∧ q.val ≠ 0 ∧ q.val ∈ P ∧ ∀ x ∈ F,
      norm₁ τ (q.val*x*q.val-cornerScalar τ p x • q.val) < ε*(τ.trace q.val).re := by
  obtain ⟨q,hqp,hq,⟨i,_,rfl⟩,h⟩ := exists_corner_L1_of_partition_energy τ
    Finset.univ p Q.piece (fun i _ => Q.piece_le i) F ε hε (by
      simpa only [Q.pinch_family_energy τ, Q.trace_total τ] using henergy)
  refine ⟨Q.piece i,hqp,hq,hP i,fun x hx => ?_⟩
  simpa only [compress_cornerCentered τ hqp] using h x hx

end CornerPartition

end

/-! Actual finite refinement of a corner partition by partitions of its blocks.
The dependent family of block sizes is flattened without changing any piece.
No small-energy partition is an input to these constructions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection M}

/-- Reindex an explicitly finite orthogonal family by Fin. -/
def ofFamily {ι : Type*} [Fintype ι] (a : ι → AlgebraProjection M)
    (ha : ∀ i j, i ≠ j → (a i).val*(a j).val=0)
    (ht : ∑ i, (a i).val=p.val) : CornerPartition p where
  size := Fintype.card ι
  piece i := a ((Fintype.equivFin ι).symm i)
  orthogonal i j hij := ha _ _ (fun h => hij ((Fintype.equivFin ι).symm.injective h))
  total := by simpa only using (Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => (a i).val)).trans ht

theorem ofFamily_pinch {ι : Type*} [Fintype ι] (a : ι → AlgebraProjection M)
    (ha : ∀ i j, i ≠ j → (a i).val*(a j).val=0)
    (ht : ∑ i, (a i).val=p.val) (x : M.toStarSubalgebra) :
    (ofFamily a ha ht).pinch x = ∑ i, (a i).val*x*(a i).val := by
  exact Equiv.sum_comp (Fintype.equivFin ι).symm (fun i => (a i).val*x*(a i).val)

/-- The partition with its corner as its only piece. -/
def single (p : AlgebraProjection M) : CornerPartition p where
  size := 1
  piece _ := p
  orthogonal i j hij := (hij (Subsingleton.elim _ _)).elim
  total := by simp

@[simp] theorem single_pinch (p : AlgebraProjection M) (x : M.toStarSubalgebra) :
    (single p).pinch x = p.val*x*p.val := by
  change (∑ _ : Fin 1, p.val*x*p.val) = _
  simp

variable (Q : CornerPartition p) (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

theorem blockFamily_orthogonal (a b : (i : Fin Q.size) × Fin (R i).size) (hab : a ≠ b) :
    ((R a.1).piece a.2).val * ((R b.1).piece b.2).val = 0 := by
  by_cases h : a.1=b.1
  · obtain ⟨i,j⟩ := a
    obtain ⟨k,l⟩ := b
    dsimp at h ⊢
    subst k
    exact (R i).orthogonal j l (fun h => hab (by cases h; rfl))
  · exact orthogonal_subprojections (Q.orthogonal a.1 b.1 h)
      ((R a.1).piece_le a.2) ((R b.1).piece_le b.2)

theorem blockFamily_total :
    (∑ a : (i : Fin Q.size) × Fin (R i).size, ((R a.1).piece a.2).val) = p.val := by
  rw [Fintype.sum_sigma]
  simpa only [(R _).total] using Q.total

/-- All blocks are replaced by their chosen finite subpartitions. -/
def refineBlocks : CornerPartition p :=
  ofFamily (fun a : (i : Fin Q.size) × Fin (R i).size => (R a.1).piece a.2)
    (Q.blockFamily_orthogonal R) (Q.blockFamily_total R)

theorem refineBlocks_refines : Q.Refines (Q.refineBlocks R) := by
  intro i
  let a := (Fintype.equivFin ((j : Fin Q.size) × Fin (R j).size)).symm i
  exact ⟨a.1,(R a.1).piece_le a.2⟩

theorem refineBlocks_mem (P : StarSubalgebra ℂ M.toStarSubalgebra)
    (hP : ∀ i j, ((R i).piece j).val ∈ P) :
    ∀ i, ((Q.refineBlocks R).piece i).val ∈ P := by
  intro i
  exact hP _ _

theorem refineBlocks_pinch (x : M.toStarSubalgebra) :
    (Q.refineBlocks R).pinch x = ∑ i, (R i).pinch x := by
  rw [refineBlocks,ofFamily_pinch,Fintype.sum_sigma]
  rfl

/-- Energy splits into the actual energies of the independently refined blocks. -/
theorem refineBlocks_energy (τ : TracialRepresentation M) (x : M.toStarSubalgebra) :
    τ.norm₂ ((Q.refineBlocks R).pinch x)^2 = ∑ i, τ.norm₂ ((R i).pinch x)^2 := by
  rw [(Q.refineBlocks R).pinch_energy τ]
  change (∑ j, τ.norm₂ (((Q.refineBlocks R).piece j).val*x*
    ((Q.refineBlocks R).piece j).val)^2) = _
  let e := (Fintype.equivFin ((i : Fin Q.size) × Fin (R i).size)).symm
  change (∑ j, τ.norm₂ (((R (e j).1).piece (e j).2).val*x*
    ((R (e j).1).piece (e j).2).val)^2) = _
  rw [show (∑ j, τ.norm₂ (((R (e j).1).piece (e j).2).val*x*
    ((R (e j).1).piece (e j).2).val)^2) =
    ∑ a : (i : Fin Q.size) × Fin (R i).size,
      τ.norm₂ (((R a.1).piece a.2).val*x*((R a.1).piece a.2).val)^2 from
        Equiv.sum_comp e (fun a => τ.norm₂ (((R a.1).piece a.2).val*x*
          ((R a.1).piece a.2).val)^2),Fintype.sum_sigma]
  exact Finset.sum_congr rfl (fun i _ => ((R i).pinch_energy τ x).symm)

theorem refines_refl : Q.Refines Q := fun i => ⟨i,le_refl _⟩

theorem refines_trans {R S : CornerPartition p} (hQR : Q.Refines R) (hRS : R.Refines S) :
    Q.Refines S := by
  intro i
  obtain ⟨j,hj⟩ := hRS i
  obtain ⟨k,hk⟩ := hQR j
  exact ⟨k,hj.trans hk⟩

end CornerPartition

end

/-! Centered energy and the block scalar term that refinement preserves.
A blockwise descent applies to centered compressions, not to their full energy. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem cornerCentered_trace_all (p : AlgebraProjection M) (x : M.toStarSubalgebra) :
    τ.trace (cornerCentered τ p x)=0 := by
  by_cases hp : p.val=0
  · simp only [cornerCentered,hp,zero_mul,mul_zero,smul_zero,sub_zero]
    exact inner_zero_right _
  · exact cornerCentered_trace τ p hp x

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)

theorem pinch_centered_trace (x : M.toStarSubalgebra) :
    τ.trace (Q.pinch (cornerCentered τ p x))=0 := by
  rw [Q.pinch_trace τ,(cornerCentered_support τ p x).1,
    (cornerCentered_support τ p x).2,cornerCentered_trace_all]

theorem pinch_centered_orthogonal (x : M.toStarSubalgebra) (c : ℂ) :
    inner ℂ (baseVector τ (c • p.val))
      (baseVector τ (Q.pinch (cornerCentered τ p x))) = 0 := by
  rw [map_smul,inner_smul_left,baseVector_inner_trace,p.property.isSelfAdjoint.star_eq,
    (Q.pinch_support _).1,Q.pinch_centered_trace τ]
  simp

/-- Pinching energy is centered energy plus the unchanged corner scalar energy. -/
theorem pinch_scalar_energy (x : M.toStarSubalgebra) :
    τ.norm₂ (Q.pinch x)^2 = τ.norm₂ (Q.pinch (cornerCentered τ p x))^2 +
      ‖cornerScalar τ p x‖^2 * (τ.trace p.val).re := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (baseVector τ (cornerScalar τ p x • p.val))
    (baseVector τ (Q.pinch (cornerCentered τ p x)))
    (Q.pinch_centered_orthogonal τ x _)
  rw [← map_add,Q.pinch_cornerCentered τ] at h
  have he : cornerScalar τ p x • p.val +
      (Q.pinch x-cornerScalar τ p x • p.val) = Q.pinch x := by abel
  rw [he,← Q.pinch_cornerCentered τ] at h
  change τ.norm₂ (Q.pinch x)*τ.norm₂ (Q.pinch x) =
    τ.norm₂ (cornerScalar τ p x • p.val)*τ.norm₂ (cornerScalar τ p x • p.val) +
      τ.norm₂ (Q.pinch (cornerCentered τ p x))*τ.norm₂ (Q.pinch (cornerCentered τ p x)) at h
  rw [τ.norm₂_smul] at h
  rw [projection_trace_sq τ p.val p.property]
  nlinarith only [h]

theorem scalar_energy_le_pinch (x : M.toStarSubalgebra) :
    ‖cornerScalar τ p x‖^2 * (τ.trace p.val).re ≤ τ.norm₂ (Q.pinch x)^2 := by
  rw [Q.pinch_scalar_energy τ]
  exact le_add_of_nonneg_left (sq_nonneg _)

end CornerPartition

end

/-! Energy of compatible block refinements, including the scalar term.
The scalar term is necessary even when the original operator has trace zero. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)
variable (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

/-- The part of the compression energy fixed by the current block traces. -/
def scalarEnergy (x : M.toStarSubalgebra) : ℝ :=
  ∑ i, ‖cornerScalar τ (Q.piece i) x‖^2 * (τ.trace (Q.piece i).val).re

theorem scalarEnergy_nonneg (x : M.toStarSubalgebra) : 0 ≤ Q.scalarEnergy τ x := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (sq_nonneg _) (by rw [projection_trace_sq τ _ (Q.piece i).property]; positivity)

theorem refineBlocks_scalar_energy (x : M.toStarSubalgebra) :
    τ.norm₂ ((Q.refineBlocks R).pinch x)^2 =
      (∑ i, τ.norm₂ ((R i).pinch (cornerCentered τ (Q.piece i) x))^2) + Q.scalarEnergy τ x := by
  rw [Q.refineBlocks_energy R τ]
  simp only [scalarEnergy,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => (R i).pinch_scalar_energy τ x)

theorem scalarEnergy_le_refineBlocks (x : M.toStarSubalgebra) :
    Q.scalarEnergy τ x ≤ τ.norm₂ ((Q.refineBlocks R).pinch x)^2 := by
  rw [Q.refineBlocks_scalar_energy τ R]
  exact le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- Compatible descent bounds centered block energies and retains the full
coarse scalar term. In particular it does not multiply that term by c. -/
theorem refineBlocks_descent (x : M.toStarSubalgebra) (c : ℝ)
    (h : ∀ i, τ.norm₂ ((R i).pinch (cornerCentered τ (Q.piece i) x))^2 ≤
      c * τ.norm₂ (cornerCentered τ (Q.piece i) x)^2) :
    τ.norm₂ ((Q.refineBlocks R).pinch x)^2 ≤
      c*(τ.norm₂ (Q.pinch x)^2-Q.scalarEnergy τ x)+Q.scalarEnergy τ x := by
  have he : τ.norm₂ (Q.pinch x)^2 =
      (∑ i, τ.norm₂ (cornerCentered τ (Q.piece i) x)^2)+Q.scalarEnergy τ x := by
    rw [Q.pinch_energy τ]
    have hi (i : Fin Q.size) : τ.norm₂ ((Q.piece i).val*x*(Q.piece i).val)^2 =
        τ.norm₂ (cornerCentered τ (Q.piece i) x)^2+
          ‖cornerScalar τ (Q.piece i) x‖^2*(τ.trace (Q.piece i).val).re := by
      have hh := (single (Q.piece i)).pinch_scalar_energy τ x
      simpa only [single_pinch,(cornerCentered_support τ _ _).1,
        (cornerCentered_support τ _ _).2] using hh
    simp only [hi,Finset.sum_add_distrib,scalarEnergy]
  rw [Q.refineBlocks_scalar_energy τ R,he,add_sub_cancel_right]
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => h i)
  rw [← Finset.mul_sum] at hh
  linarith only [hh]

/-- A target below the current scalar term cannot be reached by refining
these blocks, regardless of the quality of centered local estimates. -/
theorem no_refineBlocks_budget_below_scalar (x : M.toStarSubalgebra) (b : ℝ)
    (hb : b ≤ Q.scalarEnergy τ x) :
    ¬ τ.norm₂ ((Q.refineBlocks R).pinch x)^2 < b :=
  not_lt_of_ge (hb.trans (Q.scalarEnergy_le_refineBlocks τ R x))

end CornerPartition

end Generator.Tracial

end

end OAI
