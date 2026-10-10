import OAI.Analysis.FactorGeneration.MatrixExpectation

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! An actual irreducible subalgebra and its constructed conditional
expectation give finite pinching partitions with energy arbitrarily close
to the expectation energy. No partition or expectation is supplied. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_expectation_energy_partition (hNM : N ≤ M)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := N),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (η : ℝ) (hη : 0 < η) :
    ∃ Q : CornerPartition (identityProjection M),
      (∀ i,(Q.piece i).val.val ∈ N) ∧
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) <
        (∑ i ∈ F,τ.norm₂ (conditionalExpectation τ hNM (x i))^2)+η := by
  let Q := CornerPartition.single (identityProjection M)
  have hQ : ∀ i,(Q.piece i).val.val ∈ N := fun _ => N.one_mem
  have hpinch (a : M.toStarSubalgebra) : Q.pinch a=a := by
    rw [CornerPartition.single_pinch]
    change 1*a*1=a
    simp only [one_mul,mul_one]
  obtain ⟨R,_,hR,hE,_⟩ := exists_component_controlled_refinement τ hNM hirr Q hQ
    F x (conditionalExpectation τ hNM ∘ x)
    (fun i _ => conditionalExpectation_mem τ hNM (x i))
    (fun i _ => conditionalExpectation_orthogonal τ hNM (x i))
    (∑ i ∈ F,τ.norm₂ (conditionalExpectation τ hNM (x i))^2) η hη
    (by simp only [Function.comp_apply,hpinch,le_refl])
  exact ⟨R,hR,hE⟩

end

/-! Convert the source's decreasing irreducible chain into actual finite
pinching partitions. The chain and its irreducibility are explicit inputs;
its existence in an arbitrary factor is not asserted. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_decreasing_centered_pinching_partition (A : ℕ → VonNeumannAlgebra H)
    (hAM : ∀ n,A n ≤ M) (hA : Antitone A)
    (hirr : ∀ n,∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := A n),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hscalar : ∀ c : M.toStarSubalgebra,(∀ n,c.val ∈ A n) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (hx : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ n,∃ Q : CornerPartition (identityProjection M),
      (∀ i,(Q.piece i).val.val ∈ A n) ∧
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε := by
  obtain ⟨n,hn⟩ := decreasing_expectations_finite_centered_budget τ A hAM hA hscalar
    F x hx (ε/2) (half_pos hε)
  obtain ⟨Q,hQ,hE⟩ := exists_expectation_energy_partition τ (hAM n) (hirr n)
    F x (ε/2) (half_pos hε)
  exact ⟨n,Q,hQ,by linarith⟩

/-- Center arbitrary elements by their actual scalar trace before selecting
one partition for the whole finite family. -/
theorem exists_decreasing_scalar_pinching_partition (A : ℕ → VonNeumannAlgebra H)
    (hAM : ∀ n,A n ≤ M) (hA : Antitone A)
    (hirr : ∀ n,∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := A n),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hscalar : ∀ c : M.toStarSubalgebra,(∀ n,c.val ∈ A n) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n,∃ Q : CornerPartition (identityProjection M),
      (∀ i,(Q.piece i).val.val ∈ A n) ∧
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i)-τ.trace (x i) • (1 : M.toStarSubalgebra))^2) < ε := by
  let y : ι → M.toStarSubalgebra := fun i => x i-τ.trace (x i) • (1 : M.toStarSubalgebra)
  have hy : ∀ i ∈ F,τ.trace (y i)=0 := by
    intro i _
    dsimp [y]
    change coordinateTraceLinear τ (x i-τ.trace (x i) • (1 : M.toStarSubalgebra))=0
    rw [map_sub,map_smul]
    change τ.trace (x i)-τ.trace (x i)*τ.trace 1=0
    rw [τ.trace_one,mul_one,sub_self]
  obtain ⟨n,Q,hQ,hE⟩ := exists_decreasing_centered_pinching_partition τ A hAM hA hirr hscalar
    F y hy ε hε
  refine ⟨n,Q,hQ,?_⟩
  have h1 : Q.pinch (1 : M.toStarSubalgebra)=1 := by
    unfold CornerPartition.pinch
    simpa only [mul_one,(Q.piece _).property.isIdempotentElem.eq] using
      (show (∑ i,(Q.piece i).val)=1 from Q.total)
  simpa only [y,Q.pinch_sub,Q.pinch_smul,h1] using hE

end

/-! Restrict a compatible unit partition to an actual corner, retaining
all pieces and the exact compression. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition
variable (Q : CornerPartition (identityProjection M)) (p : AlgebraProjection M)
variable (hc : ∀ i,Commute p.val (Q.piece i).val)

def restrictPiece (i : Fin Q.size) : AlgebraProjection M :=
  ⟨p.val*(Q.piece i).val,p.property.mul (Q.piece i).property (hc i)⟩

theorem restrictPiece_le (i : Fin Q.size) : Q.restrictPiece p hc i ≤ Q.piece i := by
  change (Q.piece i).val*(p.val*(Q.piece i).val)=p.val*(Q.piece i).val
  rw [← mul_assoc,← (hc i).eq,mul_assoc,(Q.piece i).property.isIdempotentElem.eq]

def restrictTo : CornerPartition p where
  size := Q.size
  piece := Q.restrictPiece p hc
  orthogonal i j hij := orthogonal_subprojections (Q.orthogonal i j hij)
    (Q.restrictPiece_le p hc i) (Q.restrictPiece_le p hc j)
  total := by
    change (∑ i,p.val*(Q.piece i).val)=p.val
    rw [← Finset.mul_sum,Q.total]
    exact mul_one p.val

theorem restrictTo_mem (P : StarSubalgebra ℂ M.toStarSubalgebra)
    (hp : p.val ∈ P) (hQ : ∀ i,(Q.piece i).val ∈ P) :
    ∀ i,((Q.restrictTo p hc).piece i).val ∈ P :=
  fun i => P.mul_mem hp (hQ i)

theorem restrictTo_pinch (x : M.toStarSubalgebra) :
    (Q.restrictTo p hc).pinch x=Q.pinch (p.val*x*p.val) := by
  unfold pinch
  apply Finset.sum_congr rfl
  intro i _
  change (p.val*(Q.piece i).val)*x*(p.val*(Q.piece i).val)=
    (Q.piece i).val*(p.val*x*p.val)*(Q.piece i).val
  calc (p.val*(Q.piece i).val)*x*(p.val*(Q.piece i).val) =
      ((Q.piece i).val*p.val)*x*(p.val*(Q.piece i).val) :=
        congrArg (fun z => z*x*(p.val*(Q.piece i).val)) (hc i).eq
    _ = _ := by simp only [mul_assoc]

theorem restrictTo_pinch_of_supported (x : M.toStarSubalgebra)
    (hl : p.val*x=x) (hr : x*p.val=x) :
    (Q.restrictTo p hc).pinch x=Q.pinch x := by
  rw [Q.restrictTo_pinch p hc,hl,hr]

/-- The binary partition selecting p and its complement. -/
def splitUnit (p : AlgebraProjection M) : CornerPartition (identityProjection M) :=
  binary (identityProjection M) p (one_mul p.val)

theorem splitUnit_mem (P : StarSubalgebra ℂ M.toStarSubalgebra) (hp : p.val ∈ P) :
    ∀ i,((splitUnit p).piece i).val ∈ P := by
  have hall (b : Bool) :
      ((if b then p else (⟨1-p.val,p.property.one_sub⟩ : AlgebraProjection M))).val ∈ P := by
    cases b
    · exact P.sub_mem P.one_mem hp
    · exact hp
  intro i
  exact hall ((Fintype.equivFin Bool).symm i)

theorem refines_splitUnit_commutes (R : CornerPartition (identityProjection M))
    (h : (splitUnit p).Refines R) : ∀ i,Commute p.val (R.piece i).val := by
  have hall (b : Bool) (r : AlgebraProjection M)
      (hr : r ≤ (if b then p else (⟨1-p.val,p.property.one_sub⟩ : AlgebraProjection M))) :
      Commute p.val r.val := by
    cases b
    · have hl : p.val*r.val=0 := by
        change (1-p.val)*r.val=r.val at hr
        rw [sub_mul,one_mul,sub_eq_self] at hr
        exact hr
      have hright : r.val*p.val=0 := by
        simpa only [star_mul,p.property.isSelfAdjoint.star_eq,
          r.property.isSelfAdjoint.star_eq,star_zero] using congrArg star hl
      show p.val*r.val=r.val*p.val
      rw [hl,hright]
    · change r ≤ p at hr
      show p.val*r.val=r.val*p.val
      rw [show p.val*r.val=r.val from hr,projection_mul_of_le hr]
  intro i
  obtain ⟨j,hj⟩ := h i
  exact hall ((Fintype.equivFin Bool).symm j) (R.piece i) hj

end CornerPartition
end

/-! Complete a corner partition by the complementary projection. This lets
the existing compatible refinement construction act on an actual p-corner. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} {p : AlgebraProjection M}
namespace CornerPartition
variable (Q : CornerPartition p)

def completionPiece : Fin Q.size ⊕ Unit → AlgebraProjection M :=
  Sum.elim Q.piece (fun _ => ⟨1-p.val,p.property.one_sub⟩)

theorem completionPiece_orthogonal (i j : Fin Q.size ⊕ Unit) (h : i ≠ j) :
    (Q.completionPiece i).val*(Q.completionPiece j).val=0 := by
  cases i with
  | inl i =>
    cases j with
    | inl j => exact Q.orthogonal i j (fun he => h (congrArg Sum.inl he))
    | inr j =>
      change (Q.piece i).val*(1-p.val)=0
      rw [mul_sub,mul_one,projection_mul_of_le (Q.piece_le i),sub_self]
  | inr i =>
    cases j with
    | inl j =>
      change (1-p.val)*(Q.piece j).val=0
      rw [sub_mul,one_mul,show p.val*(Q.piece j).val=(Q.piece j).val from Q.piece_le j,sub_self]
    | inr j => exact (h (congrArg Sum.inr (Subsingleton.elim i j))).elim

theorem completionPiece_total : (∑ i, (Q.completionPiece i).val)=(identityProjection M).val := by
  rw [Fintype.sum_sum_type]
  change (∑ i, (Q.piece i).val)+(∑ _ : Unit, (1-p.val))=1
  calc
    _ = p.val+(1-p.val) :=
      congrArg₂ (fun x y : M.toStarSubalgebra => x+y) Q.total (by simp)
    _ = 1 := by abel

def completeUnit : CornerPartition (identityProjection M) :=
  ofFamily Q.completionPiece Q.completionPiece_orthogonal Q.completionPiece_total

theorem completeUnit_mem (P : StarSubalgebra ℂ M.toStarSubalgebra)
    (hp : p.val ∈ P) (hQ : ∀ i,(Q.piece i).val ∈ P) :
    ∀ i,((Q.completeUnit).piece i).val ∈ P := by
  intro i
  change (Q.completionPiece ((Fintype.equivFin (Fin Q.size ⊕ Unit)).symm i)).val ∈ P
  cases (Fintype.equivFin (Fin Q.size ⊕ Unit)).symm i with
  | inl j => exact hQ j
  | inr j => exact P.sub_mem P.one_mem hp

theorem completeUnit_pinch (x : M.toStarSubalgebra) :
    Q.completeUnit.pinch x=Q.pinch x+(1-p.val)*x*(1-p.val) := by
  rw [completeUnit,ofFamily_pinch,Fintype.sum_sum_type]
  simp only [completionPiece,Fintype.sum_unique]
  rfl

theorem completeUnit_pinch_supported (x : M.toStarSubalgebra) (hl : p.val*x=x) :
    Q.completeUnit.pinch x=Q.pinch x := by
  rw [Q.completeUnit_pinch,sub_mul,one_mul,hl,sub_self,zero_mul,add_zero]

theorem completeUnit_refines_split : (splitUnit p).Refines Q.completeUnit := by
  intro i
  let k := (Fintype.equivFin (Fin Q.size ⊕ Unit)).symm i
  change ∃ j, Q.completionPiece k ≤ (splitUnit p).piece j
  cases hk : k with
  | inl a =>
    refine ⟨(Fintype.equivFin Bool) true,?_⟩
    have he : ((splitUnit p).piece ((Fintype.equivFin Bool) true)).val=p.val := by
      change (if (Fintype.equivFin Bool).symm ((Fintype.equivFin Bool) true) = true
        then p else _).val=p.val
      rw [Equiv.symm_apply_apply]
      rfl
    exact (congrArg (fun z : M.toStarSubalgebra => z*(Q.piece a).val) he).trans (Q.piece_le a)
  | inr a =>
    refine ⟨(Fintype.equivFin Bool) false,?_⟩
    have he : ((splitUnit p).piece ((Fintype.equivFin Bool) false)).val=1-p.val := by
      change (if (Fintype.equivFin Bool).symm ((Fintype.equivFin Bool) false) = true
        then p else _).val=1-p.val
      rw [Equiv.symm_apply_apply]
      rfl
    exact (congrArg (fun z : M.toStarSubalgebra => z*(1-p.val)) he).trans
      p.property.one_sub.isIdempotentElem.eq

end CornerPartition
end

/-! Transfer actual corner partitions along a concrete von Neumann
subalgebra inclusion, preserving pieces, pinching and tracial energy. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

namespace CornerPartition
variable {p : AlgebraProjection N} (Q : CornerPartition p)

def mapInclusion (hNM : N ≤ M) : CornerPartition (includedProjection hNM p) where
  size := Q.size
  piece i := includedProjection hNM (Q.piece i)
  orthogonal i j hij := by
    change coordinateInclusion hNM (Q.piece i).val*coordinateInclusion hNM (Q.piece j).val=0
    rw [← map_mul,Q.orthogonal i j hij,map_zero]
  total := by
    change (∑ i,coordinateInclusion hNM (Q.piece i).val)=coordinateInclusion hNM p.val
    rw [← map_sum,Q.total]

theorem include_pinch (hNM : N ≤ M) (x : N.toStarSubalgebra) :
    (Q.mapInclusion hNM).pinch (coordinateInclusion hNM x)=coordinateInclusion hNM (Q.pinch x) := by
  unfold pinch
  change (∑ i,coordinateInclusion hNM (Q.piece i).val*coordinateInclusion hNM x*
    coordinateInclusion hNM (Q.piece i).val)=coordinateInclusion hNM _
  simp only [← map_mul,← map_sum]

theorem include_piece_mem (hNM : N ≤ M) (i : Fin Q.size) :
    ((Q.mapInclusion hNM).piece i).val.val ∈ N := (Q.piece i).val.property

/-- Unit partitions use the ambient identity, with no transport of the
underlying finite index set. -/
def includeUnit (Q : CornerPartition (identityProjection N)) (hNM : N ≤ M) :
    CornerPartition (identityProjection M) where
  size := Q.size
  piece := (Q.mapInclusion hNM).piece
  orthogonal := (Q.mapInclusion hNM).orthogonal
  total := (Q.mapInclusion hNM).total

theorem includeUnit_pinch (Q : CornerPartition (identityProjection N))
    (hNM : N ≤ M) (x : N.toStarSubalgebra) :
    (Q.includeUnit hNM).pinch (coordinateInclusion hNM x)=coordinateInclusion hNM (Q.pinch x) :=
  Q.include_pinch hNM x

theorem includeUnit_energy (Q : CornerPartition (identityProjection N))
    (τ : TracialRepresentation M) (hNM : N ≤ M) (x : N.toStarSubalgebra) :
    τ.norm₂ ((Q.includeUnit hNM).pinch (coordinateInclusion hNM x))^2=
      (restrictedTrace τ hNM).norm₂ (Q.pinch x)^2 := by
  rw [Q.includeUnit_pinch]
  rfl

end CornerPartition
end

/-! The two applications of orthogonal refinement in Popa A.1.2, equations
(2) and (3). The inner decreasing chain need only be irreducible in N;
irreducibility of its terms in the ambient M is not imposed. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_nested_chain_centered_partition (hNM : N ≤ M)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := N),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (A : ℕ → VonNeumannAlgebra H) (hAN : ∀ n,A n ≤ N) (hA : Antitone A)
    (hAirr : ∀ n,∀ c : N.toStarSubalgebra,
      (∀ a : insideAlgebra (M := N) (P := A n),
        (a : N.toStarSubalgebra)*c=c*(a : N.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hscalar : ∀ c : N.toStarSubalgebra,(∀ n,c.val ∈ A n) →
      ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (hx : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition (identityProjection M),
      (∀ i,(Q.piece i).val.val ∈ N) ∧
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε := by
  let y : ι → N.toStarSubalgebra := fun i =>
    ⟨(conditionalExpectation τ hNM (x i)).val,conditionalExpectation_mem τ hNM (x i)⟩
  have he (i : ι) : coordinateInclusion hNM (y i)=conditionalExpectation τ hNM (x i) := rfl
  have hy : ∀ i ∈ F,(restrictedTrace τ hNM).trace (y i)=0 := by
    intro i hi
    rw [restrictedTrace_trace,he,conditionalExpectation_trace,hx i hi]
  obtain ⟨n,Q,hQ,hE⟩ := exists_decreasing_centered_pinching_partition (restrictedTrace τ hNM)
    A hAN hA hAirr hscalar F y hy (ε/2) (half_pos hε)
  let R := Q.includeUnit hNM
  have hR : ∀ i,(R.piece i).val.val ∈ N := Q.include_piece_mem hNM
  have hbudget : (∑ i ∈ F,τ.norm₂ (R.pinch (conditionalExpectation τ hNM (x i)))^2) ≤ ε/2 := by
    have hi (i : ι) : τ.norm₂ (R.pinch (conditionalExpectation τ hNM (x i)))^2=
        (restrictedTrace τ hNM).norm₂ (Q.pinch (y i))^2 := by
      rw [← he]
      exact Q.includeUnit_energy τ hNM (y i)
    simpa only [hi] using hE.le
  obtain ⟨S,_,hS,hE,_⟩ := exists_component_controlled_refinement τ hNM hirr R hR
    F x (conditionalExpectation τ hNM ∘ x)
    (fun i _ => conditionalExpectation_mem τ hNM (x i))
    (fun i _ => conditionalExpectation_orthogonal τ hNM (x i))
    (ε/2) (ε/2) (half_pos hε) hbudget
  exact ⟨S,hS,by linarith⟩

end

/-! Nonzero local projections obtained from the constructed nested-chain
partition. This implements the finite squared-energy selection at the end
of A.1.2, while retaining the chain as a structural premise. -/
open scoped BigOperators
section
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

/-- Finite pinching energy selects one nonzero projection with simultaneous
strict squared-L2 bounds, with the actual trace as the weight. -/
theorem CornerPartition.exists_indexed_local_L2_piece
    {p : AlgebraProjection M} (Q : CornerPartition p)
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (ε : ℝ) (hE : (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε*(τ.trace p.val).re) :
    ∃ j : Fin Q.size,(Q.piece j).val ≠ 0 ∧
      ∀ i ∈ F,τ.norm₂ ((Q.piece j).val*x i*(Q.piece j).val)^2 <
        ε*(τ.trace (Q.piece j).val).re := by
  have htrace := Q.trace_total τ
  have he : (∑ j : Fin Q.size,∑ i ∈ F,τ.norm₂ ((Q.piece j).val*x i*(Q.piece j).val)^2) <
      ε*∑ j : Fin Q.size,(τ.trace (Q.piece j).val).re := by
    rw [Finset.sum_comm,htrace]
    simpa only [← Q.pinch_energy τ] using hE
  obtain ⟨j,_,hj,hjE⟩ := exists_small_energy_piece Finset.univ F
    (fun j => (τ.trace (Q.piece j).val).re)
    (fun j i => τ.norm₂ ((Q.piece j).val*x i*(Q.piece j).val)^2) ε
    (fun j _ => by rw [projection_trace_sq τ _ (Q.piece j).property]; positivity)
    (fun _ _ _ _ => sq_nonneg _) he
  refine ⟨j,?_,hjE⟩
  intro hz
  have ht : τ.trace (Q.piece j).val=0 := by rw [hz]; exact inner_zero_right _
  rw [ht,Complex.zero_re] at hj
  exact (lt_irrefl 0 hj)

theorem exists_nested_chain_local_piece (hNM : N ≤ M)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := N),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (A : ℕ → VonNeumannAlgebra H) (hAN : ∀ n,A n ≤ N) (hA : Antitone A)
    (hAirr : ∀ n,∀ c : N.toStarSubalgebra,
      (∀ a : insideAlgebra (M := N) (P := A n),
        (a : N.toStarSubalgebra)*c=c*(a : N.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hscalar : ∀ c : N.toStarSubalgebra,(∀ n,c.val ∈ A n) →
      ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (hx : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : AlgebraProjection M,q.val ≠ 0 ∧ q.val.val ∈ N ∧
      ∀ i ∈ F,τ.norm₂ (q.val*x i*q.val) < ε*τ.norm₂ q.val ∧
        norm₁ τ (q.val*x i*q.val) < ε*(τ.trace q.val).re := by
  obtain ⟨Q,hQ,hE⟩ := exists_nested_chain_centered_partition τ hNM hirr A hAN hA hAirr hscalar
    F x hx (ε^2) (sq_pos_of_pos hε)
  have he : (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε^2*(τ.trace (identityProjection M).val).re := by
    simpa only [show (identityProjection M).val=1 from rfl,τ.trace_one,Complex.one_re,mul_one] using hE
  obtain ⟨j,hj,hjE⟩ := Q.exists_indexed_local_L2_piece τ F x (ε^2) he
  refine ⟨Q.piece j,hj,hQ j,fun i hi => ?_⟩
  have ht := hjE i hi
  rw [projection_trace_sq τ _ (Q.piece j).property] at ht
  have hn : τ.norm₂ ((Q.piece j).val*x i*(Q.piece j).val) < ε*τ.norm₂ (Q.piece j).val := by
    nlinarith [show 0 ≤ τ.norm₂ ((Q.piece j).val*x i*(Q.piece j).val) from norm_nonneg _,
      mul_nonneg hε.le (show 0 ≤ τ.norm₂ (Q.piece j).val from norm_nonneg _)]
  exact ⟨hn,compression_norm₁_lt_of_norm₂ τ (Q.piece j) hj (x i) ε hn⟩

end

/-! Local quantization by finite matrix approximation and Bell pinching under represented trace-vector separability. -/
open scoped BigOperators
open UltrapowerBridge FiniteMatrixStage
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem exists_matrix_generated_ambient_centered_partition
    (A : ℕ → FiniteMatrixStage N)
    (hA : Monotone (fun n => (A n).units.concreteAlgebra))
    (hNM : N ≤ M) (hfactor : IsII1Factor (generated A))
    (hirr : ∀ c : M.toStarSubalgebra,(∀ a : generated A,a.val*c.val=c.val*a.val) →
      c=τ.trace c • (1 : M.toStarSubalgebra))
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (hx : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition (identityProjection M),
      (∀ i,(Q.piece i).val.val ∈ generated A) ∧
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε := by
  let R := generatedVonNeumann A
  have hRM : R ≤ M := (generatedVonNeumann_le A).trans hNM
  have hirrR : ∀ c : M.toStarSubalgebra,
      (∀ a : insideAlgebra (M := M) (P := R),
        (a : M.toStarSubalgebra)*c=c*(a : M.toStarSubalgebra)) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    refine ⟨τ.trace c,hirr c (fun a => ?_)⟩
    exact congrArg Subtype.val (hc ⟨⟨a.val,hRM a.property⟩,a.property⟩)
  let y : ι → R.toStarSubalgebra := fun i =>
    ⟨(conditionalExpectation τ hRM (x i)).val,conditionalExpectation_mem τ hRM (x i)⟩
  have he (i : ι) : coordinateInclusion hRM (y i)=conditionalExpectation τ hRM (x i) := rfl
  have hy : ∀ i ∈ F,(restrictedTrace τ hRM).trace (y i)=0 := by
    intro i hi
    rw [restrictedTrace_trace,he,conditionalExpectation_trace,hx i hi]
  obtain ⟨Q,hE⟩ := exists_matrix_generated_centered_partition A hA
    (restrictedTrace τ hRM) hfactor F y hy (ε/2) (half_pos hε)
  let Q' := Q.includeUnit hRM
  have hQ' : ∀ i,(Q'.piece i).val.val ∈ R := Q.include_piece_mem hRM
  have hb : (∑ i ∈ F,τ.norm₂ (Q'.pinch (conditionalExpectation τ hRM (x i)))^2) ≤ ε/2 := by
    have hi (i : ι) : τ.norm₂ (Q'.pinch (conditionalExpectation τ hRM (x i)))^2=
        (restrictedTrace τ hRM).norm₂ (Q.pinch (y i))^2 := by
      rw [← he]
      exact Q.includeUnit_energy τ hRM (y i)
    simpa only [hi] using hE.le
  obtain ⟨S,_,hS,hSE,_⟩ := exists_component_controlled_refinement τ hRM hirrR Q' hQ'
    F x (conditionalExpectation τ hRM ∘ x)
    (fun i _ => conditionalExpectation_mem τ hRM (x i))
    (fun i _ => conditionalExpectation_orthogonal τ hRM (x i))
    (ε/2) (ε/2) (half_pos hε) hb
  exact ⟨S,hS,by linarith⟩

theorem exists_irreducible_centered_partition (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (hx : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : CornerPartition (identityProjection M),
      (∀ i,(Q.piece i).val.val ∈ N) ∧
      (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε := by
  obtain ⟨A,_,hA,_,hR,hRN,hRM⟩ :=
    exists_irreducible_matrix_generated_II1 τ hNM hfactor hdiff hirr hsep
  obtain ⟨Q,hQ,hE⟩ := exists_matrix_generated_ambient_centered_partition τ A hA hNM hR hRM
    F x hx ε hε
  exact ⟨Q,fun i => hRN (hQ i),hE⟩

theorem exists_irreducible_local_piece (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ)))
    {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra)
    (hx : ∀ i ∈ F,τ.trace (x i)=0) (ε : ℝ) (hε : 0 < ε) :
    ∃ q : AlgebraProjection M,q.val ≠ 0 ∧ q.val.val ∈ N ∧
      ∀ i ∈ F,τ.norm₂ (q.val*x i*q.val) < ε*τ.norm₂ q.val ∧
        norm₁ τ (q.val*x i*q.val) < ε*(τ.trace q.val).re := by
  obtain ⟨Q,hQ,hE⟩ := exists_irreducible_centered_partition τ hNM hfactor hdiff hirr hsep
    F x hx (ε^2) (sq_pos_of_pos hε)
  have he : (∑ i ∈ F,τ.norm₂ (Q.pinch (x i))^2) < ε^2*(τ.trace (identityProjection M).val).re := by
    simpa only [show (identityProjection M).val=1 from rfl,τ.trace_one,Complex.one_re,mul_one] using hE
  obtain ⟨j,hj,hjE⟩ := Q.exists_indexed_local_L2_piece τ F x (ε^2) he
  refine ⟨Q.piece j,hj,hQ j,fun i hi => ?_⟩
  have ht := hjE i hi
  rw [projection_trace_sq τ _ (Q.piece j).property] at ht
  have hn : τ.norm₂ ((Q.piece j).val*x i*(Q.piece j).val) < ε*τ.norm₂ (Q.piece j).val := by
    nlinarith [show 0 ≤ τ.norm₂ ((Q.piece j).val*x i*(Q.piece j).val) from norm_nonneg _,
      mul_nonneg hε.le (show 0 ≤ τ.norm₂ (Q.piece j).val from norm_nonneg _)]
  exact ⟨hn,compression_norm₁_lt_of_norm₂ τ (Q.piece j) hj (x i) ε hn⟩

end Generator.Tracial

end

end OAI
