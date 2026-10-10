import OAI.Analysis.FactorGeneration.SpectralPinching

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Common finite refinements of two commuting corner partitions. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition
variable {p : AlgebraProjection M} (Q R : CornerPartition p)
variable (hc : ∀ i j, Commute (Q.piece i).val (R.piece j).val)

def jointPiece (a : Fin Q.size × Fin R.size) : AlgebraProjection M :=
  ⟨(Q.piece a.1).val*(R.piece a.2).val,
    (Q.piece a.1).property.mul (R.piece a.2).property (hc a.1 a.2)⟩

theorem jointPiece_le_left (a : Fin Q.size × Fin R.size) : Q.jointPiece R hc a ≤ Q.piece a.1 := by
  change (Q.piece a.1).val*((Q.piece a.1).val*(R.piece a.2).val)=(Q.piece a.1).val*(R.piece a.2).val
  rw [← mul_assoc,(Q.piece a.1).property.isIdempotentElem.eq]

theorem jointPiece_le_right (a : Fin Q.size × Fin R.size) : Q.jointPiece R hc a ≤ R.piece a.2 := by
  change (R.piece a.2).val*((Q.piece a.1).val*(R.piece a.2).val)=(Q.piece a.1).val*(R.piece a.2).val
  rw [← mul_assoc,← (hc a.1 a.2).eq,mul_assoc,(R.piece a.2).property.isIdempotentElem.eq]

theorem jointPiece_orthogonal (a b : Fin Q.size × Fin R.size) (hab : a ≠ b) :
    (Q.jointPiece R hc a).val*(Q.jointPiece R hc b).val=0 := by
  by_cases h : a.1=b.1
  · have h₂ : a.2 ≠ b.2 := fun h₂ => hab (Prod.ext h h₂)
    exact orthogonal_subprojections (R.orthogonal a.2 b.2 h₂)
      (Q.jointPiece_le_right R hc a) (Q.jointPiece_le_right R hc b)
  · exact orthogonal_subprojections (Q.orthogonal a.1 b.1 h)
      (Q.jointPiece_le_left R hc a) (Q.jointPiece_le_left R hc b)

theorem jointPiece_total : (∑ a : Fin Q.size × Fin R.size, (Q.jointPiece R hc a).val)=p.val := by
  change (∑ a : Fin Q.size × Fin R.size, (Q.piece a.1).val*(R.piece a.2).val)=p.val
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum,R.total,projection_mul_of_le (Q.piece_le _)]
  exact Q.total

def joint : CornerPartition p := ofFamily (Q.jointPiece R hc)
  (Q.jointPiece_orthogonal R hc) (Q.jointPiece_total R hc)

theorem joint_refines_left : Q.Refines (Q.joint R hc) := by
  intro i
  let a := (Fintype.equivFin (Fin Q.size × Fin R.size)).symm i
  exact ⟨a.1,Q.jointPiece_le_left R hc a⟩

theorem joint_refines_right : R.Refines (Q.joint R hc) := by
  intro i
  let a := (Fintype.equivFin (Fin Q.size × Fin R.size)).symm i
  exact ⟨a.2,Q.jointPiece_le_right R hc a⟩

/-- A spectral sum on Q is represented exactly on the common refinement. -/
theorem joint_sum_left (c : Fin Q.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size, c a.1 • (Q.jointPiece R hc a).val)=
      ∑ i, c i • (Q.piece i).val := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ j, c i • ((Q.piece i).val*(R.piece j).val))=_
  rw [← Finset.smul_sum,← Finset.mul_sum,R.total,projection_mul_of_le (Q.piece_le i)]

theorem joint_sum_right (c : Fin R.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size, c a.2 • (Q.jointPiece R hc a).val)=
      ∑ j, c j • (R.piece j).val := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ i, c j • ((Q.piece i).val*(R.piece j).val))=_
  rw [← Finset.smul_sum,← Finset.sum_mul,Q.total]
  have hleft : p.val*(R.piece j).val=(R.piece j).val := R.piece_le j
  rw [hleft]

end CornerPartition

/-! Simultaneous finite spectral approximation of two commuting self-adjoint
operators. The same actual partition is used for both. -/

theorem exists_joint_spectral_approximation (p : AlgebraProjection M)
    (a b : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hab : Commute a b) (hpa : Commute p.val a) (hpb : Commute p.val b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : CornerPartition p) (c d : Fin S.size → ℝ),
      ‖p.val*a*p.val-∑ i, (c i : ℂ) • (S.piece i).val‖ < ε ∧
      ‖p.val*b*p.val-∑ i, (d i : ℂ) • (S.piece i).val‖ < ε := by
  obtain ⟨Q,c,hQfix,hQ,hc⟩ := exists_finite_spectral_approximation_preserving_commutant p a ha ε hε
  obtain ⟨R,d,hRfix,hR,hd⟩ := exists_finite_spectral_approximation_preserving_commutant p b hb ε hε
  have hcross (i : Fin Q.size) (j : Fin R.size) : Commute (Q.piece i).val (R.piece j).val := by
    have hqp : Commute p.val (Q.piece i).val :=
      (hQ p.val hpa.symm (Commute.refl _) i).symm
    exact (hR (Q.piece i).val (hQ b hab hpb i).symm hqp j).symm
  let e := (Fintype.equivFin (Fin Q.size × Fin R.size)).symm
  refine ⟨Q.joint R hcross,fun i => c (e i).1,fun i => d (e i).2,?_,?_⟩
  · have he := Equiv.sum_comp e (fun i => (c i.1 : ℂ) • (Q.jointPiece R hcross i).val)
    change ‖p.val*a*p.val-∑ i, (c (e i).1 : ℂ) • (Q.jointPiece R hcross (e i)).val‖ < ε
    rw [he,Q.joint_sum_left R hcross (fun i => (c i : ℂ))]
    exact hc
  · have he := Equiv.sum_comp e (fun i => (d i.2 : ℂ) • (Q.jointPiece R hcross i).val)
    change ‖p.val*b*p.val-∑ i, (d (e i).2 : ℂ) • (Q.jointPiece R hcross (e i)).val‖ < ε
    rw [he,Q.joint_sum_right R hcross (fun i => (d i : ℂ))]
    exact hd

/-- Complex finite spectral sums are constructed from the joint real and
imaginary approximations. No small pinching-energy premise occurs. -/
theorem exists_complex_spectral_approximation (p : AlgebraProjection M)
    (a b : M.toStarSubalgebra) (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hab : Commute a b) (hpa : Commute p.val a) (hpb : Commute p.val b)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : CornerPartition p) (c : Fin S.size → ℂ),
      ‖p.val*(a+Complex.I • b)*p.val-∑ i, c i • (S.piece i).val‖ < ε := by
  obtain ⟨S,c,d,hc,hd⟩ := exists_joint_spectral_approximation p a b ha hb hab hpa hpb
    (ε/2) (half_pos hε)
  refine ⟨S,fun i => (c i : ℂ)+Complex.I*(d i : ℂ),?_⟩
  have he : p.val*(a+Complex.I • b)*p.val-
      (∑ i, ((c i : ℂ)+Complex.I*(d i : ℂ)) • (S.piece i).val) =
      (p.val*a*p.val-∑ i, (c i : ℂ) • (S.piece i).val)+
        Complex.I • (p.val*b*p.val-∑ i, (d i : ℂ) • (S.piece i).val) := by
    simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,add_smul,
      mul_smul,Finset.sum_add_distrib,Finset.smul_sum,smul_sub]
    abel
  rw [he]
  have hn := norm_add_le (p.val*a*p.val-∑ i, (c i : ℂ) • (S.piece i).val)
    (Complex.I • (p.val*b*p.val-∑ i, (d i : ℂ) • (S.piece i).val))
  rw [norm_smul,Complex.norm_I,one_mul] at hn
  linarith

end

/-! Finite spectral approximation for an actual normal operator. -/
section
open scoped BigOperators ComplexStarModule
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

def identityProjection (M : VonNeumannAlgebra H) : AlgebraProjection M := ⟨1,IsStarProjection.one _⟩

theorem exists_normal_spectral_approximation (x : M.toStarSubalgebra) [IsStarNormal x]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition (identityProjection M)) (c : Fin Q.size → ℂ),
      ‖x-∑ i, c i • (Q.piece i).val‖ < ε := by
  obtain ⟨Q,c,h⟩ := exists_complex_spectral_approximation (identityProjection M)
    (ℜ x) (ℑ x) (ℜ x).property (ℑ x).property (Commute.realPart_imaginaryPart x)
    (Commute.one_left _) (Commute.one_left _) ε hε
  refine ⟨Q,c,?_⟩
  simpa only [identityProjection,one_mul,mul_one,realPart_add_I_smul_imaginaryPart] using h

theorem exists_unitary_spectral_approximation (u : unitary M.toStarSubalgebra)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition (identityProjection M)) (c : Fin Q.size → ℂ),
      ‖(u : M.toStarSubalgebra)-∑ i, c i • (Q.piece i).val‖ < ε := by
  let : IsStarNormal (u : M.toStarSubalgebra) := ⟨by change star (u : M.toStarSubalgebra)*(u : M.toStarSubalgebra) = (u : M.toStarSubalgebra)*star (u : M.toStarSubalgebra); rw [u.property.1,u.property.2]⟩
  exact exists_normal_spectral_approximation (u : M.toStarSubalgebra) ε hε

end

/-! Transport constructed spectral partitions through an actual inclusion of
von Neumann algebras on the same Hilbert space. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

def algebraInclusion (h : N ≤ M) : N.toStarSubalgebra →⋆ₐ[ℂ] M.toStarSubalgebra :=
  StarSubalgebra.inclusion h

def includedProjection (h : N ≤ M) (p : AlgebraProjection N) : AlgebraProjection M :=
  ⟨algebraInclusion h p.val,by
    constructor
    · change algebraInclusion h p.val * algebraInclusion h p.val = algebraInclusion h p.val
      rw [← map_mul,p.property.isIdempotentElem.eq]
    · change star (algebraInclusion h p.val)=algebraInclusion h p.val
      rw [← map_star,p.property.isSelfAdjoint.star_eq]⟩

def includedUnitPartition (h : N ≤ M) (Q : CornerPartition (identityProjection N)) :
    CornerPartition (identityProjection M) where
  size := Q.size
  piece i := includedProjection h (Q.piece i)
  orthogonal i j hij := by
    change algebraInclusion h (Q.piece i).val * algebraInclusion h (Q.piece j).val=0
    rw [← map_mul,Q.orthogonal i j hij,map_zero]
  total := by
    change (∑ i,algebraInclusion h (Q.piece i).val)=1
    rw [← map_sum,Q.total]
    exact map_one (algebraInclusion h)

theorem includedUnitPartition_mem (h : N ≤ M) (Q : CornerPartition (identityProjection N))
    (i : Fin Q.size) : ((includedUnitPartition h Q).piece i).val.val ∈ N :=
  (Q.piece i).val.property

theorem exists_unitary_subalgebra_spectral_approximation (h : N ≤ M)
    (u : unitary M.toStarSubalgebra) (hu : (u : M.toStarSubalgebra).val ∈ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (Q : CornerPartition (identityProjection M)) (c : Fin Q.size → ℂ),
      (∀ i, (Q.piece i).val.val ∈ N) ∧
      ‖(u : M.toStarSubalgebra)-∑ i, c i • (Q.piece i).val‖ < ε := by
  let uN : unitary N.toStarSubalgebra := ⟨⟨(u : M.toStarSubalgebra).val,hu⟩,by
    constructor
    · apply Subtype.ext
      exact congrArg (fun z : M.toStarSubalgebra => z.val) u.property.1
    · apply Subtype.ext
      exact congrArg (fun z : M.toStarSubalgebra => z.val) u.property.2⟩
  obtain ⟨Q,c,hc⟩ := exists_unitary_spectral_approximation uN ε hε
  refine ⟨includedUnitPartition h Q,c,includedUnitPartition_mem h Q,?_⟩
  have hn : ‖algebraInclusion h ((uN : N.toStarSubalgebra)-
      ∑ i,c i • (Q.piece i).val)‖=‖(uN : N.toStarSubalgebra)-
      ∑ i,c i • (Q.piece i).val‖ := rfl
  rw [map_sub,map_sum] at hn
  simp only [map_smul] at hn
  change ‖(u : M.toStarSubalgebra)-∑ i,c i • algebraInclusion h (Q.piece i).val‖ < ε
  exact hn ▸ hc

end

/-! Finite simultaneous spectral approximation of any commuting self-adjoint
family, preserving a prior partition and the entire common commutant. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace CornerPartition

theorem joint_preserves_commutant (Q R : CornerPartition (identityProjection M))
    (hcross : ∀ i j,Commute (Q.piece i).val (R.piece j).val)
    (y : M.toStarSubalgebra)
    (hQ : ∀ i,Commute (Q.piece i).val y) (hR : ∀ j,Commute (R.piece j).val y) :
    ∀ k,Commute ((Q.joint R hcross).piece k).val y := by
  intro k
  let a := (Fintype.equivFin (Fin Q.size × Fin R.size)).symm k
  exact (hQ a.1).mul_left (hR a.2)

theorem joint_spectral_sum_left (Q R : CornerPartition (identityProjection M))
    (hcross : ∀ i j,Commute (Q.piece i).val (R.piece j).val)
    (c : Fin Q.size → ℂ) :
    ∃ d : Fin (Q.joint R hcross).size → ℂ,
      (∑ k,d k • ((Q.joint R hcross).piece k).val)=∑ i,c i • (Q.piece i).val := by
  let e := (Fintype.equivFin (Fin Q.size × Fin R.size)).symm
  refine ⟨fun k => c (e k).1,?_⟩
  exact (Equiv.sum_comp e (fun a => c a.1 • (Q.jointPiece R hcross a).val)).trans
    (Q.joint_sum_left R hcross c)

theorem joint_spectral_sum_right (Q R : CornerPartition (identityProjection M))
    (hcross : ∀ i j,Commute (Q.piece i).val (R.piece j).val)
    (c : Fin R.size → ℂ) :
    ∃ d : Fin (Q.joint R hcross).size → ℂ,
      (∑ k,d k • ((Q.joint R hcross).piece k).val)=∑ i,c i • (R.piece i).val := by
  let e := (Fintype.equivFin (Fin Q.size × Fin R.size)).symm
  refine ⟨fun k => c (e k).2,?_⟩
  exact (Equiv.sum_comp e (fun a => c a.2 • (Q.jointPiece R hcross a).val)).trans
    (Q.joint_sum_right R hcross c)

end CornerPartition

theorem exists_finite_abelian_spectral_refinement {ι : Type*}
    (x : ι → M.toStarSubalgebra) (hx : ∀ i,IsSelfAdjoint (x i))
    (hcomm : ∀ i j,Commute (x i) (x j))
    (Q : CornerPartition (identityProjection M))
    (hQ : ∀ y : M.toStarSubalgebra,(∀ i,Commute (x i) y) →
      ∀ j,Commute (Q.piece j).val y)
    (F : Finset ι) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : CornerPartition (identityProjection M),Q.Refines R ∧
      (∀ y : M.toStarSubalgebra,(∀ i,Commute (x i) y) →
        ∀ j,Commute (R.piece j).val y) ∧
      ∀ i ∈ F,∃ c : Fin R.size → ℂ,‖x i-∑ j,c j • (R.piece j).val‖ < ε := by
  classical
  induction F using Finset.induction_on generalizing Q with
  | empty => exact ⟨Q,Q.refines_refl,hQ,by simp⟩
  | @insert i F hiF ih =>
    obtain ⟨R,hQR,hR,happrox⟩ := ih Q hQ
    obtain ⟨S,c,_,hS,hc⟩ := exists_finite_spectral_approximation_preserving_commutant
      (identityProjection M) (x i) (hx i) ε hε
    have hcross (j : Fin R.size) (k : Fin S.size) :
        Commute (R.piece j).val (S.piece k).val :=
      (hS (R.piece j).val (hR (x i) (fun l => hcomm l i) j).symm (Commute.one_left _) k).symm
    refine ⟨R.joint S hcross,Q.refines_trans hQR (R.joint_refines_left S hcross),?_,?_⟩
    · intro y hy
      exact R.joint_preserves_commutant S hcross y (hR y hy)
        (hS y (hy i) (Commute.one_left _))
    · intro l hl
      rcases Finset.mem_insert.mp hl with rfl | hl
      · obtain ⟨d,hd⟩ := R.joint_spectral_sum_right S hcross (fun j => (c j : ℂ))
        refine ⟨d,?_⟩
        rw [hd]
        simpa only [show (identityProjection M).val=1 from rfl,one_mul,mul_one] using hc
      · obtain ⟨a,ha⟩ := happrox l hl
        obtain ⟨d,hd⟩ := R.joint_spectral_sum_left S hcross a
        exact ⟨d,by rwa [hd]⟩

end

/-! Finite orthogonal families can be completed to unit partitions. Refining
blocks retains explicit disjoint index sets whose sums recover those blocks. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem orthogonal_family_sum_projection {ι : Type*} [Fintype ι]
    (q : ι → AlgebraProjection M)
    (hq : ∀ i j, i ≠ j → (q i).val*(q j).val=0) :
    IsStarProjection (∑ i,(q i).val) := by
  classical
  constructor
  · show (∑ i,(q i).val)*(∑ i,(q i).val)=∑ i,(q i).val
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum,Finset.sum_eq_single i]
    · exact (q i).property.isIdempotentElem.eq
    · intro j _ hji
      exact hq i j hji.symm
    · simp
  · show star (∑ i,(q i).val)=∑ i,(q i).val
    simp only [star_sum, (q _).property.isSelfAdjoint.star_eq]

theorem exists_completed_orthogonal_family {ι : Type*} [Fintype ι]
    (q : ι → AlgebraProjection M)
    (hq : ∀ i j, i ≠ j → (q i).val*(q j).val=0) :
    ∃ Q : CornerPartition (identityProjection M),
      ∃ e : Option ι ≃ Fin Q.size,
        (∀ i,Q.piece (e (some i))=q i) ∧
        (Q.piece (e none)).val=1-∑ i,(q i).val := by
  classical
  let s := ∑ i,(q i).val
  have hs : IsStarProjection s := orthogonal_family_sum_projection q hq
  let a : Option ι → AlgebraProjection M := fun i =>
    i.elim ⟨1-s,hs.one_sub⟩ q
  have hleft (i : ι) : s*(q i).val=(q i).val := by
    dsimp [s]
    rw [Finset.sum_mul,Finset.sum_eq_single i]
    · exact (q i).property.isIdempotentElem.eq
    · intro j _ hji
      exact hq j i hji
    · simp
  have hright (i : ι) : (q i).val*s=(q i).val := by
    simpa only [star_mul,hs.isSelfAdjoint.star_eq,
      (q i).property.isSelfAdjoint.star_eq] using congrArg star (hleft i)
  have ha (i j : Option ι) (hij : i ≠ j) : (a i).val*(a j).val=0 := by
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => change (1-s)*(q j).val=0; rw [sub_mul,one_mul,hleft,sub_self]
    | some i =>
      cases j with
      | none => change (q i).val*(1-s)=0; rw [mul_sub,mul_one,hright,sub_self]
      | some j => exact hq i j (fun h => hij (congrArg some h))
  have ht : (∑ i,(a i).val)=(identityProjection M).val := by
    rw [Fintype.sum_option]
    change (1-s)+s=1
    abel
  let Q := CornerPartition.ofFamily a ha ht
  refine ⟨Q,Fintype.equivFin (Option ι),?_,?_⟩
  · intro i
    change a ((Fintype.equivFin (Option ι)).symm
      ((Fintype.equivFin (Option ι)) (some i)))=q i
    rw [Equiv.symm_apply_apply]
    rfl
  · change (a ((Fintype.equivFin (Option ι)).symm
      ((Fintype.equivFin (Option ι)) none))).val=1-s
    rw [Equiv.symm_apply_apply]
    rfl

namespace CornerPartition
variable {p : AlgebraProjection M} (Q : CornerPartition p)
variable (R : (i : Fin Q.size) → CornerPartition (Q.piece i))

def blockIndices (i : Fin Q.size) : Finset (Fin (Q.refineBlocks R).size) :=
  Finset.univ.filter fun j =>
    ((Fintype.equivFin ((k : Fin Q.size) × Fin (R k).size)).symm j).1=i

theorem blockIndices_disjoint {i j : Fin Q.size} (hij : i ≠ j) :
    Disjoint (Q.blockIndices R i) (Q.blockIndices R j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro k hi hj
  exact hij ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hj).2)

theorem sum_blockIndices (i : Fin Q.size) :
    (∑ j ∈ Q.blockIndices R i,((Q.refineBlocks R).piece j).val)=(Q.piece i).val := by
  classical
  rw [blockIndices,Finset.sum_filter]
  let e := (Fintype.equivFin ((k : Fin Q.size) × Fin (R k).size)).symm
  change (∑ j,if (e j).1=i then ((R (e j).1).piece (e j).2).val else 0)=_
  rw [Equiv.sum_comp e (fun a => if a.1=i then ((R a.1).piece a.2).val else 0),
    Fintype.sum_sigma]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,(R _).total]
  simp

end CornerPartition

end Generator.Tracial

end

end OAI
