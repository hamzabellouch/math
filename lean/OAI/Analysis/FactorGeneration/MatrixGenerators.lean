import OAI.Analysis.FactorGeneration.ProjectionEncoding
import OAI.Analysis.FactorGeneration.TensorRefinement

namespace OAI

noncomputable section

namespace Generator

/-! Diagonal projections and one full-support rank-one projection generate
every finite full matrix algebra, including matrices larger than size two. -/
namespace MatrixUnitSystem
open scoped BigOperators
variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable (E : MatrixUnitSystem ι A)

def fullProjectionMatrix : Matrix ι ι ℂ := fun _ _ => (Fintype.card ι : ℂ)⁻¹

omit [DecidableEq ι] in
theorem fullProjectionMatrix_projection [Nonempty ι] :
    IsStarProjection (fullProjectionMatrix (ι := ι)) := by
  have hn : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  constructor
  · ext i j
    simp only [Matrix.mul_apply,fullProjectionMatrix,Finset.sum_const,Finset.card_univ,
      nsmul_eq_mul]
    field_simp
  · ext i j
    simp [fullProjectionMatrix,Matrix.star_apply]

def fullProjection : A := E.hom (fullProjectionMatrix (ι := ι))

theorem fullProjection_projection [Nonempty ι] : IsStarProjection E.fullProjection :=
  (fullProjectionMatrix_projection (ι := ι)).map E.hom

omit [StarModule ℂ A] in
theorem diagonal_commute (i j : ι) : Commute (E.entry i i) (E.entry j j) := by
  show E.entry i i*E.entry j j=E.entry j j*E.entry i i
  by_cases h : i=j
  · subst j; rfl
  · simp [E.mul_entry,h,Ne.symm h]

theorem cut_fullProjection (i j : ι) :
    E.entry i i*E.fullProjection*E.entry j j=(Fintype.card ι : ℂ)⁻¹ • E.entry i j := by
  simp only [fullProjection,hom_apply,fullProjectionMatrix,Finset.mul_sum,Finset.sum_mul,
    mul_smul_comm,E.mul_entry,smul_ite,smul_zero]
  simp [E.mul_entry,smul_ite]

theorem recover_entry [Nonempty ι] (i j : ι) :
    (Fintype.card ι : ℂ) • (E.entry i i*E.fullProjection*E.entry j j)=E.entry i j := by
  rw [E.cut_fullProjection,smul_smul,mul_inv_cancel₀,one_smul]
  exact_mod_cast Fintype.card_ne_zero

theorem fullProjection_mem : E.fullProjection ∈ E.algebra := ⟨_,rfl⟩

theorem algebra_le_of_projection_mem [Nonempty ι] (S : StarSubalgebra ℂ A)
    (hd : ∀ i,E.entry i i ∈ S) (hq : E.fullProjection ∈ S) : E.algebra ≤ S := by
  apply (E.algebra_le_iff S).mpr
  intro i j
  rw [← E.recover_entry i j]
  exact S.smul_mem (S.mul_mem (S.mul_mem (hd i) hq) (hd j)) _

theorem algebra_eq_adjoin_projections [Nonempty ι] :
    E.algebra = StarAlgebra.adjoin ℂ (Set.range (fun i => E.entry i i) ∪ {E.fullProjection}) := by
  apply le_antisymm
  · apply E.algebra_le_of_projection_mem
    · intro i; exact StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨i,rfl⟩)
    · exact StarAlgebra.subset_adjoin ℂ _ (Or.inr rfl)
  · apply StarAlgebra.adjoin_le
    rintro x (⟨i,rfl⟩ | rfl)
    · exact E.entry_mem i i
    · exact E.fullProjection_mem

end MatrixUnitSystem

/-! Two actual self-adjoint generators for the weak closure of countably
many pairwise commuting finite full matrix factors. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem countable_projection_generator {ι : Type*} [Countable ι] [Nonempty ι]
    (e : ι → (H →L[ℂ] H)) (hp : ∀ i,IsStarProjection (e i))
    (hc : ∀ i j,Commute (e i) (e j)) :
    ∃ b : H →L[ℂ] H,IsSelfAdjoint b ∧ ‖b‖ ≤ 1 ∧ wstar {b}=wstar (Set.range e) := by
  obtain ⟨f,hf⟩ := exists_surjective_nat ι
  obtain ⟨b,hb,hn,hgen⟩ := CommutingProjectionEncoding.exists_selfAdjoint_generator
    (fun n => e (f n)) (fun n => hp (f n)) (fun n m => hc (f n) (f m))
  refine ⟨b,hb,hn,hgen.trans ?_⟩
  congr 1
  ext x
  constructor
  · rintro ⟨n,rfl⟩; exact ⟨f n,rfl⟩
  · rintro ⟨i,rfl⟩
    obtain ⟨n,rfl⟩ := hf i
    exact ⟨n,rfl⟩

namespace MatrixUnitSystem
variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem fullProjection_commute (E : MatrixUnitSystem ι A) (F : MatrixUnitSystem κ A)
    (hc : ∀ i j k l,Commute (E.entry i j) (F.entry k l)) :
    Commute E.fullProjection F.fullProjection := by
  apply (E.commute_algebra_iff _).mpr _ _ E.fullProjection_mem
  intro i j
  exact ((F.commute_algebra_iff _).mpr (fun k l => (hc i j k l).symm) _
    F.fullProjection_mem).symm

end MatrixUnitSystem
namespace FiniteMatrixStage
variable {N : VonNeumannAlgebra H}

theorem two_generators_of_commuting_factors (F : ℕ → FiniteMatrixStage N)
    (hc : ∀ n m,n ≠ m → ∀ i j k l,
      Commute ((F n).units.entry i j) ((F m).units.entry k l)) :
    ∃ a ∈ generated F,∃ b ∈ generated F,
      IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a,b}=generated F := by
  classical
  let I := (n : ℕ) × Fin (F n).size
  let : Nonempty I := ⟨⟨0,⟨0,(F 0).positive⟩⟩⟩
  let (n : ℕ) : Nonempty (Fin (F n).size) := ⟨⟨0,(F n).positive⟩⟩
  let d : I → (H →L[ℂ] H) := fun i => ((F i.1).units.entry i.2 i.2).val
  let q : ℕ → (H →L[ℂ] H) := fun n => (F n).units.fullProjection.val
  have hdproj (i : I) : IsStarProjection (d i) :=
    ((F i.1).units.diagonal_projection i.2).map N.toStarSubalgebra.subtype
  have hqproj (n : ℕ) : IsStarProjection (q n) :=
    (F n).units.fullProjection_projection.map N.toStarSubalgebra.subtype
  have hdcomm (i j : I) : Commute (d i) (d j) := by
    obtain ⟨n,i⟩ := i
    obtain ⟨m,j⟩ := j
    by_cases h : n=m
    · subst m
      exact congrArg Subtype.val ((F n).units.diagonal_commute i j).eq
    · exact congrArg Subtype.val (hc n m h i i j j).eq
  have hqcomm (n m : ℕ) : Commute (q n) (q m) := by
    by_cases h : n=m
    · subst m; exact Commute.refl _
    · exact congrArg Subtype.val ((F n).units.fullProjection_commute (F m).units (hc n m h)).eq
  obtain ⟨a,ha,_,hagen⟩ := countable_projection_generator d hdproj hdcomm
  obtain ⟨b,hb,_,hbgen⟩ := countable_projection_generator q hqproj hqcomm
  have hdmem (i : I) : d i ∈ generated F :=
    stage_le_generated F i.1 (((F i.1).units.mem_concreteAlgebra _).mpr
      ((F i.1).units.entry_mem i.2 i.2))
  have hqmem (n : ℕ) : q n ∈ generated F :=
    stage_le_generated F n (((F n).units.mem_concreteAlgebra _).mpr (F n).units.fullProjection_mem)
  have hamem : a ∈ generated F := by
    have hle : wstar {a} ≤ generated F := by
      rw [hagen]
      exact wstar_le (generated_closed F) (by rintro _ ⟨i,rfl⟩; exact hdmem i)
    exact hle (subset_wstar _ rfl)
  have hbmem : b ∈ generated F := by
    have hle : wstar {b} ≤ generated F := by
      rw [hbgen]
      exact wstar_le (generated_closed F) (by rintro _ ⟨n,rfl⟩; exact hqmem n)
    exact hle (subset_wstar _ rfl)
  refine ⟨a,hamem,b,hbmem,ha,hb,le_antisymm ?_ ?_⟩
  · exact wstar_le (generated_closed F) (by rintro _ (rfl | rfl) <;> assumption)
  · apply generated_minimal F _ (wstar_closed _)
    intro n x hx
    let y : N.toStarSubalgebra := ⟨x,(F n).units.concreteAlgebra_le hx⟩
    let S := (wstar {a,b}).comap N.toStarSubalgebra.subtype
    have hdS (i : Fin (F n).size) : (F n).units.entry i i ∈ S := by
      change d ⟨n,i⟩ ∈ wstar {a,b}
      apply (wstar_mono (s := {a}) (t := {a,b}) (by simp))
      rw [hagen]
      exact subset_wstar (Set.range d) (Set.mem_range_self (⟨n,i⟩ : I))
    have hqS : (F n).units.fullProjection ∈ S := by
      change q n ∈ wstar {a,b}
      apply (wstar_mono (s := {b}) (t := {a,b}) (by simp))
      rw [hbgen]
      exact subset_wstar _ (Set.mem_range_self n)
    exact (F n).units.algebra_le_of_projection_mem S hdS hqS
      (((F n).units.mem_concreteAlgebra y).mp hx)

end FiniteMatrixStage

end

/-! The retained tensor extensions supply commuting factors generating
exactly the original matrix-union weak closure. -/
namespace FiniteMatrixStage
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N : VonNeumannAlgebra H}

theorem concrete_le_iff (E : FiniteMatrixStage N) (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    E.units.concreteAlgebra ≤ S ↔ E.units.algebra ≤ S.comap N.toStarSubalgebra.subtype := by
  constructor
  · intro h x hx
    exact h ((E.units.mem_concreteAlgebra x).mpr hx)
  · intro h x hx
    let y : N.toStarSubalgebra := ⟨x,E.units.concreteAlgebra_le hx⟩
    exact h ((E.units.mem_concreteAlgebra y).mp hx)

theorem exists_commuting_factors_of_tensor_extensions (A : ℕ → FiniteMatrixStage N)
    (hzero : A 0=scalarStage N) (hstep : ∀ n,TensorExtension (A n) (A (n+1))) :
    ∃ F : ℕ → FiniteMatrixStage N,
      (∀ n m,n ≠ m → ∀ i j k l,Commute ((F n).units.entry i j) ((F m).units.entry k l)) ∧
      generated F=generated A := by
  have hm : Monotone (fun n => (A n).units.algebra) :=
    monotone_nat_of_le_succ (fun n => (hstep n).algebra_le)
  choose F hc he using hstep
  have hFA (n : ℕ) : (F n).units.algebra ≤ (A (n+1)).units.algebra := by
    rw [he n]; exact le_sup_right
  have hcomm_lt (n m : ℕ) (hnm : n < m) (i j : Fin (F n).size) (k l : Fin (F m).size) :
      Commute ((F n).units.entry i j) ((F m).units.entry k l) := by
    exact ((A m).units.commute_algebra_iff _).mpr (fun a b => hc m a b k l) _
      (hm (Nat.succ_le_of_lt hnm) (hFA n ((F n).units.entry_mem i j)))
  refine ⟨F,?_,le_antisymm ?_ ?_⟩
  · intro n m hnm i j k l
    rcases lt_or_gt_of_ne hnm with h | h
    · exact hcomm_lt n m h i j k l
    · exact (hcomm_lt m n h k l i j).symm
  · apply generated_minimal F _ (generated_closed A)
    intro n
    apply ((F n).concrete_le_iff _).mpr
    exact (hFA n).trans (((A (n+1)).concrete_le_iff _).mp (stage_le_generated A (n+1)))
  · apply generated_minimal A _ (generated_closed F)
    intro n
    apply ((A n).concrete_le_iff _).mpr
    induction n with
    | zero =>
      rw [hzero]
      apply ((scalarStage N).units.algebra_le_iff _).mpr
      intro i j
      exact (generated F).one_mem
    | succ n ih =>
      rw [he n]
      exact sup_le ih (((F n).concrete_le_iff _).mp (stage_le_generated F n))

theorem two_generators_of_tensor_extensions (A : ℕ → FiniteMatrixStage N)
    (hzero : A 0=scalarStage N) (hstep : ∀ n,TensorExtension (A n) (A (n+1))) :
    ∃ a ∈ generated A,∃ b ∈ generated A,
      IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a,b}=generated A := by
  obtain ⟨F,hF,hgen⟩ := exists_commuting_factors_of_tensor_extensions A hzero hstep
  rw [← hgen]
  exact two_generators_of_commuting_factors F hF

end FiniteMatrixStage

/-! The represented irreducible matrix subfactor can be constructed together
with two self-adjoint generators, without hyperfinite uniqueness. -/
namespace Tracial
open UltrapowerBridge FiniteMatrixStage
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {N M : VonNeumannAlgebra H}

theorem exists_irreducible_two_generated_subfactor
    (τ : TracialRepresentation M) (hNM : N ≤ M)
    (hfactor : ∀ c : N.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,a*c=c*a) → ∃ z : ℂ,c=z • (1 : N.toStarSubalgebra))
    (hdiff : ∀ p : N.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
      ∃ q : N.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (hirr : ∀ c : M.toStarSubalgebra,
      (∀ a : N.toStarSubalgebra,coordinateInclusion hNM a*c=c*coordinateInclusion hNM a) →
      ∃ z : ℂ,c=z • (1 : M.toStarSubalgebra))
    (hsep : TopologicalSpace.IsSeparable (Set.range (baseVector τ))) :
    ∃ P : VonNeumannAlgebra H,P ≤ N ∧ IsII1Factor P.toStarSubalgebra ∧
      (∀ c : M.toStarSubalgebra,(∀ a : P.toStarSubalgebra,a.val*c.val=c.val*a.val) →
        c=τ.trace c • (1 : M.toStarSubalgebra)) ∧
      ∃ a ∈ P,∃ b ∈ P,IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ wstar {a,b}=P.toStarSubalgebra := by
  let S : Set M.toStarSubalgebra := {b | τ.trace b=0}
  obtain ⟨x,hx,hdense⟩ := exists_countable_norm₂_dense τ S
    ⟨0,by change τ.trace 0=0; simp [TracialRepresentation.trace]⟩
    (hsep.mono (Set.image_subset_range _ _))
  obtain ⟨A,hA,hstep,_,_,hlim⟩ := exists_countable_tensor_refinement τ hNM
    hfactor hdiff hirr x hx (scalarStage N)
  have hscalar := generated_relative_scalar A τ hNM
    (scalar_common_commutant_of_dense_energy_decay τ hNM A x hdense hlim)
  obtain ⟨a,ha,b,hb,hsa,hsb,hgen⟩ := two_generators_of_tensor_extensions A hA hstep
  exact ⟨generatedVonNeumann A,generatedVonNeumann_le A,
    generated_isII1 A τ hNM hdiff hscalar,hscalar,a,ha,b,hb,hsa,hsb,hgen⟩

end Tracial

end Generator

end

end OAI
