import Mathlib.Data.Fintype.EquivFin
import OAI.Analysis.FactorGeneration.FiniteComparison
import OAI.Analysis.FactorGeneration.MatrixUnits

namespace OAI

noncomputable section

namespace Generator

/-! Halving every projection in a diffuse factor without a trace.
Maximality leaves no residual corner: a diffuse residual splits into two
nonzero orthogonal projections, and a polar link gives a strict extension. -/
section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}

/-- The sum of two orthogonal projections, in the original algebra. -/
def orthogonalSum (p q : AlgebraProjection M) (h : p.val*q.val=0) : AlgebraProjection M :=
  ⟨p.val+q.val,p.property.add q.property h⟩

theorem le_orthogonalSum_left (p q : AlgebraProjection M) (h : p.val*q.val=0) :
    p ≤ orthogonalSum p q h := by
  change (p.val+q.val)*p.val=p.val
  rw [add_mul,p.property.isIdempotentElem.eq,PartialIsometry.orthogonal_reverse _ _ h,add_zero]

theorem le_orthogonalSum_right (p q : AlgebraProjection M) (h : p.val*q.val=0) :
    q ≤ orthogonalSum p q h := by
  change (p.val+q.val)*q.val=q.val
  rw [add_mul,h,q.property.isIdempotentElem.eq,zero_add]

theorem orthogonalSum_le {p q r : AlgebraProjection M} (h : p.val*q.val=0)
    (hp : p ≤ r) (hq : q ≤ r) : orthogonalSum p q h ≤ r := by
  change r.val*(p.val+q.val)=p.val+q.val
  rw [mul_add,hp,hq]

/-- A proper diffuse subprojection splits a nonzero corner into orthogonal pieces. -/
theorem traceFree_exists_orthogonal_split
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : AlgebraProjection M) (hp : p.val≠0) :
    ∃ q r : AlgebraProjection M, q ≤ p ∧ r ≤ p ∧ q.val≠0 ∧ r.val≠0 ∧
      q.val*r.val=0 ∧ q.val+r.val=p.val := by
  obtain ⟨q,hq,hq0,hqp,hpq,hqp'⟩ := hdiff p.val p.property hp
  let r : AlgebraProjection M := ⟨p.val-q,hq.sub_of_mul_eq_right p.property hpq⟩
  refine ⟨⟨q,hq⟩,r,hpq,?_,hq0,sub_ne_zero.mpr hqp.symm,?_,?_⟩
  · change p.val*(p.val-q)=p.val-q
    rw [mul_sub,p.property.isIdempotentElem.eq,hpq]
  · change q*(p.val-q)=0
    rw [mul_sub,hqp',hq.isIdempotentElem.eq,sub_self]
  · change q+(p.val-q)=p.val
    abel

/-- The two equivalent halves are constructed by an actual partial isometry.
No trace, finite-isometry property, or separability is needed for this lemma. -/
theorem traceFree_exists_halving
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
      ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
    (p : AlgebraProjection M) :
    ∃ v : PartialIsometry M, v.support.val*v.target.val=0 ∧
      v.support.val+v.target.val=p.val := by
  obtain ⟨v,hvp,hvq,hvo,hmax⟩ := PartialIsometry.traceFree_exists_maximal_orthogonal p
  let t := orthogonalSum v.support v.target hvo
  have htp : t ≤ p := orthogonalSum_le hvo hvp hvq
  let r : AlgebraProjection M := ⟨p.val-t.val,t.property.sub_of_mul_eq_right p.property htp⟩
  have hrp : r ≤ p := by
    change p.val*(p.val-t.val)=p.val-t.val
    rw [mul_sub,p.property.isIdempotentElem.eq,htp]
  have htr : t.val*r.val=0 := by
    change t.val*(p.val-t.val)=0
    rw [mul_sub,projection_mul_of_le htp,t.property.isIdempotentElem.eq,sub_self]
  have hr0 : r.val=0 := by
    by_contra hr
    obtain ⟨q,s,hqr,hsr,hq0,hs0,hqs,_⟩ := traceFree_exists_orthogonal_split hdiff r hr
    obtain ⟨w,hwq,hws,hw0⟩ :=
      traceFree_exists_nonzero_partialIsometry_between_projections hfactor q s hq0 hs0
    have hwr : w.support ≤ r := hwq.trans hqr
    have hwtr : w.target ≤ r := hws.trans hsr
    have hvt : v.support ≤ t := le_orthogonalSum_left _ _ hvo
    have hvtt : v.target ≤ t := le_orthogonalSum_right _ _ hvo
    have hpw := projection_orthogonal_of_le htr hvt hwr
    have hqw := projection_orthogonal_of_le htr hvtt hwtr
    have hcross := projection_orthogonal_of_le htr hvt hwtr
    have hcross' := PartialIsometry.orthogonal_reverse _ _
      (projection_orthogonal_of_le htr hvtt hwr)
    have hwo := projection_orthogonal_of_le hqs hwq hws
    let u := v.patch w hpw hqw
    have hup : u.support ≤ p := orthogonalSum_le hpw hvp (hwr.trans hrp)
    have huq : u.target ≤ p := by
      change p.val*u.target.val=u.target.val
      rw [PartialIsometry.patch_target]
      rw [mul_add,hvq,show p.val*w.target.val=w.target.val from hwtr.trans hrp]
    have huo : u.support.val*u.target.val=0 := by
      rw [PartialIsometry.patch_target]
      change (v.support.val+w.support.val)*(v.target.val+w.target.val)=0
      rw [add_mul,mul_add,mul_add,hvo,hcross,hcross',hwo,add_zero,zero_add]
    have hvu : v ≤ u := v.le_patch w hpw hqw
    exact (v.patch_ne w hpw hqw hw0) (le_antisymm (hmax u hup huq huo hvu) hvu)
  exact ⟨v,hvo,(sub_eq_zero.mp hr0).symm⟩

end Tracial

/-- Halving in exactly the original concrete factor; the bicommutant packaging
does not change its operators, projection predicates, or algebra operations. -/
theorem isII1Factor_halving
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsII1Factor S)
    (p : Tracial.AlgebraProjection (vonNeumannOfWOTClosed S hS.weaklyClosed)) :
    ∃ v : Tracial.PartialIsometry (vonNeumannOfWOTClosed S hS.weaklyClosed),
      v.support.val*v.target.val=0 ∧ v.support.val+v.target.val=p.val := by
  apply Tracial.traceFree_exists_halving _ hS.diffuse p
  intro c hc
  obtain ⟨z,hz⟩ := hS.factor c hc
  exact ⟨z,hz.trans (Algebra.algebraMap_eq_smul_one z)⟩

end

/-! Finite partitions with explicit equivalence witnesses and compatible binary
refinement. The common initial projection is halved once and its two pieces
are transported to every old piece, so all new pieces remain equivalent. -/
section
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

/-- Composition with range contained in the initial projection. -/
def compose (v w : PartialIsometry M) (h : w.target ≤ v.support) : PartialIsometry M where
  support := w.support
  val := v.val*w.val
  initial := by
    calc star (v.val*w.val)*(v.val*w.val) = star w.val*(star v.val*v.val)*w.val := by
           simp only [star_mul,mul_assoc]
         _ = star w.val*w.val := by
           rw [v.initial,mul_assoc,(w.target_le_iff_mul v.support).mp h]
         _ = w.support.val := w.initial

theorem compose_target (v w : PartialIsometry M) (h : w.target ≤ v.support) :
    (compose v w h).target.val=v.val*w.target.val*star v.val := by
  change (v.val*w.val)*star (v.val*w.val)=v.val*(w.val*star w.val)*star v.val
  simp only [star_mul,mul_assoc]

theorem compose_target_le (v w : PartialIsometry M) (h : w.target ≤ v.support) :
    (compose v w h).target ≤ v.target := by
  apply ((compose v w h).target_le_iff_mul v.target).mpr
  change v.target.val*(v.val*w.val)=v.val*w.val
  rw [← mul_assoc,v.target_mul]

end PartialIsometry

/-- A partition of p with actual partial isometries from a common projection.
The cross identities encode orthogonality. This structure is constructed below. -/
structure EquivalentPartition (p : AlgebraProjection M) (ι : Type*) [Fintype ι] where
  base : AlgebraProjection M
  leg : ι → PartialIsometry M
  initial : ∀ i, (leg i).support=base
  cross : ∀ i j, i≠j → star (leg i).val*(leg j).val=0
  total : ∑ i, (leg i).target.val=p.val
  bound : ∀ i, (leg i).target ≤ p

namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem orthogonal (E : EquivalentPartition p ι) (i j : ι) (hij : i≠j) :
    (E.leg i).target.val*(E.leg j).target.val=0 := by
  change ((E.leg i).val*star (E.leg i).val)*((E.leg j).val*star (E.leg j).val)=0
  calc _ = (E.leg i).val*(star (E.leg i).val*(E.leg j).val)*star (E.leg j).val := by
           simp only [mul_assoc]
       _ = 0 := by rw [E.cross i j hij,mul_zero,zero_mul]

/-- Every ordered pair of pieces has a displayed equivalence witness. -/
def link (E : EquivalentPartition p ι) (i j : ι) : PartialIsometry M :=
  (E.leg j).compose (E.leg i).adjoint (by
    have h : (E.leg i).adjoint.target=(E.leg i).support := by
      apply Subtype.ext
      change star (E.leg i).val*star (star (E.leg i).val)=(E.leg i).support.val
      rw [star_star,(E.leg i).initial]
    rw [h,E.initial,E.initial])

theorem link_support (E : EquivalentPartition p ι) (i j : ι) :
    (E.link i j).support=(E.leg i).target := rfl

theorem link_target (E : EquivalentPartition p ι) (i j : ι) :
    (E.link i j).target=(E.leg j).target := by
  apply Subtype.ext
  change ((E.leg j).val*star (E.leg i).val)*star ((E.leg j).val*star (E.leg i).val)=_
  calc _ = (E.leg j).val*(star (E.leg i).val*(E.leg i).val)*star (E.leg j).val := by
           simp only [star_mul,star_star,mul_assoc]
       _ = (E.leg j).val*star (E.leg j).val := by
           rw [(E.leg i).initial,E.initial,← E.initial j,(E.leg j).mul_support]
       _ = _ := rfl

/-- Refinement is performed on the common initial corner and transported. -/
def refine (E : EquivalentPartition p ι) (F : EquivalentPartition E.base κ) :
    EquivalentPartition p (ι × κ) where
  base := F.base
  leg a := (E.leg a.1).compose (F.leg a.2) (by rw [E.initial]; exact F.bound a.2)
  initial a := F.initial a.2
  cross a b hab := by
    change star ((E.leg a.1).val*(F.leg a.2).val)*
      ((E.leg b.1).val*(F.leg b.2).val)=0
    rw [star_mul]
    have hr : (star (F.leg a.2).val*star (E.leg a.1).val)*
        ((E.leg b.1).val*(F.leg b.2).val)=
        star (F.leg a.2).val*(star (E.leg a.1).val*(E.leg b.1).val)*(F.leg b.2).val := by
      simp only [mul_assoc]
    rw [hr]
    by_cases h : a.1=b.1
    · rw [h,(E.leg b.1).initial,E.initial,mul_assoc,
        ((F.leg b.2).target_le_iff_mul E.base).mp (F.bound b.2)]
      exact F.cross a.2 b.2 (fun hh => hab (Prod.ext h hh))
    · rw [E.cross a.1 b.1 h,mul_zero,zero_mul]
  total := by
    rw [Fintype.sum_prod_type]
    simp only [PartialIsometry.compose_target,← Finset.sum_mul,← Finset.mul_sum,F.total]
    have h (i : ι) : (E.leg i).val*E.base.val=(E.leg i).val := by
      rw [← E.initial i,(E.leg i).mul_support]
    simp only [h]
    exact E.total
  bound a := ((E.leg a.1).compose_target_le (F.leg a.2) _).trans (E.bound a.1)

theorem refine_parent (E : EquivalentPartition p ι) (F : EquivalentPartition E.base κ) (i : ι) :
    (∑ j, ((E.refine F).leg (i,j)).target.val)=(E.leg i).target.val := by
  change (∑ j, ((E.leg i).compose (F.leg j) (by rw [E.initial]; exact F.bound j)).target.val)=_
  simp only [PartialIsometry.compose_target,← Finset.sum_mul,← Finset.mul_sum,F.total]
  rw [← E.initial i,(E.leg i).mul_support]
  rfl

/-- Depth zero consists of the original projection itself. -/
def singleton (p : AlgebraProjection M) : EquivalentPartition p Unit where
  base := p
  leg _ := PartialIsometry.onProjection p
  initial _ := rfl
  cross i j hij := (hij (Subsingleton.elim _ _)).elim
  total := by simp only [PartialIsometry.onProjection_target,Fintype.sum_unique]
  bound _ := by rw [PartialIsometry.onProjection_target]

/-- Two equivalent orthogonal halves, as a family with a common initial corner. -/
def ofHalving (v : PartialIsometry M) (ho : v.support.val*v.target.val=0)
    (hp : v.support.val+v.target.val=p.val) : EquivalentPartition p Bool where
  base := v.support
  leg b := if b then v else PartialIsometry.onProjection v.support
  initial b := by cases b <;> rfl
  cross b c hbc := by
    have h : v.support.val*v.val=0 := by
      calc _ = v.support.val*(v.target.val*v.val) := by rw [v.target_mul]
           _ = 0 := by rw [← mul_assoc,ho,zero_mul]
    cases b <;> cases c
    · exact (hbc rfl).elim
    · simpa only [Bool.false_eq_true,ite_false,ite_true,PartialIsometry.onProjection,
        v.support.property.isSelfAdjoint.star_eq] using h
    · simpa only [Bool.false_eq_true,ite_false,ite_true,PartialIsometry.onProjection,
        star_mul,star_zero,v.support.property.isSelfAdjoint.star_eq] using congrArg star h
    · exact (hbc rfl).elim
  total := by
    simp only [Fintype.sum_bool,ite_true,Bool.false_eq_true,ite_false,
      PartialIsometry.onProjection_target]
    exact (add_comm _ _).trans hp
  bound b := by
    have he : orthogonalSum v.support v.target ho=p := Subtype.ext hp
    cases b
    · simpa only [Bool.false_eq_true,ite_false,PartialIsometry.onProjection_target,he]
        using le_orthogonalSum_left v.support v.target ho
    · simpa only [ite_true,he] using le_orthogonalSum_right v.support v.target ho

end EquivalentPartition
end Tracial

/-! Coherent dyadic equivalent partitions and matrix units, constructed from
scalar center and diffuseness without a trace. DyadicIndex is reused as a
finite binary index type; no tracial partition construction is used. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace Tracial
variable {M : VonNeumannAlgebra H}
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The matrix entries associated to the explicit common-source legs. -/
def entry (E : EquivalentPartition p ι) (i j : ι) : M.toStarSubalgebra :=
  (E.leg i).val*star (E.leg j).val

theorem entry_diagonal (E : EquivalentPartition p ι) (i : ι) :
    E.entry i i=(E.leg i).target.val := rfl

theorem entry_star (E : EquivalentPartition p ι) (i j : ι) :
    star (E.entry i j)=E.entry j i := by simp only [entry,star_mul,star_star]

theorem entry_mul [DecidableEq ι] (E : EquivalentPartition p ι) (i j k l : ι) :
    E.entry i j*E.entry k l=if j=k then E.entry i l else 0 := by
  change ((E.leg i).val*star (E.leg j).val)*((E.leg k).val*star (E.leg l).val)=_
  have hr : ((E.leg i).val*star (E.leg j).val)*((E.leg k).val*star (E.leg l).val)=
      (E.leg i).val*(star (E.leg j).val*(E.leg k).val)*star (E.leg l).val := by
    simp only [mul_assoc]
  rw [hr]
  by_cases h : j=k
  · subst k
    rw [ite_eq_left rfl,(E.leg j).initial,E.initial,← E.initial i,(E.leg i).mul_support]
    rfl
  · rw [ite_eq_right h,E.cross j k h,mul_zero,zero_mul]

/-- Every old matrix entry is exactly the sum of its corresponding child entries. -/
theorem refine_entry (E : EquivalentPartition p ι) (F : EquivalentPartition E.base κ)
    (i j : ι) : (∑ b, (E.refine F).entry (i,b) (j,b))=E.entry i j := by
  have he (b : κ) : (E.refine F).entry (i,b) (j,b)=
      (E.leg i).val*(F.leg b).target.val*star (E.leg j).val := by
    change ((E.leg i).val*(F.leg b).val)*star ((E.leg j).val*(F.leg b).val)=_
    simp only [star_mul,PartialIsometry.target,mul_assoc]
  rw [show (∑ b, (E.refine F).entry (i,b) (j,b))=
    ∑ b, (E.leg i).val*(F.leg b).target.val*star (E.leg j).val from Finset.sum_congr rfl (fun b _ => he b)]
  rw [← Finset.sum_mul,← Finset.mul_sum,F.total,← E.initial i,(E.leg i).mul_support]
  rfl

/-- A partition of the identity yields a unital full matrix-unit system. -/
def matrixUnits [DecidableEq ι] (E : EquivalentPartition p ι) (hp : p.val=1) :
    MatrixUnitSystem ι M.toStarSubalgebra where
  entry := E.entry
  star_entry := E.entry_star
  mul_entry := E.entry_mul
  total := E.total.trans hp

/-- A partition of a nonzero projection has no zero piece, since every
piece is equivalent to every other piece by the displayed links. -/
theorem target_ne_zero (E : EquivalentPartition p ι) (hp : p.val≠0) (i : ι) :
    (E.leg i).target.val≠0 := by
  intro hi
  have hz (j : ι) : (E.leg j).target.val=0 := by
    have hw : (E.link i j).val=0 := by
      have hm := (E.link i j).mul_support
      rw [E.link_support,hi,mul_zero] at hm
      exact hm.symm
    rw [← E.link_target i j]
    change (E.link i j).val*star (E.link i j).val=0
    rw [hw,zero_mul]
  have ht := E.total
  simp only [hz,Finset.sum_const_zero] at ht
  exact hp ht.symm

end EquivalentPartition

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

/-- Choose the actual two-leg partition supplied by trace-free halving. -/
def traceFreeBinaryPartition (p : AlgebraProjection M) : EquivalentPartition p Bool :=
  let h := traceFree_exists_halving hfactor hdiff p
  EquivalentPartition.ofHalving h.choose h.choose_spec.1 h.choose_spec.2

/-- A coherent family: each successor halves the previous common initial
projection once and transports that halving to all its equivalent pieces. -/
def traceFreeDyadicPartition (p : AlgebraProjection M) :
    (n : ℕ) → EquivalentPartition p (DyadicIndex n)
  | 0 => EquivalentPartition.singleton p
  | n+1 =>
    let E := traceFreeDyadicPartition p n
    E.refine (traceFreeBinaryPartition hfactor hdiff E.base)

theorem traceFreeDyadicPartition_parent (p : AlgebraProjection M) (n : ℕ) (i : DyadicIndex n) :
    (∑ b : Bool, ((traceFreeDyadicPartition hfactor hdiff p (n+1)).leg (i,b)).target.val)=
      ((traceFreeDyadicPartition hfactor hdiff p n).leg i).target.val :=
  EquivalentPartition.refine_parent _ _ i

theorem traceFreeDyadicPartition_entry (p : AlgebraProjection M) (n : ℕ)
    (i j : DyadicIndex n) :
    (∑ b : Bool, (traceFreeDyadicPartition hfactor hdiff p (n+1)).entry (i,b) (j,b))=
      (traceFreeDyadicPartition hfactor hdiff p n).entry i j :=
  EquivalentPartition.refine_entry _ _ i j

/-- Actual matrix units of sizes 2^n, with coherent inclusions. -/
def traceFreeDyadicMatrixUnits (n : ℕ) : MatrixUnitSystem (DyadicIndex n) M.toStarSubalgebra :=
  (traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).matrixUnits rfl

theorem traceFreeDyadicMatrixUnits_compatible (n : ℕ) (i j : DyadicIndex n) :
    (∑ b : Bool, (traceFreeDyadicMatrixUnits hfactor hdiff (n+1)).entry (i,b) (j,b))=
      (traceFreeDyadicMatrixUnits hfactor hdiff n).entry i j :=
  traceFreeDyadicPartition_entry hfactor hdiff _ n i j

end Tracial

/-- Coherent dyadic matrix units in the unchanged original concrete factor. -/
theorem isII1Factor_dyadic_matrixUnits
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) (hS : IsII1Factor S) :
    ∃ E : (n : ℕ) → MatrixUnitSystem (Tracial.DyadicIndex n) S,
      ∀ (n : ℕ) (i j : Tracial.DyadicIndex n),
        (∑ b : Bool, (E (n+1)).entry (i,b) (j,b))=(E n).entry i j := by
  let M := vonNeumannOfWOTClosed S hS.weaklyClosed
  have hf : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra) := by
    intro c hc
    obtain ⟨z,hz⟩ := hS.factor c hc
    exact ⟨z,hz.trans (Algebra.algebraMap_eq_smul_one z)⟩
  exact ⟨Tracial.traceFreeDyadicMatrixUnits hf hS.diffuse,
    Tracial.traceFreeDyadicMatrixUnits_compatible hf hS.diffuse⟩

end

/-! Actual sums of countable orthogonal partial isometries, including least
initial/final support identities. No trace or countable-cofinality premise. -/
namespace Tracial

section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

variable (a : ℕ → PartialIsometry M)
variable (hp : ∀ i j, i ≠ j → (a i).support.val*(a j).support.val=0)
variable (hq : ∀ i j, i ≠ j → (a i).target.val*(a j).target.val=0)

include hp hq in
theorem exists_orthogonalPartialSum (n : ℕ) :
    ∃ v : PartialIsometry M, v.val=∑ i ∈ Finset.range n, (a i).val ∧
      v.support.val=∑ i ∈ Finset.range n, (a i).support.val ∧
      v.target.val=∑ i ∈ Finset.range n, (a i).target.val := by
  induction n with
  | zero => exact ⟨zero, by simp [zero], by simp [zero], by simp [zero,target]⟩
  | succ n ih =>
    obtain ⟨v,hv,hs,ht⟩ := ih
    have ho₁ : v.support.val*(a n).support.val=0 := by
      rw [hs,Finset.sum_mul]
      exact Finset.sum_eq_zero (fun i hi => hp i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
    have ho₂ : v.target.val*(a n).target.val=0 := by
      rw [ht,Finset.sum_mul]
      exact Finset.sum_eq_zero (fun i hi => hq i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
    refine ⟨patch v (a n) ho₁ ho₂, ?_, ?_, ?_⟩
    · change v.val+(a n).val=_
      rw [hv,Finset.sum_range_succ]
    · change v.support.val+(a n).support.val=_
      rw [hs,Finset.sum_range_succ]
    · rw [patch_target,ht,Finset.sum_range_succ]

def orthogonalPartialSum (n : ℕ) : PartialIsometry M :=
  (exists_orthogonalPartialSum a hp hq n).choose

theorem orthogonalPartialSum_val (n : ℕ) :
    (orthogonalPartialSum a hp hq n).val=∑ i ∈ Finset.range n, (a i).val :=
  (exists_orthogonalPartialSum a hp hq n).choose_spec.1

theorem orthogonalPartialSum_support (n : ℕ) :
    (orthogonalPartialSum a hp hq n).support.val=∑ i ∈ Finset.range n, (a i).support.val :=
  (exists_orthogonalPartialSum a hp hq n).choose_spec.2.1

theorem orthogonalPartialSum_target (n : ℕ) :
    (orthogonalPartialSum a hp hq n).target.val=∑ i ∈ Finset.range n, (a i).target.val :=
  (exists_orthogonalPartialSum a hp hq n).choose_spec.2.2

theorem le_orthogonalPartialSum (i n : ℕ) (hin : i < n) :
    a i ≤ orthogonalPartialSum a hp hq n := by
  change (orthogonalPartialSum a hp hq n).val*(a i).support.val=(a i).val
  rw [orthogonalPartialSum_val,Finset.sum_mul]
  apply Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hin) _ |>.trans (a i).mul_support
  intro j _ hji
  calc (a j).val*(a i).support.val = ((a j).val*(a j).support.val)*(a i).support.val := by
         rw [(a j).mul_support]
       _ = 0 := by rw [mul_assoc,hp j i hji,mul_zero]

theorem orthogonalPartialSum_monotone : Monotone (orthogonalPartialSum a hp hq) := by
  apply monotone_nat_of_le_succ
  intro n
  let v := orthogonalPartialSum a hp hq n
  have ho₁ : v.support.val*(a n).support.val=0 := by
    rw [orthogonalPartialSum_support,Finset.sum_mul]
    exact Finset.sum_eq_zero (fun i hi => hp i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
  have ho₂ : v.target.val*(a n).target.val=0 := by
    rw [orthogonalPartialSum_target,Finset.sum_mul]
    exact Finset.sum_eq_zero (fun i hi => hq i n (Nat.ne_of_lt (Finset.mem_range.mp hi)))
  have he : orthogonalPartialSum a hp hq (n+1)=patch v (a n) ho₁ ho₂ := by
    apply ext
    change (orthogonalPartialSum a hp hq (n+1)).val=v.val+(a n).val
    rw [orthogonalPartialSum_val,show v.val=∑ i ∈ Finset.range n, (a i).val from
      orthogonalPartialSum_val a hp hq n,Finset.sum_range_succ]
  rw [he]
  exact v.le_patch (a n) ho₁ ho₂

include hp hq in
/-- An actual infinite orthogonal sum, with least upper bound characterizations
for both support projections. It may be used to construct a shift. -/
theorem traceFree_orthogonal_sum :
    ∃ v : PartialIsometry M, (∀ i, a i ≤ v) ∧
      (∀ p : AlgebraProjection M, v.support ≤ p ↔ ∀ i, (a i).support ≤ p) ∧
      (∀ q : AlgebraProjection M, v.target ≤ q ↔ ∀ i, (a i).target ≤ q) := by
  obtain ⟨v,hv,hs,ht⟩ := traceFree_monotone_least_supports
    (orthogonalPartialSum a hp hq) (orthogonalPartialSum_monotone a hp hq)
  have hav (i : ℕ) : a i ≤ v :=
    (le_orthogonalPartialSum a hp hq i (i+1) (Nat.lt_succ_self i)).trans (hv (i+1))
  refine ⟨v,hav,?_,?_⟩
  · intro p
    refine ⟨fun h i => (support_mono (hav i)).trans h, fun h => hs p ?_⟩
    intro n
    change p.val*(orthogonalPartialSum a hp hq n).support.val=_
    rw [orthogonalPartialSum_support,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => h i)
  · intro q
    refine ⟨fun h i => (target_mono (hav i)).trans h, fun h => ht q ?_⟩
    intro n
    change q.val*(orthogonalPartialSum a hp hq n).target.val=_
    rw [orthogonalPartialSum_target,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => h i)

end PartialIsometry
end

/-! Projection equivalence and subequivalence are witnessed by actual partial
isometries in the original algebra. No dimension or trace oracle is used. -/
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem adjoint_target (v : PartialIsometry M) : v.adjoint.target=v.support := by
  apply Subtype.ext
  change star v.val*star (star v.val)=v.support.val
  rw [star_star,v.initial]

theorem compose_target_of_eq (v w : PartialIsometry M) (h : w.target=v.support) :
    (v.compose w (le_of_eq h)).target=v.target := by
  apply Subtype.ext
  rw [compose_target,h,v.mul_support]
  rfl

/-- Link two ranges whose displayed partial isometries have the same source. -/
def rangeLink (v w : PartialIsometry M) (h : v.support=w.support) : PartialIsometry M :=
  w.compose v.adjoint (by rw [adjoint_target,h])

theorem rangeLink_support (v w : PartialIsometry M) (h : v.support=w.support) :
    (rangeLink v w h).support=v.target := rfl

theorem rangeLink_target (v w : PartialIsometry M) (h : v.support=w.support) :
    (rangeLink v w h).target=w.target :=
  compose_target_of_eq w v.adjoint ((adjoint_target v).trans h)

end PartialIsometry
namespace AlgebraProjection

def Subequivalent (p q : AlgebraProjection M) : Prop :=
  ∃ v : PartialIsometry M, v.support=p ∧ v.target ≤ q

def Equivalent (p q : AlgebraProjection M) : Prop :=
  ∃ v : PartialIsometry M, v.support=p ∧ v.target=q

theorem subequivalent_refl (p : AlgebraProjection M) : p.Subequivalent p :=
  ⟨PartialIsometry.onProjection p,rfl,le_of_eq (PartialIsometry.onProjection_target p)⟩

theorem subequivalent_of_le {p q : AlgebraProjection M} (h : p ≤ q) :
    p.Subequivalent q :=
  ⟨PartialIsometry.onProjection p,rfl,(le_of_eq (PartialIsometry.onProjection_target p)).trans h⟩

theorem subequivalent_trans {p q r : AlgebraProjection M}
    (h : p.Subequivalent q) (k : q.Subequivalent r) : p.Subequivalent r := by
  obtain ⟨v,hv,hvq⟩ := h
  obtain ⟨w,hw,hwr⟩ := k
  have hc : v.target ≤ w.support := by rw [hw]; exact hvq
  exact ⟨w.compose v hc,hv,(w.compose_target_le v hc).trans hwr⟩

theorem equivalent_refl (p : AlgebraProjection M) : p.Equivalent p :=
  ⟨PartialIsometry.onProjection p,rfl,PartialIsometry.onProjection_target p⟩

theorem equivalent_symm {p q : AlgebraProjection M} (h : p.Equivalent q) : q.Equivalent p := by
  obtain ⟨v,hv,hvq⟩ := h
  exact ⟨v.adjoint,hvq,v.adjoint_target.trans hv⟩

theorem equivalent_trans {p q r : AlgebraProjection M}
    (h : p.Equivalent q) (k : q.Equivalent r) : p.Equivalent r := by
  obtain ⟨v,hv,hvq⟩ := h
  obtain ⟨w,hw,hwr⟩ := k
  have hc : v.target=w.support := hvq.trans hw.symm
  exact ⟨w.compose v (le_of_eq hc),hv,(w.compose_target_of_eq v hc).trans hwr⟩

theorem Equivalent.subequivalent {p q : AlgebraProjection M} (h : p.Equivalent q) :
    p.Subequivalent q := by
  obtain ⟨v,hv,hvq⟩ := h
  exact ⟨v,hv,le_of_eq hvq⟩

/-- Scalar-center comparison gives totality of actual subequivalence. -/
theorem subequivalent_total
    (hfactor : ∀ c : M.toStarSubalgebra,
      (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
    (p q : AlgebraProjection M) : p.Subequivalent q ∨ q.Subequivalent p := by
  obtain ⟨v,hp,hq,h⟩ := traceFree_exists_partialIsometry_comparison hfactor p q
  rcases h with h | h
  · exact Or.inl ⟨v,h,hq⟩
  · exact Or.inr ⟨v.adjoint,h,by rw [v.adjoint_target]; exact hp⟩

end AlgebraProjection

/-! Finiteness excludes an infinite family of nonzero equivalent orthogonal
projections. The shift and both of its least supports are constructed. -/

/-- The infinite shift omits the first range. Finiteness then forces that
range, and hence the common source projection, to be zero. -/
theorem traceFree_finite_orthogonal_copies_eq_zero
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (r : AlgebraProjection M) (a : ℕ → PartialIsometry M)
    (hs : ∀ i, (a i).support=r)
    (ho : ∀ i j, i≠j → (a i).target.val*(a j).target.val=0) : r.val=0 := by
  let w (i : ℕ) := PartialIsometry.rangeLink (a i) (a (i+1)) ((hs i).trans (hs (i+1)).symm)
  have hw₁ (i : ℕ) : (w i).support=(a i).target := rfl
  have hw₂ (i : ℕ) : (w i).target=(a (i+1)).target := PartialIsometry.rangeLink_target _ _ _
  obtain ⟨v,hv,hvp,hvq⟩ := PartialIsometry.traceFree_orthogonal_sum w
    (by intro i j h; rw [hw₁,hw₁]; exact ho i j h)
    (by intro i j h; rw [hw₂,hw₂]; exact ho (i+1) (j+1) (by omega))
  have hle : v.target ≤ v.support := by
    apply (hvq v.support).mpr
    intro i
    rw [hw₂,← hw₁ (i+1)]
    exact PartialIsometry.support_mono (hv (i+1))
  have he : v.target=v.support := v.target_eq_support_of_finite hfinite hle
  let c : AlgebraProjection M := ⟨1-(a 0).target.val,(a 0).target.property.one_sub⟩
  have hc : v.target ≤ c := by
    apply (hvq c).mpr
    intro i
    rw [hw₂]
    change (1-(a 0).target.val)*(a (i+1)).target.val=(a (i+1)).target.val
    rw [sub_mul,one_mul,ho 0 (i+1) (by omega),sub_zero]
  have h0 : (a 0).target ≤ c := by
    apply (PartialIsometry.support_mono (hv 0)).trans
    rw [← he]
    exact hc
  have hz : (a 0).target.val=0 := by
    change (1-(a 0).target.val)*(a 0).target.val=(a 0).target.val at h0
    rw [sub_mul,one_mul,(a 0).target.property.isIdempotentElem.eq,sub_self] at h0
    exact h0.symm
  have ha : (a 0).val=0 := by
    have h := (a 0).target_mul
    rw [hz,zero_mul] at h
    exact h.symm
  rw [← hs 0,← (a 0).initial,ha,star_zero,zero_mul]

/-- Subequivalence into every member of an orthogonal sequence is impossible
for a nonzero projection in a finite algebra. -/
theorem traceFree_finite_subequivalent_orthogonal_eq_zero
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (r : AlgebraProjection M) (q : ℕ → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0)
    (h : ∀ i, r.Subequivalent (q i)) : r.val=0 := by
  choose a hs ht using h
  exact traceFree_finite_orthogonal_copies_eq_zero hfinite r a hs (by
    intro i j hij
    exact projection_orthogonal_of_le (ho i j hij) (ht i) (ht j))

/-! Finite comparison and cancellation with actual partial isometries.
No trace, dimension, or representation is assumed. -/
namespace AlgebraProjection

variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
/-- Mutual subequivalence is equivalence in a finite algebra. -/
theorem equivalent_of_mutual_subequivalent {p q : AlgebraProjection M}
    (hpq : p.Subequivalent q) (hqp : q.Subequivalent p) : p.Equivalent q := by
  obtain ⟨v,hv,hvq⟩ := hpq
  obtain ⟨w,hw,hwp⟩ := hqp
  have hc : v.target ≤ w.support := by rw [hw]; exact hvq
  let u := w.compose v hc
  have hu : u.target ≤ u.support := by
    change u.target ≤ v.support
    rw [hv]
    exact (w.compose_target_le v hc).trans hwp
  have he : u.target=p := (u.target_eq_support_of_finite hfinite hu).trans hv
  have hw' : w.target=p := le_antisymm hwp (by
    rw [← he]; exact w.compose_target_le v hc)
  exact ⟨w.adjoint,hw',w.adjoint_target.trans hw⟩

include hfinite in
/-- Equivalent comparable projections in a finite algebra coincide. -/
theorem eq_of_equivalent_of_le {p q : AlgebraProjection M}
    (he : p.Equivalent q) (hle : p ≤ q) : p=q := by
  obtain ⟨v,hv,ht⟩ := he
  exact ht.symm.trans ((v.target_eq_support_of_finite_of_le hfinite (by
    rw [hv,ht]; exact hle)).trans hv) |>.symm

include hfinite in
/-- Any embedding onto a subprojection of an equivalent projection is onto. -/
theorem target_eq_of_equivalent (v : PartialIsometry M) (q : AlgebraProjection M)
    (he : v.support.Equivalent q) (hle : v.target ≤ q) : v.target=q := by
  have hv : v.target.Equivalent v.support := ⟨v.adjoint,rfl,v.adjoint_target⟩
  exact eq_of_equivalent_of_le hfinite (equivalent_trans hv he) hle

theorem subequivalent_orthogonalSum {p q r s : AlgebraProjection M}
    (hp : p.val*r.val=0) (hq : q.val*s.val=0)
    (h₁ : p.Subequivalent q) (h₂ : r.Subequivalent s) :
    (orthogonalSum p r hp).Subequivalent (orthogonalSum q s hq) := by
  obtain ⟨v,hv,hvq⟩ := h₁
  obtain ⟨w,hw,hws⟩ := h₂
  have hi : v.support.val*w.support.val=0 := by rw [hv,hw]; exact hp
  have ht := projection_orthogonal_of_le hq hvq hws
  refine ⟨v.patch w hi ht,Subtype.ext (by
    change v.support.val+w.support.val=_
    rw [hv,hw]
    rfl),?_⟩
  have he : (v.patch w hi ht).target=orthogonalSum v.target w.target ht :=
    Subtype.ext (v.patch_target w hi ht)
  rw [he]
  exact orthogonalSum_le ht (hvq.trans (le_orthogonalSum_left _ _ hq))
    (hws.trans (le_orthogonalSum_right _ _ hq))

theorem equivalent_orthogonalSum {p q r s : AlgebraProjection M}
    (hp : p.val*r.val=0) (hq : q.val*s.val=0)
    (h₁ : p.Equivalent q) (h₂ : r.Equivalent s) :
    (orthogonalSum p r hp).Equivalent (orthogonalSum q s hq) := by
  obtain ⟨v,hv,hvq⟩ := h₁
  obtain ⟨w,hw,hws⟩ := h₂
  have hi : v.support.val*w.support.val=0 := by rw [hv,hw]; exact hp
  have ht : v.target.val*w.target.val=0 := by rw [hvq,hws]; exact hq
  refine ⟨v.patch w hi ht,Subtype.ext (by
    change v.support.val+w.support.val=_
    rw [hv,hw]
    rfl),Subtype.ext ?_⟩
  rw [PartialIsometry.patch_target,hvq,hws]
  rfl

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))

include hfinite hfactor in
/-- Cancel equivalent orthogonal pieces from a subequivalence. -/
theorem subequivalent_cancel {p q r s : AlgebraProjection M}
    (hp : p.val*r.val=0) (hq : q.val*s.val=0) (he : p.Equivalent q)
    (h : (orthogonalSum p r hp).Subequivalent (orthogonalSum q s hq)) :
    r.Subequivalent s := by
  rcases subequivalent_total hfactor r s with hgood | hrev
  · exact hgood
  · obtain ⟨v,hv,ht⟩ := equivalent_symm he
    obtain ⟨w,hw,hwr⟩ := hrev
    have hi : v.support.val*w.support.val=0 := by rw [hv,hw]; exact hq
    have ho : v.target.val*w.target.val=0 := by
      rw [ht]; exact projection_orthogonal_of_le hp le_rfl hwr
    let u := v.patch w hi ho
    have hus : u.support=orthogonalSum q s hq := Subtype.ext (by
      change v.support.val+w.support.val=_; rw [hv,hw]; rfl)
    have hut : u.target ≤ orthogonalSum p r hp := by
      have hu : u.target=orthogonalSum v.target w.target ho :=
        Subtype.ext (v.patch_target w hi ho)
      rw [hu]
      exact orthogonalSum_le ho (by rw [ht]; exact le_orthogonalSum_left _ _ hp)
        (hwr.trans (le_orthogonalSum_right _ _ hp))
    have heq : u.support.Equivalent (orthogonalSum p r hp) := by
      rw [hus]
      exact equivalent_of_mutual_subequivalent hfinite ⟨u,hus,hut⟩ h
    have hu := congrArg Subtype.val (target_eq_of_equivalent hfinite u _ heq hut)
    rw [PartialIsometry.patch_target,ht] at hu
    change p.val+w.target.val=p.val+r.val at hu
    have hw' : w.target=r := Subtype.ext (add_left_cancel hu)
    exact (equivalent_symm (show s.Equivalent r from ⟨w,hw,hw'⟩)).subequivalent

include hfinite hfactor in
theorem equivalent_cancel {p q r s : AlgebraProjection M}
    (hp : p.val*r.val=0) (hq : q.val*s.val=0) (he : p.Equivalent q)
    (h : (orthogonalSum p r hp).Equivalent (orthogonalSum q s hq)) :
    r.Equivalent s :=
  equivalent_of_mutual_subequivalent hfinite
    (subequivalent_cancel hfinite hfactor hp hq he h.subequivalent)
    (subequivalent_cancel hfinite hfactor hq hp (equivalent_symm he)
      (equivalent_symm h).subequivalent)

/-- The relative complement is the actual difference of the operators. -/
def remainder (p q : AlgebraProjection M) (h : p ≤ q) : AlgebraProjection M :=
  ⟨q.val-p.val,p.property.sub_of_mul_eq_right q.property h⟩

theorem remainder_orthogonal (p q : AlgebraProjection M) (h : p ≤ q) :
    p.val*(remainder p q h).val=0 := by
  change p.val*(q.val-p.val)=0
  rw [mul_sub,projection_mul_of_le h,p.property.isIdempotentElem.eq,sub_self]

theorem orthogonalSum_remainder (p q : AlgebraProjection M) (h : p ≤ q) :
    orthogonalSum p (remainder p q h) (remainder_orthogonal p q h)=q :=
  Subtype.ext (by change p.val+(q.val-p.val)=q.val; abel)

theorem remainder_le (p q : AlgebraProjection M) (h : p ≤ q) : remainder p q h ≤ q := by
  change q.val*(q.val-p.val)=q.val-p.val
  rw [mul_sub,q.property.isIdempotentElem.eq,h]

include hfinite hfactor in
/-- Comparison respects subtraction of equivalent pieces. -/
theorem remainder_subequivalent {p q P Q : AlgebraProjection M}
    (hp : p ≤ P) (hq : q ≤ Q) (he : p.Equivalent q) (h : P.Subequivalent Q) :
    (remainder p P hp).Subequivalent (remainder q Q hq) := by
  apply subequivalent_cancel hfinite hfactor
    (remainder_orthogonal p P hp) (remainder_orthogonal q Q hq) he
  simpa only [orthogonalSum_remainder] using h

include hfinite hfactor in
theorem remainder_equivalent {p q P Q : AlgebraProjection M}
    (hp : p ≤ P) (hq : q ≤ Q) (he : p.Equivalent q) (h : P.Equivalent Q) :
    (remainder p P hp).Equivalent (remainder q Q hq) := by
  apply equivalent_cancel hfinite hfactor
    (remainder_orthogonal p P hp) (remainder_orthogonal q Q hq) he
  simpa only [orthogonalSum_remainder] using h

end AlgebraProjection
end Tracial

/-! Actual finite sums of orthogonal partial isometries and finite subsets of
equivalent partitions. The finite subset is arbitrary, without an index order. -/
open scoped BigOperators
namespace Tracial
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
namespace PartialIsometry

theorem exists_finsetSum {ι : Type*} (a : ι → PartialIsometry M) (s : Finset ι)
    (hp : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).support.val*(a j).support.val=0)
    (hq : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).target.val*(a j).target.val=0) :
    ∃ v : PartialIsometry M, v.val=∑ i ∈ s, (a i).val ∧
      v.support.val=∑ i ∈ s, (a i).support.val ∧
      v.target.val=∑ i ∈ s, (a i).target.val := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨zero,by simp [zero],by simp [zero],by simp [zero,target]⟩
  | @insert i s hi ih =>
    obtain ⟨v,hv,hs,ht⟩ := ih
      (fun j hj k hk => hp j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      (fun j hj k hk => hq j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
    have ho₁ : (a i).support.val*v.support.val=0 := by
      rw [hs,Finset.mul_sum]
      exact Finset.sum_eq_zero (fun j hj => hp i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun h => hi (h.symm ▸ hj)))
    have ho₂ : (a i).target.val*v.target.val=0 := by
      rw [ht,Finset.mul_sum]
      exact Finset.sum_eq_zero (fun j hj => hq i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun h => hi (h.symm ▸ hj)))
    refine ⟨(a i).patch v ho₁ ho₂,?_,?_,?_⟩
    · change (a i).val+v.val=_
      rw [hv,Finset.sum_insert hi]
    · change (a i).support.val+v.support.val=_
      rw [hs,Finset.sum_insert hi]
    · rw [patch_target,ht,Finset.sum_insert hi]

end PartialIsometry
namespace AlgebraProjection

theorem isStarProjection_sum {ι : Type*} (a : ι → AlgebraProjection M) (s : Finset ι)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).val*(a j).val=0) :
    IsStarProjection (∑ i ∈ s, (a i).val) := by
  obtain ⟨v,_,hs,_⟩ := PartialIsometry.exists_finsetSum
    (fun i => PartialIsometry.onProjection (a i)) s ho
    (by simpa only [PartialIsometry.onProjection_target] using ho)
  change v.support.val=(∑ i ∈ s, (a i).val) at hs
  exact hs ▸ v.support.property

def finsetSum {ι : Type*} (a : ι → AlgebraProjection M) (s : Finset ι)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).val*(a j).val=0) : AlgebraProjection M :=
  ⟨∑ i ∈ s, (a i).val,isStarProjection_sum a s ho⟩

theorem finsetSum_le_iff {ι : Type*} (a : ι → AlgebraProjection M) (s : Finset ι)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (a i).val*(a j).val=0) (p : AlgebraProjection M) :
    finsetSum a s ho ≤ p ↔ ∀ i ∈ s, a i ≤ p := by
  classical
  constructor
  · intro h i hi
    apply le_trans ?_ h
    change (∑ j ∈ s, (a j).val)*(a i).val=(a i).val
    rw [Finset.sum_mul]
    exact (Finset.sum_eq_single_of_mem i hi
      (fun j hj hji => ho j hj i hi hji)).trans (a i).property.isIdempotentElem.eq
  · intro h
    change p.val*(∑ i ∈ s, (a i).val)=∑ i ∈ s, (a i).val
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl h

end AlgebraProjection
namespace EquivalentPartition
variable {p : AlgebraProjection M} {ι : Type*} [Fintype ι]

def subset (E : EquivalentPartition p ι) (s : Finset ι) : AlgebraProjection M :=
  AlgebraProjection.finsetSum (fun i => (E.leg i).target) s
    (fun i _ j _ => E.orthogonal i j)

theorem subset_val (E : EquivalentPartition p ι) (s : Finset ι) :
    (E.subset s).val=∑ i ∈ s, (E.leg i).target.val := rfl

theorem subset_le_iff (E : EquivalentPartition p ι) (s : Finset ι) (q : AlgebraProjection M) :
    E.subset s ≤ q ↔ ∀ i ∈ s, (E.leg i).target ≤ q :=
  AlgebraProjection.finsetSum_le_iff _ _ _ _

theorem subset_le (E : EquivalentPartition p ι) (s : Finset ι) : E.subset s ≤ p :=
  (E.subset_le_iff s p).mpr (fun i _ => E.bound i)

theorem subset_mono (E : EquivalentPartition p ι) {s t : Finset ι} (h : s ⊆ t) :
    E.subset s ≤ E.subset t :=
  (E.subset_le_iff s _).mpr (fun i hi => (E.subset_le_iff t _).mp le_rfl i (h hi))

theorem subset_univ (E : EquivalentPartition p ι) : E.subset Finset.univ=p :=
  Subtype.ext E.total

theorem subset_empty (E : EquivalentPartition p ι) : (E.subset ∅).val=0 := by
  simp only [subset_val,Finset.sum_empty]

theorem subset_singleton [DecidableEq ι] (E : EquivalentPartition p ι) (i : ι) :
    E.subset {i}=(E.leg i).target := Subtype.ext (by simp only [subset_val,Finset.sum_singleton])

/-- A bijection of subsets gives a sum of explicit matrix-unit links. -/
theorem subset_equivalent_of_equiv (E : EquivalentPartition p ι) (s t : Finset ι)
    (e : s ≃ t) : (E.subset s).Equivalent (E.subset t) := by
  let a (i : s) := E.link i.val (e i).val
  obtain ⟨v,_,hs,ht⟩ := PartialIsometry.exists_finsetSum a Finset.univ
    (by
      intro i _ j _ hij
      exact E.orthogonal i.val j.val (fun h => hij (Subtype.ext h)))
    (by
      intro i _ j _ hij
      change (E.link i.val (e i).val).target.val*(E.link j.val (e j).val).target.val=0
      rw [E.link_target,E.link_target]
      exact E.orthogonal _ _ (fun h => hij (e.injective (Subtype.ext h))))
  refine ⟨v,Subtype.ext ?_,Subtype.ext ?_⟩
  · rw [hs]
    change (∑ i : s, (E.leg i.val).target.val)=∑ i ∈ s, (E.leg i).target.val
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach s (fun i => (E.leg i).target.val))
  · rw [ht]
    change (∑ i : s, (E.link i.val (e i).val).target.val)=_
    simp only [E.link_target]
    rw [e.sum_comp (fun i : t => (E.leg i.val).target.val)]
    change (∑ i : t, (E.leg i.val).target.val)=∑ i ∈ t, (E.leg i).target.val
    simpa only [Finset.attach_eq_univ] using
      (Finset.sum_attach t (fun i => (E.leg i).target.val))

theorem subset_equivalent_of_card_eq (E : EquivalentPartition p ι) (s t : Finset ι)
    (h : s.card=t.card) : (E.subset s).Equivalent (E.subset t) :=
  E.subset_equivalent_of_equiv s t (Finset.equivOfCardEq h)

/-- Subset sums stay compatible with refinement to all children. -/
theorem subset_refine {κ : Type*} [Fintype κ] (E : EquivalentPartition p ι)
    (F : EquivalentPartition E.base κ) (s : Finset ι) :
    (E.refine F).subset (s ×ˢ Finset.univ)=E.subset s := by
  apply Subtype.ext
  rw [subset_val,Finset.sum_product]
  exact Finset.sum_congr rfl (fun i _ => E.refine_parent F i)

/-! Exact finite cardinal comparison of sums of equivalent nonzero projections.
Finiteness prevents a larger collection from embedding in a smaller one. -/

theorem subset_mul_piece_of_not_mem (E : EquivalentPartition p ι) (s : Finset ι)
    (i : ι) (hi : i ∉ s) : (E.subset s).val*(E.leg i).target.val=0 := by
  rw [subset_val,Finset.sum_mul]
  exact Finset.sum_eq_zero (fun j hj => E.orthogonal j i (fun h => hi (h ▸ hj)))

theorem subset_le_subset_iff (E : EquivalentPartition p ι) (hp : p.val≠0)
    (s t : Finset ι) : E.subset s ≤ E.subset t ↔ s ⊆ t := by
  constructor
  · intro h i hi
    by_contra hit
    have hh := (E.subset_le_iff s _).mp h i hi
    change (E.subset t).val*(E.leg i).target.val=(E.leg i).target.val at hh
    rw [E.subset_mul_piece_of_not_mem t i hit] at hh
    exact E.target_ne_zero hp i hh.symm
  · exact E.subset_mono

theorem subset_subequivalent_of_card_le (E : EquivalentPartition p ι)
    (s t : Finset ι) (h : s.card ≤ t.card) : (E.subset s).Subequivalent (E.subset t) := by
  obtain ⟨u,hut,hu⟩ := Finset.exists_subset_card_eq h
  exact AlgebraProjection.subequivalent_trans
    (E.subset_equivalent_of_card_eq s u hu.symm).subequivalent
    (AlgebraProjection.subequivalent_of_le (E.subset_mono hut))

/-- The witness-based comparison agrees exactly with cardinal comparison. -/
theorem subset_subequivalent_iff_card_le
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (E : EquivalentPartition p ι) (hp : p.val≠0) (s t : Finset ι) :
    (E.subset s).Subequivalent (E.subset t) ↔ s.card ≤ t.card := by
  refine ⟨fun h => ?_,E.subset_subequivalent_of_card_le s t⟩
  by_contra hn
  have hlt : t.card < s.card := Nat.lt_of_not_ge hn
  obtain ⟨u,hus,hu⟩ := Finset.exists_subset_card_eq (Nat.le_of_lt hlt)
  have hsu : (E.subset s).Subequivalent (E.subset u) :=
    AlgebraProjection.subequivalent_trans h
      (E.subset_equivalent_of_card_eq t u hu.symm).subequivalent
  have hle : E.subset u ≤ E.subset s := E.subset_mono hus
  have he : E.subset u=E.subset s := AlgebraProjection.eq_of_equivalent_of_le hfinite
    (AlgebraProjection.equivalent_of_mutual_subequivalent hfinite
      (AlgebraProjection.subequivalent_of_le hle) hsu) hle
  have hs : s ⊆ u := (E.subset_le_subset_iff hp s u).mp (le_of_eq he.symm)
  have hc := Finset.card_le_card hs
  omega

theorem subset_equivalent_iff_card_eq
    (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
    (E : EquivalentPartition p ι) (hp : p.val≠0) (s t : Finset ι) :
    (E.subset s).Equivalent (E.subset t) ↔ s.card=t.card := by
  constructor
  · intro h
    exact Nat.le_antisymm ((E.subset_subequivalent_iff_card_le hfinite hp s t).mp h.subequivalent)
      ((E.subset_subequivalent_iff_card_le hfinite hp t s).mp
        (AlgebraProjection.equivalent_symm h).subequivalent)
  · exact E.subset_equivalent_of_card_eq s t

theorem subset_orthogonal_of_disjoint (E : EquivalentPartition p ι)
    (s t : Finset ι) (h : Disjoint s t) : (E.subset s).val*(E.subset t).val=0 := by
  rw [subset_val,subset_val,Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mul_sum]
  exact Finset.sum_eq_zero (fun j hj => E.orthogonal i j (fun he =>
    Finset.disjoint_left.mp h hi (he.symm ▸ hj)))

theorem subset_union [DecidableEq ι] (E : EquivalentPartition p ι)
    (s t : Finset ι) (h : Disjoint s t) :
    E.subset (s ∪ t)=orthogonalSum (E.subset s) (E.subset t)
      (E.subset_orthogonal_of_disjoint s t h) :=
  Subtype.ext (Finset.sum_union h)

theorem subset_insert [DecidableEq ι] (E : EquivalentPartition p ι)
    (s : Finset ι) (i : ι) (hi : i ∉ s) :
    (E.subset (insert i s)).val=(E.subset s).val+(E.leg i).target.val := by
  rw [subset_val,Finset.sum_insert hi,add_comm]
  rfl

end EquivalentPartition
end Tracial

end Generator

end

end OAI
