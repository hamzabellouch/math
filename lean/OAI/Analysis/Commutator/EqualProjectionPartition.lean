import Mathlib
import OAI.Analysis.Commutator.DiffuseHalving
import OAI.Analysis.Commutator.MatrixUnits
import OAI.Analysis.Commutator.VonNeumannCStar

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure EqualPartition (M : VonNeumannAlgebra H) (ι : Type*) [Fintype ι] where
  base : H →L[ℂ] H
  base_mem : base∈M
  base_projection : IsStarProjection base
  v : ι → H →L[ℂ] H
  mem : ∀ i,v i∈M
  initial : ∀ i,star (v i)*v i=base
  source : ∀ i,v i*base=v i
  cross : ∀ i j,i≠j → star (v i)*v j=0
  total : ∑ i,v i*star (v i)=1

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

local instance : DecidableEq ι := Classical.decEq ι

lemma triple (i : ι) : D.v i*star (D.v i)*D.v i=D.v i := by
  rw [mul_assoc,D.initial,D.source]

lemma final_projection (i : ι) : IsStarProjection (D.v i*star (D.v i)) :=
  ⟨by change (D.v i*star (D.v i))*(D.v i*star (D.v i))=D.v i*star (D.v i)
      rw [←mul_assoc,D.triple],IsSelfAdjoint.mul_star_self _⟩

lemma final_cross (i j : ι) (hij : i≠j) :
    (D.v i*star (D.v i))*(D.v j*star (D.v j))=0 := by
  rw [mul_assoc,←mul_assoc (star (D.v i)),D.cross i j hij,zero_mul,mul_zero]

def matrixHom : Matrix ι ι ℂ →⋆ₐ[ℂ] M := by
  classical
  let q : M := ⟨D.base,D.base_mem⟩
  let v : ι → M := fun i => ⟨D.v i,D.mem i⟩
  let p : ι → M := fun i => v i*star (v i)
  exact MatrixUnits.ofPartialIsometries q p v
    (fun i => Subtype.ext (D.initial i)) (fun _ => rfl)
    (fun i => Subtype.ext (D.source i)) (fun i => Subtype.ext (D.triple i))
    (fun i => IsSelfAdjoint.star_eq (IsSelfAdjoint.mul_star_self (v i)))
    (fun i j hij => Subtype.ext (D.final_cross i j hij))
    (Subtype.ext (by
      change M.toStarSubalgebra.subtype (∑ i,p i)=M.toStarSubalgebra.subtype 1
      rw [map_sum,map_one]
      exact D.total))

include D in
theorem exists_double (hfac : FactorCorner.IsFactor M)
    (hd : DiffuseProjection.HasNoMinimalProjections M) : Nonempty (EqualPartition M (ι × Bool)) := by
  classical
  obtain ⟨w,hww,hsum⟩ := diffuse_halving M hfac hd D.base_mem D.base_projection
  let a := w.initial
  let t : Bool → H →L[ℂ] H := fun b => if b then w.val else a
  have ha : IsStarProjection a := w.initial_projection
  have hti : ∀ b,star (t b)*t b=a := by
    intro b
    cases b <;> simp only [t,Bool.false_eq_true,↓reduceIte,ha.isSelfAdjoint.star_eq,
      ha.isIdempotentElem.eq]
    rfl
  have hts : ∀ b,t b*a=t b := by
    intro b
    cases b
    · exact ha.isIdempotentElem.eq
    · exact w.mul_initial
  have htb : ∀ b,D.base*t b=t b := by
    intro b
    cases b
    · exact (ha.le_iff_mul_eq_right D.base_projection).mp w.source_le
    · exact w.target_mul D.base_projection
  have htc : ∀ b c,b≠c → star (t b)*t c=0 := by
    intro b c hbc
    cases b <;> cases c
    · exact (hbc rfl).elim
    · simpa only [t,Bool.false_eq_true,↓reduceIte,ha.isSelfAdjoint.star_eq] using
        w.initial_mul_self_eq_zero hww
    · simpa only [t,Bool.false_eq_true,↓reduceIte,star_mul,star_zero,←show a=w.initial from rfl,ha.isSelfAdjoint.star_eq,star_star] using
        congrArg star (w.initial_mul_self_eq_zero hww)
    · exact (hbc rfl).elim
  have hsumt : (∑ b : Bool,t b*star (t b))=D.base := by
    simpa only [Fintype.sum_bool,t,Bool.false_eq_true,↓reduceIte,
      ha.isSelfAdjoint.star_eq,ha.isIdempotentElem.eq,add_comm,a,Link.final] using hsum
  refine ⟨⟨a,M.mul_mem (M.star_mem' w.mem) w.mem,ha,
    fun i => D.v i.1*t i.2,?_,?_,?_,?_,?_⟩⟩
  · intro i
    apply M.mul_mem (D.mem i.1)
    cases i.2
    · exact M.mul_mem (M.star_mem' w.mem) w.mem
    · exact w.mem
  · intro i
    rw [star_mul,show star (t i.2)*star (D.v i.1)*(D.v i.1*t i.2)=
      star (t i.2)*(star (D.v i.1)*D.v i.1)*t i.2 by noncomm_ring,
      D.initial,mul_assoc,htb,hti]
  · intro i
    rw [mul_assoc,hts]
  · intro i j hij
    rw [star_mul,show star (t i.2)*star (D.v i.1)*(D.v j.1*t j.2)=
      star (t i.2)*(star (D.v i.1)*D.v j.1)*t j.2 by noncomm_ring]
    by_cases he : i.1=j.1
    · rw [he,D.initial,mul_assoc,htb,htc i.2 j.2 (fun h => hij (Prod.ext he h))]
    · rw [D.cross i.1 j.1 he,mul_zero,zero_mul]
  · rw [Fintype.sum_prod_type]
    simp only [star_mul]
    calc
      _=∑ i,D.v i*(∑ b : Bool,t b*star (t b))*star (D.v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Finset.mul_sum,Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b hb
        noncomm_ring
      _=∑ i,D.v i*star (D.v i) := by simp only [hsumt,D.source]
      _=1 := D.total

def singleton (M : VonNeumannAlgebra H) : EqualPartition M Unit where
  base := 1
  base_mem := M.one_mem
  base_projection := IsStarProjection.one _
  v := fun _ => 1
  mem := fun _ => M.one_mem
  initial := by simp
  source := by simp
  cross := by intros; contradiction
  total := by simp

end EqualPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
