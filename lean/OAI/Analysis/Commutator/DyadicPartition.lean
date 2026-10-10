import Mathlib
import OAI.Analysis.Commutator.DyadicCuts
import OAI.Analysis.Commutator.EqualProjectionPartition

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison.PartialIsometryOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace EqualPartition

variable {M : VonNeumannAlgebra H} {ι : Type*} [Fintype ι]

variable (D : EqualPartition M ι)

local instance : DecidableEq ι := Classical.decEq ι

def double (w : Link M D.base D.base) (hww : w.val*w.val=0)
    (hsum : w.initial+w.final=D.base) : EqualPartition M (ι × Bool) := by
  classical
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
  refine ⟨a,M.mul_mem (M.star_mem' w.mem) w.mem,ha,
    fun i => D.v i.1*t i.2,?_,?_,?_,?_,?_⟩
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

lemma double_base (w : Link M D.base D.base) (hww : w.val*w.val=0)
    (hsum : w.initial+w.final=D.base) : (D.double w hww hsum).base=w.initial := rfl

lemma double_val (w : Link M D.base D.base) (hww : w.val*w.val=0)
    (hsum : w.initial+w.final=D.base) (i : ι) (b : Bool) :
    (D.double w hww hsum).v (i,b)=D.v i*(if b then w.val else w.initial) := rfl

lemma base_ne_zero [Nontrivial H] : D.base≠0 := by
  intro hz
  have hv : ∀ i,D.v i=0 := by
    intro i
    simpa only [hz,mul_zero] using (D.source i).symm
  have hone : (1 : H →L[ℂ] H)=0 := by
    rw [←D.total]
    simp only [hv,zero_mul,Finset.sum_const_zero]
  exact one_ne_zero hone

end EqualPartition

namespace DyadicPartition

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M)

def Index : ℕ → Type
  | 0 => Unit
  | n+1 => Index n × Bool

instance indexFintype : (n : ℕ) → Fintype (Index n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => @instFintypeProd (Index n) Bool (indexFintype n) inferInstance

instance indexNonempty : (n : ℕ) → Nonempty (Index n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n+1 => @instNonemptyProd (Index n) Bool (indexNonempty n) inferInstance

def partition : (n : ℕ) → EqualPartition M (Index n)
  | 0 => EqualPartition.singleton M
  | n+1 =>
    let D := partition n
    let e : ProjectionIn M := ⟨D.base,D.base_mem,D.base_projection⟩
    D.double (DyadicCuts.half M hfac hd e) (DyadicCuts.half_square M hfac hd e)
      (DyadicCuts.half_sum M hfac hd e)

lemma cardinality (n : ℕ) : Fintype.card (Index n)=2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Index n × Bool)=2^(n+1)
    rw [Fintype.card_prod,Fintype.card_bool,ih,pow_succ]

lemma base_eq_cut (n : ℕ) : (partition M hfac hd n).base=(DyadicCuts.cut M hfac hd n).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (DyadicCuts.half M hfac hd ⟨(partition M hfac hd n).base,_,_⟩).initial=_
    have he : (⟨(partition M hfac hd n).base,(partition M hfac hd n).base_mem,
      (partition M hfac hd n).base_projection⟩ : ProjectionIn M)=DyadicCuts.cut M hfac hd n := by
      cases h : DyadicCuts.cut M hfac hd n
      simp only [h] at ih
      cases ih
      rfl
    rw [he]
    rfl

lemma exists_base_subEquivalent [TopologicalSpace.SeparableSpace H]
    (hfin : IsFiniteAlgebra M) {e : H →L[ℂ] H}
    (heM : e∈M) (he : IsStarProjection e) (hen : e≠0) :
    ∃ n,SubEquivalent M (partition M hfac hd n).base e := by
  obtain ⟨n,hn⟩ := DyadicCuts.exists_subEquivalent M hfac hd hfin heM he hen
  exact ⟨n,by rwa [base_eq_cut]⟩

end DyadicPartition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
