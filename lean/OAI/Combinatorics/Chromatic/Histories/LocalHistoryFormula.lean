import Mathlib
import OAI.Combinatorics.Chromatic.Walls.SectionLineProgram

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]

inductive LocalHistoryFormula (M E:Type*) [AddCommGroup E] [Module ℝ E] where
  | zero
  | stop (degree:ℕ) (exponent:M)
  | add (left right:LocalHistoryFormula M E)
  | jump (degree:ℕ) (source target:M) (transfer:LineTransfer E) (tail:LocalHistoryFormula M E)

namespace LocalHistoryFormula
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (e:M →+ E)
variable (F:CompletedPositive LaurentRay.vUnit Ω C)
def eval (A:ℕ → M → LaurentSeries ℚ) : LocalHistoryFormula M E → LaurentSeries ℚ
  | .zero=>0
  | .stop j m=>A j m
  | .add p q=>eval A p+eval A q
  | .jump d m r t p=>monomialJump Ω (t.operator Ω C e F) d m r*eval A p

def Positive : LocalHistoryFormula M E → Prop
  | .zero=>True
  | .stop _ _=>True
  | .add p q=>Positive p ∧ Positive q
  | .jump d m r t p=>LaurentPositive.Positive (monomialJump Ω (t.operator Ω C e F) d m r) ∧ Positive p

def Bounded (b:M) (N:ℕ) : LocalHistoryFormula M E → Prop
  | .zero=>True
  | .stop j m=>j≤N ∧ HasRootDegree C j (m-b)
  | .add p q=>Bounded b N p ∧ Bounded b N q
  | .jump d _ _ _ p=>0<d ∧ ∃j,j+d≤N ∧ Bounded b j p

def sumList : List (LocalHistoryFormula M E) → LocalHistoryFormula M E
  | []=>.zero
  | p::ps=>.add p (sumList ps)

lemma eval_sumList (A:ℕ → M → LaurentSeries ℚ) (ps:List (LocalHistoryFormula M E)) :
    eval Ω C e F A (sumList ps)=(ps.map (eval Ω C e F A)).sum := by
  induction ps with
  | nil=>rfl
  | cons p ps ih=>simp only [sumList,eval,List.map_cons,List.sum_cons,ih]
lemma positive_sumList (ps:List (LocalHistoryFormula M E))
    (hp:∀p∈ps,Positive Ω C e F p) : Positive Ω C e F (sumList ps) := by
  induction ps with
  | nil=>trivial
  | cons p ps ih=>exact ⟨hp p (by simp),ih (fun q hq=>hp q (by simp [hq]))⟩
lemma bounded_sumList (b:M) (N:ℕ) (ps:List (LocalHistoryFormula M E))
    (hp:∀p∈ps,Bounded C b N p) : Bounded C b N (sumList ps) := by
  induction ps with
  | nil=>trivial
  | cons p ps ih=>exact ⟨hp p (by simp),ih (fun q hq=>hp q (by simp [hq]))⟩
lemma eval_positive (A:ℕ → M → LaurentSeries ℚ) (p:LocalHistoryFormula M E)
    (hp:Positive Ω C e F p) (hA:∀j m,LaurentPositive.Positive (A j m)) :
    LaurentPositive.Positive (eval Ω C e F A p) := by
  induction p with
  | zero=>exact positive_zero
  | stop j m=>exact hA j m
  | add p q ihp ihq=>exact (ihp hp.1).add (ihq hp.2)
  | jump d m r t p ih=>exact hp.1.mul (ih hp.2)
end LocalHistoryFormula
end
end ElementaryPositivity.QuantumTorus

end
section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesAdjoint PowerSeriesSplit LaurentPositive WallUnits
open scoped BigOperators
open Classical
noncomputable section
variable {M E I:Type*} [AddCommGroup M] [AddCommGroup E] [Module ℝ E] [Fintype I]
namespace LocalHistoryFormula
variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M) (e:M →+ E)
variable (F:CompletedPositive LaurentRay.vUnit Ω C)
def finSum {J:Type*} (s:Finset J) (f:J → LocalHistoryFormula M E) : LocalHistoryFormula M E :=
  sumList (s.toList.map f)
lemma eval_finSum {J:Type*} (s:Finset J) (f:J → LocalHistoryFormula M E)
    (A:ℕ → M → LaurentSeries ℚ) :
    eval Ω C e F A (finSum s f)=∑j∈s,eval Ω C e F A (f j) := by
  rw [finSum,eval_sumList,List.map_map]
  simp
lemma positive_finSum {J:Type*} (s:Finset J) (f:J → LocalHistoryFormula M E)
    (hp:∀j∈s,Positive Ω C e F (f j)) : Positive Ω C e F (finSum s f) := by
  apply positive_sumList
  intro p hp'
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hp'
  exact hp j (Finset.mem_toList.mp hj)
lemma bounded_finSum {J:Type*} (s:Finset J) (f:J → LocalHistoryFormula M E)
    (b:M) (N:ℕ) (hp:∀j∈s,Bounded C b N (f j)) : Bounded C b N (finSum s f) := by
  apply bounded_sumList
  intro p hp'
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hp'
  exact hp j (Finset.mem_toList.mp hj)
end LocalHistoryFormula

variable (Ω:M →+ M →+ ℤ) (C:(I → ℤ) →+ M)
variable (e:M →+ E) (he:Function.Injective e)
variable (B:E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hB:∀x,B x x=0)
variable (hcomp:∀a b,B (e a) (e b)=(Ω a b:ℝ))
variable (L:Module.Dual ℝ E) (hdeg:∀n m,HasRootDegree C n m → L (e m)=(n:ℝ))
include he hB hcomp hdeg in

lemma common_history_producer (F:CompletedPositive LaurentRay.vUnit Ω C)
    (incoming:PositiveIncomingPrescription Ω C F) (b:M) :
    ∀N (h:Module.Dual ℝ E) (r:M),HasRootDegree C N (r-b) →
      ∃p:LocalHistoryFormula M E,
        p.Positive Ω C e F ∧ p.Bounded C b N ∧
        ∀X:PowerSeries (Torus LaurentRay.vUnit Ω),ShiftGraded LaurentRay.vUnit Ω C b X →
          p.eval Ω C e F (fun j m=>coeff j (sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω m) X) m)=
            coeff N (sectionValue LaurentRay.vUnit Ω C F (h.toAddMonoidHom.comp e) X) r := by
  have walls:=positive_walls_through Ω C e he B hB hcomp L hdeg F incoming
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih=>
    intro h r hr
    obtain ⟨ts,hpos,hid⟩:=section_line_program Ω C e he B hB hcomp L hdeg F N (walls N) h r
    have HT:∀(t:LineTransfer E) (j:Fin N) (m:{m:M // m∈gradePoints C b j}),
        ∃p:LocalHistoryFormula M E,p.Positive Ω C e F ∧ p.Bounded C b j ∧
          ∀X:PowerSeries (Torus LaurentRay.vUnit Ω),ShiftGraded LaurentRay.vUnit Ω C b X →
            p.eval Ω C e F (fun k a=>coeff k (sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω a) X) a)=
              coeff j (sectionValue LaurentRay.vUnit Ω C F (t.source.toAddMonoidHom.comp e) X) m := by
      intro t j m
      exact ih j j.isLt t.source m ((mem_gradePoints C b m j).mp m.property)
    choose p hp hb heval using HT
    let q (t:LineTransfer E):LocalHistoryFormula M E:=
      .finSum Finset.univ (fun j:Fin N=>.finSum (gradePoints C b j).attach (fun m=>
        .jump (N-j.val) m.val r t (p t j m)))
    have qp:∀t∈ts,(q t).Positive Ω C e F:=by
      intro t ht
      apply LocalHistoryFormula.positive_finSum
      intro j hj
      apply LocalHistoryFormula.positive_finSum
      intro m hm
      exact ⟨hpos t ht (N-j.val) (Nat.sub_le _ _) m.val,hp t j m⟩
    have qb:∀t∈ts,(q t).Bounded C b N:=by
      intro t ht
      apply LocalHistoryFormula.bounded_finSum
      intro j hj
      apply LocalHistoryFormula.bounded_finSum
      intro m hm
      exact ⟨by omega,j.val,by omega,hb t j m⟩
    have qe:∀t (X:PowerSeries (Torus LaurentRay.vUnit Ω)),ShiftGraded LaurentRay.vUnit Ω C b X →
        (q t).eval Ω C e F (fun k a=>coeff k (sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω a) X) a)=
          t.delta Ω C e F b X N r := by
      intro t X hX
      unfold q
      rw [LocalHistoryFormula.eval_finSum]
      unfold LineTransfer.delta
      rw [←Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      rw [LocalHistoryFormula.eval_finSum]
      calc
        _=∑m∈(gradePoints C b j).attach,
          coeff j (sectionValue LaurentRay.vUnit Ω C F (t.source.toAddMonoidHom.comp e) X) m.val*
            monomialJump Ω (t.operator Ω C e F) (N-j.val) m.val r:=by
          apply Finset.sum_congr rfl
          intro m hm
          change monomialJump Ω (t.operator Ω C e F) (N-j.val) m.val r*_= _
          rw [heval t j m X hX,mul_comm]
        _= _:=Finset.sum_attach (gradePoints C b j) (fun m=>
          coeff j (sectionValue LaurentRay.vUnit Ω C F (t.source.toAddMonoidHom.comp e) X) m*
            monomialJump Ω (t.operator Ω C e F) (N-j.val) m r)
    let out:LocalHistoryFormula M E:=.add (.stop N r) (.sumList (ts.map q))
    refine ⟨out,⟨trivial,?_⟩,⟨⟨le_rfl,hr⟩,?_⟩,?_⟩
    · apply LocalHistoryFormula.positive_sumList
      intro a ha
      obtain ⟨t,ht,rfl⟩:=List.mem_map.mp ha
      exact qp t ht
    · apply LocalHistoryFormula.bounded_sumList
      intro a ha
      obtain ⟨t,ht,rfl⟩:=List.mem_map.mp ha
      exact qb t ht
    · intro X hX
      change coeff N (sectionValue LaurentRay.vUnit Ω C F (incomingCovector Ω r) X) r+
        LocalHistoryFormula.eval Ω C e F _ (.sumList (ts.map q))=_
      rw [LocalHistoryFormula.eval_sumList,List.map_map]
      apply Eq.trans _ (hid b X hX).symm
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro t ht
      exact qe t X hX
end
end ElementaryPositivity.QuantumTorus

end

end OAI
