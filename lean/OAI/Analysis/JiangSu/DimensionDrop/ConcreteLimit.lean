import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.DimensionDrop.SequentialCStarChain
import OAI.Analysis.JiangSu.DimensionDrop.PermutationUnitary

namespace OAI

section

noncomputable section
namespace JiangSuConstruction
open scoped ComplexOrder CStarAlgebra

structure PositivePair where
  p : ℕ
  q : ℕ
  p_pos : 0<p
  q_pos : 0<q

def PositivePair.next (x : PositivePair) : PositivePair :=
  let m := canonicalMultiplicities x.p_pos x.q_pos
  ⟨x.p*m.k,x.q*m.l,Nat.mul_pos x.p_pos m.k_pos,Nat.mul_pos x.q_pos m.l_pos⟩

def stagePair : ℕ → PositivePair
  | 0 => ⟨2,3,by omega,by omega⟩
  | n+1 => (stagePair n).next

lemma stagePair_prime_powers (n : ℕ) :
    ∃ a b : ℕ, (stagePair n).p=2^a ∧ (stagePair n).q=3^b := by
  induction n with
  | zero => exact ⟨1,1,by norm_num [stagePair],by norm_num [stagePair]⟩
  | succ n ih =>
    obtain ⟨a,b,hp,hq⟩ := ih
    refine ⟨a+8*(stagePair n).q,b+8*(stagePair n).p,?_,?_⟩
    · change (stagePair n).p*2^(8*(stagePair n).q)=_
      rw [hp,pow_add]
    · change (stagePair n).q*3^(8*(stagePair n).p)=_
      rw [hq,pow_add]

lemma stagePair_coprime (n : ℕ) : (stagePair n).p.Coprime (stagePair n).q := by
  obtain ⟨a,b,hp,hq⟩ := stagePair_prime_powers n
  rw [hp,hq]
  exact (show Nat.Coprime 2 3 by decide).pow a b

abbrev StageAlgebra (n : ℕ) : Type := ↥(DimensionDrop (stagePair n).p (stagePair n).q)

local instance (priority := 2000) stageSemiring (n : ℕ) : Semiring (StageAlgebra n) :=
  (inferInstance : CStarAlgebra (StageAlgebra n)).toSemiring

instance stageAlgebraNontrivial (n : ℕ) : Nontrivial (StageAlgebra n) := by
  let : NeZero (stagePair n).p := ⟨(stagePair n).p_pos.ne'⟩
  let : NeZero (stagePair n).q := ⟨(stagePair n).q_pos.ne'⟩
  infer_instance

def stageStep (n : ℕ) : StageAlgebra n →⋆ₐ[ℂ] StageAlgebra (n+1) :=
  concreteStep (canonicalMultiplicities (stagePair n).p_pos (stagePair n).q_pos)
lemma stageStep_injective (n : ℕ) : Function.Injective (stageStep n) :=
  concreteStep_injective _

def concreteSystem : SequentialCStar.System StageAlgebra :=
  SequentialCStar.System.ofSequence stageStep stageStep_injective

abbrev PrimeDropLimit := concreteSystem.Limit

instance primeDropLimitNontrivial : Nontrivial PrimeDropLimit :=
  (concreteSystem.inclusion_isometry 0).injective.nontrivial

theorem primeDropLimit_finite_stage (x : PrimeDropLimit) {ε : ℝ} (hε : 0<ε) :
    ∃ (n : ℕ) (a : StageAlgebra n), ‖x-concreteSystem.inclusion n a‖<ε :=
  concreteSystem.finite_stage_approximation x hε

end JiangSuConstruction

end
end

end OAI
