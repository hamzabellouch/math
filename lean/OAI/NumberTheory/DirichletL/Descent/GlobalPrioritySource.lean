import OAI.NumberTheory.DirichletL.Inversion.WholePriorityRetainedSource

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def globalPriorityOuter (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)(x:Source ι Jo):ℂ:=
  w x*(priorityOuter p hg x.cube negative Ψ m (fun _=>1) ray core x.quotientSupport:ℂ)

def globalPriorityWeight (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)
    (J:Finset σ)(a:σ→ι→ℂ)(x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0):ℂ:=
  coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) (secondParentOf x)

def normalizedGlobalPriorityWeight (negative:Bool)(Ψ:O→*ℂ)(m:O)
    (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(w:Source ι Jo→ℂ)
    (J:Finset σ)(a:σ→ι→ℂ)(x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0):ℂ:=
  globalPriorityWeight p hg negative Ψ m ray core w J a x/(coefficientBound:ℂ)

theorem globalPriorityWeight_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(original:Finset (Source ι Jo))(pool:Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(hw:∀x∈original,‖w x‖≤1)(hΨ:∀u,‖Ψ u‖≤1)
    (J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ha:∀i∈J,∀k∈lists i,‖a i k‖≤1)
    (R:SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx:x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) R):
    ‖globalPriorityWeight p hg negative Ψ m ray core w J a x‖≤coefficientBound:=by
  apply InverseMomentWholeRetainedSource.whole_coefficient_norm p hinj (fun x=>extra x.cube)
    original negative J lists a _ coefficientBound ha
  · intro y hy
    rw [globalPriorityOuter,norm_mul]
    have hn:=priorityOuter_norm p hg y.cube negative Ψ m (fun _=>1) ray core y.quotientSupport
      (by simp) (hΨ _)
    exact (mul_le_mul (hw y hy) hn (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · exact ((mem_unifiedSource p pool _ R x).mp hx).1

theorem normalizedGlobalPriorityWeight_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(original:Finset (Source ι Jo))(pool:Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(hw:∀x∈original,‖w x‖≤1)(hΨ:∀u,‖Ψ u‖≤1)
    (J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(ha:∀i∈J,∀k∈lists i,‖a i k‖≤1)
    (R:SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (x:MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx:x∈unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) R):
    ‖normalizedGlobalPriorityWeight p hg negative Ψ m ray core w J a x‖≤1:=by
  rw [normalizedGlobalPriorityWeight,norm_div,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  exact (div_le_one coefficientBound_pos).mpr
    (globalPriorityWeight_norm p hg hinj extra original pool negative Ψ m ray core w hw hΨ J lists a ha R x hx)

omit [DecidableEq σ] in
theorem globalPriority_sum_normalized
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(J:Finset σ)(a:σ→ι→ℂ)
    (source:Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0))
    (H:MarkedSecondSource ι (Jo+(J.card+J.card)) 0→ℂ):
    (∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w J a x*H x)=
      (coefficientBound:ℂ)*∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w J a x*H x:=by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  unfold normalizedGlobalPriorityWeight
  have hn:(coefficientBound:ℂ)≠0:=by exact_mod_cast coefficientBound_pos.ne'
  field_simp
end SevenEighths.InverseMoment

end

end OAI
