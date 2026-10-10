import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFullBranches

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InversePrioritySecondSource InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InverseMomentGlobalPriorityTail
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal](hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
def globalPriorityOriginalEnergy (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
        a om X t Y ray core (parent p x)).re

def globalPriorityTailAggregate (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ‖∑y∈wholeAssignedParents p (fun x=>extra x.cube) original negative J lists,
      coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w) y*
      priorityTailParent p hg hp hinj extra pool negative
        (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
        m slots J lists a V X Y R y‖

theorem global_priority_three_branches
    (hp:∀i,p i≠0)(hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)(hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ)(hX:0<X)(hY:0<Y)(R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t;
    globalPriorityOriginalEnergy p hg hp hinj extra pool original w negative Ψ m slots lists a om X t Y≤
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a V X Y R+
      globalPriorityRetainedAggregate p hg hp hcop extra pool original w negative Ψ m slots lists a V X Y R+
      globalPriorityTailAggregate p hg hp hinj extra pool original w negative Ψ m slots lists a V X Y R:=by
  dsimp only
  unfold globalPriorityOriginalEnergy globalPriorityZeroAggregate globalPriorityRetainedAggregate globalPriorityTailAggregate
  rw [←mul_add,←mul_add]
  simp only [←Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro ray hray
  apply Finset.sum_le_sum
  intro core hcore
  apply Finset.sum_le_sum
  intro J hJ
  have hb:=global_priority_slice_full_tail p hg hp hcop hinj hc hpr extra pool original w negative Ψ m
    ray core slots J lists a om lo hi hlo hs X t Y hX hY R
  dsimp only at hb
  rw [original_paired_tail p hg hp hinj]
  exact (Complex.re_le_norm _).trans hb
end SevenEighths.InverseMoment

end

end OAI
