import OAI.NumberTheory.DirichletL.Descent.WholePriorityBranches
import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityPhysical

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_priority_signed_branches
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (Source ι Jo)) (w:Source ι Jo→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots assigned (fun i=>lists i\extra x.cube) a om X t Y ray core (parent p x))=
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x))+
    (∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x)+
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)) := by
  intro V Ψ₀ parents source
  rw [global_priority_physical_source p hp hcop hg hinj hc hpr extra pool original negative Ψ m ray core w
    slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  rw [wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj original negative assigned lists a
      (globalPriorityOuter p hg negative Ψ m ray core w)
      (priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R),
    wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj original negative assigned lists a
      (globalPriorityOuter p hg negative Ψ m ray core w)
      (priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R)]
  rfl

theorem global_priority_slice_bound
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (Source ι Jo)) (w:Source ι Jo→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots assigned (fun i=>lists i\extra x.cube) a om X t Y ray core (parent p x)‖≤
    (∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖)+
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x‖+
    (∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖) := by
  intro V Ψ₀ parents source
  rw [global_priority_signed_branches p hg hp hcop hinj hc hpr extra pool original w negative
    Ψ m ray core slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  have hn (H:Source ι Jo→ℂ):
      ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
        (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*H x‖≤
      ∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
        ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*‖H x‖:=by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro x hx
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hn _) (le_refl _))) (hn _))

end SevenEighths.InverseMoment

end

end OAI
