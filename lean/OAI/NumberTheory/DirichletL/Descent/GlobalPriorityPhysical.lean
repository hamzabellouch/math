import OAI.NumberTheory.DirichletL.Descent.GlobalPriorityEnergy

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InversePrincipalEnergy InverseSecondPrincipalCaller
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_priority_physical_source
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)(original:Finset (Source ι Jo))
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (w:Source ι Jo→ℂ)(slots J:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ)(hX:0<X)(hY:0<Y)(R:Finset ι→Finset ι→ℝ):
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative J lists
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let V:=principalWindow om lo hi hlo hs negative t
    let H:=fun y:SecondParentSource ι (Jo+(J.card+J.card))=>markedRadial p (slots\J)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X
    let K:=fun y:SecondParentSource ι (Jo+(J.card+J.card))=>secondVariableCutoff p y R
    let coeff:=coefficient p J a (globalPriorityOuter p hg negative Ψ m ray core w)
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
        a om X t Y ray core (parent p x))=
    (∑y∈parents,coeff y*truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y))+
    (∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z*
      ∑x∈unifiedSource p pool parents (fun _=>R),globalPriorityWeight p hg negative Ψ m ray core w J a x*
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots J lists a V X Y z x)+
    (∑y∈parents,coeff y*secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)):=by
  intro parents Ψ₀ V H K coeff
  rw [whole_signed_source_full p hp hcop hg hinj hc hpr extra pool original
    (globalPriorityOuter p hg negative Ψ m ray core w) negative Ψ m slots J lists a
    om lo hi hlo hs X t Y hX hY ray core R (fun _ _=>())]
  exact fullPhysical_unified p hg hp hcop hinj extra pool parents coeff negative Ψ m slots J lists a
    V X Y ray core R (fun _ _=>())
end SevenEighths.InverseMoment

end

end OAI
