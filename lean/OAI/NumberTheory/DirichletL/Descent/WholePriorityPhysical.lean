import OAI.NumberTheory.DirichletL.Descent.WholePriorityParents
import OAI.NumberTheory.DirichletL.Inversion.PrioritySecondSource

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentWholePriorityPhysical
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InverseMomentWholePriorityParents InversePrioritySecondSource
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ] [Fintype κ]
variable {Jo : ℕ} (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def fullPhysical (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ)
    (y : SecondParentSource ι Jo) : ℂ :=
  let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
  let ll := fun i=>lists i\extra y.cube
  let H := markedRadial p (slots\J) (residualLists p negative ll y) a ∅ V X
  let K := secondVariableCutoff p y R
  truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K +
    (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ₀ m slots J ll a V X Y ray x) +
    secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K

theorem whole_parent_full
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ)
    (y : SecondParentSource ι Jo) (hq : y.quotient=sourceIdeal p (quotientSupport p y)) :
    parentPoisson p hp hg hinj pool negative Ψ m slots J
      (fun i=>lists i\extra y.cube) a om X t Y r core y =
    fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
      (principalWindow om lo hi hlo hs negative t) X Y r core R label y :=
  parentPoisson_full p hp hcop hg hinj hc hpr y pool hq negative Ψ m slots J
    (fun i=>lists i\extra y.cube) a om lo hi hlo hs X t Y hX hY r core R label

omit [DecidableEq σ] in
theorem whole_residual_lists_attach
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (q : Source ι Jo×((∀ i∈J,ι)×(∀ i∈J,ι))) :
    residualLists p negative (fun i=>lists i\extra (attach p J q).cube) (attach p J q)=
      fun i=>lists i\wholeExtractedSupport (fun x=>extra x.cube) negative q.1 := by
  rw [residualLists_attach p hinj]
  funext i
  ext k
  simp only [Finset.mem_sdiff,wholeExtractedSupport,Finset.mem_union]
  change (k ∈ lists i ∧ k ∉ extra q.1.cube) ∧ k ∉ extractedSupport negative q.1 ↔ _
  tauto

theorem whole_signed_source_full
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (source : Finset (Source ι Jo)) (w : Source ι Jo→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    (∑ x∈source,w x*(‖primeMark J lists a
      (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots J
        (fun i=>lists i\extra x.cube) a om X t Y r core (parent p x)) =
    ∑ y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
      coefficient p J a w y *
        fullPhysical p hp hcop hg hinj extra pool negative Ψ m slots J lists a
          (principalWindow om lo hi hlo hs negative t) X Y r core R label y := by
  have he := wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj source negative J lists a w
    (fun y=>parentPoisson p hp hg hinj pool negative Ψ m slots J
      (fun i=>lists i\extra y.cube) a om X t Y r core y)
  refine he.trans ?_
  apply Finset.sum_congr rfl
  intro y hy
  obtain ⟨x,hx,q,hq,rfl⟩ :=
    (mem_wholeAssignedParents p (fun x=>extra x.cube) source negative J lists y).mp hy
  rw [forget_attach]
  apply congrArg (coefficient p J a w (attach p J (x,q))* ·)
  have hquot : (attach p J (x,q)).quotient=sourceIdeal p (quotientSupport p (attach p J (x,q))) := by
    rw [quotientSupport_attach p hinj];rfl
  exact whole_parent_full p hp hcop hg hinj hc hpr extra pool negative Ψ m slots J lists a
    om lo hi hlo hs X t Y hX hY r core R label (attach p J (x,q)) hquot

end SevenEighths.InverseMomentWholePriorityPhysical

end

end OAI
