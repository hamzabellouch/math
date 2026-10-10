import OAI.NumberTheory.DirichletL.Descent.WholePriorityParentBounds
import OAI.NumberTheory.DirichletL.Descent.GlobalPrioritySource

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

lemma tail_forget (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι→Finset ι→ℝ)
    (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R
      (forgetAppended (Jo:=Jo) y)=
    priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R y := rfl

theorem original_paired_tail (hp : ∀i,p i≠0)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (source : Finset (Source ι Jo))
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι→Finset ι→ℝ) :
    (∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
      coefficient p J a w y*priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R y)=
    ∑x∈source,w x*(‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R (parent p x) := by
  rw [wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj]
  simp only [tail_forget]

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI
