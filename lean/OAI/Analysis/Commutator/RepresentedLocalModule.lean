import Mathlib
import OAI.Analysis.Commutator.CyclicLocalModule

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.MatrixCornerImplementation

open ConcreteCorner

variable {A H ι : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [DecidableEq ι]

variable (L : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (M : VonNeumannAlgebra H)
  (hM : ∀ a : A, L a∈M)

include hM in
lemma cyclicSubspace_le_ambient (ξ : H) :
    cyclicSubspace L.range ξ≤cyclicSubspace M.toStarSubalgebra ξ := by
  apply Submodule.topologicalClosure_mono
  rintro y ⟨a,⟨b,rfl⟩,rfl⟩
  exact ⟨L b,hM b,rfl⟩

include hM in
theorem exists_represented_local_module {p : A} (hp : IsStarProjection p)
    (v : ι → A)
    (hcol : ∀ i j, star (v i)*v j=if i=j then p else 0)
    (hinit : ∀ i, p*star (v i)=star (v i))
    (htotal : ∑ i, v i*star (v i)=1)
    (G : H →L[ℂ] H)
    (hGp : G.comp (L p)=(L p).comp G)
    (hGv : ∀ i, G.comp (L (v i))=(L (v i)).comp G)
    (ξ : H) (hpξ : L p ξ=ξ)
    {ε : ℝ} (hε : 0≤ε)
    (hδ : ∀ a : H →L[ℂ] H, a∈M → L p*a=a → a*L p=a →
      ‖G.comp a-a.comp G‖≤ε*‖a‖) :
    ∃ T : H →L[ℂ] H, (∀ a : A, T.comp (L a)=(L a).comp T) ∧
      ∀ z∈cyclicSubspace L.range ξ, ‖G z-T z‖≤(16*ε)*‖z‖ := by
  let f : A →⋆ₐ[ℂ] Algebra M := L.codRestrict M.toStarSubalgebra hM
  have hc (i j : ι) : star (f (v i))*f (v j)=if i=j then f p else 0 := by
    simpa only [map_mul,map_star,apply_ite,map_zero] using congrArg f (hcol i j)
  have hi (i : ι) : f p*star (f (v i))=star (f (v i)) := by
    simpa only [map_mul,map_star] using congrArg f (hinit i)
  have ht : ∑ i, f (v i)*star (f (v i))=1 := by
    simpa only [map_sum,map_mul,map_star,map_one] using congrArg f htotal
  have hb (a : Corner (hp.map f)) :
      ‖G.comp (inclusion M (a:Algebra M))-(inclusion M (a:Algebra M)).comp G‖≤ε*‖a‖ := by
    exact hδ ((a:Algebra M):H →L[ℂ] H) (a:Algebra M).property
      (congrArg (fun b : Algebra M => (b:H →L[ℂ] H)) a.property.1)
      (congrArg (fun b : Algebra M => (b:H →L[ℂ] H)) a.property.2)
  obtain ⟨T,hT,hn⟩ := exists_local_module M (hp.map f) (fun i => f (v i)) hc hi ht
    G hGp hGv ξ hpξ hε hb
  exact ⟨T,fun a => hT (f a),fun z hz => hn z (cyclicSubspace_le_ambient L M hM ξ hz)⟩

end Kadison.MatrixCornerImplementation

end

end
end

end OAI
