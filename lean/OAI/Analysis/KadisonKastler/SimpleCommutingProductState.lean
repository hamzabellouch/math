import OAI.Analysis.KadisonKastler.ProductStateMarginalChange
import OAI.Analysis.KadisonKastler.PureRestrictionFactorization

namespace OAI

/-! # Product states for commuting simple C-star algebras

First extend a pure state and use its scalar commutant compression. Two
successive GNS compressions then prescribe arbitrary states on both algebras.
Only the simplicity and faithful embedding of the two algebras are required.
-/

namespace KadisonKastler

open NaimarkZFC

noncomputable section

variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

theorem state_gns_injective_of_simple
    [PartialOrder A] [StarOrderedRing A] (hA : CStarSimple A)
    (f : A →L[ℂ] ℂ) (hf : IsState f) :
    Function.Injective (positiveOfSquares f hf.2).gnsStarAlgHom := by
  let P := positiveOfSquares f hf.2
  have hn : ‖gnsVector P‖=1 := gnsVector_norm_eq_one P ((isState_iff f).mp hf).1
  let : Nontrivial P.GNS := ⟨⟨gnsVector P,0,by
    intro h
    rw [h,norm_zero] at hn
    exact zero_ne_one hn⟩⟩
  exact CurrentMain.simple_starAlgHom_injective hA P.gnsStarAlgHom

theorem exists_product_state_of_commuting_simple [Nontrivial A]
    (hA : CStarSimple A) (hB : CStarSimple B)
    (ι : A →⋆ₐ[ℂ] C) (hι : Function.Injective ι)
    (κ : B →⋆ₐ[ℂ] C)
    (hcomm : ∀ a b, Commute (ι a) (κ b))
    (f : A →L[ℂ] ℂ) (hf : IsState f) (g : B →L[ℂ] ℂ) (hg : IsState g) :
    ∃ φ : C →L[ℂ] ℂ, IsState φ ∧ ∀ a b, φ (ι a*κ b)=f a*g b := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  obtain ⟨f₀,hf₀,hpure⟩ := exists_pure_state (A:=A)
  obtain ⟨φ₀,hφ₀,hres⟩ := exists_state_extension_of_embedding ι hι f₀ hf₀
  let g₀ := restrictState κ φ₀
  have hg₀ : IsState g₀ := isState_restrict κ φ₀ hφ₀
  have hp₀ : IsPureState (restrictState ι φ₀) := by rwa [hres]
  have hprod₀ (a : A) (b : B) : φ₀ (ι a*κ b)=f₀ a*g₀ b := by
    rw [pure_restriction_commuting_factorization ι φ₀ hφ₀ hp₀ (κ b)
      (fun c => (hcomm c b).symm) a]
    have hval : φ₀ (ι a)=f₀ a := congrArg (fun L : A →L[ℂ] ℂ => L a) hres
    rw [hval]
    rfl
  have hswap (b : B) (a : A) : φ₀ (κ b*ι a)=g₀ b*f₀ a := by
    rw [← (hcomm a b).eq,hprod₀,mul_comm]
  obtain ⟨φ₁,hφ₁,hprod₁⟩ := exists_product_state_change_left κ ι
    (fun b a => (hcomm a b).symm) φ₀ hφ₀ g₀ hg₀ f₀ hf₀ hswap
    (state_gns_injective_of_simple hB g₀ hg₀) g hg
  have hprod₂ (a : A) (b : B) : φ₁ (ι a*κ b)=f₀ a*g b := by
    rw [(hcomm a b).eq,hprod₁,mul_comm]
  exact exists_product_state_change_left ι κ hcomm φ₁ hφ₁ f₀ hf₀ g hg hprod₂
    (state_gns_injective_of_simple hA f₀ hf₀) f hf

end

end KadisonKastler

end OAI
