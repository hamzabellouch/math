import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionChart
import OAI.AlgebraicGeometry.Seshadri.Divisors.MixedSections

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory
open MaximalSeshadri.Frames MaximalSeshadri.Projective
variable {X : Scheme}

lemma normalized_mixed_coefficient {M : X.Modules} (s₀ : O X ⟶ M)
    (U : X.Opens) (hU : U ≤ SectionOpens.isoOpen s₀) (n : ℕ)
    (s : Fin n → (O X ⟶ M)) :
    coefficient (sectionFrameOn (powerSection s₀ n) U
        (hU.trans (sectionOpen_le_powerSection s₀ n)))
      (restrictSection U.ι (mixedPowerSection n s)) =
      ∏ i, coefficient (sectionFrameOn s₀ U hU) (restrictSection U.ι (s i)) := by
  let e := sectionFrameOn s₀ U hU
  let f := sectionFrameOn (powerSection s₀ n) U
    (hU.trans (sectionOpen_le_powerSection s₀ n))
  let c := frameChange (localPowerFrame U e n) f
  have hc : (c : Γ(U.toScheme, ⊤)) * endValue (powerRestrictionUnit U n).hom = 1 := by
    have hh := coefficient_change (localPowerFrame U e n) f
      (restrictSection U.ι (powerSection s₀ n))
    rw [local_powerSection_coefficient U e s₀ n,
      sectionFrameOn_normalized (powerSection s₀ n) U
        (hU.trans (sectionOpen_le_powerSection s₀ n)),
      sectionFrameOn_normalized s₀ U hU, one_pow, mul_one] at hh
    exact hh.symm
  change coefficient f _ = _
  rw [coefficient_change (localPowerFrame U e n) f,
    local_mixedPowerSection_coefficient U e n s, ← mul_assoc]
  exact (congrArg (fun value => value * ∏ i,
    coefficient e (restrictSection U.ι (s i))) hc).trans (one_mul _)

def quarticSection {M : X.Modules} (a b c d : O X ⟶ M) :
    O X ⟶ modulePow X M 4 := mixedPowerSection 4 ![a,b,c,d]

lemma quarticSection_pure {M : X.Modules} (a : O X ⟶ M) :
    quarticSection a a a a = powerSection a 4 := by
  apply (congrArg (mixedPowerSection 4) (show ![a,a,a,a] = fun _ => a from by
    funext i; fin_cases i <;> rfl)).trans
  exact mixedPowerSection_const 4 a

lemma quarticSection_normalized {M : X.Modules} (s₀ a b c d : O X ⟶ M)
    (U : X.Opens) (hU : U ≤ SectionOpens.isoOpen s₀) :
    coefficient (sectionFrameOn (powerSection s₀ 4) U
        (hU.trans (sectionOpen_le_powerSection s₀ 4)))
      (restrictSection U.ι (quarticSection a b c d)) =
      coefficient (sectionFrameOn s₀ U hU) (restrictSection U.ι a) *
      coefficient (sectionFrameOn s₀ U hU) (restrictSection U.ι b) *
      coefficient (sectionFrameOn s₀ U hU) (restrictSection U.ι c) *
      coefficient (sectionFrameOn s₀ U hU) (restrictSection U.ι d) := by
  refine (normalized_mixed_coefficient s₀ U hU 4 ![a,b,c,d]).trans ?_
  simp [Fin.prod_univ_succ, mul_assoc]

end
end MaximalSeshadri.Geometry

end


end
end

end OAI
