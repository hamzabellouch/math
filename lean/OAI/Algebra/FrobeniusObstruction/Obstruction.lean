import Mathlib
import OAI.Algebra.FrobeniusObstruction.LiftProducts

namespace OAI

noncomputable section
open scoped BigOperators

namespace BoundaryOnly.FormalObstruction.FixedResidue
open Frobenius MixedForms
variable {ι k : Type*} [Fintype ι] [DecidableEq ι] [Field k]
variable (ell : ℕ) (hell : 0 < ell)

 omit [DecidableEq ι] in
 theorem scalar_eq_fixedResidue (v : Ext (k := k) (ι := ι) →ₗ[k] k) :
    scalar ell hell v = fixedResidue
      (quotientCoeff ell (topExponent ell) (topExponent_good hell)) v := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro e
  rfl

end BoundaryOnly.FormalObstruction.FixedResidue

namespace BoundaryOnly.FormalObstruction
open Frobenius MixedForms

                                                                  
                                                                              
                                                          
theorem no_formal_data
    (k : Type*) [Field k] (ell : ℕ) [CharP k ell]
    (hprime : ell.Prime) (hchar : 2 < ell)
    (d : ℕ) (hd : 5 ≤ d) (n : Fin d → ℕ) :
    ¬ Nonempty (FormalData (k := k) n) := by
  let : Fact ell.Prime := ⟨hprime⟩
  rintro ⟨D⟩
  let hell : 0 < ell := by omega
  let htwo : 1 < ell := by omega
  obtain ⟨v,J,x,hJ,hx,hy,hpair⟩ := ActualBlocks.selected_block_cycles ell hchar hd D
  obtain ⟨i,j,l,hi,hj,hl,hij,hil,hjl⟩ := Finset.two_lt_card_iff.mp (by omega : 2 < J.card)
  let s : Fin d → ThreeParameters.Ring k := ThreeParameters.chosen i j l
  have hs (r : Fin d) : ThreeParameters.augmentation k (s r) = 0 :=
    ThreeParameters.chosen_augmentation i j l r
  have hs2 (r : Fin d) : s r * s r = 0 := ThreeParameters.chosen_square i j l r
  have hout (r : Fin d) (hr : r ∉ J) : s r = 0 :=
    ThreeParameters.chosen_outside J i j l hi hj hl r hr
  obtain ⟨beta,hbeta,hbeta0⟩ := ActualBlocks.parameter_cycle ell D J s hs hs2 hout x hx hy
  let a := firstSlopes s
  have ha : ∀ r, ThreeParameters.augmentation k (a r) = 0 := firstSlopes_augmentation s hs
  obtain ⟨eta,heta⟩ := movingNormal_cubic_primitive ell htwo D a ha i j l
  have hw : a (i,0) * a (j,0) * a (l,0) = ThreeParameters.w k := by
    simp only [a, firstSlopes, ite_true]
    exact ThreeParameters.chosen_product i j l hij hil hjl
  rw [hw] at heta
  apply FixedResidue.unit_residue_contradiction ell hell v (parameterPartial ell)
    (movingPotential ell D a ha) (movingNormal ell htwo D a ha) beta eta hbeta heta
  rw [map_mul, reduce_movingNormal, hbeta0, FixedResidue.scalar_eq_fixedResidue]
  exact hpair

end BoundaryOnly.FormalObstruction

end

end OAI
