import OAI.NumberTheory.Ostmann.Tree.AffinePairAlgebra
import OAI.NumberTheory.Ostmann.Tree.PairMellin
import OAI.NumberTheory.Ostmann.Tree.ReciprocalTwist

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [Fact p.Prime]

def pairTest (g : ZMod p → ℂ) (σ : (ZMod p)ˣ) (d t : ZMod p) : ℂ :=
  g (pairFirst σ d t)*conj (g (pairSecond σ d t))

def diagonalPairValue (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ) (a : ZMod p)
    (σ lam : (ZMod p)ˣ) (d : ZMod p) : ℂ :=
  pairTest g σ d ((lam:ZMod p)*d)*η d*ZMod.stdAddChar (-(a*d))

theorem diagonalPair_affine_point (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ)
    (a : ZMod p) (σ lam : (ZMod p)ˣ) (hσ : (σ:ZMod p)^2=1) (hg0 : g 0=0)
    (d : ZMod p) :
    let G := reciprocalTwist g η (-a*(σ:ZMod p))
    let r := affinePairParameter σ lam d
    conj (G r)*G (r-r^2*((σ:ZMod p)/(lam:ZMod p))) =
      η lam*diagonalPairValue g η a σ lam d := by
  dsimp
  simp only [reciprocalTwist, affinePairParameter_inv, affinePairParameter_transformed_inv]
  by_cases hd : d=0
  · subst d
    simp [diagonalPairValue,pairTest,pairFirst,pairSecond,hg0]
  by_cases ht : (lam:ZMod p)*d=1
  · simp only [ht, pairFirst, pairSecond, sub_self, div_zero, hg0, zero_mul, map_zero, mul_zero]
    simp [diagonalPairValue,pairTest,ht,pairFirst,pairSecond,hg0]
  let x := pairFirst σ d ((lam:ZMod p)*d)
  let z := pairSecond σ d ((lam:ZMod p)*d)
  have hz : z≠0 := div_ne_zero (mul_ne_zero (Units.ne_zero σ) hd) (sub_ne_zero.mpr ht)
  have hx : x=((lam:ZMod p)*d)*z := by dsimp [x,z,pairFirst,pairSecond]; ring
  have hdiff : x-z=(σ:ZMod p)*d := pair_difference σ d _ ht
  have hchar : conj (η z)*η x=η lam*η d := by
    rw [hx, map_mul, map_mul]
    calc
      _ = (η lam*η d)*(conj (η z)*η z) := by ring
      _ = _ := by rw [conjugate_character_cancel η z hz, mul_one]
  have hphase : conj (ZMod.stdAddChar ((-a*(σ:ZMod p))*z))*
      ZMod.stdAddChar ((-a*(σ:ZMod p))*x)=ZMod.stdAddChar (-(a*d)) := by
    rw [Supply.conj_stdAddChar, ← AddChar.map_add_eq_mul]
    congr 1
    calc
      _ = (-a*(σ:ZMod p))*(x-z) := by ring
      _ = (-a*(σ:ZMod p))*((σ:ZMod p)*d) := by rw [hdiff]
      _ = (-(a*d))*(σ:ZMod p)^2 := by ring
      _ = _ := by rw [hσ,mul_one]
  change conj (g z*η z*ZMod.stdAddChar ((-a*(σ:ZMod p))*z))*
      (g x*η x*ZMod.stdAddChar ((-a*(σ:ZMod p))*x)) =
    η lam*((g x*conj (g z))*η d*ZMod.stdAddChar (-(a*d)))
  simp only [map_mul]
  calc
    _ = (g x*conj (g z))*(conj (η z)*η x)*
      (conj (ZMod.stdAddChar ((-a*(σ:ZMod p))*z))*ZMod.stdAddChar ((-a*(σ:ZMod p))*x)) := by ring
    _ = _ := by rw [hchar,hphase]; ring

theorem diagonalPair_affine_mean (g : ZMod p → ℂ) (η : MulChar (ZMod p) ℂ)
    (a : ZMod p) (σ lam : (ZMod p)ˣ) (hσ : (σ:ZMod p)^2=1) (hg0 : g 0=0) :
    mean (diagonalPairValue g η a σ lam) =
      conj (η lam) * weightedAffine (fun r => conj (reciprocalTwist g η (-a*(σ:ZMod p)) r))
        (reciprocalTwist g η (-a*(σ:ZMod p))) ((σ:ZMod p)/(lam:ZMod p)) := by
  let G := reciprocalTwist g η (-a*(σ:ZMod p))
  let φ : ZMod p → ℂ := fun r => conj (G r)*G (r-r^2*((σ:ZMod p)/(lam:ZMod p)))
  have hG : G 0=0 := reciprocalTwist_zero g η _ hg0
  have hφ0 : φ 0=0 := by simp [φ,hG]
  have hφc : φ ((lam/σ:(ZMod p)ˣ):ZMod p)=0 := by
    have hr : (((lam/σ:(ZMod p)ˣ):ZMod p))-(((lam/σ:(ZMod p)ˣ):ZMod p))^2*
        ((σ:ZMod p)/(lam:ZMod p))=0 := by
      simp only [Units.val_div_eq_div_val]
      field_simp
      ring
    simp only [φ,hr,hG,mul_zero]
  have hi : Function.Bijective (fun d : ZMod p => 1-(lam:ZMod p)*d) := by
    constructor
    · intro d e h
      exact mul_left_cancel₀ (Units.ne_zero lam) (sub_right_injective h)
    · intro y
      refine ⟨(1-y)/(lam:ZMod p), ?_⟩
      field_simp
      ring
  have hs : (∑ d : ZMod p, φ (affinePairParameter σ lam d)) = ∑ r : (ZMod p)ˣ, φ r := by
    dsimp [affinePairParameter]
    rw [hi.sum_comp (fun t => φ (pairMobiusValue (lam/σ) t)),
      pairMobius_sum (lam/σ) φ hφ0 hφc, ← sum_units_of_zero φ hφ0]
  have hv : weightedAffine (fun r => conj (G r)) G ((σ:ZMod p)/(lam:ZMod p)) =
      η lam*mean (diagonalPairValue g η a σ lam) := by
    change (p:ℂ)⁻¹*(∑ r : (ZMod p)ˣ, φ r) = _
    rw [← hs]
    simp_rw [show ∀ d, φ (affinePairParameter σ lam d)=η lam*diagonalPairValue g η a σ lam d from
      fun d => diagonalPair_affine_point g η a σ lam hσ hg0 d]
    rw [← Finset.mul_sum]
    dsimp [mean]
    ring
  change _ = conj (η lam)*weightedAffine (fun r => conj (G r)) G _
  rw [hv, ← mul_assoc, conjugate_character_cancel η lam (Units.ne_zero lam), one_mul]

end
end Ostmann.FiniteField

end OAI
