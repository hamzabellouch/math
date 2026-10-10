import OAI.NumberTheory.CubicMoment.Transform.MetaplecticBlockMean

namespace OAI

/-! Literal free-variable parametrization of each supported Voronoi
block, including the ramified exponent k=0 (j=-1). -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma metaplectic_lambda_ne_zero : lambdaE ≠ 0 := by
  intro h
  apply traceLambda_ne_zero
  rw [←lambdaE_coe,h]
  rfl

def metaplecticFreeArgument (k : ℕ) (ζ : Eisensteinˣ)
    (h h' : PrimaryArgument) (w : Eisenstein) : MetaplecticDualArgument :=
  if hw : w ≠ 0 then
    ⟨lambdaE^k*ζ.val*h.val*w*h'.val^3,
      mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (pow_ne_zero k metaplectic_lambda_ne_zero) ζ.ne_zero)
        (primary_ne_zero h.property)) hw) (pow_ne_zero 3 (primary_ne_zero h'.property))⟩
  else ⟨1,one_ne_zero⟩

lemma metaplecticFreeArgument_val (k : ℕ) (ζ : Eisensteinˣ)
    (h h' : PrimaryArgument) {w : Eisenstein} (hw : w ≠ 0) :
    (metaplecticFreeArgument k ζ h h' w).val = lambdaE^k*ζ.val*h.val*w*h'.val^3 := by
  simp only [metaplecticFreeArgument,dite_eq_left hw]

lemma metaplecticFreeArgument_frequency (k : ℕ) (ζ : Eisensteinˣ)
    (h h' : PrimaryArgument) {w : Eisenstein} (hw : w ≠ 0) :
    metaplecticFrequency (metaplecticFreeArgument k ζ h h' w) =
      traceLambda^((k:ℤ)-1)*(ζ.val:ℂ)*(h.val:ℂ)*(w:ℂ)*(h'.val:ℂ)^3 := by
  unfold metaplecticFrequency
  rw [metaplecticFreeArgument_val k ζ h h' hw]
  push_cast
  rw [lambdaE_coe,zpow_sub₀ traceLambda_ne_zero,zpow_natCast,zpow_one]
  ring

lemma metaplecticFreeArgument_injective (k : ℕ) (ζ : Eisensteinˣ)
    (h h' : PrimaryArgument) :
    Set.InjOn (metaplecticFreeArgument k ζ h h') {w | w ≠ 0} := by
  intro u hu v hv he
  have hx := congrArg Subtype.val he
  rw [metaplecticFreeArgument_val k ζ h h' hu,metaplecticFreeArgument_val k ζ h h' hv] at hx
  have hc := mul_right_cancel₀ (pow_ne_zero 3 (primary_ne_zero h'.property)) hx
  exact mul_left_cancel₀ (mul_ne_zero (mul_ne_zero
    (pow_ne_zero k metaplectic_lambda_ne_zero) ζ.ne_zero) (primary_ne_zero h.property)) hc

/-- Within a fixed supported block, the free primary variable indexes
exactly the original frequencies, without multiplicity loss. -/
lemma metaplectic_free_sum_reindex (k : ℕ) (ζ : Eisensteinˣ)
    (h h' : PrimaryArgument) (S : Finset MetaplecticDualArgument)
    (w : MetaplecticDualArgument → Eisenstein)
    (hw : ∀ n ∈ S, primary (w n))
    (he : ∀ n ∈ S, n.val = lambdaE^k*ζ.val*h.val*w n*h'.val^3)
    (F : MetaplecticDualArgument → ℂ) :
    (∑ n ∈ S, F n) =
      ∑ b ∈ S.image w, F (metaplecticFreeArgument k ζ h h' b) := by
  have hn (n : MetaplecticDualArgument) (hn : n ∈ S) :
      metaplecticFreeArgument k ζ h h' (w n) = n := by
    apply Subtype.ext
    rw [metaplecticFreeArgument_val k ζ h h' (primary_ne_zero (hw n hn))]
    exact (he n hn).symm
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hns
    rw [hn n hns]
  · intro n hn' m hm' hnm
    rw [←hn n hn',←hn m hm',hnm]

end CubicFirstMoment

end

end OAI
