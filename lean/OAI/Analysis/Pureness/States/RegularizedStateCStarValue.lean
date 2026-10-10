import OAI.Analysis.Pureness.States.FiniteQuasitraceCStarValue
import OAI.Analysis.Pureness.States.RegularizedStateCauchyEmbedding

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup Filter
open scoped Topology NNReal ENNReal ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

lemma regularizedStateCauchyEmbedding_isometry (n : ℕ) :
    Isometry (regularizedStateCauchyEmbedding hsimple y hy f n) :=
  NonUnitalStarAlgHom.isometry (regularizedStateCauchyEmbedding hsimple y hy f n).toNonUnitalStarAlgHom
    (regularizedStateCauchyEmbedding_injective hsimple y hy f n)

lemma normalizedStateCauchyValue_continuous : Continuous (normalizedStateCauchyValue hsimple y hy f) :=
  continuous_const.mul (finiteQuasitraceCauchyValue_continuous _ _ _ _ 0)

lemma normalizedStateCauchyValue_square_eq_zero_iff (x : RegularizedStateCauchyQuotient hsimple y hy f 0) :
    normalizedStateCauchyValue hsimple y hy f (star x*x) = 0 ↔ x = 0 := by
  have hc : (regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal ≠ 0 :=
    (ENNReal.toReal_pos (finiteState_regularized_unit hsimple y hy f).1.ne'
      (finiteState_regularized_unit hsimple y hy f).2).ne'
  have hc' : ((regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹ : ℂ) ≠ 0 := by
    exact_mod_cast inv_ne_zero hc
  unfold normalizedStateCauchyValue
  rw [mul_eq_zero,or_iff_right hc']
  exact finiteQuasitraceCauchyValue_square_eq_zero_iff _ _ _ _ 0 x

lemma normalizedStateCauchyValue_cfc_add
    (x : selfAdjoint (RegularizedStateCauchyQuotient hsimple y hy f 0))
    (g h : ℝ → ℝ) (hg : Continuous g) (hh : Continuous h) :
    normalizedStateCauchyValue hsimple y hy f (cfc g x.1+cfc h x.1) =
      normalizedStateCauchyValue hsimple y hy f (cfc g x.1)+normalizedStateCauchyValue hsimple y hy f (cfc h x.1) := by
  unfold normalizedStateCauchyValue
  rw [finiteQuasitraceCauchyValue_cfc_add _ _ _ _ 0 x g h hg hh,mul_add]

lemma regularizedStateCauchyQuotient_finite (n : ℕ)
    (x : RegularizedStateCauchyQuotient hsimple y hy f n) (hx : star x*x = 1) : x*star x = 1 :=
  finiteQuasitraceCauchyQuotient_finite _ _ _ _ n x hx

lemma normalizedStateCStarValue_internal_root_rank (M : Positive (FinMatrix A 1)) :
    Tendsto (fun k => ENNReal.ofReal
      (normalizedStateCauchyValue hsimple y hy f
        (Positive.power (Positive.rootExponent k)
          (Positive.map (regularizedStateCauchyEmbedding hsimple y hy f 0).toNonUnitalStarAlgHom M)).1).re)
      atTop (nhds (ENNReal.ofReal
        (regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹ *
        regularizedFiniteDimension f.toAddHom f.monotone (finitePositiveClass 1 M))) := by
  let c : ℝ := (regularizedFiniteDimension f.toAddHom f.monotone finiteUnitClass).toReal⁻¹
  have hc : 0 ≤ c := inv_nonneg.mpr ENNReal.toReal_nonneg
  have ht := finiteQuasitraceCStarValue_internal_root_rank
    (regularizedFiniteDimension f.toAddHom f.monotone)
    (regularizedFiniteDimension_monotone f.toAddHom f.monotone)
    (regularizedState_dimension_lsc y f) (regularizedState_dimension_finite hsimple y hy f) 0 M
  have hm := (ENNReal.continuous_const_mul (a := ENNReal.ofReal c) ENNReal.ofReal_ne_top).continuousAt.tendsto.comp ht
  have he (x : RegularizedStateCauchyQuotient hsimple y hy f 0) :
      ENNReal.ofReal (normalizedStateCauchyValue hsimple y hy f x).re =
        ENNReal.ofReal c*ENNReal.ofReal
          (finiteQuasitraceCauchyValue _ _ _ _ 0 x).re := by
    unfold normalizedStateCauchyValue
    rw [← Complex.ofReal_inv]
    change ENNReal.ofReal (((c : ℂ)*_).re) = _
    rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,ENNReal.ofReal_mul hc]
  simp only [he]
  exact hm
end CuntzPureness

end

end OAI
