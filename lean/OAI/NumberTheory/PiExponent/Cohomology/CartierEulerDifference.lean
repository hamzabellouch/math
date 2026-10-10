import OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear
import OAI.NumberTheory.PiExponent.Geometry.CartierSequence

namespace OAI

namespace PiExponent.NumericalAmpleness

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames


variable {X : Scheme.{0}}

theorem eulerCharacteristic_eq_pred_of_cohomology_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d : ℕ)
    (hzero : ∀ z : cohomology M d, z = 0) :
    eulerCharacteristic p d M = eulerCharacteristic p (d-1) M := by
  have : Subsingleton (cohomology M d) :=
    ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  have hdim : cohomologyDimension p M d = 0 := by
    let := Module.compHom (cohomology M d) (baseScalars p)
    exact Module.finrank_zero_of_subsingleton
  cases d with
  | zero => rfl
  | succ d =>
    simp only [Nat.add_sub_cancel, eulerCharacteristic, Finset.sum_range_succ,
      hdim, Nat.cast_zero, mul_zero, add_zero]

theorem cartier_euler_difference
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData)
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ e' : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ e'.hom))})
    (d : ℕ)
    (hfiniteM : ∀ q ≤ d, letI := Module.compHom (cohomology M.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology M.sheaf q))
    (hfiniteN : ∀ q ≤ d, letI := Module.compHom (cohomology N.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf q))
    (hfiniteRestricted : ∀ q ≤ d,
      letI := Module.compHom
        (cohomology ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) q)
        (baseScalars (I.subschemeι ≫ p))
      FiniteDimensional ℂ (cohomology ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) q))
    (hzeroM : ∀ z : cohomology M.sheaf (d+1), z = 0)
    (hzeroRestricted : ∀ z : cohomology ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) d,
      z = 0) :
    eulerCharacteristic p d N.sheaf - eulerCharacteristic p d M.sheaf =
      eulerCharacteristic (I.subschemeι ≫ p) (d-1)
        ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) := by
  obtain ⟨hz,hS⟩ := PiExponentSeshadri.CartierSequence.exact p M N φ I heq
  have : Subsingleton (cohomology M.sheaf (d+1)) :=
    ⟨fun a b => (hzeroM a).trans (hzeroM b).symm⟩
  have hfinitePushforward (q : ℕ) (hq : q ≤ d) :
      letI := Module.compHom
        (cohomology ((Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) q) (baseScalars p)
      FiniteDimensional ℂ
        (cohomology ((Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) q) := by
    let := Module.compHom
      (cohomology ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) q)
      (baseScalars (I.subschemeι ≫ p))
    let := Module.compHom
      (cohomology ((Scheme.Modules.pushforward I.subschemeι).obj
        ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) q) (baseScalars p)
    have := hfiniteRestricted q hq
    let e := ClosedImmersionSerreTransfer.cohomologyLinearEquiv I.subschemeι p
      ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) q
    exact FiniteDimensional.of_surjective e.toLinearMap e.surjective
  have hEuler := eulerCharacteristic_add p hS d hfiniteM hfiniteN hfinitePushforward
  change eulerCharacteristic p d N.sheaf = eulerCharacteristic p d M.sheaf +
    eulerCharacteristic p d ((Scheme.Modules.pushforward I.subschemeι).obj
      ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) at hEuler
  rw [ClosedImmersionSerreTransfer.euler_pushforward,
    eulerCharacteristic_eq_pred_of_cohomology_zero (I.subschemeι ≫ p)
      ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf) d hzeroRestricted] at hEuler
  exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hEuler)

end
end PiExponent.NumericalAmpleness

end OAI
