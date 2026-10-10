import Mathlib
import OAI.NumberTheory.PiExponent.Approximation.LinePullback
import OAI.NumberTheory.PiExponent.Cohomology.EulerExact
import OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler
import OAI.NumberTheory.PiExponent.Geometry.CartierSequence

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

namespace PiExponent.CartierDegreeLength


theorem cartier_euler_difference_eq_sum_local_lengths
    {X : Scheme.{0}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (M N : LineBundle X) (φ : M.sheaf ⟶ N.sheaf) [Mono φ]
    (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (heq : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      ∃ e : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ d : N.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
        I.ideal U = Ideal.span {U.1.topIso.hom
          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))})
    (hfiniteM : ∀ n ≤ 1, letI := Module.compHom (cohomology M.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology M.sheaf n))
    (hfiniteN : ∀ n ≤ 1, letI := Module.compHom (cohomology N.sheaf n) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf n))
    [Subsingleton (cohomology M.sheaf 2)] :
    letI : Finite I.subscheme := finite_subscheme_of_curve p hd I hI
    letI : Fintype I.subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 N.sheaf - eulerCharacteristic p 1 M.sheaf =
      ∑ x : I.subscheme,
        ((Module.length (I.subscheme.presheaf.stalk x)
          (I.subscheme.presheaf.stalk x)).toNat : ℤ) := by
  let : Finite I.subscheme := finite_subscheme_of_curve p hd I hI
  let : Fintype I.subscheme := Fintype.ofFinite _
  obtain ⟨hz, hseq⟩ := PiExponentSeshadri.CartierSequence.exact p M N φ I heq
  have hfiniteZ (n : ℕ) (_hn : n ≤ 1) :=
    PiExponentSeshadri.FiniteSupport.finite_line_pushforward_finiteDimensional
      I.subschemeι p (N.pullback I.subschemeι) n
  have h := eulerCharacteristic_add p hseq 1 hfiniteM hfiniteN hfiniteZ
  have hdiff : eulerCharacteristic p 1 N.sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1
        ((Scheme.Modules.pushforward I.subschemeι).obj
          ((Scheme.Modules.pullback I.subschemeι).obj N.sheaf)) := by
    exact sub_eq_iff_eq_add.mpr (by simpa [add_comm] using h)
  exact hdiff.trans
    (PiExponentSeshadri.FiniteSupport.finite_line_euler_eq_sum_stalk_lengths
      I.subschemeι p (N.pullback I.subschemeι) 1)

end PiExponent.CartierDegreeLength

end

end OAI
