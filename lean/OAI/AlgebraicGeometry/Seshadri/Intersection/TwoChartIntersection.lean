import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.ChartPolynomial
import OAI.AlgebraicGeometry.Seshadri.Cohomology.LaurentH0

namespace OAI

section
noncomputable section
                                              
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

variable {K : Type} [Field K] {U V W : Scheme.{0}} [IsAffine U] [IsAffine V]

theorem two_chart_intersection_finite
    (kU : K →+* Γ(U,⊤)) (kV : K →+* Γ(V,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ U) (b : W ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b]
    (hka : a.appTop.hom.comp kU = kW) (hkb : b.appTop.hom.comp kV = kW)
    (u : Γ(U,⊤)) (v : Γ(V,⊤))
    (ha : a.opensRange = U.basicOpen u) (_hb : b.opensRange = V.basicOpen v)
    (huv : a.appTop u * b.appTop v = 1)
    (hu : (Polynomial.eval₂RingHom kU u).Finite)
    (hv : (Polynomial.eval₂RingHom kV v).Finite)
    (L : LineBundle U) (P : LineBundle V) (N : W.Modules)
    (e : L.sheaf.restrict a ≅ N) (d : P.sheaf.restrict b ≅ N) :
    Module.Finite K ↥((chartMap kU kW a hka L.sheaf e).range ⊓
        (chartMap kV kW b hkb P.sheaf d).range) := by
  let := polynomialModule kU u L.sheaf ⊤
  let := polynomialModule kV v P.sheaf ⊤
  let := polynomialModule kW (a.appTop u) N ⊤
  let := polynomialTower kU u L.sheaf ⊤
  let := polynomialTower kV v P.sheaf ⊤
  let := polynomialTower kW (a.appTop u) N ⊤
  let : Module.Finite K[X] (Sections kU L.sheaf ⊤) := polynomial_finite kU u L hu
  let : Module.Finite K[X] (Sections kV P.sheaf ⊤) := polynomial_finite kV v P hv
  let F := chartPolynomialMap kU kW a hka L.sheaf e u
  let G := chartMap kV kW b hkb P.sheaf d
  let : IsLocalizedModule.Away (Polynomial.X : K[X]) F :=
    chartPolynomialMap_localize kU kW a hka L.sheaf e u ha
  have hInv (y : Sections kV P.sheaf ⊤) :
      (Polynomial.X : K[X]) • G ((Polynomial.X : K[X]) • y) = G y := by
    change (Polynomial.eval₂RingHom kW (a.appTop u)) Polynomial.X •
      G ((Polynomial.eval₂RingHom kV v) Polynomial.X • y) = G y
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [chartMap_smul, ← mul_smul, huv, one_smul]
  exact LaurentCech.intersection_finite F G hInv
end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
