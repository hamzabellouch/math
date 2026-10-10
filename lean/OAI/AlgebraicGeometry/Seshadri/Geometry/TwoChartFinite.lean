import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Cohomology.LaurentCech
import OAI.AlgebraicGeometry.Seshadri.Geometry.ChartPolynomial

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped Polynomial

variable {K : Type} [Field K] {U V W : Scheme.{0}} [IsAffine U] [IsAffine V]

theorem two_chart_cokernel_finite
    (kU : K →+* Γ(U,⊤)) (kV : K →+* Γ(V,⊤)) (kW : K →+* Γ(W,⊤))
    (a : W ⟶ U) (b : W ⟶ V) [IsOpenImmersion a] [IsOpenImmersion b]
    (hka : a.appTop.hom.comp kU = kW) (hkb : b.appTop.hom.comp kV = kW)
    (u : Γ(U,⊤)) (v : Γ(V,⊤))
    (ha : a.opensRange = U.basicOpen u) (hb : b.opensRange = V.basicOpen v)
    (huv : a.appTop u * b.appTop v = 1)
    (hu : (Polynomial.eval₂RingHom kU u).Finite)
    (L : LineBundle U) (P : LineBundle V) (N : W.Modules)
    (e : L.sheaf.restrict a ≅ N) (d : P.sheaf.restrict b ≅ N) :
    Module.Finite K (Sections kW N ⊤ ⧸
      ((chartMap kU kW a hka L.sheaf e).range ⊔
        (chartMap kV kW b hkb P.sheaf d).range)) := by
  let := polynomialModule kU u L.sheaf ⊤
  let := polynomialModule kV v P.sheaf ⊤
  let := polynomialModule kW (a.appTop u) N ⊤
  have := polynomialTower kU u L.sheaf ⊤
  have := polynomialTower kV v P.sheaf ⊤
  have := polynomialTower kW (a.appTop u) N ⊤
  have : Module.Finite K[X] (Sections kU L.sheaf ⊤) := polynomial_finite kU u L hu
  let F := chartPolynomialMap kU kW a hka L.sheaf e u
  let G := chartMap kV kW b hkb P.sheaf d
  have : IsLocalizedModule.Away (Polynomial.X : K[X]) F :=
    chartPolynomialMap_localize kU kW a hka L.sheaf e u ha
  have hInv (y : Sections kV P.sheaf ⊤) :
      (Polynomial.X : K[X]) • G ((Polynomial.X : K[X]) • y) = G y := by
    change (Polynomial.eval₂RingHom kW (a.appTop u)) Polynomial.X •
      G ((Polynomial.eval₂RingHom kV v) Polynomial.X • y) = G y
    simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rw [chartMap_smul, ← mul_smul, huv, one_smul]
  have hDen (x : OpenSections N ⊤) : ∃ n : ℕ, ∃ y : Sections kV P.sheaf ⊤,
      (Polynomial.X : K[X])^n • G y = x := by
    let : Module Γ(V,⊤) (OpenSections N ⊤) :=
      Module.compHom (OpenSections N ⊤) b.appTop.hom
    let G' := chartModuleMap P.sheaf b d
    have : IsLocalizedModule.Away v G' := chartModuleMap_localize P.sheaf b d v hb
    obtain ⟨n,y,hy⟩ := IsLocalizedModule.Away.surj G' v x
    refine ⟨n,y,?_⟩
    change (Polynomial.eval₂RingHom kW (a.appTop u)) (Polynomial.X^n) • G y = x
    simp only [map_pow, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    change b.appTop (v^n) • (x : OpenSections N ⊤) = G' y at hy
    change (a.appTop u)^n • (G' y : OpenSections N ⊤) = x
    rw [← hy, map_pow, ← mul_smul, ← mul_pow, huv, one_pow, one_smul]
  exact LaurentCech.cokernel_finite F G hInv hDen
end
end MaximalSeshadri.Geometry.BaseSections
end


end
end

end OAI
