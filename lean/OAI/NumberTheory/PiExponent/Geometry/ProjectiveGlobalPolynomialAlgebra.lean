import OAI.NumberTheory.PiExponent.Cohomology.GradedH0
import OAI.NumberTheory.PiExponent.Cohomology.ProjectiveLaurentVertex
import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra
noncomputable section
open scoped BigOperators
open MvPolynomial
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponentSeshadri.Projective


variable {σ K : Type*} [Fintype σ] [CommRing K]

def chartExponent (i : σ) (b : σ →₀ ℕ) : ChartExponent i :=
  Finsupp.equivFunOnFinite.symm (fun j => b j.val)

@[simp] theorem chartExponent_apply (i : σ) (b : σ →₀ ℕ) (j : ChartVariables i) :
    chartExponent i b j = b j.val := rfl

theorem dehomogenize_monomial (i : σ) (b : σ →₀ ℕ) (r : K) :
    dehomogenize i (MvPolynomial.monomial b r) =
      MvPolynomial.monomial (chartExponent i b) r := by
  classical
  rw [dehomogenize, MvPolynomial.eval₂Hom_monomial, MvPolynomial.monomial_eq]
  congr 1
  rw [Finsupp.prod_fintype, Finsupp.prod_fintype]
  · rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
    simp
    apply Finset.prod_congr rfl
    intro j _
    simp [j.property]
  · intro j
    simp
  · intro j
    simp

theorem encode_chartExponent (i : σ) (n : ℕ) (b : σ →₀ ℕ) (hb : b.degree = n) :
    ProjectiveLaurentVertex.encode i (n : ℤ) (chartExponent i b) =
      GradedH0.encode n ⟨b, hb⟩ := by
  classical
  apply Subtype.ext
  funext j
  by_cases hj : j = i
  · subst j
    rw [ProjectiveLaurentVertex.encode_self]
    erw [GradedH0.encode_apply]
    have hs : (b i : ℤ) + ∑ j : ChartVariables i, (b j.val : ℤ) = n := by
      rw [← Fintype.sum_eq_add_sum_subtype_ne (fun j => (b j : ℤ)) i,
        ← Nat.cast_sum, ← Finsupp.degree_eq_sum, hb]
    simpa only [chartExponent_apply] using (eq_sub_iff_add_eq.mpr hs).symm
  · change (ProjectiveLaurentVertex.encode i (n : ℤ) (chartExponent i b)).val
      (⟨j, hj⟩ : ChartVariables i) = _
    exact ProjectiveLaurentVertex.encode_other i (n : ℤ) (chartExponent i b) ⟨j, hj⟩

theorem polynomialLaurent_monomial (n : ℕ) (b : σ →₀ ℕ) (hb : b.degree = n) (r : K) :
    GradedH0.polynomialLaurent n ⟨MvPolynomial.monomial b r,
      MvPolynomial.isHomogeneous_monomial r hb⟩ =
      Finsupp.single (GradedH0.encode n ⟨b, hb⟩) r := by
  classical
  simp [GradedH0.polynomialLaurent, GradedH0.homogeneousPolynomialEquiv,
    MvPolynomial.monomial, GradedH0.exponentEquiv,
    AddMonoidAlgebra.supportedEquivFinsupp]
  have hs : (Finsupp.supportedEquivFinsupp (R := K) {b : σ →₀ ℕ | b.degree = n})
      ⟨Finsupp.single b r, Finsupp.single_mem_supported K r hb⟩ =
      Finsupp.single ⟨b, hb⟩ r := by
    apply (Finsupp.supportedEquivFinsupp (R := K) {b : σ →₀ ℕ | b.degree = n}).symm.injective
    apply Subtype.ext
    simp
  change (Finsupp.domLCongr (GradedH0.exponentEquiv n)
    ((Finsupp.supportedEquivFinsupp (R := K) {b : σ →₀ ℕ | b.degree = n})
      ⟨Finsupp.single b r, Finsupp.single_mem_supported K r hb⟩)).extendDomain = _
  rw [hs]
  change (Finsupp.domLCongr (GradedH0.exponentEquiv n)
    (Finsupp.single (⟨b, hb⟩ : GradedH0.PolynomialExponent (ι := σ) n) r)).extendDomain = _
  erw [Finsupp.domLCongr_single, Finsupp.extendDomain_single]
  rfl

theorem vertexLaurent_dehomogenize (i : σ) (n : ℕ)
    (p : MvPolynomial.homogeneousSubmodule σ K n) :
    vertexLaurent i (n : ℤ) (dehomogenize i p.val) = GradedH0.polynomialLaurent n p := by
  rcases p with ⟨p, hp⟩
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
    change vertexLaurent i (n : ℤ) (dehomogenize i 0) = GradedH0.polynomialLaurent n 0
    simp only [map_zero]
  | add p q hp hq ihp ihq =>
    change vertexLaurent i (n : ℤ) (dehomogenize i (p + q)) =
      GradedH0.polynomialLaurent n (⟨p, hp⟩ + ⟨q, hq⟩)
    rw [map_add, map_add, map_add, ihp, ihq]
  | monomial b r hb =>
    have hd : b.degree = n := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hb
    rw [dehomogenize_monomial, vertexLaurent_monomial,
      polynomialLaurent_monomial n b hd r, encode_chartExponent i n b hd]

end
end PiExponent.GeometrySupport.ProjectiveGlobalPolynomialAlgebra

end OAI
