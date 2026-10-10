import OAI.Geometry.Relativity.CKS.HeatEquation

namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open Set Filter MvPolynomial
open scoped Topology ContDiff Manifold

def inversePolynomials (p : ℕ → Poly) (n : ℕ) : Poly :=
  (1 - CKSSpectralHeat.eigenvalue n / 2)⁻¹ • p n

lemma inversePolynomials_rapid (p : ℕ → Poly) (hp : PolynomialRapid p) :
    PolynomialRapid (inversePolynomials p) := by
  intro w b
  have h := CKSSpectralHeat.inverseCoeff_rapid (fun n => sphereEval (rotationWord w (p n))) (hp w) b
  simpa only [inversePolynomials, rotationWord_smul, map_smul, CKSSpectralHeat.inverseCoeff] using h

lemma inversePolynomials_harmonic (p : ℕ → Poly) (hh : HighHarmonic p) :
    HighHarmonic (inversePolynomials p) := by
  intro n
  refine ⟨(homogeneousSubmodule (Fin 3) ℝ (n+2)).smul_mem _ (hh n).1, ?_⟩
  simp only [inversePolynomials, map_smul, (hh n).2, smul_zero]

lemma heatTerm_inverse (p : ℕ → Poly) (a : HeatJet) (n : ℕ) (z : SpaceTime) :
    heatTerm (inversePolynomials p) a n z =
      (1 - CKSSpectralHeat.eigenvalue n / 2)⁻¹ * heatTerm p a n z := by
  simp only [heatTerm, inversePolynomials, rotationWord_smul, radialExtension_poly_smul]
  ring

lemma casimir_terms_summable (p : ℕ → Poly) (hp : PolynomialRapid p)
    (hh : HighHarmonic p) (a : HeatJet) {z : SpaceTime} (hz : z ∈ heatDomain) :
    Summable (fun n => -CKSSpectralHeat.eigenvalue n * heatTerm p a n z) := by
  have h := ((jointHeatSeries_summable p hp (a.1, (0,1)::(0,1)::a.2) hz).add
    (jointHeatSeries_summable p hp (a.1, (0,2)::(0,2)::a.2) hz)).add
    (jointHeatSeries_summable p hp (a.1, (1,2)::(1,2)::a.2) hz)
  exact h.congr (fun n => heatTerm_casimir p hh a n z)

theorem spatialHeat_inverse_equation (p : ℕ → Poly) (hp : PolynomialRapid p)
    (hh : HighHarmonic p) (a : HeatJet) (t : ℝ) {x : Ambient} (hx : x ≠ 0) :
    spatialHeat (inversePolynomials p) a t x +
      smoothCasimir (spatialHeat (inversePolynomials p) a t) x / 2 = spatialHeat p a t x := by
  have hip := inversePolynomials_rapid p hp
  have hih := inversePolynomials_harmonic p hh
  rw [spatialHeat_casimir_series _ hip hih a t hx, ← tsum_div_const]
  unfold spatialHeat jointHeatSeries
  rw [← (jointHeatSeries_summable _ hip a hx).tsum_add
    ((casimir_terms_summable _ hip hih a hx).div_const 2)]
  congr 1
  funext n
  rw [heatTerm_inverse]
  have hd : 1 - CKSSpectralHeat.eigenvalue n / 2 ≠ 0 := by
    have he := CKSSpectralHeat.eigenvalue_ge_six n
    linarith
  calc
    _ = ((1 - CKSSpectralHeat.eigenvalue n / 2)⁻¹ *
      (1 - CKSSpectralHeat.eigenvalue n / 2)) * heatTerm p a n (t,x) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]

lemma harmonic_sphereIntegral_zero {p : Poly} {l : ℕ} (hp : p.IsHomogeneous l)
    (hΔ : laplacian p = 0) (hl : l ≠ 0) : sphereIntegral (sphereEval p) = 0 := by
  have he := congrArg (fun q => sphereIntegral (sphereEval q)) (harmonic_rotation_eigenvalue hp hΔ)
  simp only [map_add, map_smul, sphereIntegral_rotation 0 1 (by decide), sphereIntegral_rotation 0 2 (by decide),
    sphereIntegral_rotation 1 2 (by decide), smul_eq_mul, add_zero] at he
  have hc : -((l : ℝ) * ((l : ℝ) + 1)) ≠ 0 := by
    exact neg_ne_zero.mpr (mul_ne_zero (Nat.cast_ne_zero.mpr hl) (by positivity))
  exact (mul_eq_zero.mp he.symm).resolve_left hc

lemma sphereHeatJet_mean_zero (p : ℕ → Poly) (hp : PolynomialRapid p)
    (hh : HighHarmonic p) (a : HeatJet) (t : ℝ) : sphereIntegral (sphereHeatJet p a t) = 0 := by
  rw [sphereHeatJet, CKSSpectralHeat.heat_deriv _ (hp a.2),
    sphereIntegral.map_tsum (CKSSpectralHeat.term_deriv_summable _ (hp a.2) a.1 t)]
  have hz (n : ℕ) : sphereIntegral (sphereEval (rotationWord a.2 (p n))) = 0 :=
    harmonic_sphereIntegral_zero (rotationWord_harmonic (hh n).1 (hh n).2 a.2).1
      (rotationWord_harmonic (hh n).1 (hh n).2 a.2).2 (by omega)
  simp only [CKSSpectralHeat.term_deriv, map_smul, hz, smul_zero, tsum_zero]

end
end CKSSphericalHarmonics

end

end OAI
