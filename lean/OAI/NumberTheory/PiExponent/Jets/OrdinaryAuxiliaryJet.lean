import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree
import OAI.NumberTheory.PiExponent.Jets.JetGeometry
import OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace PiExponent.OrdinaryAuxiliaryJet

def formalJet {n : ℕ} (c : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  MvPolynomial.aeval (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i)

def evaluation {n : ℕ} (K : ℕ) (V : Fin n → ℝ) (H : ℝ)
    (c : Fin K → Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₗ[ℂ]
      ((Fin K × ↥(strictWeightedSimplex V H)) → ℂ) :=
  LinearMap.pi (fun r =>
    (MvPowerSeries.coeff (InterpolationMatrix.exponentVector r.2.val)).comp
      (formalJet (c r.1)).toLinearMap)

theorem polynomialOfCoefficients_supportBound {n : ℕ} (W : Fin n → ℝ)
    (hW : ∀ i, 0 < W i) (N : ℝ)
    (x : ↥(realWeightedSimplex W N) → ℂ) :
    WeightedSliceDegree.SupportBound W N
      (polynomialOfCoefficients (realWeightedSimplex W N) x) := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp
    (polynomialOfCoefficients_support _ x he)
  have h := (mem_realWeightedSimplex hW).mp ha
  simpa only [Finsupp.weight_eq_sum, InterpolationMatrix.exponentVector_apply,
    nsmul_eq_mul, mul_comm] using h

theorem eventually_exists_auxiliaryPolynomial {n : ℕ}
    (W V : Fin n → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a^n * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (c : Fin K → Fin n → ℂ) :
    ∀ᶠ N : ℝ in atTop, ∃ p : MvPolynomial (Fin n) ℂ, p ≠ 0 ∧
      WeightedSliceDegree.SupportBound (fun i => (W i : ℝ)) N p ∧
      ∀ j d, Finsupp.weight (fun i => (V i : ℝ)) d < a*N →
        MvPowerSeries.coeff d (formalJet (c j) p) = 0 := by
  classical
  filter_upwards [eventually_auxiliary_card_lt W V hW hV K ha hvol] with N hN
  let S := realWeightedSimplex (fun i => (W i : ℝ)) N
  let E := (evaluation K (fun i => (V i : ℝ)) (a*N) c).comp (polynomialOfCoefficients S)
  have hcard : Fintype.card (Fin K × ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (a*N))) <
      Fintype.card S := by simpa [S] using hN
  obtain ⟨x, hx, hEx⟩ := exists_nonzero_kernel_of_card_lt E hcard
  refine ⟨polynomialOfCoefficients S x, ?_, ?_, ?_⟩
  · intro hp
    apply hx
    apply polynomialOfCoefficients_injective S
    simpa using hp
  · exact polynomialOfCoefficients_supportBound (fun i => (W i : ℝ))
      (fun i => by exact_mod_cast hW i) N x
  · intro j d hd
    have hmem : (fun i => d i) ∈ strictWeightedSimplex (fun i => (V i : ℝ)) (a*N) := by
      apply (mem_strictWeightedSimplex (fun i => by exact_mod_cast hV i)).mpr
      simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hd
    have hh := congrFun hEx (j, ⟨(fun i => d i), hmem⟩)
    have hd' : InterpolationMatrix.exponentVector (fun i => d i) = d := by ext i; rfl
    simpa [E, evaluation, hd'] using hh

theorem eventually_exists_auxiliaryPolynomial_nat {n : ℕ}
    (W V : Fin n → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℚ} (ha : 0 < a)
    (hvol : (K : ℝ) * (a : ℝ)^n * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (c : Fin K → Fin n → ℂ) :
    ∀ᶠ N : ℕ in atTop, ∃ p : MvPolynomial (Fin n) ℂ, p ≠ 0 ∧
      WeightedSliceDegree.SupportBound (fun i => (W i : ℝ)) N p ∧
      ∀ j, formalJet (c j) p ∈
        JetGeometry.rationalWeightedIdeal V (fun i => le_of_lt (hV i)) (a*N) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_exists_auxiliaryPolynomial W V hW hV K
      (by exact_mod_cast ha) hvol c)
  filter_upwards [h] with N hN
  obtain ⟨p, hp, hw, hv⟩ := hN
  refine ⟨p, hp, hw, ?_⟩
  intro j d hd
  apply hv j d
  have hcast : ((Finsupp.weight V d : ℚ) : ℝ) < (a : ℝ)*(N : ℝ) := by exact_mod_cast hd
  simpa [Finsupp.weight_eq_sum, nsmul_eq_mul] using hcast

end PiExponent.OrdinaryAuxiliaryJet
end

end OAI
