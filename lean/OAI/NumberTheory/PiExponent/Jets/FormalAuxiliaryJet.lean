import OAI.NumberTheory.PiExponent.Jets.FormalLogJet
import OAI.NumberTheory.PiExponent.Polynomials.AuxiliaryPolynomial

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace PiExponent

def formalJetEvaluation {m : ℕ} (K : ℕ)
    (V : Fin (m+1) → ℝ) (H : ℝ) (c : Fin K → Fin m → ℂ) :
    PiExponentApprox.FramePolynomial m →ₗ[ℂ]
      ((Fin K × ↥(strictWeightedSimplex V H)) → ℂ) :=
  LinearMap.pi (fun ρ =>
    (MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)).comp
      (FormalLogJet.formalJet (c ρ.1)).toLinearMap)

theorem eventually_exists_formalJet_auxiliaryPolynomial {m : ℕ}
    (W V : Fin (m+1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a^(m+1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℝ in atTop, ∃ p : PiExponentApprox.FramePolynomial m, p ≠ 0 ∧
      PiExponentApprox.HasWeightedDegreeLE (fun i => (W i : ℝ)) N p ∧
      ∀ j d, Finsupp.weight (fun i => (V i : ℝ)) d < a*N →
        MvPowerSeries.coeff d (FormalLogJet.formalJet (c j) p) = 0 := by
  filter_upwards [eventually_exists_auxiliaryPolynomial W V hW hV K ha hvol] with N hN
  obtain ⟨p, hp, hw, he⟩ := hN (formalJetEvaluation K (fun i => (V i : ℝ)) (a*N) c)
  refine ⟨p, hp, hw, ?_⟩
  intro j d hd
  have hmem : (fun i => d i) ∈ strictWeightedSimplex (fun i => (V i : ℝ)) (a*N) := by
    apply (mem_strictWeightedSimplex (fun i => by exact_mod_cast hV i)).mpr
    simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hd
  have hh := congrFun he (j, ⟨(fun i => d i), hmem⟩)
  have hd' : InterpolationMatrix.exponentVector (fun i => d i) = d := by ext i; rfl
  simpa [formalJetEvaluation, hd'] using hh

theorem eventually_exists_formalJet_auxiliaryPolynomial_nat {m : ℕ}
    (W V : Fin (m+1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℚ} (ha : 0 < a)
    (hvol : (K : ℝ) * (a : ℝ)^(m+1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℕ in atTop, ∃ p : PiExponentApprox.FramePolynomial m, p ≠ 0 ∧
      PiExponentApprox.HasWeightedDegreeLE (fun i => (W i : ℝ)) N p ∧
      ∀ j, FormalLogJet.formalJet (c j) p ∈
        JetGeometry.rationalWeightedIdeal V (fun i => le_of_lt (hV i)) (a*N) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_exists_formalJet_auxiliaryPolynomial W V hW hV K
      (by exact_mod_cast ha) hvol c)
  filter_upwards [h] with N hN
  obtain ⟨p, hp, hw, hv⟩ := hN
  refine ⟨p, hp, hw, ?_⟩
  intro j d hd
  apply hv j d
  have hcast : ((Finsupp.weight V d : ℚ) : ℝ) < (a : ℝ)*(N : ℝ) := by exact_mod_cast hd
  simpa [Finsupp.weight_eq_sum, nsmul_eq_mul] using hcast

end PiExponent

end

end OAI
