import OAI.AlgebraicGeometry.CartierSections.FormalValuation
import OAI.AlgebraicGeometry.CartierSections.Weights

namespace OAI

/-!
# Valuations induced by formal expansions

A formal coordinate expansion pulls back the monomial valuation to the
original ring. Injective expansions give finite values on nonzero elements.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal
namespace CartierSections
section ExpansionBridge
variable {σ k R : Type*} [Fintype σ] [Field k] [CommRing R] [Algebra k R]

/-- The infimum of the real weights of nonzero coefficients. -/
def seriesWeight (w : σ → ℝ) (f : MvPowerSeries σ k) : ENNReal :=
  ⨅ (d : σ →₀ ℕ) (_ : MvPowerSeries.coeff d f ≠ 0), ENNReal.ofReal (realWeight w d)

def IsMonomialInExpansion (v : AddValuation R ENNReal)
    (θ : R →ₐ[k] MvPowerSeries σ k) (w : σ → ℝ) : Prop :=
  ∀ f, v f = seriesWeight w (θ f)

lemma coe_finsupp_weight (w : σ → ℝ≥0) (d : σ →₀ ℕ) :
    (Finsupp.weight w d : ℝ) = realWeight (fun i => (w i : ℝ)) d := by
  rw [Finsupp.weight_eq_sum]
  simp [realWeight, NNReal.coe_sum, nsmul_eq_mul, mul_comm]

lemma formalValue_eq_seriesWeight (w : σ → ℝ≥0) (f : MvPowerSeries σ k) :
    FormalMonomial.value w f = seriesWeight (fun i => (w i : ℝ)) f := by
  unfold FormalMonomial.value seriesWeight
  congr 1
  funext d
  congr 1
  funext hd
  rw [← coe_finsupp_weight, ENNReal.ofReal_coe_nnreal]

/-- Pull back a formal monomial valuation along an expansion homomorphism. -/
def expansionValuation (θ : R →ₐ[k] MvPowerSeries σ k) (w : σ → ℝ≥0) :
    AddValuation R ENNReal := (FormalMonomial.valuation w).comap θ.toRingHom

lemma expansionValuation_monomial (θ : R →ₐ[k] MvPowerSeries σ k) (w : σ → ℝ≥0) :
    IsMonomialInExpansion (expansionValuation θ w) θ (fun i => (w i : ℝ)) := by
  intro f
  exact formalValue_eq_seriesWeight w (θ f)

lemma expansionValuation_finite (θ : R →ₐ[k] MvPowerSeries σ k)
    (hθ : Function.Injective θ) (w : σ → ℝ≥0) {f : R} (hf : f ≠ 0) :
    expansionValuation θ w f < ⊤ := by
  have hf' : θ f ≠ 0 := by
    intro h
    apply hf
    apply hθ
    simpa using h
  obtain ⟨d, hd, he⟩ := FormalMonomial.value_attained w hf'
  change FormalMonomial.value w (θ f) < ⊤
  rw [he]
  exact ENNReal.coe_lt_top

end ExpansionBridge
end CartierSections

end

end OAI
