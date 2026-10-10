import OAI.NumberTheory.Ostmann.Supply.FiniteParseval

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators ComplexConjugate
variable {p : ℕ} [NeZero p]
local notation "H" => EuclideanSpace ℂ (ZMod p)

def unitaryDFTLinear : H →ₗ[ℂ] H where
  toFun f := WithLp.toLp 2 (unitaryDFT f)
  map_add' f g := by
    ext v
    simp only [PiLp.add_apply, WithLp.ofLp_add, unitaryDFT, map_add,
      Pi.add_apply, add_div]
  map_smul' c f := by
    ext v
    simp only [PiLp.smul_apply, WithLp.ofLp_smul, unitaryDFT,
      RingHom.id_apply, map_smul, Pi.smul_apply, smul_eq_mul, mul_div_assoc]

@[simp] theorem unitaryDFTLinear_apply (f : H) (v : ZMod p) :
    unitaryDFTLinear f v = unitaryDFT f v := rfl

def fourierIsometry : H →ₗᵢ[ℂ] H where
  toLinearMap := unitaryDFTLinear
  norm_map' f := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    exact unitaryDFT_parseval f

def fourierEquiv : H ≃ₗᵢ[ℂ] H :=
  LinearIsometryEquiv.ofSurjective fourierIsometry
    (LinearMap.injective_iff_surjective.mp (fourierIsometry (p := p)).injective)

@[simp] theorem fourierEquiv_apply (f : H) (v : ZMod p) :
    fourierEquiv f v = unitaryDFT f v := rfl

theorem fourierEquiv_inner (f g : H) :
    inner ℂ (fourierEquiv f) (fourierEquiv g) = inner ℂ f g :=
  fourierEquiv.inner_map_map f g

end Ostmann.Supply

end

end OAI
