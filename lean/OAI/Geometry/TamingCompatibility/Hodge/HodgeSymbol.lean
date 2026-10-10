import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.DirectionalEnergy

namespace OAI

section
section

section
noncomputable section
open scoped RealInnerProductSpace
namespace TamingCompatibility.UnitaryFrame

theorem hodge_principal_symbol (ξ : V) (a : W) :
    wedge ξ (interior ξ a) + star (wedge ξ (interior ξ (star a))) = ‖ξ‖^2 • a := by
  rw [EuclideanSpace.real_norm_sq_eq]
  ext i
  fin_cases i <;> simp [wedge,interior,star,Fin.sum_univ_succ] <;> ring

theorem hodge_symbol_energy (ξ : V) (a : W) :
    ‖interior ξ a‖^2 + ‖interior ξ (star a)‖^2 = ‖ξ‖^2*‖a‖^2 := by
  simp only [EuclideanSpace.real_norm_sq_eq]
  simp [interior,star,Fin.sum_univ_succ]
  ring
end TamingCompatibility.UnitaryFrame

namespace TamingCompatibility.HermitianHodge
open GeometricSymbol UnitaryFrame UnitaryBasis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (J : E →ₗᵢ[ℝ] E) (hJ : ∀ u, J (J u) = -u)
  (hdim : Module.finrank ℝ E = 4) (F : GeometricSymbol.TwoForm E)
  (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)

omit [FiniteDimensional ℝ E] in
lemma coords_add (b : OrthonormalBasis (Fin 4) ℝ E) (a c : GeometricSymbol.TwoForm E) :
    coords b (a+c) = coords b a + coords b c := by ext i; fin_cases i <;> rfl

include hJ hdim hF

theorem hodge_principal_symbol (ξ : E) (a : GeometricSymbol.TwoForm E) :
    GeometricSymbol.symbol ξ a +
      star J.toContinuousLinearMap F (GeometricSymbol.symbol ξ (star J.toContinuousLinearMap F a)) =
        ‖ξ‖^2 • a := by
  obtain ⟨b,h0,h1,h2,h3⟩ := exists_unitary_basis J hJ hdim
  apply coords_injective b
  rw [coords_add,coords_star b _ h0 h1 h2 h3 F hF,coords_symbol,coords_symbol,
    coords_star b _ h0 h1 h2 h3 F hF,coords_smul]
  rw [UnitaryFrame.hodge_principal_symbol,b.repr.norm_map]
end TamingCompatibility.HermitianHodge

namespace TamingCompatibility.MetricHodge
open MetricForms MetricModel
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

def metricSymbol (g : Metric E) (ξ : E) (a : MetricForms.Form E 2) : MetricForms.Form E 2 :=
  (formEquiv g 2).symm (GeometricSymbol.symbol ((equiv g).symm ξ) (formEquiv g 2 a))

lemma metricSymbol_apply (g : Metric E) (ξ : E) (a : MetricForms.Form E 2) (v w : E) :
    metricSymbol g ξ a ![v,w] = g.bilinear ξ v * a ![ξ,w] - g.bilinear ξ w * a ![ξ,v] := by
  change GeometricSymbol.symbol ((equiv g).symm ξ) (formEquiv g 2 a)
    ![(equiv g).symm v,(equiv g).symm w] = _
  rw [GeometricSymbol.symbol_apply]
  rfl

theorem hodge_principal_symbol (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u, J (J u) = -u)
    (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form E 2)
    (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
    (ξ : E) (a : MetricForms.Form E 2) :
    metricSymbol g ξ a + starTwo g J F (metricSymbol g ξ (starTwo g J F a)) =
      g.bilinear ξ ξ • a := by
  apply (formEquiv g 2).injective
  rw [map_add,formEquiv_starTwo g J horth,map_smul]
  simp only [metricSymbol,ContinuousLinearEquiv.apply_symm_apply]
  rw [formEquiv_starTwo g J horth]
  have he := HermitianHodge.hodge_principal_symbol (isometry g J horth) hJ
    ((finrank_model g).trans hdim) (formEquiv g 2 F) hF ((equiv g).symm ξ) (formEquiv g 2 a)
  rw [← real_inner_self_eq_norm_sq] at he
  exact he
end TamingCompatibility.MetricHodge

end
end

section
noncomputable section
open MeasureTheory
open scoped SchwartzMap LineDeriv RealInnerProductSpace
namespace TamingCompatibility.HodgeFlatEnergy
open EuclideanEnergy
open DirectionalEnergy (directionDeriv)

def pairing (f g : S) : ℝ := ∫ x, f x*g x
lemma pairing_add_left (a b c : S) : pairing (a+b) c = pairing a c+pairing b c := by
  simp only [pairing,add_apply,add_mul]
  exact integral_add (schwartz_mul_integrable a c) (schwartz_mul_integrable b c)
lemma pairing_add_right (a b c : S) : pairing a (b+c) = pairing a b+pairing a c := by
  simp only [pairing,add_apply,mul_add]
  exact integral_add (schwartz_mul_integrable a b) (schwartz_mul_integrable a c)
lemma pairing_neg_left (a b : S) : pairing (-a) b = -pairing a b := by simp [pairing, integral_neg]
lemma pairing_neg_right (a b : S) : pairing a (-b) = -pairing a b := by simp [pairing, integral_neg]
lemma pairing_sub_left (a b c : S) : pairing (a-b) c = pairing a c-pairing b c := by
  rw [sub_eq_add_neg,pairing_add_left,pairing_neg_left,sub_eq_add_neg]
lemma pairing_sub_right (a b c : S) : pairing a (b-c) = pairing a b-pairing a c := by
  rw [sub_eq_add_neg,pairing_add_right,pairing_neg_right,sub_eq_add_neg]
lemma pairing_comm (a b : S) : pairing a b = pairing b a := by simp only [pairing,mul_comm]
lemma pairing_partial_swap (b : Fin 4 → V) (i j : Fin 4) (f g : S) :
    pairing (directionDeriv b i f) (directionDeriv b j g) =
      pairing (directionDeriv b j f) (directionDeriv b i g) :=
  DirectionalEnergy.partial_mul_integral_swap b i j f g

lemma pairing_field_swap (b : Fin 4 → V) (i j : Fin 4) (f g : S) :
    pairing (directionDeriv b i f) (directionDeriv b j g) =
      pairing (directionDeriv b i g) (directionDeriv b j f) := by
  rw [pairing_partial_swap, pairing_comm]

lemma directionDeriv_neg (b : Fin 4 → V) (i : Fin 4) (f : S) :
    directionDeriv b i (-f) = -directionDeriv b i f := by
  ext x
  simp [directionDeriv]

def delta (b : Fin 4 → V) (a : Fin 6 → S) : Fin 4 → S :=
  ![-directionDeriv b 1 (a 0)-directionDeriv b 2 (a 1)-directionDeriv b 3 (a 2),
    directionDeriv b 0 (a 0)-directionDeriv b 2 (a 3)-directionDeriv b 3 (a 4),
    directionDeriv b 0 (a 1)+directionDeriv b 1 (a 3)-directionDeriv b 3 (a 5),
    directionDeriv b 0 (a 2)+directionDeriv b 1 (a 4)+directionDeriv b 2 (a 5)]
def star (a : Fin 6 → S) : Fin 6 → S := ![a 5,-a 4,a 3,a 2,-a 1,a 0]

def energy (b : Fin 4 → V) (a : Fin 6 → S) : ℝ :=
  (∑ i, pairing (delta b a i) (delta b a i)) + ∑ i, pairing (delta b (star a) i) (delta b (star a) i)
def gradientEnergy (b : Fin 4 → V) (a : Fin 6 → S) : ℝ :=
  ∑ i : Fin 4, ∑ j : Fin 6, pairing (directionDeriv b i (a j)) (directionDeriv b i (a j))

theorem energy_eq_gradient (b : Fin 4 → V) (a : Fin 6 → S) : energy b a = gradientEnergy b a := by
  simp only [energy,gradientEnergy,Fin.sum_univ_succ]
  simp [delta,star, directionDeriv_neg,
    pairing_add_left,pairing_add_right,pairing_sub_left,pairing_sub_right,
    pairing_neg_left,pairing_neg_right]
  simp only [pairing_field_swap,pairing_partial_swap]
  ring
end TamingCompatibility.HodgeFlatEnergy

end
end

end
end

end OAI
