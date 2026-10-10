import Mathlib
import OAI.Geometry.TamingCompatibility.Charts.SquareCutoff
import OAI.Geometry.TamingCompatibility.Hodge.HodgeCommutatorPowers

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.ComplexMatrix
open HilbertSobolev EuclideanSobolevOperators TemperedDistribution Filter Set
open LocalMatrixOperator EuclideanEnergy
open scoped SchwartzMap LineDeriv Topology
variable {m : ℕ}

lemma fullShiftedSquare_cutoff_locality
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (ζ : 𝓢(V,ℂ)) (G : Fin 4 → Fin 4 → V → ℝ)
    (hG : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*G i j x) • ContinuousLinearMap.id ℝ (R 6))
    (g h : 𝓢(V,ℂ)) (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(V,C 6)) :
    smulLeftCLM (C 6) g (fullShiftedSquare a b ρ ζ (smulLeftCLM (C 6) h u)) =
      smulLeftCLM (C 6) g (fullShiftedSquare a b ρ ζ u) := by
  rw [full_shifted_square_expansion a b ρ ζ G hG,
    full_shifted_square_expansion a b ρ ζ G hG]
  simp only [map_add,map_neg]
  rw [directionalPrincipal_locality e (fullPrincipalScalar a ρ) g h hh u,
    matrixLowerOrder_locality _ _ _ _ _ g h hh u]

lemma normalizedFullSquare_cutoff_locality
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (G : Fin 4 → Fin 4 → V → ℝ)
    (hG : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*G i j x) • ContinuousLinearMap.id ℝ (R 6))
    (g h : 𝓢(V,ℂ)) (hh : ∀ x ∈ tsupport g, h =ᶠ[𝓝 x] fun _ => 1) (u : 𝓢'(V,C 6)) :
    smulLeftCLM (C 6) g (normalizedFullSquare a b ρ θ (smulLeftCLM (C 6) h u)) =
      smulLeftCLM (C 6) g (normalizedFullSquare a b ρ θ u) := by
  change smulLeftCLM (C 6) g (smulLeftCLM (C 6) θ _) = smulLeftCLM (C 6) g (smulLeftCLM (C 6) θ _)
  rw [coefficient_products_commute g θ,coefficient_products_commute g θ]
  apply congrArg (smulLeftCLM (C 6) θ)
  exact fullShiftedSquare_cutoff_locality a b ρ 0 G hG g h hh u

def LocallyEqual (U : Set V) (u v : 𝓢'(V,C 6)) : Prop :=
  ∀ χ : 𝓢(V,ℂ), HasCompactSupport (χ : V → ℂ) → tsupport χ ⊆ U →
    smulLeftCLM (C 6) χ u = smulLeftCLM (C 6) χ v

lemma normalizedFullSquare_local_congr
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (G : Fin 4 → Fin 4 → V → ℝ)
    (hG : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*G i j x) • ContinuousLinearMap.id ℝ (R 6))
    {U : Set V} (hU : IsOpen U) {u v : 𝓢'(V,C 6)} (huv : LocallyEqual U u v) :
    LocallyEqual U (normalizedFullSquare a b ρ θ u) (normalizedFullSquare a b ρ θ v) := by
  intro χ hc hχU
  obtain ⟨η,hη,hηU,hηχ⟩ := exists_outer_cutoff hU χ hc hχU
  rw [← normalizedFullSquare_cutoff_locality a b ρ θ G hG χ η hηχ u,
    huv η hη hηU,normalizedFullSquare_cutoff_locality a b ρ θ G hG χ η hηχ v]

lemma LocallyEqual.refl (U : Set V) (u : 𝓢'(V,C 6)) : LocallyEqual U u u :=
  fun _ _ _ => rfl

lemma LocallyEqual.symm {U : Set V} {u v : 𝓢'(V,C 6)} (h : LocallyEqual U u v) :
    LocallyEqual U v u := fun χ hc hχ => (h χ hc hχ).symm

lemma LocallyEqual.trans {U : Set V} {u v w : 𝓢'(V,C 6)}
    (h : LocallyEqual U u v) (h' : LocallyEqual U v w) : LocallyEqual U u w :=
  fun χ hc hχ => (h χ hc hχ).trans (h' χ hc hχ)

lemma LocallyEqual.sub {U : Set V} {u v w z : 𝓢'(V,C 6)}
    (h : LocallyEqual U u v) (h' : LocallyEqual U w z) : LocallyEqual U (u-w) (v-z) := by
  intro χ hc hχ
  rw [map_sub,map_sub,h χ hc hχ,h' χ hc hχ]

lemma LocallyEqual.fiberMap {U : Set V} {u v : 𝓢'(V,C 6)}
    (h : LocallyEqual U u v) (M : C 6 →L[ℂ] C 6) :
    LocallyEqual U (fiberMap M u) (fiberMap M v) := by
  intro χ hc hχ
  rw [← fiberMap_product,← fiberMap_product,h χ hc hχ]

lemma normalizedFullSquare_power_local_congr
    (a : Fin 4 → 𝓢(V,R 6 →L[ℝ] R m)) (b : 𝓢(V,R 6 →L[ℝ] R m))
    (ρ : 𝓢(V,ℝ)) (θ : 𝓢(V,ℂ)) (G : Fin 4 → Fin 4 → V → ℝ)
    (hG : ∀ i j x, (ρ x • a i x).adjoint ∘L a j x + (ρ x • a j x).adjoint ∘L a i x =
      (2*G i j x) • ContinuousLinearMap.id ℝ (R 6))
    {U : Set V} (hU : IsOpen U) (k : ℕ) {u v : 𝓢'(V,C 6)} (huv : LocallyEqual U u v) :
    LocallyEqual U (((normalizedFullSquare a b ρ θ)^k) u) (((normalizedFullSquare a b ρ θ)^k) v) := by
  induction k with
  | zero => simpa using huv
  | succ k ih =>
    rw [pow_succ',mul_apply_eq_comp,mul_apply_eq_comp]
    exact normalizedFullSquare_local_congr a b ρ θ G hG hU ih

lemma triple_product_cancel (χ θ ρ : 𝓢(V,ℂ))
    (h : ∀ z ∈ tsupport χ, θ z * ρ z = 1) (u : 𝓢'(V,C 6)) :
    smulLeftCLM (C 6) χ (smulLeftCLM (C 6) θ (smulLeftCLM (C 6) ρ u)) =
      smulLeftCLM (C 6) χ u := by
  rw [smulLeftCLM_smulLeftCLM_apply ρ.hasTemperateGrowth θ.hasTemperateGrowth,
    smulLeftCLM_smulLeftCLM_apply (ρ.hasTemperateGrowth.mul θ.hasTemperateGrowth)
      χ.hasTemperateGrowth]
  have he : ((ρ : V → ℂ) * θ) * χ = (χ : V → ℂ) := by
    ext z
    change (ρ z * θ z) * χ z = χ z
    rw [mul_comm (ρ z) (θ z)]
    by_cases hz : z ∈ tsupport χ
    · rw [h z hz,one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz,mul_zero]
  rw [he]
end TamingCompatibility.ComplexMatrix

end
end

section
noncomputable section
namespace TamingCompatibility
open scoped SchwartzMap
namespace ComplexMatrix

def antiMatrix : C 6 →L[ℂ] C 6 :=
  (1/2:ℂ) • (ContinuousLinearMap.id ℂ _ -
    (unit 6 6 0 0 + unit 6 6 1 4 - unit 6 6 2 3 - unit 6 6 3 2 + unit 6 6 4 1 + unit 6 6 5 5))

lemma antiMatrix_embed (v : R 6) :
    antiMatrix (embed 6 v) = embed 6 (UnitaryFrame.antiInvariantPart v) := by
  ext i
  fin_cases i <;> simp [antiMatrix,unit_apply,UnitaryFrame.antiInvariantPart,
    UnitaryFrame.jAction,embed_apply] <;> ring
end ComplexMatrix

namespace HodgeFrame
open GeometricSymbol UnitaryFrame
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
lemma coordinates_antiInvariant (b : Fin 4 → E) (J : E →L[ℝ] E)
    (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2) (a : MetricForms.Form E 2) :
    coordinates b ((1/2:ℝ) • (a - a.compContinuousLinearMap J)) =
      UnitaryFrame.antiInvariantPart (coordinates b a) := by
  have hc (x y : E) : (⇑J ∘ ![x,y]) = ![J x,J y] := by
    ext i; fin_cases i <;> rfl
  have hs := GeometricSymbol.eval_swap a (b 0) (b 1)
  have ht := GeometricSymbol.eval_swap a (b 2) (b 3)
  ext i
  fin_cases i <;>
    simp [coordinates_apply,UnitaryFrame.antiInvariantPart,UnitaryFrame.jAction,
      FormMetric.pairLeft,FormMetric.pairRight,h0,h1,h2,h3,
      GeometricSymbol.eval_neg_left,GeometricSymbol.eval_neg_right,hs,ht,
      hc]
end HodgeFrame

namespace HodgeChart
open ManifoldForms ManifoldHodge HodgeFrame GeometricChart ComplexMatrix
open scoped Manifold ContDiff
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
variable (J : AlmostComplexStructure X) (α : TwoForm X)
  (ht : Tames α J) (p : X) (D : GeometricChart.Data J α ht p)

lemma rawVector_antiInvariantPart (a : TwoForm X) {z : Space} (hz : z ∈ D.domain) :
    rawVector J α ht p D (antiInvariantPart J a) z =
      UnitaryFrame.antiInvariantPart (rawVector J α ht p D a z) := by
  unfold rawVector
  rw [pullback_antiInvariantPart J a p (D.domain_subset hz)]
  obtain ⟨h0,h1,h2,h3⟩ := D.frame_complex z hz
  exact coordinates_antiInvariant (fun i => D.frame i z) (coordinateJ J p z) h0 h1 h2 h3 _

lemma complex_rawVector_antiInvariantPart (a : TwoForm X) {z : Space} (hz : z ∈ D.domain) :
    embed 6 (rawVector J α ht p D (antiInvariantPart J a) z) =
      antiMatrix (embed 6 (rawVector J α ht p D a z)) := by
  rw [rawVector_antiInvariantPart J α ht p D a hz,antiMatrix_embed]
end HodgeChart
end TamingCompatibility

end
end

end
end

end OAI
