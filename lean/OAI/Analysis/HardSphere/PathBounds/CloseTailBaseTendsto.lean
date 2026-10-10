import Mathlib
import OAI.Analysis.HardSphere.Thermodynamics.SpatialCloseScale2

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology

lemma closeTailBase_tendsto_zero (G b : ℝ) :
    Tendsto (fun D : ℝ ↦ (G/b^2)*D^(-(4/3):ℝ)) atTop (𝓝 0) := by
  simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<4/3)).const_mul (G/b^2)

lemma closeTailProbability_tendsto_zero (G b : ℝ) {Q : ℕ} (hQ : 0<Q) :
    Tendsto (fun D : ℝ ↦ ((G/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) := by
  have hQpos : (0:ℝ)<Q := by exact_mod_cast hQ
  have he : (0:ℝ)<1/(Q:ℝ) := by positivity
  have hc := (Real.continuous_rpow_const he.le).continuousAt.tendsto.comp (closeTailBase_tendsto_zero G b)
  simpa only [Function.comp_def,Real.zero_rpow he.ne'] using hc

lemma smallness_of_large_density {n : ℕ} (L : Length) {D α αmax : ℝ}
    (hDeq : D=(n:ℝ)/L.val^3) (hD : 1≤D) (hα : 0≤α) (hαmax : α≤αmax)
    (hlarge : 2*(2*Real.pi*αmax)^3≤D) :
    (n:ℝ)*(2*Real.pi*(α/D))^3≤L.val^3/2 := by
  have hDpos : 0<D := zero_lt_one.trans_le hD
  have hL3 : 0<L.val^3 := pow_pos L.property _
  have hn : (n:ℝ)=D*L.val^3 := ((eq_div_iff hL3.ne').mp hDeq).symm
  have halpha : (2*Real.pi*α)^3≤(2*Real.pi*αmax)^3 := by gcongr
  have hDsq : D≤D^2 := by nlinarith only [mul_le_mul_of_nonneg_left hD hDpos.le]
  have hratio : (2*Real.pi*α)^3/D^2≤1/2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hDpos)).mpr
    nlinarith only [halpha,hlarge,hDsq]
  calc
    _ = L.val^3*((2*Real.pi*α)^3/D^2) := by rw [hn]; field_simp
    _ ≤ L.val^3*(1/2) := mul_le_mul_of_nonneg_left hratio hL3.le
    _ = _ := by ring

theorem spatial_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g → ∀ A : Finset (CubeCell K),
      groundPositionLaw n L g {X | ∀ v∈A, θ*D≤((localCloseLabels L (spatialCloseScale D b) (unitCenter L v) X).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card)) := by
  obtain ⟨Q,hQ,htail⟩ := spatial_scaled_close_tail
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,Gθ,hb,hb1,hGθ,hfin⟩ := htail θ hθ
  refine ⟨b,Gθ,hb,hb1,hGθ,closeTailProbability_tendsto_zero Gθ b hQ,?_⟩
  intro αmax
  have hev : ∀ᶠ D : ℝ in atTop, (Gθ/b^2)*D^(-(4/3):ℝ)<1 :=
    (tendsto_order.1 (closeTailBase_tendsto_zero Gθ b)).2 1 zero_lt_one
  obtain ⟨D₁,hD₁⟩ := eventually_atTop.1 hev
  let D₀ : ℝ := max 1 (max D₁ (2*(2*Real.pi*αmax)^3))
  refine ⟨D₀,le_max_left _ _,?_⟩
  intro n K _ L hL D α hL100 hDeq hD₀ hα hαmax g hg A
  have hD : 1≤D := (le_max_left _ _).trans hD₀
  have hD1 : D₁≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD₀)
  have hlarge : 2*(2*Real.pi*αmax)^3≤D := (le_max_right _ _).trans ((le_max_right _ _).trans hD₀)
  have hDpos : 0<D := zero_lt_one.trans_le hD
  have hαpos : 0<α := zero_lt_one.trans_le hα
  have hprod : D*(α/D)=α := by field_simp
  exact hfin n K L hL (α/D) D hL100 hDeq hD (by rwa [hprod]) (by positivity)
    (smallness_of_large_density L hDeq hD hαpos.le hαmax hlarge) (hD₁ D hD1).le g hg A

end HardSphere

end

end OAI
