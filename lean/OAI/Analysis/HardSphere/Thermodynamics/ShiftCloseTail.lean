import Mathlib
import OAI.Analysis.HardSphere.Geometry.ShiftClose
import OAI.Analysis.HardSphere.Operators.Stationary

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere
open Wiener
theorem spatial_translated_scaled_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (r D : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → 1≤D → 1≤D*r → 0<r →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
      (Gθ/b^2)*D^(-(4/3):ℝ)≤1 →
    ∀ (g : Jet n L), IsGroundVector n L r g → ∀ (z : Torus L) (A : Finset (CubeCell K)),
      groundPositionLaw n L g {X | ∀ v∈A, θ*D≤((localCloseLabels L (spatialCloseScale D b) (unitCenter L v+z) X).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card)) := by
  obtain ⟨Q,hQ,C,c,G,hC,hc,hG,hgrid⟩ := spatial_translated_grid_close_probability
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,hb,hb1,hcoef⟩ := exists_close_scale hC hc hθ
  let Gθ : ℝ := 8*G/θ
  have hGθ : 0<Gθ := by dsimp [Gθ]; positivity
  refine ⟨b,Gθ,hb,hb1,hGθ,?_⟩
  intro n K _ L hL r D hL100 hDeq hD hα hr hsmall hbase g hg z A
  have hDpos : 0<D := zero_lt_one.trans_le hD
  have hs := spatialCloseScale_pos hDpos hb
  have hsb := (spatialCloseScale_le hD hb.le).trans hb1
  have hh : 0<θ*D/8 := by positivity
  have hcD : (C+1)*D≤c/b^3*((θ*D/8)/4) := by
    have hmul := mul_le_mul_of_nonneg_right hcoef hDpos.le
    have he : (c/b^3*(θ/32))*D=c/b^3*((θ*D/8)/4) := by ring
    rwa [he] at hmul
  have hq := spatial_close_base_bound hG.le hθ hDpos hb hα
  have hp := hgrid n K L hL r b D (θ*D/8) hDeq hD hα hr hb hh
    (by linarith only [hsb]) (by linarith only [hsb,hL100]) hsmall hcD (hq.trans hbase) g hg z A
  have ht : 8*(θ*D/8)=θ*D := by ring
  simp only [ht,Real.rpow_eq_pow] at hp
  apply hp.trans
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _)
  apply Real.rpow_le_rpow (by positivity) hq
  positivity

theorem spatial_translated_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g → ∀ (z : Torus L) (A : Finset (CubeCell K)),
      groundPositionLaw n L g {X | ∀ v∈A, θ*D≤((localCloseLabels L (spatialCloseScale D b) (unitCenter L v+z) X).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card)) := by
  obtain ⟨Q,hQ,htail⟩ := spatial_translated_scaled_close_tail
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
  intro n K _ L hL D α hL100 hDeq hD₀ hα hαmax g hg z A
  have hD : 1≤D := (le_max_left _ _).trans hD₀
  have hD1 : D₁≤D := (le_max_left _ _).trans ((le_max_right _ _).trans hD₀)
  have hlarge : 2*(2*Real.pi*αmax)^3≤D := (le_max_right _ _).trans ((le_max_right _ _).trans hD₀)
  have hDpos : 0<D := zero_lt_one.trans_le hD
  have hαpos : 0<α := zero_lt_one.trans_le hα
  have hprod : D*(α/D)=α := by field_simp
  exact hfin n K L hL (α/D) D hL100 hDeq hD (by rwa [hprod]) (by positivity)
    (smallness_of_large_density L hDeq hD hαpos.le hαmax hlarge) (hD₁ D hD1).le g hg z A

theorem spatial_translated_stationary_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ (T : ℝ), 0≤T → ∀ (q : Time) (z : Torus L) (A : Finset (CubeCell K)),
      groundPathLaw n L (α/D) T g {ω | ∀ v∈A,
        θ*D≤((localCloseLabels L (spatialCloseScale D b) (unitCenter L v+z) (ω q)).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card)) := by
  obtain ⟨Q,hQ,htail⟩ := spatial_translated_close_tail
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,Gθ,hb,hb1,hGθ,hlim,hfin⟩ := htail θ hθ
  refine ⟨b,Gθ,hb,hb1,hGθ,hlim,?_⟩
  intro αmax
  obtain ⟨D₀,hD₀,hDfin⟩ := hfin αmax
  refine ⟨D₀,hD₀,?_⟩
  intro n K inst L hL D α hL100 hDeq hD hα hαmax g hg T hT q z A
  simp only [localCloseLabels_eq_pairCloseLabels]
  rw [hg.groundPathLaw_close_event L T hT q (fun v ↦ unitCenter L v+z) A]
  simpa only [localCloseLabels_eq_pairCloseLabels] using
    hDfin n K L hL D α hL100 hDeq hD hα hαmax g hg z A

end HardSphere

end
end

end

end OAI
