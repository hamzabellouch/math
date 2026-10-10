import Mathlib
import OAI.Analysis.HardSphere.Geometry.SpatialGridCloseProbability

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter
noncomputable section

lemma spatialCloseScale_le {D b : ℝ} (hD : 1≤D) (hb : 0≤b) : spatialCloseScale D b≤b := by
  unfold spatialCloseScale
  calc
    _ ≤ b*1 := mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos hD (by norm_num)) hb
    _ = _ := mul_one _

lemma spatialCloseScale_square {D b : ℝ} (hD : 0<D) :
    (spatialCloseScale D b)^2*D^2=b^2*D^(4/3:ℝ) := by
  unfold spatialCloseScale
  rw [mul_pow,←Real.rpow_mul_natCast hD.le]
  calc
    _ = b^2*(D^((-1/3:ℝ)*2)*D^(2:ℝ)) := by rw [Real.rpow_ofNat]; ring_nf
    _ = b^2*D^(((-1/3:ℝ)*2)+2) := by rw [Real.rpow_add hD]
    _ = _ := by norm_num

lemma spatial_close_base_bound {G θ D b r : ℝ} (hG : 0≤G) (hθ : 0<θ) (hD : 0<D)
    (hb : 0<b) (hα : 1≤D*r) :
    G/((θ*D/8)*(spatialCloseScale D b)^2)/((D*r)*D)≤
      ((8*G/θ)/b^2)*D^(-(4/3):ℝ) := by
  have hs := spatialCloseScale_pos hD hb
  have hden : D≤(D*r)*D := by nlinarith only [mul_le_mul_of_nonneg_right hα hD.le]
  have heq := spatialCloseScale_square (b:=b) hD
  have hrpow : 0<D^(4/3:ℝ) := Real.rpow_pos_of_pos hD _
  have hinv : D^(-(4/3):ℝ)=(D^(4/3:ℝ))⁻¹ := Real.rpow_neg hD.le _
  calc
    _ ≤ G/((θ*D/8)*(spatialCloseScale D b)^2)/D :=
      div_le_div_of_nonneg_left (by positivity) hD hden
    _ = ((8*G/θ)/b^2)*D^(-(4/3):ℝ) := by
      rw [hinv]
      field_simp
      linear_combination -G*heq

end
end HardSphere

namespace HardSphere
open MeasureTheory Set Filter
noncomputable section

lemma exists_close_scale {C c θ : ℝ} (hC : 0<C) (hc : 0<c) (hθ : 0<θ) :
    ∃ b : ℝ, 0<b ∧ b≤1/4 ∧ (C+1)≤c/b^3*(θ/32) := by
  let b := min (1/4) (c*θ/(64*(C+1)))
  have hb : 0<b := lt_min (by norm_num) (by positivity)
  have hb1 : b≤1/4 := min_le_left _ _
  have hbsmall : b*(64*(C+1))≤c*θ := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hpow : b^3≤b := by
    have hb01 : b≤1 := by linarith only [hb1]
    have hsq : b^2≤b := by nlinarith only [mul_le_mul_of_nonneg_left hb01 hb.le]
    nlinarith only [mul_le_mul_of_nonneg_left hsq hb.le,hsq]
  have hcoef : (C+1)*(32*b^3)≤c*θ := by
    have hmul := mul_le_mul_of_nonneg_left hpow (by positivity : 0≤32*(C+1))
    nlinarith only [hmul,hbsmall,mul_nonneg hb.le (by positivity : 0≤C+1)]
  refine ⟨b,hb,hb1,?_⟩
  have he : c/b^3*(θ/32)=c*θ/(32*b^3) := by ring
  rw [he]
  exact (le_div_iff₀ (by positivity)).mpr hcoef

theorem spatial_scaled_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (r D : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → 1≤D → 1≤D*r → 0<r →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
      (Gθ/b^2)*D^(-(4/3):ℝ)≤1 →
    ∀ (g : Jet n L), IsGroundVector n L r g → ∀ A : Finset (CubeCell K),
      groundPositionLaw n L g {X | ∀ v∈A, θ*D≤((localCloseLabels L (spatialCloseScale D b) (unitCenter L v) X).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card)) := by
  obtain ⟨Q,hQ,C,c,G,hC,hc,hG,hgrid⟩ := spatial_grid_close_probability
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,hb,hb1,hcoef⟩ := exists_close_scale hC hc hθ
  let Gθ : ℝ := 8*G/θ
  have hGθ : 0<Gθ := by dsimp [Gθ]; positivity
  refine ⟨b,Gθ,hb,hb1,hGθ,?_⟩
  intro n K _ L hL r D hL100 hDeq hD hα hr hsmall hbase g hg A
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
    (by linarith only [hsb]) (by linarith only [hsb,hL100]) hsmall hcD (hq.trans hbase) g hg A
  have ht : 8*(θ*D/8)=θ*D := by ring
  simp only [ht,Real.rpow_eq_pow] at hp
  apply hp.trans
  apply ENNReal.ofReal_le_ofReal
  apply pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _)
  apply Real.rpow_le_rpow (by positivity) hq
  positivity

end
end HardSphere

end
end
end
end
end
end
end
end

end OAI
