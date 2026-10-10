import Mathlib
import OAI.Analysis.HardSphere.Geometry.SpatialScalarSquare

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
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

theorem weighted_local_penalty : ∃ C c : ℝ, 0< C ∧ 0< c ∧
    ∀ (n K : ℕ) (L : Length) ( _hL : L.val=(K:ℝ)) (r s D : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤ D → 1≤ D*r → 0< r → 0< s → 2*s≤1 → 10*s≤ L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤ L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)), A.Nonempty → ∀ (u : Jet n L), u∈dirichletDomain n L r →
      (D*r)*((∫ X, weightedSiteCount L A X*‖u.1 X‖^2)-C*D*(A.card:ℝ)*‖u.1‖^2)+
        c*r/s^3*(∫ X, ((localizedNearLabels L A s X).card:ℝ)*‖u.1 X‖^2)≤ energy u-energy g*‖u.1‖^2 := by
  obtain ⟨P,R,hP,hR,hbefore⟩ := spatial_before_square
  let a : ℝ := Real.exp (-1)/(128*Real.sqrt 3)
  let c : ℝ := Real.exp (-8)*(27/(524288*Real.sqrt 3))
  have ha : 0< a := by dsimp [a]; positivity
  have hc : 0< c := by dsimp [c]; positivity
  have hM : 0< P+R+1 := by linarith only [hP,hR]
  obtain ⟨B,hB,hcount⟩ := weighted_count_coercivity_integral a (P+R+1) ha hM
  refine ⟨B,c,hB,hc,?_⟩
  intro n K L hL r s D hDeq hD hα hr hs hs' hsL hsmall g hg A hA u hu
  let α := D*r
  let F := ∫ X, weightedSiteCount L A X*‖u.1 X‖^2
  let Q := ∫ X, weightedUnitPairCount hL A X*‖u.1 X‖^2
  let T := ∫ X, ((localizedNearLabels L A s X).card:ℝ)*‖u.1 X‖^2
  let Z := B*D*(A.card:ℝ)*‖u.1‖^2
  have hF : 0≤ F := integral_nonneg (fun X ↦ mul_nonneg (weightedSiteCount_nonneg L A X) (sq_nonneg _))
  have hαpos : 0<α := zero_lt_one.trans_le hα
  have hDpos : 0< D := zero_lt_one.trans_le hD
  have hmul : α*(a/D)=a*r := by dsimp [α]; field_simp
  have hdensity : P*(n:ℝ)*r/L.val^3=P*α := by dsimp [α]; rw [hDeq]; ring
  have hb := hbefore n K L hL r s hr hs hs' hsL hsmall g hg A hA u hu
  rw [hdensity] at hb
  change a*r*Q+c*r/s^3*T-(P*α+R)*F≤ energy u-energy g*‖u.1‖^2 at hb
  have hq := mul_le_mul_of_nonneg_left (hcount n K L hL A hA D hD u.1) hαpos.le
  change α*((P+R+1)*F)≤α*(a/D*Q+Z) at hq
  rw [mul_add,←mul_assoc α (a/D),hmul] at hq
  have he := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα hR.le) hF
  dsimp [α,Z] at hq hb he ⊢
  nlinarith only [hq,hb,he]

def spatialCloseScale (D b : ℝ) : ℝ := b*D^(-(1/3:ℝ))

lemma spatialCloseScale_pos {D b : ℝ} (hD : 0< D) (hb : 0< b) : 0< spatialCloseScale D b :=
  mul_pos hb (Real.rpow_pos_of_pos hD _)

lemma spatialCloseScale_cube {D b : ℝ} (hD : 0< D) : D*(spatialCloseScale D b)^3=b^3 := by
  unfold spatialCloseScale
  rw [mul_pow,←Real.rpow_mul_natCast hD.le]
  norm_num
  rw [Real.rpow_neg_one]
  field_simp

theorem spatial_localized_form : ∃ C c : ℝ, 0< C ∧ 0< c ∧
    ∀ (n K : ℕ) (L : Length) ( _hL : L.val=(K:ℝ)) (r b D : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤ D → 1≤ D*r → 0< r → 0< b →
      2*spatialCloseScale D b≤1 → 10*spatialCloseScale D b≤ L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤ L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)) (u : Jet n L), u∈dirichletDomain n L r →
      (D*r)*(∫ X, (weightedSiteCount L A X-C*D*(A.card:ℝ)+
        c/b^3*((localizedNearLabels L A (spatialCloseScale D b) X).card:ℝ))*‖u.1 X‖^2)≤
        energy u-energy g*‖u.1‖^2 := by
  obtain ⟨C,c,hC,hc,hbound⟩ := weighted_local_penalty
  refine ⟨C,c,hC,hc,?_⟩
  intro n K L hL r b D hDeq hD hα hr hb hs' hsL hsmall g hg A u hu
  by_cases hA : A.Nonempty
  · have hDpos : 0< D := zero_lt_one.trans_le hD
    have hs := spatialCloseScale_pos hDpos hb
    have h := hbound n K L hL r (spatialCloseScale D b) D hDeq hD hα hr hs hs' hsL hsmall g hg A hA u hu
    have hf := weightedSiteCount_integrable L A u.1
    have hk := localizedNearLabels_integrable L A (spatialCloseScale D b) u.1
    have hn : Integrable (fun X ↦ ‖u.1 X‖^2) volume := (Lp.memLp u.1).integrable_norm_pow (by norm_num)
    have hsub : Integrable (fun X ↦ weightedSiteCount L A X*‖u.1 X‖^2-(C*D*(A.card:ℝ))*‖u.1 X‖^2) volume := hf.sub (hn.const_mul _)
    have heq : (fun X ↦ (weightedSiteCount L A X-C*D*(A.card:ℝ)+c/b^3*((localizedNearLabels L A (spatialCloseScale D b) X).card:ℝ))*‖u.1 X‖^2)=
        fun X ↦ (weightedSiteCount L A X*‖u.1 X‖^2-(C*D*(A.card:ℝ))*‖u.1 X‖^2)+c/b^3*(((localizedNearLabels L A (spatialCloseScale D b) X).card:ℝ)*‖u.1 X‖^2) := by funext X; ring
    rw [heq,integral_add hsub (hk.const_mul _),integral_sub hf (hn.const_mul _),
      integral_const_mul,integral_const_mul,←IndicatorStrong.norm_sq_integral]
    have he : (D*r)*(c/b^3)=c*r/(spatialCloseScale D b)^3 := by
      rw [←spatialCloseScale_cube (b:=b) hDpos]
      field_simp
    rw [mul_add,←mul_assoc (D*r) (c/b^3),he]
    exact h
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    have hz (X : Configuration n L) : localizedNearLabels L ∅ (spatialCloseScale D b) X=∅ := by
      classical
      simp [localizedNearLabels]
    simp only [weightedSiteCount,Finset.not_nonempty_empty,ite_false,Finset.card_empty,Nat.cast_zero,
      mul_zero,sub_zero,hz,add_zero,zero_mul,integral_zero]
    exact sub_nonneg.mpr (hg.rayleigh_all u hu)

end HardSphere

end

end OAI
