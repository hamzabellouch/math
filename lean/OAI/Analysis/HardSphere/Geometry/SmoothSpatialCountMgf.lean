import Mathlib
import OAI.Analysis.HardSphere.Geometry.ExpWeightedMultiplier

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
open MeasureTheory Set Filter ProbabilityTheory
open scoped ComplexConjugate

lemma smooth_spatial_count_mgf : ∃ C αstar : ℝ, 0 < C ∧ 0 < αstar ∧
    ∀ (n K : ℕ) (L : Length) (_hL : L.val=(K:ℝ)) (r D : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → 0<r → 1≤L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)), A.Nonempty → ∀ t∈Icc 0 (Real.exp 1),
      cgf (smoothWeightedCount L A) (groundPositionLaw n L g) t≤C*D*(A.card:ℝ)*t := by
  obtain ⟨C,hC,hp⟩ := weighted_count_penalty
  let e : ℝ := Real.exp 1
  let em : ℝ := Real.exp (-1)
  let H : ℝ := 3*(spatialMetricConstant:ℝ)^2*Real.exp 1
  let αstar : ℝ := 1+2*e^3*H
  have he : 0<e := Real.exp_pos _
  have hem : 0<em := Real.exp_pos _
  have hH : 0≤H := by dsimp [H]; positivity
  have hαstar : 0<αstar := by dsimp [αstar]; positivity
  have heem : e*em=1 := exp_one_mul_exp_neg_one
  have he3 : e^3*em=e^2 := by calc
    _ = e^2*(e*em) := by ring
    _ = e^2 := by rw [heem,mul_one]
  refine ⟨2*e*C,αstar,by positivity,hαstar,?_⟩
  intro n K L hL r D hDeq hD hα hr hsize hsmall g hg A hA
  let := groundPositionLaw_probability g hg.2.2.1
  have hα1 : 1≤D*r := by
    have h0 : 0≤2*e^3*H := by positivity
    dsimp [αstar] at hα
    linarith only [h0,hα]
  have hαpos : 0<D*r := zero_lt_one.trans_le hα1
  have hbG (X : Configuration n L) : |smoothWeightedCount L A X| ≤ e*(n:ℝ) := by
    rw [abs_of_nonneg (smoothWeightedCount_nonneg L A X)]
    exact smoothWeightedCount_le L A X
  apply bounded_cgf_le (groundPositionLaw n L g) (smoothWeightedCount_continuous L A).measurable hbG he.le
  intro t ht
  let f := expWeightedMultiplier n L A t
  let M := mgf (smoothWeightedCount L A) (groundPositionLaw n L g) t
  let R := ∫ X, smoothWeightedCount L A X*Real.exp (t*smoothWeightedCount L A X) ∂groundPositionLaw n L g
  have hR : 0≤R := integral_nonneg (fun X ↦ mul_nonneg (smoothWeightedCount_nonneg L A X) (Real.exp_pos _).le)
  have hpen := hp n K L hL r D hDeq hD hα1 hr hsize hsmall g hg A (f.onJet g) (f.onJet_mem_domain hg.1)
  have hlow := expWeightedMultiplier_weight_lower A hA t g
  have hdef := expWeightedMultiplier_defect A t hg
  change energy (f.onJet g)-energy g*‖f.onScalar g.1‖^2≤t^2/4*H*R at hdef
  change em*R≤∫ X, weightedSiteCount L A X*‖(f.onScalar g.1) X‖^2 at hlow
  change (D*r)*((∫ X, weightedSiteCount L A X*‖(f.onScalar g.1) X‖^2)-C*D*(A.card:ℝ)*‖f.onScalar g.1‖^2)≤
    energy (f.onJet g)-energy g*‖f.onScalar g.1‖^2 at hpen
  rw [show ‖f.onScalar g.1‖^2=M from expWeightedMultiplier_mass A t g] at hpen hdef
  have hbound : (D*r)*(em*R-C*D*(A.card:ℝ)*M)≤(t^2/4*H)*R := by
    have h := mul_le_mul_of_nonneg_left hlow hαpos.le
    nlinarith only [h,hpen,hdef]
  have ht2 : t^2≤e^2 := (sq_le_sq₀ ht.1 he.le).mpr ht.2
  have hαH : 2*e^3*H≤D*r := by
    dsimp [αstar] at hα
    linarith only [hα]
  have hαHem := mul_le_mul_of_nonneg_right hαH hem.le
  have heq : (2*e^3*H)*em=2*e^2*H := by
    calc
      _ = 2*H*(e^3*em) := by ring
      _ = _ := by rw [he3]; ring
  rw [heq] at hαHem
  have hc : t^2/4*H≤(D*r)*em/2 := by
    have htH := mul_le_mul_of_nonneg_right ht2 hH
    have hn : 0≤e^2*H := mul_nonneg (sq_nonneg _) hH
    nlinarith only [htH,hαHem,hn]
  have hmul := mul_le_mul_of_nonneg_right hc hR
  have hRbound : em*R≤2*(C*D*(A.card:ℝ))*M := by
    apply (mul_le_mul_iff_right₀ hαpos).mp
    nlinarith only [hbound,hmul]
  have h := mul_le_mul_of_nonneg_left hRbound he.le
  rw [←mul_assoc e em R,heem,one_mul] at h
  change R≤(2*e*C)*D*(A.card:ℝ)*M
  exact h.trans_eq (by ring)

theorem spatial_count_mgf : ∃ C αstar : ℝ, 0 < C ∧ 0 < αstar ∧
    ∀ (n K : ℕ) (L : Length) (_hL : L.val=(K:ℝ)) (r D : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → 0<r → 1≤L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)) (z : ℝ), 0≤z → z≤1 →
      Real.log (∫ X, Real.exp (z*weightedSiteCount L A X) ∂groundPositionLaw n L g)≤
        C*z*D*(A.card:ℝ) := by
  obtain ⟨C,αstar,hC,hαstar,hmgf⟩ := smooth_spatial_count_mgf
  refine ⟨C*Real.exp 1,αstar,by positivity,hαstar,?_⟩
  intro n K L hL r D hDeq hD hα hr hsize hsmall g hg A z hz hz'
  let := groundPositionLaw_probability g hg.2.2.1
  by_cases hA : A.Nonempty
  · have hbF (X : Configuration n L) : |weightedSiteCount L A X| ≤ (n:ℝ) := by
      rw [abs_of_nonneg (weightedSiteCount_nonneg L A X)]
      exact weightedSiteCount_le L A X
    have hbG (X : Configuration n L) : |smoothWeightedCount L A X| ≤ Real.exp 1*(n:ℝ) := by
      rw [abs_of_nonneg (smoothWeightedCount_nonneg L A X)]
      exact smoothWeightedCount_le L A X
    have hiF := bounded_mgf_integrable (groundPositionLaw n L g) (weightedSiteCount_continuous L A).measurable hbF z
    have hiG := bounded_mgf_integrable (groundPositionLaw n L g) (smoothWeightedCount_continuous L A).measurable hbG (Real.exp 1*z)
    have hlog : Real.log (∫ X, Real.exp (z*weightedSiteCount L A X) ∂groundPositionLaw n L g)≤
        cgf (smoothWeightedCount L A) (groundPositionLaw n L g) (Real.exp 1*z) := by
      apply Real.log_le_log (mgf_pos hiF)
      apply integral_mono hiF hiG
      intro X
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left (weightedSiteCount_le_smooth L A hA X) hz
      exact h.trans_eq (by ring)
    apply hlog.trans
    have ht : Real.exp 1*z∈Icc 0 (Real.exp 1) := ⟨mul_nonneg (Real.exp_pos _).le hz,
      by simpa using mul_le_mul_of_nonneg_left hz' (Real.exp_pos 1).le⟩
    exact (hmgf n K L hL r D hDeq hD hα hr hsize hsmall g hg A hA (Real.exp 1*z) ht).trans_eq (by ring)
  · have he : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    simp [weightedSiteCount]

end HardSphere

end

end OAI
