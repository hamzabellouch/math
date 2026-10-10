import Mathlib
import OAI.Analysis.HardSphere.PathBounds.LatticeExponentialSum
import OAI.Analysis.HardSphere.Conditioning.WeightedUnitPairCount

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

lemma spatial_scalar_square {c M D m : ℝ} (hc : 0< c) (hD : 1≤ D) (hm : 0≤ m) :
    M*m ≤ c/D*(m*(m-1))+(c+M)^2/(4*c)*D := by
  have hDpos : 0< D := zero_lt_one.trans_le hD
  have hd : c/D≤ c := (div_le_iff₀ hDpos).mpr (by nlinarith only [hc.le,hD])
  have he : c/D*(m-(c+M)*D/(2*c))^2=
      c/D*m^2-(c+M)*m+(c+M)^2/(4*c)*D := by
    field_simp
    ring
  have hp := mul_nonneg (div_nonneg hc.le hDpos.le) (sq_nonneg (m-(c+M)*D/(2*c)))
  rw [he] at hp
  have hh := mul_le_mul_of_nonneg_right hd hm
  nlinarith only [hp,hh]

lemma weightedSiteCount_integrable {n : ℕ} (L : Length) (A : Finset (Torus L)) (u : ScalarL2 n L) :
    Integrable (fun X ↦ weightedSiteCount L A X*‖u X‖^2) volume :=
  L2_bounded_weight_integrable u (weightedSiteCount_continuous L A).measurable
    (fun X ↦ by rw [abs_of_nonneg (weightedSiteCount_nonneg L A X)]; exact weightedSiteCount_le L A X)

theorem weighted_count_coercivity (c M : ℝ) (hc : 0< c) (hM : 0< M) : ∃ B : ℝ, 0< B ∧
    ∀ (n K : ℕ) (L : Length) (hL : L.val=(K:ℝ)) (A : Finset (Torus L)), A.Nonempty →
    ∀ (D : ℝ), 1≤ D → ∀ (X : Configuration n L),
      M*weightedSiteCount L A X≤ c/D*weightedUnitPairCount hL A X+B*D*(A.card:ℝ) := by
  obtain ⟨Q,hQ,hgrid⟩ := unitGrid_site_exponential_bound
  let e := Real.exp 1
  let V := (c+M*e)^2/(4*c)
  have he : 0< e := Real.exp_pos _
  have hV : 0< V := by dsimp [V]; positivity
  refine ⟨V*Q,mul_pos hV hQ,?_⟩
  intro n K L hL A hA D hD X
  have hp (v : CubeCell K) : 0≤ Real.exp (-spatialSiteDistance L A (unitCenter L v)) := (Real.exp_pos _).le
  have hs := Finset.sum_le_sum (s:=(Finset.univ : Finset (CubeCell K))) (fun v _ ↦
    mul_le_mul_of_nonneg_left (spatial_scalar_square (M:=M*e) hc hD (Nat.cast_nonneg (unitOccupation hL (fun _ ↦ True) v X))) (hp v))
  change (∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))*(M*e*(unitOccupation hL (fun _ ↦ True) v X:ℝ)))≤
    ∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))*(c/D*unitPairCount hL (fun _ ↦ True) v X+V*D) at hs
  have hf := mul_le_mul_of_nonneg_left (weightedSiteCount_le_cell hL A hA X) hM.le
  have hg := mul_le_mul_of_nonneg_left (hgrid K L hL A hA) (mul_nonneg hV.le (zero_le_one.trans hD))
  calc
    _ ≤ M*(e*(∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))*(unitOccupation hL (fun _ ↦ True) v X:ℝ))) := hf
    _ = ∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))*(M*e*(unitOccupation hL (fun _ ↦ True) v X:ℝ)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      ring
    _ ≤ _ := hs
    _ = c/D*weightedUnitPairCount hL A X+V*D*(∑ v : CubeCell K, Real.exp (-spatialSiteDistance L A (unitCenter L v))) := by
      simp only [weightedUnitPairCount,mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro v _ <;> ring
    _ ≤ c/D*weightedUnitPairCount hL A X+(V*Q)*D*(A.card:ℝ) := by
      have heq : V*D*(Q*(A.card:ℝ))=(V*Q)*D*(A.card:ℝ) := by ring
      rw [←heq]
      exact add_le_add le_rfl hg

lemma weighted_count_coercivity_integral (c M : ℝ) (hc : 0< c) (hM : 0< M) : ∃ B : ℝ, 0< B ∧
    ∀ (n K : ℕ) (L : Length) (hL : L.val=(K:ℝ)) (A : Finset (Torus L)), A.Nonempty →
    ∀ (D : ℝ), 1≤ D → ∀ (u : ScalarL2 n L),
      M*(∫ X, weightedSiteCount L A X*‖u X‖^2)≤
        c/D*(∫ X, weightedUnitPairCount hL A X*‖u X‖^2)+B*D*(A.card:ℝ)*‖u‖^2 := by
  obtain ⟨B,hB,hbound⟩ := weighted_count_coercivity c M hc hM
  refine ⟨B,hB,?_⟩
  intro n K L hL A hA D hD u
  have hf := weightedSiteCount_integrable L A u
  have hq := weightedUnitPairCount_integrable hL A u
  have hn : Integrable (fun X ↦ ‖u X‖^2) volume := (Lp.memLp u).integrable_norm_pow (by norm_num)
  have hh := integral_mono ((hf.const_mul M)) ((hq.const_mul (c/D)).add (hn.const_mul (B*D*(A.card:ℝ))))
    (fun X ↦ by have hp := mul_le_mul_of_nonneg_right (hbound n K L hL A hA D hD X) (sq_nonneg ‖u X‖); simpa only [Pi.add_apply,add_mul,mul_assoc] using hp)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hq.const_mul (c/D)) (hn.const_mul _)] at hh
  simp only [integral_const_mul,←IndicatorStrong.norm_sq_integral] at hh
  exact hh

end HardSphere

end

end OAI
