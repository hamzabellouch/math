import Mathlib
import OAI.Probability.Ballisticity.Walk.FixedQuenchedKernel

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

theorem strip_templates {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ b a D ε : ℝ, 0 ≤ b  ∧  1 ≤ a  ∧  0 ≤ D  ∧  0 < ε  ∧  ε ≤ 1  ∧
      ∀ H : ℝ, ∃ A : Set (Path d), MeasurableSet A  ∧  ε ≤ (annealedLaw ν).real A  ∧
        ∀ u Z, Z ∈ A  →  ∀ k,
          (0 ≤ tiltedCoordinate (realPosition (step e)) u b a (Z k)  ∧
            signedCoordinate u (Z k) ≤ a*D*(1+dot (realPosition (Z k)) (realPosition (step e)))) ∨
          H < dot (realPosition (Z k)) (realPosition (step e)) := by
  let ℓ := realPosition (step e)
  have hℓ := unit_direction_coordinate_bound ℓ (signed_direction_unit e)
  have he : dot (realPosition (step e)) ℓ=1 := signed_direction_unit e
  have hp := noDrop_positive_of_directionallyTransient ν ℓ htrans
  have := conditionedLaw_probability ν ℓ hp.ne'
  obtain ⟨c,C,hc,hC,C0,hheight⟩ := conditioned_height_template ν ℓ hℓ htrans (1/20) (by norm_num)
  norm_num only at hheight
  let M := C0+2
  let b : ℝ := 1+1/c
  have hb : 1 ≤ b := by dsimp only [b]; linarith [one_div_pos.mpr hc]
  have hbc : 1 ≤ b*c := by dsimp only [b]; rw [add_mul,one_mul,one_div_mul_cancel hc.ne']; linarith
  have hMM : (M:ℝ)=(C0:ℝ)+2 := by simp [M]
  have hMpos : (2:ℝ) ≤ M := by rw [hMM]; linarith [Nat.cast_nonneg (α := ℝ) C0]
  let R : Path d  →  ℝ := fun X => wordRadius (firstWord ℓ X)
  have hR := conditioned_wordRadius_integrable ν hue ℓ (signed_direction_unit e) htrans
  let m := ∫ X, R X ∂conditionedLaw ν ℓ
  have hm : 0 ≤  m := integral_nonneg fun X => wordRadius_nonneg _
  let a := max (M:ℝ) (100*(m+1))
  have hMa : (M:ℝ) ≤ a := le_max_left _ _
  have hma : 100*(m+1) ≤ a := le_max_right _ _
  have ha : 1 ≤ a := by linarith
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hIa (K : ℕ) : truncatedMean (conditionedLaw ν ℓ) R (a*K) < 2*(1/100:ℝ)*a := by
    have hi : truncatedMean (conditionedLaw ν ℓ) R (a*K) ≤  m :=
      integral_mono (integrable_min_nonneg _ R
        (measurable_wordRadius.comp (measurable_firstWord ℓ)) (fun X => wordRadius_nonneg _) _ (by positivity))
        hR (fun _ => min_le_left _ _)
    linarith
  let D : ℝ := (M:ℝ)+1+1/c
  have hD : (M:ℝ)+1 ≤ D := by dsimp only [D]; linarith [one_div_pos.mpr hc]
  have hDc : 1 ≤ D*c := by
    dsimp only [D]
    rw [add_mul,one_div_mul_cancel hc.ne']
    have := mul_nonneg (show 0 ≤ (M:ℝ)+1 by positivity) hc.le
    linarith
  obtain ⟨κ,hκ,hrows⟩ := environment_uniform_elliptic ν hue
  let ε : ℝ := (κ:ℝ)^M*(annealedLaw ν).real (NoDrop ℓ 0)*(4/5)
  have hε : 0 < ε := by
    exact mul_pos (mul_pos (pow_pos (NNReal.coe_pos.mpr hκ) M)
      (ENNReal.toReal_pos hp.ne' (measure_ne_top _ _))) (by norm_num)
  have hA (H : ℝ) : ∃ A : Set (Path d), MeasurableSet A  ∧  ε ≤ (annealedLaw ν).real A  ∧
      ∀ u Z, Z ∈ A  →  ∀ k, (0 ≤ tiltedCoordinate ℓ u b a (Z k)  ∧
        signedCoordinate u (Z k) ≤ a*D*(1+dot (realPosition (Z k)) ℓ)) ∨ H < dot (realPosition (Z k)) ℓ := by
    obtain ⟨K,hK⟩ := exists_nat_gt ((H+(C0:ℝ))/c)
    have hK' := (div_lt_iff₀ hc).mp hK
    have hg : (4/5:ℝ) ≤ (conditionedLaw ν ℓ).real (WordTemplate ℓ c C C0 a K) := by
      have h := controlled_template_probability ν ℓ htrans c C C0 (1/100) a ha0 1 K (by norm_num)
        hheight (by norm_num) (hIa K)
      simpa only [one_mul] using h.le
    refine ⟨ForwardTemplate ℓ e c C C0 a K M,measurableSet_forwardTemplate ℓ e c C C0 a K M,
      forwardTemplate_probability_lower ν ℓ htrans e (by rw [he]; norm_num) c C C0 a K M κ hrows hg,?_⟩
    intro u Z hZ k
    apply (forwardTemplate_control ℓ u e c C C0 a b D H K M ha (by linarith) (by rw [he]; norm_num)
      hbc ?_ ?_ ?_ hD hDc ?_ hZ k).2
    · rw [he,mul_one,hMM]; linarith
    · rw [he,mul_one,hMM]
      have hba : a ≤ a*(2*b-1) := by nlinarith
      nlinarith
    · have hstep : -1 ≤ signedCoordinate u (step e) := by
        have h := signedCoordinate_abs_le_norm u (step e)
        rw [latticeVector_step_norm] at h
        exact (abs_le.mp h).1
      dsimp only [tiltedCoordinate]
      rw [he,mul_one]
      nlinarith
    · rw [he,mul_one]; linarith
  have hε1 : ε ≤ 1 := by
    obtain ⟨A,_,hA,_⟩ := hA 0
    exact hA.trans measureReal_le_one
  exact ⟨b,a,D,ε,by linarith,ha,by linarith,hε,hε1,hA⟩

end DirectionalTransience

end

end OAI
