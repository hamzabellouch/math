import Mathlib
import OAI.Probability.SKRatio.Matrices.PlantedSquares

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory Filter Set Real
namespace SKRatio.Planted
open SKRatioClock.Regression MatrixNet
attribute [local instance] Classical.propDecidable

lemma affine_coordinates_max_rare (β : ℝ) {u : ℝ} (hu : 0<u)
    (I : ℕ → Type) [∀ n, Fintype (I n)] {D : ℝ} (hD : 0<D) (k : ℕ)
    (hcard : ∀ᶠ n in atTop, (Fintype.card (I n):ℝ) ≤ D*(n:ℝ)^k) :
    ExponentiallyRare (fun n => standardArrayLaw (I n))
      (fun n => {z | ∃ i, u < |β/sqrt n*z i+β^2/(n:ℝ)|}) := by
  by_cases hβ : β=0
  · apply (exponentiallyRare_empty (fun n => standardArrayLaw (I n))).mono
    refine Eventually.of_forall ?_
    intro n z hz
    obtain ⟨i,hi⟩ := hz
    simp [hβ] at hi
    linarith
  have hβ2 : 0<β^2 := sq_pos_of_ne_zero hβ
  have hc : 0<u^2/(8*β^2) := by positivity
  have ht := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (β^2)
  have he : ∀ᶠ n in atTop, ∀ i : I n,
      standardArrayLaw (I n) {z | u < |β/sqrt n*z i+β^2/(n:ℝ)|} ≤
        ENNReal.ofReal (2*exp (-(u^2/(8*β^2))*n)) := by
    filter_upwards [eventually_ge_atTop 1,
      ht.eventually (gt_mem_nhds (by linarith : (0:ℝ)<u/2))] with n hn hm i
    have hn0 : 0<n := lt_of_lt_of_le (by norm_num) hn
    have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn0
    have hsn : sqrt (n:ℝ)≠0 := (sqrt_pos.mpr hnr).ne'
    have hbpos : 0 < |β| := abs_pos.mpr hβ
    have hs := subgaussian_abs_tail
      (gaussian_hasSubgaussianMGF (coordinate_hasLaw i))
      (u*sqrt n/(2*|β|)) (by positivity)
    have hex : -(u*sqrt n/(2*|β|))^2/(2*(1:ℝ)) = -(u^2/(8*β^2))*(n:ℝ) := by
      simp only [div_pow,mul_pow,sq_sqrt hnr.le,sq_abs]
      field_simp
      ring
    simp only [NNReal.coe_one,hex] at hs
    rw [←ENNReal.ofReal_ofNat 2,←ENNReal.ofReal_mul (by norm_num)] at hs
    refine (measure_mono (show {z : I n → ℝ | u < |β/sqrt n*z i+β^2/(n:ℝ)|} ⊆
      {z : I n → ℝ | u*sqrt n/(2*|β|) ≤ |z i|} from ?_)).trans hs
    intro z hz
    change u < |β/sqrt n*z i+β^2/(n:ℝ)| at hz
    have hb := abs_add_le (β/sqrt n*z i) (β^2/(n:ℝ))
    rw [abs_of_nonneg (by positivity : 0≤β^2/(n:ℝ)),abs_mul,abs_div,
      abs_of_nonneg (sqrt_nonneg _)] at hb
    have hi : u/2 ≤ |β|/sqrt n*|z i| := by
      linarith
    apply (div_le_iff₀ (by positivity : 0<2*|β|)).mpr
    have hii := (le_div_iff₀ (sqrt_pos.mpr hnr)).mp
      (show u/2 ≤ |β| *|z i|/sqrt n by simpa only [div_mul_eq_mul_div] using hi)
    nlinarith only [hii]
  have hr := exponentiallyRare_iUnion_polynomial (fun n => standardArrayLaw (I n))
    (fun n i => {z | u < |β/sqrt n*z i+β^2/(n:ℝ)|}) hc
    (by norm_num : (0:ℝ)<2) hD k hcard he
  apply hr.mono
  exact Eventually.of_forall (fun n z hz => mem_iUnion.mpr hz)

lemma affine_max_entry_rare (β : ℝ) {u : ℝ} (hu : 0<u) :
    ExponentiallyRare (fun n => standardArrayLaw (Edge n))
      (fun n => {z | ∃ e : Edge n, u < |affineDisorder β z e|}) := by
  apply affine_coordinates_max_rare β hu (Edge) (D := 1) (by norm_num) 2
  refine Eventually.of_forall ?_
  intro n
  have hc := Fintype.card_subtype_le (fun e : Fin n × Fin n => e.1<e.2)
  have hh : Fintype.card (Edge n)≤n*n := by simpa [Edge] using hc
  have hreal : (Fintype.card (Edge n):ℝ) ≤ (n:ℝ)*(n:ℝ) := by exact_mod_cast hh
  simpa only [one_mul,pow_two] using hreal

end SKRatio.Planted

end
end

end OAI
