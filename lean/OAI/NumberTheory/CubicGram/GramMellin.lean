import Mathlib
import OAI.NumberTheory.CubicGram.InnerExtension

namespace OAI

/-! Finite-row Mellin estimates and dyadic Gram decay. -/

section

noncomputable section
open scoped BigOperators FourierTransform SchwartzMap ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma finite_row_integral_bound (P : Finset Eisenstein) (K : ℝ → ℂ)
    (F : ℝ → Eisenstein → ℂ) (hK : Integrable K)
    (hF : ∀ a ∈ P, Continuous (fun t => F t a)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t, (∑ a ∈ P, ‖F t a‖^2) ≤ B) :
    (∑ a ∈ P, ‖∫ t : ℝ, K t * F t a‖^2) ≤
      (∫ t : ℝ, ‖K t‖)^2 * B := by
  let V : ℝ → EuclideanSpace ℂ P := fun t => WithLp.toLp 2 (fun a => F t a.val)
  have hV : Continuous V := by
    exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : P => ℂ)).symm.continuous.comp
      (continuous_pi fun a => hF a.val a.property)
  have hv t : ‖V t‖ ≤ Real.sqrt B := by
    have hs := coefficientVector_norm_sq P (F t)
    change ‖V t‖^2 = _ at hs
    nlinarith [hbound t, Real.sq_sqrt hB, _root_.norm_nonneg (V t), Real.sqrt_nonneg B]
  have hI : Integrable (fun t => K t • V t) := by
    apply (hK.norm.mul_const (Real.sqrt B)).mono'
      (hK.aestronglyMeasurable.smul hV.aestronglyMeasurable)
    filter_upwards with t
    change ‖K t • V t‖ ≤ ‖K t‖ * Real.sqrt B
    rw [_root_.norm_smul]
    exact mul_le_mul_of_nonneg_left (hv t) (_root_.norm_nonneg _)
  have hn : ‖∫ t : ℝ, K t • V t‖ ≤ (∫ t : ℝ, ‖K t‖) * Real.sqrt B := by
    calc
      _ ≤ ∫ t : ℝ, ‖K t • V t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, ‖K t‖ * Real.sqrt B := by
        apply integral_mono hI.norm (hK.norm.mul_const _)
        intro t
        change ‖K t • V t‖ ≤ ‖K t‖ * Real.sqrt B
        rw [_root_.norm_smul]
        exact mul_le_mul_of_nonneg_left (hv t) (_root_.norm_nonneg _)
      _ = _ := integral_mul_const _ _
  have he : (∫ t : ℝ, K t • V t) =
      WithLp.toLp 2 (fun a : P => ∫ t : ℝ, K t * F t a.val) := by
    apply PiLp.ext
    intro a
    have h := (EuclideanSpace.proj a).integral_comp_comm hI
    exact h.symm
  have hs := coefficientVector_norm_sq P (fun a => ∫ t : ℝ, K t * F t a)
  rw [← he] at hs
  rw [← hs]
  calc
    _ ≤ ((∫ t : ℝ, ‖K t‖) * Real.sqrt B)^2 := by
      exact pow_le_pow_left₀ (_root_.norm_nonneg _) hn 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt hB]

lemma continuous_gramMellinPhase (x : ℝ) : Continuous (fun t => gramMellinPhase t x) := by
  exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_id.mul_const _))

lemma gram_row_mellin_integral (H : Finset Eisenstein) (v : Eisenstein → ℂ)
    (x : Eisenstein → ℝ) (hx : ∀ n ∈ H, x n ∈ Set.Icc (1 : ℝ) 2)
    (y : ℝ) (hy : y ∈ Set.Icc (1 : ℝ) 2)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∑ n ∈ H, v n * radialDualProfile W (ρ*x n/y)) =
      ∫ t : ℝ, gramMellinCoefficient W hW hW' ρ t *
        (star (gramMellinPhase t y) * ∑ n ∈ H, v n * gramMellinPhase t (x n)) := by
  have hi (n : Eisenstein) : Integrable (fun t =>
      gramMellinCoefficient W hW hW' ρ t *
        (star (gramMellinPhase t y) * (v n * gramMellinPhase t (x n)))) := by
    apply (gramMellinCoefficient_integrable W hW hW' ρ).mul_bdd (c := ‖v n‖)
      (((continuous_gramMellinPhase y).star.mul
        (continuous_const.mul (continuous_gramMellinPhase (x n)))).aestronglyMeasurable)
    filter_upwards with t
    change ‖star (gramMellinPhase t y) * (v n * gramMellinPhase t (x n))‖ ≤ ‖v n‖
    simp only [norm_mul,norm_star,norm_gramMellinPhase,mul_one,one_mul,le_refl]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum H (fun n _ => hi n)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [radialDualProfile_mellin_separated W hW hW' hρ (hx n hn) hy,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  ring

theorem gram_dyad_mellin_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ 2*N →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ N ≤ norm b ∧ norm b ≤ 2*N) →
      ∀ (j : ℕ) (v : Eisenstein → ℂ) (D : ℝ), 0 ≤ D →
      (∀ n ∈ frequencyDyad j, ‖v n‖ ≤ D) →
      ∀ (W : ℝ → ℂ) (hW : HasCompactSupport W) (hW' : ContDiff ℝ ∞ W)
        (ρ : ℝ), 0 ≤ ρ →
      (∑ b ∈ P, ‖∑ n ∈ frequencyDyad j, v n*cubicSymbol b n *
        radialDualProfile W (ρ*(norm n/(2 : ℝ)^j)/(norm b/N))‖^2) ≤
        (∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖)^2 *
        (C*((2*N)*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
          (2*N+(2 : ℝ)^j+((2*N)*(2 : ℝ)^j)^(2/3 : ℝ))*D^2) := by
  obtain ⟨C,hC,hc⟩ := cubic_inner_extension hε
  refine ⟨C,hC,?_⟩
  intro P N hN hP j v D hD hv W hW hW' ρ hρ
  have hNpos : 0 < N := by linarith
  let F : ℝ → Eisenstein → ℂ := fun t b =>
    star (gramMellinPhase t (norm b/N)) *
      ∑ n ∈ frequencyDyad j, (v n*gramMellinPhase t (norm n/(2 : ℝ)^j))*cubicSymbol b n
  have hF b : Continuous (fun t => F t b) := by
    apply (continuous_gramMellinPhase _).star.mul
    apply continuous_finsetSum
    intro n hn
    exact (continuous_const.mul (continuous_gramMellinPhase _)).mul continuous_const
  have hb t : (∑ b ∈ P, ‖F t b‖^2) ≤
      C*((2*N)*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
          (2*N+(2 : ℝ)^j+((2*N)*(2 : ℝ)^j)^(2/3 : ℝ))*D^2 := by
    simp only [F,norm_mul,norm_star,norm_gramMellinPhase,one_mul]
    apply hc P (2*N) (by linarith) (fun b hb => ⟨(hP b hb).1,(hP b hb).2.1,(hP b hb).2.2.2⟩)
      j _ D hD
    intro n hn
    simpa only [norm_mul,norm_gramMellinPhase,mul_one] using hv n hn
  have h := finite_row_integral_bound P (gramMellinCoefficient W hW hW' ρ) F
    (gramMellinCoefficient_integrable W hW hW' ρ) (fun b _ => hF b) (by positivity) hb
  have he b (hb : b ∈ P) : (∑ n ∈ frequencyDyad j, v n*cubicSymbol b n *
        radialDualProfile W (ρ*(norm n/(2 : ℝ)^j)/(norm b/N))) =
      ∫ t : ℝ, gramMellinCoefficient W hW hW' ρ t * F t b := by
    have hx n (hn : n ∈ frequencyDyad j) : norm n/(2 : ℝ)^j ∈ Set.Icc (1 : ℝ) 2 := by
      obtain ⟨hl,hu⟩ := frequencyDyad_norm hn
      constructor
      · exact (le_div_iff₀ (by positivity)).mpr (by simpa using hl)
      · exact (div_le_iff₀ (by positivity)).mpr hu
    have hy : norm b/N ∈ Set.Icc (1 : ℝ) 2 := by
      exact ⟨(le_div_iff₀ (by linarith)).mpr (by simpa using (hP b hb).2.2.1),
        (div_le_iff₀ (by linarith)).mpr (hP b hb).2.2.2⟩
    rw [gram_row_mellin_integral (frequencyDyad j) (fun n => v n*cubicSymbol b n)
      _ hx _ hy W hW hW' hρ]
    apply integral_congr_ae
    filter_upwards with t
    congr 2
    apply Finset.sum_congr rfl
    intro n hn
    ring
  convert h using 1
  apply Finset.sum_congr rfl
  intro b hb
  rw [he b hb]

theorem gram_dyad_mellin_rapidDecay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ 2*N →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ N ≤ norm b ∧ norm b ≤ 2*N) →
      ∀ (j : ℕ) (v : Eisenstein → ℂ) (D : ℝ), 0 ≤ D →
      (∀ n ∈ frequencyDyad j, ‖v n‖ ≤ D) → ∀ ρ : ℝ, 0 ≤ ρ →
      (1+ρ)^(2*A) *
        (∑ b ∈ P, ‖∑ n ∈ frequencyDyad j, v n*cubicSymbol b n *
          radialDualProfile W (ρ*(norm n/(2 : ℝ)^j)/(norm b/N))‖^2) ≤
        C*((2*N)*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
          (2*N+(2 : ℝ)^j+((2*N)*(2 : ℝ)^j)^(2/3 : ℝ))*D^2 := by
  obtain ⟨C,hC,hc⟩ := gram_dyad_mellin_bound hε
  obtain ⟨M,hM,hm⟩ := gramMellinCoefficient_mass_rapidDecay W hW hW' A
  refine ⟨M^2*C,by positivity,?_⟩
  intro P N hN hP j v D hD hv ρ hρ
  have hNpos : 0 < N := by linarith
  have h := hc P N hN hP j v D hD hv W hW hW' ρ hρ
  have hmass : (1+ρ)^(2*A)*(∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖)^2 ≤ M^2 := by
    have hh := pow_le_pow_left₀ (show 0 ≤ (1+ρ)^A *
      (∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖) from by positivity) (hm ρ hρ) 2
    simpa only [mul_pow,← pow_mul,mul_comm A 2] using hh
  calc
    _ ≤ (1+ρ)^(2*A) * ((∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖)^2 *
        (C*((2*N)*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
          (2*N+(2 : ℝ)^j+((2*N)*(2 : ℝ)^j)^(2/3 : ℝ))*D^2)) := by gcongr
    _ = ((1+ρ)^(2*A)*(∫ t : ℝ, ‖gramMellinCoefficient W hW hW' ρ t‖)^2) *
        (C*((2*N)*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
          (2*N+(2 : ℝ)^j+((2*N)*(2 : ℝ)^j)^(2/3 : ℝ))*D^2) := by ring
    _ ≤ M^2 * (C*((2*N)*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
          (2*N+(2 : ℝ)^j+((2*N)*(2 : ℝ)^j)^(2/3 : ℝ))*D^2) := by gcongr
    _ = _ := by ring

theorem gramDualTerm_dyad_rapidDecay (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (A : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ 2*N →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ N ≤ norm b ∧ norm b ≤ 2*N) →
      ∀ (a : Eisenstein), primary a → ∀ (Z : ℝ), 0 ≤ Z → ∀ j : ℕ,
      (1+Z*(2 : ℝ)^j/(27*norm a*N))^(2*A) *
        (∑ b ∈ P, ‖∑ n ∈ frequencyDyad j, gramDualTerm a b W Z n‖^2) ≤
        C*((2*N)*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
          (2*N+(2 : ℝ)^j+((2*N)*(2 : ℝ)^j)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hc⟩ := gram_dyad_mellin_rapidDecay W hW hW' hε A
  refine ⟨C,hC,?_⟩
  intro P N hN hP a ha Z hZ j
  have hNpos : 0 < N := by linarith
  let v : Eisenstein → ℂ := fun n => star (cubicSymbol a n) *
    (Real.fourierChar (tracePair (n : ℂ) (1/(3*traceLambda))) : ℂ)
  have hv n (hn : n ∈ frequencyDyad j) : ‖v n‖ ≤ 1 := by
    simpa only [v,norm_mul,norm_star,Circle.norm_coe,mul_one] using norm_cubicSymbol_le_one ha n
  have ha0 : 0 < norm a := norm_pos_of_ne_zero (primary_ne_zero ha)
  have han : norm a ≠ 0 := ne_of_gt ha0
  have hN0 : N ≠ 0 := by linarith
  have hJ : (2 : ℝ)^j ≠ 0 := by positivity
  have he b (hb : b ∈ P) n : gramDualTerm a b W Z n =
      v n*cubicSymbol b n * radialDualProfile W
        ((Z*(2 : ℝ)^j/(27*norm a*N))*(norm n/(2 : ℝ)^j)/(norm b/N)) := by
    rw [gramDualTerm_radial a b W hZ]
    have hbn : norm b ≠ 0 := ne_of_gt (norm_pos_of_ne_zero (primary_ne_zero (hP b hb).1))
    have hr : Z*norm n/(27*norm (a*b)) =
        (Z*(2 : ℝ)^j/(27*norm a*N))*(norm n/(2 : ℝ)^j)/(norm b/N) := by
      simp only [norm,Subalgebra.coe_mul,Complex.normSq_mul] at *
      field_simp
    rw [hr]
    dsimp [v]
    ring
  have h := hc P N hN hP j v 1 (by norm_num) hv
    (Z*(2 : ℝ)^j/(27*norm a*N)) (by positivity)
  simp only [one_pow,mul_one] at h
  convert h using 1
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  congr 2
  apply Finset.sum_congr rfl
  intro n hn
  exact he b hb n

end CubicFirstMoment
end
end

end OAI
