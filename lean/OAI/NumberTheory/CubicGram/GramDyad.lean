import Mathlib
import OAI.NumberTheory.CubicGram.GramMellin

namespace OAI

/-! Weighted dyadic row summation and explicit coprime Gram bounds. -/

section

noncomputable section
open scoped BigOperators ContDiff
open Set Filter MeasureTheory Topology
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma norm_sum_sq_weighted {ι : Type*} (I : Finset ι) (v : ι → ℂ)
    (w : ι → ℝ) (hw : ∀ i ∈ I, 0 < w i) :
    ‖∑ i ∈ I, v i‖^2 ≤ (∑ i ∈ I, w i)*(∑ i ∈ I, ‖v i‖^2/w i) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq I (fun i => Real.sqrt (w i))
    (fun i => ‖v i‖/Real.sqrt (w i))
  have h1 : (∑ i ∈ I, Real.sqrt (w i)*(‖v i‖/Real.sqrt (w i))) =
      ∑ i ∈ I, ‖v i‖ := by
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [ne_of_gt (Real.sqrt_pos.mpr (hw i hi))]
  have h2 : (∑ i ∈ I, (Real.sqrt (w i))^2) = ∑ i ∈ I, w i := by
    exact Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hw i hi).le)
  have h3 : (∑ i ∈ I, (‖v i‖/Real.sqrt (w i))^2) = ∑ i ∈ I, ‖v i‖^2/w i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [div_pow,Real.sq_sqrt (hw i hi).le]
  rw [h1,h2,h3] at h
  exact (pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_sum_le I v) 2).trans h

lemma finite_rows_weighted_sum (P : Finset Eisenstein) (n : ℕ)
    (F : ℕ → Eisenstein → ℂ) (w : ℕ → ℝ) (hw : ∀ j, 0 < w j) :
    (∑ b ∈ P, ‖∑ j ∈ Finset.range n, F j b‖^2) ≤
      (∑ j ∈ Finset.range n, w j)*
        (∑ j ∈ Finset.range n, (∑ b ∈ P, ‖F j b‖^2)/w j) := by
  calc
    _ ≤ ∑ b ∈ P, (∑ j ∈ Finset.range n, w j)*
        (∑ j ∈ Finset.range n, ‖F j b‖^2/w j) :=
      Finset.sum_le_sum (fun b _ => norm_sum_sq_weighted _ (fun j => F j b) w (fun j _ => hw j))
    _ = _ := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp_rw [Finset.sum_div]

lemma dyadic_weight_partial_sum {c : ℝ} (hc : 0 < c) (n : ℕ) :
    (∑ j ∈ Finset.range n, (c*2^j)/(1+c*2^j)^2) ≤ 2 := by
  have h := mul_le_mul_of_nonneg_left (dyadic_decay_partial_sum hc n) hc.le
  simp_rw [Finset.mul_sum,← mul_div_assoc] at h
  have he : c*2/c = (2 : ℝ) := by field_simp
  simpa only [he] using h

def gramDyadConstant (p : ℝ) : ℝ := 4*2^p/(2^p-1)

lemma gramDyadConstant_pos {p : ℝ} (hp : 0 < p) : 0 < gramDyadConstant p := by
  have h := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hp
  unfold gramDyadConstant
  positivity

lemma gram_power_partial_sum {p c : ℝ} (hp : 0 < p) (hp4 : p ≤ 4)
    (hc : 0 < c) (n : ℕ) :
    (∑ j ∈ Finset.range n, ((2 : ℝ)^j)^p/(1+c*2^j)^8) ≤
      gramDyadConstant p * c^(-p) := by
  have h := real_dyadic_decay p hp hp4 hc
  exact (h.1.sum_le_tsum (Finset.range n) (fun j _ => by positivity)).trans h.2

lemma gram_envelope_weight {N c J ε : ℝ} (hN : 0 < N) (hc : 0 < c) (hJ : 0 < J) :
    ((N*J)^ε*J*(N+J+(N*J)^(2/3 : ℝ))/(1+c*J)^10) /
        (c*J/(1+c*J)^2) =
      (N^ε/c)*(N*J^ε/(1+c*J)^8 + J^(1+ε)/(1+c*J)^8 +
        N^(2/3 : ℝ)*J^(2/3+ε : ℝ)/(1+c*J)^8) := by
  rw [Real.mul_rpow hN.le hJ.le,Real.mul_rpow hN.le hJ.le,
    Real.rpow_add hJ,Real.rpow_add hJ,Real.rpow_one]
  have hd : 1+c*J ≠ 0 := by positivity
  field_simp

lemma gram_dyad_partial_rows (P : Finset Eisenstein) (F : ℕ → Eisenstein → ℂ)
    {N c ε C : ℝ} (hN : 0 < N) (hc : 0 < c) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC : 0 ≤ C)
    (hF : ∀ j : ℕ, (1+c*2^j)^10 * (∑ b ∈ P, ‖F j b‖^2) ≤
      C*(N*(2 : ℝ)^j)^ε*(2 : ℝ)^j*(N+(2 : ℝ)^j+(N*(2 : ℝ)^j)^(2/3 : ℝ)))
    (n : ℕ) :
    (∑ b ∈ P, ‖∑ j ∈ Finset.range n, F j b‖^2) ≤
      2*C*(N^ε/c)*(N*gramDyadConstant ε*c^(-ε) +
        gramDyadConstant (1+ε)*c^(-(1+ε)) +
        N^(2/3 : ℝ)*gramDyadConstant (2/3+ε)*c^(-(2/3+ε))) := by
  let w : ℕ → ℝ := fun j => c*2^j/(1+c*2^j)^2
  have hw j : 0 < w j := by dsimp [w]; positivity
  have h := finite_rows_weighted_sum P n F w hw
  have hrow j : (∑ b ∈ P, ‖F j b‖^2)/w j ≤
      C*(N^ε/c)*(N*((2 : ℝ)^j)^ε/(1+c*2^j)^8 +
        ((2 : ℝ)^j)^(1+ε)/(1+c*2^j)^8 +
        N^(2/3 : ℝ)*((2 : ℝ)^j)^(2/3+ε : ℝ)/(1+c*2^j)^8) := by
    have hh := (le_div_iff₀' (by positivity : 0 < (1+c*2^j)^10)).mpr (hF j)
    have hd := div_le_div_of_nonneg_right hh (hw j).le
    apply hd.trans_eq
    dsimp [w]
    rw [show C*(N*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
      (N+(2 : ℝ)^j+(N*(2 : ℝ)^j)^(2/3 : ℝ)) =
      C*((N*(2 : ℝ)^j)^ε*(2 : ℝ)^j*
      (N+(2 : ℝ)^j+(N*(2 : ℝ)^j)^(2/3 : ℝ))) by ring]
    rw [mul_div_assoc,mul_div_assoc,gram_envelope_weight hN hc (by positivity)]
    ring
  have he := Finset.sum_le_sum (s := Finset.range n) (fun j _ => hrow j)
  simp_rw [← Finset.mul_sum,Finset.sum_add_distrib,mul_div_assoc,← Finset.mul_sum] at he
  have hp0 := gram_power_partial_sum hε (by linarith : ε ≤ 4) hc n
  have hp1 := gram_power_partial_sum (by linarith : 0 < 1+ε) (by linarith : 1+ε ≤ 4) hc n
  have hp2 := gram_power_partial_sum (by linarith : 0 < 2/3+ε) (by linarith : 2/3+ε ≤ 4) hc n
  have ht := dyadic_weight_partial_sum hc n
  apply h.trans
  calc
    _ ≤ 2 * (C*(N^ε/c)*(N*(gramDyadConstant ε*c^(-ε)) +
        gramDyadConstant (1+ε)*c^(-(1+ε)) +
        N^(2/3 : ℝ)*(gramDyadConstant (2/3+ε)*c^(-(2/3+ε))))) := by
      apply mul_le_mul ht _ (Finset.sum_nonneg (fun j _ => div_nonneg (by positivity) (hw j).le)) (by norm_num)
      apply he.trans
      gcongr
    _ = _ := by ring

theorem gramDualTerm_rows_explicit (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ 2*N →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ N ≤ norm b ∧ norm b ≤ 2*N) →
      ∀ (a : Eisenstein), primary a → Squarefree a →
      (∀ b ∈ P, IsCoprime a b ∧ a ≠ b) → ∀ (Z : ℝ), 0 < Z →
      let c := Z/(27*norm a*N)
      (∑ b ∈ P, ‖∑' n : Eisenstein, gramDualTerm a b W Z n‖^2) ≤
        C*((2*N)^ε/c)*((2*N)*gramDyadConstant ε*c^(-ε) +
          gramDyadConstant (1+ε)*c^(-(1+ε)) +
          (2*N)^(2/3 : ℝ)*gramDyadConstant (2/3+ε)*c^(-(2/3+ε))) := by
  obtain ⟨C,hC,hc⟩ := gramDualTerm_dyad_rapidDecay W hW hW' hε 5
  refine ⟨2*C,by positivity,?_⟩
  intro P N hN hP a ha hsa hab Z hZ
  have hNpos : 0 < N := by linarith
  dsimp only
  let c : ℝ := Z/(27*norm a*N)
  have han : 0 < norm a := norm_pos_of_ne_zero (primary_ne_zero ha)
  have hc0 : 0 < c := by dsimp [c]; positivity
  let F : ℕ → Eisenstein → ℂ := fun j b => ∑ n ∈ frequencyDyad j, gramDualTerm a b W Z n
  have hf j : (1+c*2^j)^10*(∑ b ∈ P, ‖F j b‖^2) ≤
      C*((2*N)*(2 : ℝ)^j)^ε*(2 : ℝ)^j*(2*N+(2 : ℝ)^j+((2*N)*(2 : ℝ)^j)^(2/3 : ℝ)) := by
    have h := hc P N hN hP a ha Z hZ.le j
    have he : Z*(2 : ℝ)^j/(27*norm a*N) = c*2^j := by dsimp [c]; ring
    simpa only [he,show 2*5=10 from rfl,F] using h
  have hp n := gram_dyad_partial_rows P F (by positivity : 0 < 2*N) hc0 hε hε1 hC.le hf n
  have hs b (hb : b ∈ P) : HasSum (fun j => F j b) (∑' n, gramDualTerm a b W Z n) :=
    hasSum_frequencyDyad _ (summable_gramDualTerm ha (hP b hb).1 W hW hW' hZ)
      (gramDualTerm_zero ha (hP b hb).1 hsa (hP b hb).2.1 (hab b hb).1 (hab b hb).2 W Z)
  have ht := tendsto_finsetSum P (fun b hb => ((hs b hb).tendsto_sum_nat.norm.pow 2))
  exact le_of_tendsto ht (Filter.Eventually.of_forall hp)

theorem primaryCharacterGram_coprime_explicit (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hW' : ContDiff ℝ ∞ W) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : Finset Eisenstein) (N : ℝ), 1 ≤ 2*N →
      (∀ b ∈ P, primary b ∧ Squarefree b ∧ N ≤ norm b ∧ norm b ≤ 2*N) →
      ∀ (a : Eisenstein), primary a → Squarefree a →
      (∀ b ∈ P, IsCoprime a b ∧ a ≠ b) → ∀ (Z : ℝ), 0 < Z →
      let c := Z/(27*norm a*N)
      (∑ b ∈ P, ‖primaryCharacterGram a b W Z‖^2) ≤
        (Z^2/(81*norm a*N)) *
        (C*((2*N)^ε/c)*((2*N)*gramDyadConstant ε*c^(-ε) +
          gramDyadConstant (1+ε)*c^(-(1+ε)) +
          (2*N)^(2/3 : ℝ)*gramDyadConstant (2/3+ε)*c^(-(2/3+ε)))) := by
  obtain ⟨C,hC,hc⟩ := gramDualTerm_rows_explicit W hW hW' hε hε1
  refine ⟨C,hC,?_⟩
  intro P N hN hP a ha hsa hab Z hZ
  have hNpos : 0 < N := by linarith
  dsimp only
  have han : 0 < norm a := norm_pos_of_ne_zero (primary_ne_zero ha)
  have hrow b (hb : b ∈ P) : ‖primaryCharacterGram a b W Z‖^2 ≤
      (Z^2/(81*norm a*N))*‖∑' n : Eisenstein, gramDualTerm a b W Z n‖^2 := by
    rw [norm_primaryCharacterGram_poisson ha (hP b hb).1 hsa (hP b hb).2.1 (hab b hb).1 W hW hW' hZ,
      mul_pow,div_pow,mul_pow,Real.sq_sqrt (norm_nonneg (a*b))]
    have hn : norm (a*b) = norm a * norm b := Complex.normSq_mul _ _
    rw [hn]
    norm_num only [show (9 : ℝ)^2 = 81 from by norm_num]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    nlinarith [(hP b hb).2.2.1]
  calc
    _ ≤ ∑ b ∈ P, (Z^2/(81*norm a*N))*‖∑' n : Eisenstein, gramDualTerm a b W Z n‖^2 :=
      Finset.sum_le_sum hrow
    _ = (Z^2/(81*norm a*N))*(∑ b ∈ P, ‖∑' n : Eisenstein, gramDualTerm a b W Z n‖^2) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hc P N hN hP a ha hsa hab Z hZ) (by positivity)

end CubicFirstMoment
end
end

end OAI
