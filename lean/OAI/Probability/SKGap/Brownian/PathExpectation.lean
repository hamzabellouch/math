import Mathlib
import OAI.Probability.SKGap.Localization.ExpectedCutoff
import OAI.Probability.SKGap.Brownian.PathBiasBase

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def pathExpected (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (j : ℝ) (a : ι → ℝ)
    (z : ℝ) (i : ι) : ℝ :=
  expectedCutoff f R hR (pathDiagonal a z)
    (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)) (j/(Fintype.card ι:ℝ)) i

lemma pathExpected_continuous (f : 𝓢(ℝ,ℂ)) {R j A : ℝ} {a : ι → ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA0 : 0 ≤ A)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (i : ι) :
    ContinuousOn (fun z => pathExpected f R hR j a z i) (Icc 0 1) := by
  have hq := diagonal_mean_bounds hj ha hA
  apply continuousOn_expected_realTruncatedK f hR _ i _ (pathBound f R j A)
  · unfold pathDiagonal; fun_prop
  · unfold pathShift; fun_prop
  · intro z; exact diagonal_transpose _
  · intro z; exact diagonal_transpose _
  · intro z hz
    exact (path_constants_bound f hR hj hA0 hA hq.1 hq.2 hz).1

omit [Nonempty ι] in
lemma pathExpected_zero (f : 𝓢(ℝ,ℂ)) {R : ℝ} (hR : 0 ≤ R) (j : ℝ)
    (a : ι → ℝ) (i : ι) : pathExpected f R hR j a 0 i = 1 := by
  unfold pathExpected expectedCutoff
  have hd : pathDiagonal a 0 = 0 := by simp [pathDiagonal]
  simp only [hd,realTruncatedK_zero_diagonal,Matrix.one_apply_eq,integral_const,probReal_univ,one_smul]

lemma pathExpected_bound (f : 𝓢(ℝ,ℂ)) {R j A z : ℝ} {a : ι → ℝ}
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA0 : 0 ≤ A)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hz : z ∈ Icc (0:ℝ) 1) (i : ι) :
    |pathExpected f R hR j a z i| ≤ pathBound f R j A := by
  have hq := diagonal_mean_bounds hj ha hA
  have hb := (path_constants_bound f hR hj hA0 hA hq.1 hq.2 hz).1
  have hm := norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1))
    (ae_of_all _ (fun g => show ‖realTruncatedK f R hR (pathDiagonal a z)
      (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)) (goeMatrix (j/(Fintype.card ι:ℝ)) g) i i‖ ≤ pathBound f R j A from by
      rw [Real.norm_eq_abs]
      exact (matrix_entry_le_opNorm _ i i).trans
        ((realTruncatedK_opNorm f hR _ _ _ (diagonal_transpose _) (diagonal_transpose _)).trans hb)))
  simpa only [pathExpected,expectedCutoff,Real.norm_eq_abs,probReal_univ,mul_one] using hm

lemma path_self_consistency (f : 𝓢(ℝ,ℂ)) {lo hi R j A rate z : ℝ} {a : ι → ℝ}
    (hlo : 0 < lo) (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA0 : 0 ≤ A) (hrate : 0 < rate)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hz : z ∈ Icc (0:ℝ) 1)
    (hp : (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet (j/(Fintype.card ι:ℝ)) R lo hi (pathDiagonal a z)
        (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)))ᶜ ≤
          3*Real.exp (-rate*(Fintype.card ι:ℝ))) (i : ι) :
    let k := pathExpected f R hR j a z
    let B := pathBound f R j A
    let L := pathLip f R j A
    |k i-1-z^2*j*a i*(∑ b, (1/(Fintype.card ι:ℝ))*a b*(k b-1))*k i| ≤
      (loopErrorConstantTwo j A B rate+A*loopErrorConstantOne j A B L rate)/(Fintype.card ι:ℝ) := by
  intro k B L
  let n : ℝ := Fintype.card ι
  let q := (j/n)*∑ b, a b
  let d : ι → ℝ := fun b => sqrt z*sqrt (a b)
  let c : ι → ℝ := fun _ => z*q
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hn1 : 1 ≤ n := by
    dsimp [n]
    exact_mod_cast Fintype.card_pos (α := ι)
  have hq := diagonal_mean_bounds hj ha hA
  have hcst := path_constants_bound f hR hj hA0 hA hq.1 hq.2 hz
  have hconst := path_constants_nonneg f hR hj hA0
  have hd (b : ι) : (d b)^2=z*a b := by
    dsimp [d]; rw [mul_pow,sq_sqrt hz.1,sq_sqrt (ha b)]
  have hdi : (d i)^2 ≤ A := by rw [hd]; exact (mul_le_of_le_one_left (ha i) hz.2).trans (hA i)
  have hci : |c i| ≤ j*A := by
    rw [abs_of_nonneg (mul_nonneg hz.1 hq.1)]
    exact (mul_le_of_le_one_left hq.1 hz.2).trans hq.2
  have he1 := (cutoffErrorOne_bound f (pathDiagonal a z) (pathShift z q) hj hA0 hconst.1 hconst.2 hR
    hcst.1 hcst.2.1 hcst.2.2 (le_refl _)).trans
      (loop_error_one_absorption hj hA0 hconst.1 hconst.2 hrate hn1 hp)
  have he2 := (cutoffErrorTwo_bound f d c i hj hA0 hconst.1 hR hcst.1 hdi hci (le_refl _)).trans
      (loop_error_two_absorption hj hA0 hconst.1 hrate hn1 hp)
  have he := actual_cutoff_self_consistency f hlo hf hR (div_nonneg hj hn.le) d c i
  dsimp only at he
  have hs : (j/n)*(∑ b, (d b)^2*k b)-c i =
      z*j*(∑ b, (1/n)*a b*(k b-1)) := by
    dsimp only [c,q]
    simp_rw [hd,Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _
    ring
  have heq : (d i)^2*((j/n)*(∑ b, (d b)^2*k b)-c i)*k i =
      z^2*j*a i*(∑ b, (1/n)*a b*(k b-1))*k i := by rw [hs,hd]; ring
  change |k i-1-(d i)^2*((j/n)*(∑ b, (d b)^2*k b)-c i)*k i| ≤ _ at he
  rw [heq] at he
  apply he.trans
  calc
    _ ≤ loopErrorConstantTwo j A B rate/n+A*(loopErrorConstantOne j A B L rate/n) := by
      apply add_le_add he2
      rw [abs_of_nonneg (sq_nonneg _)]
      apply (mul_le_mul_of_nonneg_left he1 (sq_nonneg _)).trans
      exact mul_le_mul_of_nonneg_right hdi (div_nonneg
        (loopErrorConstants_nonneg j A B L rate hj hA0 hconst.1 hconst.2 hrate).1 hn.le)
    _ = _ := by ring
end SKGap
end
end

section
noncomputable section
namespace SKGap

lemma exists_bootstrap_constants {j A M : ℝ} (hj : 0 ≤ j) (hA : 0 ≤ A)
    (hM : 0 ≤ M) (hsub : j*A^2 < 1) :
    ∃ δ γ e : ℝ, 0 < δ ∧ 0 < γ ∧ 0 < e ∧
      ∀ ε, 0 ≤ ε → ε ≤ e →
        j*A^2*(1+j*A*M*δ+ε) ≤ 1-γ ∧ A*ε/γ < δ := by
  let g := 1-j*A^2
  let d := j*A^2*(j*A*M+1)
  let δ := g/(4*(d+1))
  let γ := g/2
  have hg : 0 < g := sub_pos.mpr hsub
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hγ : 0 < γ := half_pos hg
  have hdδ : (d+1)*δ = g/4 := by dsimp [δ]; field_simp
  refine ⟨δ,γ,min δ (δ*γ/(2*(A+1))),hδ,hγ,lt_min hδ (by positivity),?_⟩
  intro ε hε he
  have heδ := he.trans (min_le_left _ _)
  have he' := (le_div_iff₀ (show (0:ℝ)<2*(A+1) by positivity)).mp
    (he.trans (min_le_right _ _))
  constructor
  · have hdδ' : d*δ ≤ g/4 := by nlinarith
    have hf : j*A^2*(1+j*A*M*δ+ε) ≤ j*A^2+d*δ := by
      dsimp only [d]
      nlinarith [mul_nonneg (mul_nonneg hj (sq_nonneg A)) (sub_nonneg.mpr heδ)]
    apply hf.trans
    dsimp only [γ,g] at *
    linarith
  · apply (div_lt_iff₀ hγ).mpr
    have hh : A*ε ≤ (A+1)*ε := by nlinarith
    have hp : 0 < δ*γ := mul_pos hδ hγ
    nlinarith
end SKGap

namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set Filter
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap Topology

def pathRate (j A : ℝ) : ℝ :=
  min (1/(π^2*j)) (((1-sqrt j*A)^2)^2/(16*π^2*j*A^2))

lemma pathRate_pos {j A : ℝ} (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1) :
    0 < pathRate j A := by
  have hh : 0 < 1-sqrt j*A := sub_pos.mpr hs
  unfold pathRate
  exact lt_min (by positivity) (by positivity)

lemma path_interval {j A : ℝ} (hj : 0 ≤ j) (hA : 0 ≤ A) (hs : sqrt j*A < 1) :
    0 < (1-sqrt j*A)^2/4 ∧
    (1-sqrt j*A)^2/4 ≤ 2+A*(2*sqrt j+1+j*A) := by
  have hh := mul_nonneg (sqrt_nonneg j) hA
  have hgap : 0 < 1-sqrt j*A := sub_pos.mpr hs
  have hp : (1-sqrt j*A)^2 ≤ 1 := by nlinarith
  refine ⟨by positivity,?_⟩
  have hx : 0 ≤ A*(2*sqrt j+1+j*A) := by positivity
  linarith

lemma path_size_eventually {j A : ℝ} (hs : sqrt j*A < 1) :
    ∀ᶠ n : ℕ in atTop,
      2*sqrt A*sqrt (sqrt (2*j^2*A^2/(n:ℝ))) ≤ (1-sqrt j*A)^2/4 := by
  have hgap : 0 < (1-sqrt j*A)^2/4 := by
    have hh := sub_pos.mpr hs
    positivity
  have ht : Tendsto (fun n : ℕ => 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(n:ℝ)))) atTop (𝓝 0) := by
    have hh := ((tendsto_const_div_atTop_nhds_zero_nat (2*j^2*A^2)).sqrt.sqrt).const_mul (2*sqrt A)
    simpa only [sqrt_zero,mul_zero] using hh
  exact (ht.eventually (gt_mem_nhds hgap)).mono (fun _ h => h.le)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
lemma path_goodSet_exponential {j A z : ℝ} {a : ι → ℝ}
    (hj : 0 < j) (hA0 : 0 < A) (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A)
    (hs : sqrt j*A < 1)
    (herr : 2*sqrt A*sqrt (sqrt (2*j^2*A^2/(Fintype.card ι:ℝ))) ≤ (1-sqrt j*A)^2/4)
    (hz : z ∈ Icc (0:ℝ) 1) :
    (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet (j/(Fintype.card ι:ℝ)) (2*sqrt j+1+1)
        ((1-sqrt j*A)^2/4) (2+A*(2*sqrt j+1+j*A))
        (pathDiagonal a z) (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)))ᶜ ≤
          3*Real.exp (-pathRate j A*(Fintype.card ι:ℝ)) := by
  have hh := path_goodSet_failure hj hA0 (by norm_num : (0:ℝ)<1) ha hA hs herr hz
  dsimp only at hh
  apply hh.trans
  have h₁ := min_le_left (1/(π^2*j)) (((1-sqrt j*A)^2)^2/(16*π^2*j*A^2))
  have h₂ := min_le_right (1/(π^2*j)) (((1-sqrt j*A)^2)^2/(16*π^2*j*A^2))
  have he₁ : Real.exp (-(1:ℝ)^2*(Fintype.card ι:ℝ)/(π^2*j)) ≤
      Real.exp (-pathRate j A*(Fintype.card ι:ℝ)) := by
    apply Real.exp_le_exp.mpr
    change _ ≤ -min _ _ * _
    have hn : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    convert neg_le_neg (mul_le_mul_of_nonneg_right h₁ hn) using 1 <;> first | rfl | ring
  have he₂ : Real.exp (-((1-sqrt j*A)^2)^2*(Fintype.card ι:ℝ)/(16*π^2*j*A^2)) ≤
      Real.exp (-pathRate j A*(Fintype.card ι:ℝ)) := by
    apply Real.exp_le_exp.mpr
    change _ ≤ -min _ _ * _
    have hn : (0:ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    convert neg_le_neg (mul_le_mul_of_nonneg_right h₂ hn) using 1 <;> first | rfl | ring
  linarith
end SKGap
end
end

end OAI
