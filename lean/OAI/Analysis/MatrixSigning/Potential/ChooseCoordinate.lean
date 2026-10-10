import Mathlib
import OAI.Analysis.MatrixSigning.Potential.LineShiftIteratedDeriv
import OAI.Analysis.MatrixSigning.Optimization.Select

namespace OAI

open Matrix

namespace CurrentKS.Difference

section
open scoped BigOperators

def chooseCoordinate {N : ℕ} [NeZero N] (g : Fin N → ℚ) : Fin N :=
  CurrentKS.Descent.select (fun i => -|g i|) 0 (List.finRange N)

lemma chooseCoordinate_max {N : ℕ} [NeZero N] (g : Fin N → ℚ) (i : Fin N) :
    |g i| ≤ |g (chooseCoordinate g)| := by
  have hh := CurrentKS.Descent.select_le (fun i => -|g i|) (0 : Fin N) (List.finRange N)
    i (by simp)
  exact neg_le_neg_iff.mp hh

theorem chosen_gradient {N : ℕ} [NeZero N] (g : Fin N → ℝ) (ghat : Fin N → ℚ)
    {a : ℝ} (ha : 0 < a) (herr : ∀ i,|(ghat i:ℝ)-g i| ≤ a/8)
    (hlarge : ∃ i,a ≤ |g i|) :
    let i := chooseCoordinate ghat
    3*a/4 ≤ |g i| ∧ ((0 ≤ ghat i → 0 < g i) ∧ (ghat i < 0 → g i < 0)) := by
  dsimp
  obtain ⟨j,hj⟩ := hlarge
  let i := chooseCoordinate ghat
  have hm : |(ghat j:ℝ)| ≤ |(ghat i:ℝ)| := by exact_mod_cast chooseCoordinate_max ghat j
  have hjerr := abs_le.mp (herr j)
  have hierr := abs_le.mp (herr i)
  have hsmall : |g j|-a/8 ≤ |(ghat j:ℝ)| := by
    have hh := abs_sub_abs_le_abs_sub (g j) (ghat j:ℝ)
    rw [abs_sub_comm] at hh
    linarith [herr j]
  have hgsize : 3*a/4 ≤ |g i| := by
    have hh := abs_sub_abs_le_abs_sub (ghat i:ℝ) (g i)
    linarith [herr i]
  refine ⟨hgsize,?_,?_⟩
  · intro hnonneg
    have hn : (0:ℝ) ≤ ghat i := by exact_mod_cast hnonneg
    rw [abs_of_nonneg hn] at hm
    linarith
  · intro hneg
    have hn : (ghat i:ℝ) < 0 := by exact_mod_cast hneg
    rw [abs_of_neg hn] at hm
    linarith

lemma gradient_decrease {f0 f1 a s M v : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hs1 : s ≤ 1/4) (hstep : M*s ≤ a/4) (hv : v ≤ -3*a/4)
    (htaylor : f1 ≤ f0+s*v+M*s^2/2) : f1 ≤ f0-(5/2:ℝ)*a*s^2 := by
  have hv' := mul_le_mul_of_nonneg_left hv hs.le
  have hstep' := mul_le_mul_of_nonneg_left hstep hs.le
  have hsmall := mul_le_mul_of_nonneg_left hs1 (show 0≤a*s by positivity)
  nlinarith

lemma opposite_decrease {f0 fp fm L Q a s M : ℝ} (ha : 0 < a) (hs : 0 < s)
    (hstep : M*s ≤ a/4) (hQ : Q ≤ -6*a*s^2)
    (hp : fp ≤ f0+L+Q/2+M*s^3/6) (hm : fm ≤ f0-L+Q/2+M*s^3/6) :
    fp ≤ f0-2*a*s^2 ∨ fm ≤ f0-2*a*s^2 := by
  have he := mul_le_mul_of_nonneg_left hstep (sq_nonneg s)
  have hpos : 0<a*s^2 := by positivity
  by_contra h
  push Not at h
  nlinarith

end

open Set
open scoped ContDiff

variable {N : ℕ}

def rationalGradientDirection [NeZero N] (g : Fin N → ℚ) : Fin N → ℚ :=
  (if 0 ≤ g (chooseCoordinate g) then (-1:ℚ) else 1) • (Pi.single (chooseCoordinate g) 1 : Fin N → ℚ)

def gradientDirection [NeZero N] (g : Fin N → ℚ) : Fin N → ℝ :=
  (if 0 ≤ g (chooseCoordinate g) then (-1:ℝ) else 1) • (Pi.single (chooseCoordinate g) 1 : Fin N → ℝ)

lemma rationalGradientDirection_cast [NeZero N] (g : Fin N → ℚ) :
    (fun i => (rationalGradientDirection g i:ℝ))=gradientDirection g := by
  classical
  funext j
  simp only [rationalGradientDirection,gradientDirection,Pi.smul_apply,smul_eq_mul,
    Rat.cast_mul,Pi.single_apply]
  split_ifs <;> norm_num

lemma gradientDirection_bound [NeZero N] (g : Fin N → ℚ) : ‖gradientDirection g‖ ≤ 1 := by
  classical
  unfold gradientDirection
  split_ifs <;> simp only [neg_smul,one_smul,norm_neg]
  all_goals
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    by_cases hi : i=chooseCoordinate g <;> simp [hi]

lemma gradientDirection_derivative [NeZero N] (L : (Fin N → ℝ) →L[ℝ] ℝ)
    (ghat : Fin N → ℚ) {a : ℝ} (ha : 0 < a)
    (herr : ∀ i,|(ghat i:ℝ)-L (Pi.single i (1:ℝ))| ≤ a/8)
    (hlarge : ∃ i,a ≤ |L (Pi.single i (1:ℝ))|) :
    L (gradientDirection ghat) ≤ -3*a/4 := by
  have hc := chosen_gradient (fun i => L (Pi.single i (1:ℝ))) ghat ha herr hlarge
  dsimp only at hc
  unfold gradientDirection
  split_ifs with hs
  · have hp := hc.2.1 hs
    rw [abs_of_pos hp] at hc
    simp only [map_smul,smul_eq_mul,neg_one_mul]
    linarith [hc.1]
  · have hp := hc.2.2 (lt_of_not_ge hs)
    rw [abs_of_neg hp] at hc
    simp only [one_smul]
    linarith [hc.1]

theorem gradient_candidate_decrease [NeZero N] (f : (Fin N → ℝ) → ℝ)
    (x : Fin N → ℝ) (ghat : Fin N → ℚ) {a s M : ℝ}
    (ha : 0 < a) (hs : 0 < s) (hs1 : s ≤ 1/4) (hstep : M*s ≤ a/4)
    (herr : ∀ i,|(ghat i:ℝ)-fderiv ℝ f x (Pi.single i (1:ℝ))| ≤ a/8)
    (hlarge : ∃ i,a ≤ |fderiv ℝ f x (Pi.single i (1:ℝ))|)
    (hf : ∀ t ∈ Icc 0 s,ContDiffAt ℝ 2 f (x+t • gradientDirection ghat))
    (hM : ∀ t ∈ Ioo 0 s,
      |iteratedDeriv 2 (fun r : ℝ => f ((x+t • gradientDirection ghat)+r • gradientDirection ghat)) 0| ≤ M) :
    f (x+s • gradientDirection ghat) ≤ f x-(5/2:ℝ)*a*s^2 := by
  have hd := gradientDirection_derivative (fderiv ℝ f x) ghat ha herr hlarge
  have ht := (abs_le.mp (line_linear_remainder hs hf hM)).2
  apply gradient_decrease ha hs hs1 hstep hd
  linarith

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem opposite_candidates_decrease (f : E → ℝ) (x q : E) {a s M : ℝ}
    (ha : 0 < a) (hs : 0 < s) (hstep : M*s ≤ a/4)
    (hQ : fderiv ℝ (fderiv ℝ f) x q q ≤ -6*a*s^2)
    (hf : ∀ v ∈ ({q,-q}:Set E),∀ t ∈ Icc (0:ℝ) 1,ContDiffAt ℝ 3 f (x+t • v))
    (hM : ∀ v ∈ ({q,-q}:Set E),∀ t ∈ Ioo (0:ℝ) 1,
      |iteratedDeriv 3 (fun r : ℝ => f ((x+t • v)+r • v)) 0| ≤ M*s^3) :
    f (x+q) ≤ f x-2*a*s^2 ∨ f (x-q) ≤ f x-2*a*s^2 := by
  have hp := line_quadratic_remainder (by norm_num : (0:ℝ)<1)
    (hf q (by simp)) (hM q (by simp))
  have hm := line_quadratic_remainder (by norm_num : (0:ℝ)<1)
    (hf (-q) (by simp)) (hM (-q) (by simp))
  simp only [one_smul,one_mul,one_pow] at hp hm
  have hneg : fderiv ℝ (fderiv ℝ f) x (-q) (-q)=fderiv ℝ (fderiv ℝ f) x q q := by
    simp only [map_neg,_root_.neg_apply,neg_neg]
  rw [hneg,map_neg,← sub_eq_add_neg] at hm
  apply opposite_decrease (L := fderiv ℝ f x q) ha hs hstep hQ
  · linarith [(abs_le.mp hp).2]
  · linarith [(abs_le.mp hm).2]

end CurrentKS.Difference

end OAI
