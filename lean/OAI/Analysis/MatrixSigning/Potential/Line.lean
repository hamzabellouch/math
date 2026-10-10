import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Coordinates

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Scalar Filter
open scoped BigOperators Topology

variable {N : ℕ}
def line (x h : Coordinates N) (s : ℝ) : Coordinates N := fun i => x i+s*h i

@[simp] lemma line_zero (x h : Coordinates N) : line x h 0 = x := by funext i; simp [line]

lemma hasDerivAt_line_coord (x h : Coordinates N) (a : ℝ) (i : Fin N) :
    HasDerivAt (fun s => line x h s i) (h i) a := by
  have hh := (hasDerivAt_const a (x i)).add ((hasDerivAt_id a).mul_const (h i))
  simp only [zero_add,one_mul] at hh
  exact hh

lemma contDiff_line (x h : Coordinates N) {n : WithTop ℕ∞} : ContDiff ℝ n (line x h) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.add (contDiff_id.mul contDiff_const)

lemma eventually_line_interior (x h : Coordinates N) {a : ℝ}
    (hx : ∀ i, |line x h a i| < 1) : ∀ᶠ s in 𝓝 a, ∀ i, |line x h s i| < 1 := by
  apply Filter.eventually_all.mpr
  intro i
  exact ((hasDerivAt_line_coord x h a i).continuousAt.abs).eventually (eventually_lt_nhds (hx i))

def penalty (x : Coordinates N) : ℝ := ∑ i, psi (x i)

def penalty₁ (x h : Coordinates N) : ℝ := ∑ i, psi₁ (x i)*h i

def penalty₂ (x h : Coordinates N) : ℝ := ∑ i, -kappa (x i)*(h i)^2

lemma contDiffAt_penalty {x : Coordinates N} (hx : ∀ i, |x i| < 1) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n penalty x := by
  apply ContDiffAt.sum
  intro i _
  exact (contDiffAt_psi (hx i)).comp x (contDiffAt_apply ℝ ℝ i x)

lemma hasDerivAt_penalty_line (x h : Coordinates N) (a : ℝ) (hx : ∀ i, |line x h a i| < 1) :
    HasDerivAt (fun s => penalty (line x h s)) (penalty₁ (line x h a) h) a := by
  apply HasDerivAt.fun_sum
  intro i _
  exact (hasDerivAt_psi (hx i)).comp a (hasDerivAt_line_coord x h a i)

lemma hasDerivAt_penalty₁_line (x h : Coordinates N) (a : ℝ) (hx : ∀ i, |line x h a i| < 1) :
    HasDerivAt (fun s => penalty₁ (line x h s) h) (penalty₂ (line x h a) h) a := by
  apply HasDerivAt.fun_sum
  intro i _
  convert ((hasDerivAt_psi₁ (hx i)).comp a (hasDerivAt_line_coord x h a i)).mul_const (h i) using 1 <;> try rfl
  ring

lemma penalty_line_first (x h : Coordinates N) (hx : ∀ i, |x i| < 1) :
    deriv (fun s => penalty (line x h s)) 0 = penalty₁ x h := by
  simpa only [line_zero] using (hasDerivAt_penalty_line x h 0 (by simpa only [line_zero] using hx)).deriv

lemma penalty_line_second (x h : Coordinates N) (hx : ∀ i, |x i| < 1) :
    deriv (deriv (fun s => penalty (line x h s))) 0 = penalty₂ x h := by
  have he : deriv (fun s => penalty (line x h s)) =ᶠ[𝓝 (0 : ℝ)] fun s => penalty₁ (line x h s) h := by
    filter_upwards [eventually_line_interior x h (a := 0) (by simpa only [line_zero] using hx)] with s hs
    exact (hasDerivAt_penalty_line x h s hs).deriv
  rw [he.deriv_eq]
  simpa only [line_zero] using (hasDerivAt_penalty₁_line x h 0 (by simpa only [line_zero] using hx)).deriv

lemma second_deriv_add {f g : ℝ → ℝ} {a : ℝ} (hf : ContDiffAt ℝ 2 f a) (hg : ContDiffAt ℝ 2 g a) :
    deriv (deriv (fun s => f s+g s)) a = deriv (deriv f) a+deriv (deriv g) a := by
  simpa only [show (2 : ℕ) = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using iteratedDeriv_fun_add hf hg

lemma second_deriv_const_mul (c : ℝ) (f : ℝ → ℝ) (a : ℝ) :
    deriv (deriv (fun s => c*f s)) a = c*deriv (deriv f) a := by
  simpa only [show (2 : ℕ) = 1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using
    (iteratedDeriv_const_mul_field (n := 2) (x := a) c f)

end CurrentKS.State

end

end OAI
