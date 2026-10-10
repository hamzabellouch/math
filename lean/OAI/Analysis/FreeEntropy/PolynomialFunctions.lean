import OAI.Analysis.FreeEntropy.GaussianMvStein

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace FiniteEntropySeparation
variable {ι : Type u1} [Fintype ι] [DecidableEq ι]
 def IsRealPolynomial (f : (ι → ℝ) → ℝ) : Prop := ∃ P : MvPolynomial ι ℝ, f = fun x => MvPolynomial.eval x P
 theorem mvPolynomial_hasCoordinateDeriv {ι : Type u1} [Fintype ι] [DecidableEq ι] (P : MvPolynomial ι ℝ) (i : ι) (x : ι → ℝ) :
    HasDerivAt (fun t => MvPolynomial.eval (Function.update x i t) P)
      (MvPolynomial.eval x (MvPolynomial.pderiv i P)) (x i) := by
  induction P using MvPolynomial.induction_on with
  | C r => simpa using hasDerivAt_const (x i) r
  | add P Q hP hQ =>
    convert hP.add hQ using 1 <;> try rfl
    · funext t; simp
    · simp
  | mul_X P j hP =>
    by_cases h : j=i
    · subst j
      convert hP.mul (hasDerivAt_id (x i)) using 1 <;> try rfl
      · funext t; simp
      · simp [mul_comm, add_comm]
    · convert hP.mul_const (x j) using 1 <;> try rfl
      · funext t; simp [Function.update_of_ne h]
      · simp [MvPolynomial.pderiv_X_of_ne h, mul_comm]
 namespace IsRealPolynomial
 theorem const {ι : Type u1} [Fintype ι] [DecidableEq ι] (r : ℝ) : IsRealPolynomial (fun _ : ι → ℝ => r) := ⟨MvPolynomial.C r, by simp⟩
 theorem coord {ι : Type u1} [Fintype ι] [DecidableEq ι] (i : ι) : IsRealPolynomial (fun x : ι → ℝ => x i) := ⟨MvPolynomial.X i, by simp⟩
 theorem add {ι : Type u1} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (hg : IsRealPolynomial g) :
    IsRealPolynomial (fun x => f x+g x) := by
  obtain ⟨P,rfl⟩ := hf; obtain ⟨Q,rfl⟩ := hg
  exact ⟨P+Q,by simp⟩
 theorem sub {ι : Type u1} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (hg : IsRealPolynomial g) :
    IsRealPolynomial (fun x => f x-g x) := by
  obtain ⟨P,rfl⟩ := hf; obtain ⟨Q,rfl⟩ := hg
  exact ⟨P-Q,by simp⟩
 theorem mul {ι : Type u1} [Fintype ι] [DecidableEq ι] {f g : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (hg : IsRealPolynomial g) :
    IsRealPolynomial (fun x => f x*g x) := by
  obtain ⟨P,rfl⟩ := hf; obtain ⟨Q,rfl⟩ := hg
  exact ⟨P*Q,by simp⟩
 theorem const_mul {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (r : ℝ) :
    IsRealPolynomial (fun x => r*f x) := (const r).mul hf
 theorem mul_const {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (r : ℝ) :
    IsRealPolynomial (fun x => f x*r) := hf.mul (const r)
 theorem neg {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) : IsRealPolynomial (fun x => -f x) := by
  simpa using (const 0).sub hf
 theorem pow {ι : Type u1} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (n : ℕ) : IsRealPolynomial (fun x => f x^n) := by
  obtain ⟨P,rfl⟩ := hf
  exact ⟨P^n,by simp⟩
 theorem finset_sum {κ : Type u2} (s : Finset κ) {f : κ → (ι → ℝ) → ℝ}
    (hf : ∀ k ∈ s, IsRealPolynomial (f k)) : IsRealPolynomial (fun x => ∑ k ∈ s, f k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (ι := ι) 0
  | @insert k s hk ih =>
    simpa [hk] using (hf k (mem_insert_self _ _)).add (ih (fun j hj => hf j (mem_insert_of_mem hj)))
 theorem continuous {ι : Type u1} [Fintype ι] [DecidableEq ι] {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) : Continuous f := by
  obtain ⟨P,rfl⟩ := hf
  exact P.continuous_eval
 theorem integrable {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) : Integrable f (productGaussian ι) := by
  obtain ⟨P,rfl⟩ := hf
  exact gaussian_mvPolynomial_integrable P
 theorem derivative {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (i : ι) :
    IsRealPolynomial (coordinateDerivative f i) := by
  obtain ⟨P,rfl⟩ := hf
  refine ⟨MvPolynomial.pderiv i P, ?_⟩
  funext x
  exact (mvPolynomial_hasCoordinateDeriv P i x).deriv
 theorem hasDerivAt {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (i : ι) (x : ι → ℝ) :
    HasDerivAt (fun t => f (Function.update x i t)) (coordinateDerivative f i x) (x i) := by
  obtain ⟨P,rfl⟩ := hf
  have hd := mvPolynomial_hasCoordinateDeriv P i x
  exact hd.congr_deriv hd.deriv.symm
 theorem stein {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) (i : ι) :
    (∫ x, x i*f x ∂productGaussian ι) = ∫ x, coordinateDerivative f i x ∂productGaussian ι := by
  obtain ⟨P,rfl⟩ := hf
  exact gaussian_mvPolynomial_stein P i
 theorem poincare {f : (ι → ℝ) → ℝ} (hf : IsRealPolynomial f) :
    (∫ x, (f x-∫ y, f y ∂productGaussian ι)^2 ∂productGaussian ι) ≤
      ∑ i, ∫ x, (coordinateDerivative f i x)^2 ∂productGaussian ι := by
  obtain ⟨P,rfl⟩ := hf
  exact gaussian_mvPolynomial_poincare P
 end IsRealPolynomial
end FiniteEntropySeparation

end

end OAI
