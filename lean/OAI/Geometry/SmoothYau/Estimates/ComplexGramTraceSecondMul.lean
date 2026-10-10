import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.ProductSphereFstPower

namespace OAI

noncomputable section
open Set Filter Function Module
open scoped Topology ContDiff InnerProductSpace Matrix
namespace YauCounterexamples
section SecondTraceProduct
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [DecidableEq ι]
lemma complexGramTrace_second_mul (e : Basis ι ℝ E) {f g : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (x : E) :
    complexGramTrace e (fun v w => fderiv ℝ
      (fun y => fderiv ℝ (fun z => f z*g z) y w) x v) =
      complexGramTrace e (fun v w => fderiv ℝ (fun y => fderiv ℝ f y w) x v)*g x +
      2*complexGramTrace e (fun v w => fderiv ℝ f x w*fderiv ℝ g x v) +
      f x*complexGramTrace e (fun v w => fderiv ℝ (fun y => fderiv ℝ g y w) x v) := by
  simp_rw [second_mul_complex hf hg]
  rw [complexGramTrace_add,complexGramTrace_add,complexGramTrace_add,
    complexGramTrace_mul_right,complexGramTrace_mul_left]
  have hflip := complexGramTrace_flip e (fun v w => fderiv ℝ f x w*fderiv ℝ g x v)
  change complexGramTrace e (fun v w => fderiv ℝ f x v*fderiv ℝ g x w) = _ at hflip
  rw [hflip]
  ring
end SecondTraceProduct
variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ B]
  {n m : ℕ} [Fact (Module.finrank ℝ A = n+1)] [Fact (Module.finrank ℝ B = m+1)]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] in
lemma productSphere_power_mixed_trace (e : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (p : Metric.sphere (0:A) 1) (q : Metric.sphere (0:B) 1) (a b : A) (c d : B) (k l : ℕ) :
    complexGramTrace e (fun v w =>
      fderiv ℝ (productSphere_fstPower p (planarLinear a b) k) 0 w*
      fderiv ℝ (productSphere_sndPower q (planarLinear c d) l) 0 v) = 0 := by
  simp_rw [productSphere_fstPower_first,productSphere_sndPower_first]
  calc
    _ = ((k:ℂ)*(planarLinear a b p)^(k-1)*((l:ℂ)*(planarLinear c d q)^(l-1)))*
      (∑ i, ∑ j, ((Matrix.gram ℝ e)⁻¹ i j:ℂ)*
        planarLinear a b (unitSphereFrame p (e j).fst)*
        planarLinear c d (unitSphereFrame q (e i).snd)) := by
      unfold complexGramTrace
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := by rw [productSphere_mixed_planar_contraction]; ring
omit [FiniteDimensional ℝ A] [FiniteDimensional ℝ B] in
lemma productSphere_power_trace (e : Basis ι ℝ (WithLp 2 (Euclidean n×Euclidean m)))
    (p : Metric.sphere (0:A) 1) (q : Metric.sphere (0:B) 1) (a b : A) (c d : B)
    (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l)
    (ha : inner ℝ a a = 1) (hb : inner ℝ b b = 1) (hab : inner ℝ a b = 0)
    (hc : inner ℝ c c = 1) (hd : inner ℝ d d = 1) (hcd : inner ℝ c d = 0) :
    complexGramTrace e (fun v w => fderiv ℝ (fun y => fderiv ℝ
      (fun z => productSphere_fstPower p (planarLinear a b) k z*
        productSphere_sndPower q (planarLinear c d) l z) y w) 0 v) =
      -((k:ℂ)*((k:ℂ)+(n:ℂ)-1)+(l:ℂ)*((l:ℂ)+(m:ℂ)-1))*
        (planarLinear a b p)^k*(planarLinear c d q)^l := by
  rw [complexGramTrace_second_mul (e:=e) (productSphere_fstPower_smooth _ _ _)
    (productSphere_sndPower_smooth _ _ _)]
  rw [productSphere_power_mixed_trace,productSphere_fstPower_trace e p a b k hk ha hb hab,
    productSphere_sndPower_trace e q c d l hl hc hd hcd,
    productSphere_fstPower_zero,productSphere_sndPower_zero]
  ring
end YauCounterexamples
end

end OAI
