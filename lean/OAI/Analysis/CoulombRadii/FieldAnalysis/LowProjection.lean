import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.TsumFixed

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
section LowProjection
variable {A B ι : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SigmaFinite μ] [SigmaFinite ν]
    (v : ι → A → ℂ) (hv : ∀ i, MemLp (v i) 2 μ)

noncomputable def lowProjection (s : Finset ι) (f : B × A → ℂ) (z : B × A) : ℂ :=
  ∑ i ∈ s, fiberContract (μ := μ) (v i) f z.1 * v i z.2

include hv in
lemma lowProjection_memLp (s : Finset ι) {f : B × A → ℂ} (hf : MemLp f 2 (ν.prod μ)) :
    MemLp (lowProjection (μ := μ) v s f) 2 (ν.prod μ) :=
  memLp_finsetSum s (fun i _ => tensorPair_memLp (fiberContract_memLp (hv i) hf) (hv i))

include hv in
lemma lowProjection_tail_memLp (s : Finset ι) {f : B × A → ℂ}
    (hf : MemLp f 2 (ν.prod μ)) (x : A) :
    MemLp (fun y => lowProjection (μ := μ) v s f (y,x)) 2 ν :=
  memLp_finsetSum s (fun i _ => (fiberContract_memLp (hv i) hf).mul_const (v i x))

include hv in
lemma lowProjection_eq_contract (s : Finset ι) {f : B × A → ℂ}
    (hf : MemLp f 2 (ν.prod μ)) (x : A) :
    (fun y => lowProjection (μ := μ) v s f (y,x)) =ᵐ[ν]
      fiberContract (μ := μ) (lowOrbital v s x) f := by
  filter_upwards [memLp_fiber_ae hf] with y hy
  unfold lowProjection fiberContract lowOrbital
  rw [show (fun a => star (∑ i ∈ s, star (v i x) * v i a) * f (y,a)) =
      (fun a => ∑ i ∈ s, (star (v i a) * f (y,a)) * v i x) from by
    funext a
    simp only [star_sum, star_mul, star_star, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [integral_finsetSum s (fun i _ => (integrable_star_mul (hv i) hy).mul_const (v i x))]
  simp only [integral_mul_const]

end LowProjection
end Coulomb

end
end

end OAI
