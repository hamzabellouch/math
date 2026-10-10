import Mathlib
import OAI.Analysis.CoulombIonization.Variational.OrbitalPole

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open scoped BigOperators

namespace CoulombAtom
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma occupation_pair_sum_complex (p : ι → ℝ) (f : ι → ι → ℂ) (hf : ∀ i, f i i = 0) :
    (∑ m : ι → Bool, (occupationWeight p m : ℂ) *
      ∑ i, ∑ j, if m i && m j then f i j else 0) =
      ∑ i, ∑ j, (p i : ℂ)*(p j : ℂ)*f i j := by
  have hre (b : Bool) (z : ℂ) : (if b then z else 0).re = if b then z.re else 0 := by
    cases b <;> rfl
  have him (b : Bool) (z : ℂ) : (if b then z else 0).im = if b then z.im else 0 := by
    cases b <;> rfl
  apply Complex.ext
  · simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_mul,sub_zero,hre,Complex.mul_im,add_zero] using
      occupation_pair_sum p (fun i j => (f i j).re) (fun i => by rw [hf i]; rfl)
  · simpa only [Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_mul,zero_add,add_zero,him,Complex.mul_re,sub_zero] using
      occupation_pair_sum p (fun i j => (f i j).im) (fun i => by rw [hf i]; rfl)

end CoulombAtom

end

end OAI
