import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialSliceGrowth
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequencePolynomialImage
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponentialOperations

namespace OAI

/-! # Polynomial image volume on subexponentially growing cubes -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem compact_polynomial_family_image_growing_sequence
    {P : Type*} [TopologicalSpace P]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n k : ℕ) (hn : 1 ≤ n)
    (f : P × (Fin (n + k) → ℝ) → (Fin n → ℝ)) (hf : Continuous f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (R : ℕ → ℝ) (hR : ∀ r, 1 ≤ R r) (hRupper : HasSubexponentialUpperBoundSeq scale R)
    (c : ℝ) (hc : 0 < c) (v₀ : Fin n → ℝ) (z₀ : Fin k → ℝ)
    (hanchor : ∀ r, Fin.append v₀ z₀ ∈ closedBall 0 (R r))
    (hdet : ∀ a ∈ S, c ≤ |(fderiv ℝ (fun v => f (a, Fin.append v z₀)) v₀).det|)
    (E : ℕ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 (R r))
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧ (∀ r, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  obtain ⟨D, p, hp, hvalue⟩ := hpoly.exists_uniform_polynomials
  have heval (i : Fin n) (x : Fin (n + k) → ℝ) :
      Continuous (fun a => MvPolynomial.eval x (p a i)) := by
    have harg : Continuous (fun a : P => (a, x)) := continuous_id.prodMk continuous_const
    have h : Continuous (fun a : P => f (a, x) i) := (continuous_apply i).comp (hf.comp harg)
    simpa only [hvalue] using h
  obtain ⟨A, hA, hbounds⟩ := uniform_polynomial_slice_derivative_bounds p D hp heval S hS
  let L := fun r => A * (R r + 3) ^ ((n + k) * D)
  have hL (r : ℕ) : 1 ≤ L r := by
    have hpow : 1 ≤ (R r + 3) ^ ((n + k) * D) := one_le_pow₀ (by linarith [hR r])
    exact one_le_mul_of_one_le_of_one_le hA hpow
  have hRadd : HasSubexponentialUpperBoundSeq scale (fun r => R r + 3) :=
    hRupper.add (sequence_subexponential_upper_const hscale 3) hscale
  have hLupper : HasSubexponentialUpperBoundSeq scale L :=
    (sequence_subexponential_upper_const hscale A).mul
      (hRadd.pow hscale (Eventually.of_forall (fun r => by linarith [hR r])) _)
      (Eventually.of_forall (fun _ => hA.trans' zero_le_one))
  let df := fun r v z => fderiv ℝ (fun w => f (b r, Fin.append w z)) v
  have hdfpoly (a : P) (v : Fin n → ℝ) (z : Fin k → ℝ) :
      fderiv ℝ (fun w => f (a, Fin.append w z)) v = polynomialSliceDifferential (p a) v z := by
    have he : (fun w i => MvPolynomial.eval (Fin.append w z) (p a i)) =
        (fun w => f (a, Fin.append w z)) := by
      funext w i
      exact hvalue a (Fin.append w z) i
    have h := hasFDerivAt_polynomialSlice (p a) v z
    rw [he] at h
    exact h.fderiv
  have hminor (r : ℕ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
      MvPolynomial.eval (Fin.append v z) (polynomialJacobianMinor (p (b r))) = (df r v z).det := by
    rw [eval_polynomialJacobianMinor, ← hdfpoly]
  have hder (r : ℕ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
      HasFDerivAt (fun w => f (b r, Fin.append w z)) (df r v z) v := by
    rw [show df r v z = polynomialSliceDifferential (p (b r)) v z from hdfpoly _ _ _]
    convert hasFDerivAt_polynomialSlice (p (b r)) v z using 1
    funext w i
    exact (hvalue (b r) (Fin.append w z) i).symm
  apply exists_subexponential_polynomial_image_sequence scale hscale rem n k (max 1 (n * (D - 1)))
    hn (le_max_left _ _) (fun r x => f (b r, x)) df
    (fun r => polynomialJacobianMinor (p (b r)))
    (fun r => (totalDegree_polynomialJacobianMinor_le _ (hp (b r))).trans (le_max_right _ _))
    hminor R L (fun _ => c) hR hL (fun _ => hc) hRupper hLupper
    (sequence_subexponential_lower_const hscale hc)
    (fun r z _ v _ => hder r v z) (fun r z hz v hv => ?_)
    (fun r z hz v w hv hw => ?_) (fun _ => Fin.append v₀ z₀) hanchor
    (fun r => by rw [hminor]; exact hdet (b r) (hb r)) E hE hER hm hmlower
  · change ‖fderiv ℝ (fun w => f (b r, Fin.append w z)) v‖ ≤ L r
    rw [hdfpoly]
    have h := (hbounds (b r) (hb r) (R r + 2) (by linarith [hR r])).1 v z hv (by linarith)
    simpa only [L, show 1 + (R r + 2) = R r + 3 by ring] using h
  · change ‖fderiv ℝ (fun u => f (b r, Fin.append u z)) v -
      fderiv ℝ (fun u => f (b r, Fin.append u z)) w‖ ≤ L r * dist v w
    rw [hdfpoly, hdfpoly]
    have h := (hbounds (b r) (hb r) (R r + 2) (by linarith [hR r])).2 v w z hv hw (by linarith)
    simpa only [L, show 1 + (R r + 2) = R r + 3 by ring] using h

end PolycyclicRecognition

end

end OAI
