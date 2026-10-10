import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothPolynomialFamilyImage
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SequencePolynomialImage

namespace OAI

/-! # Polynomial image volume along the actual profile-scale sequence -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem compact_smooth_polynomial_family_image_sequence
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (scale : ℕ → ℝ) (hscale : Tendsto scale atTop atTop)
    (rem : RemezPolynomialInput) (n k : ℕ) (hn : 1 ≤ n)
    (f : P × (Fin (n + k) → ℝ) → (Fin n → ℝ))
    (hf : ContDiff ℝ 2 f)
    (hpoly : HasPolynomialCoordinates (fun a x => f (a, x)))
    (S : Set P) (hS : IsCompact S) (b : ℕ → P) (hb : ∀ r, b r ∈ S)
    (R c : ℝ) (hR : 1 ≤ R) (hc : 0 < c)
    (v₀ : Fin n → ℝ) (z₀ : Fin k → ℝ)
    (hanchor : Fin.append v₀ z₀ ∈ closedBall 0 R)
    (hdet : ∀ a ∈ S, c ≤ |(fderiv ℝ (fun v => f (a, Fin.append v z₀)) v₀).det|)
    (E : ℕ → Set (Fin (n + k) → ℝ)) (hE : ∀ r, MeasurableSet (E r))
    (hER : ∀ r, E r ⊆ closedBall 0 R)
    (hm : ∀ r, 0 < (volume (E r)).toReal)
    (hmlower : HasSubexponentialLowerBoundSeq scale (fun r => (volume (E r)).toReal)) :
    ∃ C : ℕ → Set (Fin n → ℝ),
      (∀ r, IsCompact (C r)) ∧ (∀ r, C r ⊆ (fun x => f (b r, x)) '' E r) ∧
      HasSubexponentialLowerBoundSeq scale (fun r => (volume (C r)).toReal) := by
  obtain ⟨D, p, hp, hvalue⟩ := hpoly.exists_uniform_polynomials
  let F : (P × (Fin k → ℝ)) × (Fin n → ℝ) → (Fin n → ℝ) :=
    fun x => f (x.1.1, Fin.append x.2 x.1.2)
  have hF : ContDiff ℝ 2 F := hf.comp
    (contDiff_fst.fst.prodMk ((contDiff_finAppend n k).comp (contDiff_snd.prodMk contDiff_fst.snd)))
  obtain ⟨L, hL, hbound, hosc⟩ := compact_family_derivative_bounds F hF
    (hS.prod (isCompact_closedBall (0 : Fin k → ℝ) R)) (R + 2)
  let df := fun r v z => fderiv ℝ (fun w => f (b r, Fin.append w z)) v
  have hdfpoly (a : P) (v : Fin n → ℝ) (z : Fin k → ℝ) :
      fderiv ℝ (fun w => f (a, Fin.append w z)) v = polynomialSliceDifferential (p a) v z := by
    have he : (fun w i => MvPolynomial.eval (Fin.append w z) (p a i)) =
        (fun w => f (a, Fin.append w z)) := by
      funext w i
      exact hvalue a (Fin.append w z) i
    have hh := hasFDerivAt_polynomialSlice (p a) v z
    rw [he] at hh
    exact hh.fderiv
  have hminor (r : ℕ) (v : Fin n → ℝ) (z : Fin k → ℝ) :
      MvPolynomial.eval (Fin.append v z) (polynomialJacobianMinor (p (b r))) = (df r v z).det := by
    rw [eval_polynomialJacobianMinor, ← hdfpoly]
  apply exists_subexponential_polynomial_image_sequence scale hscale rem n k (max 1 (n * (D - 1))) hn (le_max_left _ _)
    (fun r x => f (b r, x)) df (fun r => polynomialJacobianMinor (p (b r)))
    (fun r => (totalDegree_polynomialJacobianMinor_le _ (hp (b r))).trans (le_max_right _ _))
    hminor (fun _ => R) (fun _ => L) (fun _ => c) (fun _ => hR) (fun _ => hL) (fun _ => hc)
    (sequence_subexponential_upper_const hscale R) (sequence_subexponential_upper_const hscale L) (sequence_subexponential_lower_const hscale hc)
    (fun r z _ v _ => ?_) (fun r z hz v hv => ?_) (fun r z hz v w hv hw => ?_)
    (fun _ => Fin.append v₀ z₀) (fun _ => hanchor)
    (fun r => by rw [hminor]; exact hdet (b r) (hb r)) E hE hER hm hmlower
  · exact ((hF.comp ((contDiff_const (c := (b r, z))).prodMk contDiff_id)).differentiable
      (by norm_num) v).hasFDerivAt
  · exact hbound (b r, z) ⟨hb r, by simpa using hz⟩ v hv
  · exact hosc (b r, z) ⟨hb r, by simpa using hz⟩ v w hv hw

end PolycyclicRecognition

end

end OAI
