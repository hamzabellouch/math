import OAI.Geometry.SurfaceImmersion.Correction.PolynomialLocalMeanProfile
import OAI.Geometry.SurfaceImmersion.Correction.FiniteMeanThreshold

namespace OAI

/-! Polynomial growth of the actual finite mean iteration and of the
finite value budget appearing in its explicit smallness threshold. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma HasPolynomialBound.nonneg {f : ℝ → ℝ} (hf : HasPolynomialBound f)
    {x : ℝ} (hx : 1 ≤ x) : 0 ≤ f x := by
  obtain ⟨_,_,_,h⟩ := hf
  exact (h x hx).1

end ClosedSurfaceR4.RealModes

namespace ClosedSurfaceR4.PhaseMean
open RealModes FiniteMean

theorem polynomialMeanProfile_growth (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G : ℕ → ℝ → ℝ) (hC : ∀ m, 0 ≤ C m) (hG : ∀ m, HasPolynomialBound (G m))
    (m : ℕ) {H : ℝ → ℝ} (hH : HasPolynomialBound H) :
    HasPolynomialBound (fun x => polynomialMeanProfile p C (fun r => G r x) m (H x)) :=
  (polynomialBound_const (hC m)).mul
    (((hG m).add ((polynomialBound_const zero_le_one).max hH)).pow (p m))

def polynomialMeanSize (L : ℕ) (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G H : ℕ → ℝ → ℝ) (j m : ℕ) (x : ℝ) : ℝ :=
  sizeBound L (fun r => H r x) (polynomialMeanProfile p C (fun r => G r x)) j m

def polynomialMeanDifference (L : ℕ) (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G H : ℕ → ℝ → ℝ) (j m : ℕ) (x : ℝ) : ℝ :=
  differenceBound L (fun r => H r x)
    (polynomialMeanProfile p C (fun r => G r x)) (polynomialMeanProfile p C (fun r => G r x)) j m

theorem polynomialMeanSize_growth (L : ℕ) (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G H : ℕ → ℝ → ℝ) (hC : ∀ m, 0 ≤ C m)
    (hG : ∀ m, HasPolynomialBound (G m)) (hH : ∀ m, HasPolynomialBound (H m))
    (j m : ℕ) : HasPolynomialBound (polynomialMeanSize L p C G H j m) := by
  induction j generalizing m with
  | zero => exact hH m
  | succ j ih =>
    exact (hH m).add (polynomialMeanProfile_growth p C G hC hG m (ih (m+L)))

theorem polynomialMeanDifference_growth (L : ℕ) (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G H : ℕ → ℝ → ℝ) (hC : ∀ m, 0 ≤ C m)
    (hG : ∀ m, HasPolynomialBound (G m)) (hH : ∀ m, HasPolynomialBound (H m))
    (j m : ℕ) : HasPolynomialBound (polynomialMeanDifference L p C G H j m) := by
  induction j generalizing m with
  | zero => exact polynomialMeanProfile_growth p C G hC hG m (hH (m+L))
  | succ j ih =>
    exact (polynomialMeanProfile_growth p C G hC hG m
      ((polynomialMeanSize_growth L p C G H hC hG hH (j+1) (m+L)).max
        (polynomialMeanSize_growth L p C G H hC hG hH j (m+L)))).mul (ih (m+L))

/-- A polynomial upper bound for the finite quantity controlling the
radius of the mean iteration; it is uniform in the iteration index. -/
theorem polynomialMean_threshold_budget (L : ℕ) (p : ℕ → ℕ) (C : ℕ → ℝ)
    (G H : ℕ → ℝ → ℝ) (hC : ∀ m, 0 ≤ C m)
    (hG : ∀ m, HasPolynomialBound (G m)) (hH : ∀ m, HasPolynomialBound (H m)) (n : ℕ) :
    ∃ d : ℕ, ∃ A : ℝ, 1 ≤ A ∧ ∀ x : ℝ, 1 ≤ x → ∀ j ≤ n,
      polynomialMeanProfile p C (fun r => G r x) 0 (polynomialMeanSize L p C G H j L x) ≤ A*x^d := by
  let f := fun j x => polynomialMeanProfile p C (fun r => G r x) 0
    (polynomialMeanSize L p C G H j L x)
  have hf (j : ℕ) : HasPolynomialBound (f j) :=
    polynomialMeanProfile_growth p C G hC hG 0 (polynomialMeanSize_growth L p C G H hC hG hH j L)
  obtain ⟨d,A,hA,hsum⟩ := HasPolynomialBound.sum (Finset.range (n+1)) f (fun j _ => hf j)
  refine ⟨d,A,hA,?_⟩
  intro x hx j hj
  exact (Finset.single_le_sum (fun i _ => (hf i).nonneg hx)
    (Finset.mem_range.mpr (by omega : j < n+1))).trans (hsum x hx).2

end ClosedSurfaceR4.PhaseMean

end

end OAI
