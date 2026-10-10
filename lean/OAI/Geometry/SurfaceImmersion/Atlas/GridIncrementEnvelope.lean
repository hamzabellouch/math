import OAI.Geometry.SurfaceImmersion.Correction.PolynomialBudgetAlgebra

namespace OAI

/-! Polynomial envelopes for the full free/forced grid increment. -/
noncomputable section
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes

def gridInteractionCount (n : ℝ) : ℝ := n+2*n^2

lemma gridInteractionCount_nonneg {n : ℝ} (hn : 0 ≤ n) :
    0 ≤ gridInteractionCount n := by unfold gridInteractionCount; positivity

lemma gridInteractionCount_mono {n N : ℝ} (hn : 0 ≤ n) (h : n ≤ N) :
    gridInteractionCount n ≤ gridInteractionCount N := by
  unfold gridInteractionCount
  gcongr

def gridIncrementSize (α β : ℕ → ℝ → ℝ) (H : ℝ → ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  α m x*H x+β m x*gridInteractionCount (H x)

def gridIncrementError (α β γ ζ T : ℕ → ℝ → ℝ) (D : ℕ → ℝ) (H : ℝ → ℝ)
    (m : ℕ) (x : ℝ) : ℝ :=
  ζ m x*H x+γ m x*gridInteractionCount (H x)+T m x+
    D m*(2*(α (m+1) x*H x)*(β (m+1) x*gridInteractionCount (H x))+
      (β (m+1) x*gridInteractionCount (H x))^2)

lemma gridInteractionCount_polynomial {H : ℝ → ℝ} (hH : HasPolynomialBound H) :
    HasPolynomialBound (fun x => gridInteractionCount (H x)) :=
  hH.add ((polynomialBound_const (by norm_num : (0:ℝ) ≤ 2)).mul (hH.pow 2))

lemma gridIncrementSize_polynomial (α β : ℕ → ℝ → ℝ) (H : ℝ → ℝ)
    (hα : ∀ m, HasPolynomialBound (α m)) (hβ : ∀ m, HasPolynomialBound (β m))
    (hH : HasPolynomialBound H) (m : ℕ) :
    HasPolynomialBound (gridIncrementSize α β H m) :=
  ((hα m).mul hH).add ((hβ m).mul (gridInteractionCount_polynomial hH))

lemma gridIncrementError_polynomial (α β γ ζ T : ℕ → ℝ → ℝ) (D : ℕ → ℝ) (H : ℝ → ℝ)
    (hα : ∀ m, HasPolynomialBound (α m)) (hβ : ∀ m, HasPolynomialBound (β m))
    (hγ : ∀ m, HasPolynomialBound (γ m)) (hζ : ∀ m, HasPolynomialBound (ζ m))
    (hT : ∀ m, HasPolynomialBound (T m)) (hD : ∀ m, 0 ≤ D m)
    (hH : HasPolynomialBound H) (m : ℕ) :
    HasPolynomialBound (gridIncrementError α β γ ζ T D H m) := by
  have hN := gridInteractionCount_polynomial hH
  exact ((((hζ m).mul hH).add ((hγ m).mul hN)).add (hT m)).add
    ((polynomialBound_const (hD m)).mul
      ((((polynomialBound_const (by norm_num : (0:ℝ) ≤ 2)).mul ((hα (m+1)).mul hH)).mul
        ((hβ (m+1)).mul hN)).add (((hβ (m+1)).mul hN).pow 2)))

lemma gridIncrementSize_bound {a b n N δ τ : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 ≤ n) (hnN : n ≤ N)
    (hδ : 0 ≤ δ) (hτ : 0 ≤ τ) :
    (a*n+b*gridInteractionCount n)*(δ*τ) ≤
      (a*N+b*gridInteractionCount N)*(δ*τ) := by
  apply mul_le_mul_of_nonneg_right _ (mul_nonneg hδ hτ)
  exact add_le_add (mul_le_mul_of_nonneg_left hnN ha)
    (mul_le_mul_of_nonneg_left (gridInteractionCount_mono hn hnN) hb)

lemma gridIncrementError_bound {a b c d t D n N δ τ η : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ht : 0 ≤ t) (hD : 0 ≤ D) (hn : 0 ≤ n) (hnN : n ≤ N)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hδτ : δ ≤ τ) (hτ1 : τ ≤ 1) (hη : 0 ≤ η) :
    η*(d*n*(δ*τ)+c*gridInteractionCount n*δ^2)+δ^2*t*η+
      D*(2*(a*n)*(b*gridInteractionCount n)+(b*gridInteractionCount n)^2)*(δ^3/τ) ≤
    (d*N+c*gridInteractionCount N+t+
      D*(2*(a*N)*(b*gridInteractionCount N)+(b*gridInteractionCount N)^2)) *
      (δ*η+δ^3/τ) := by
  have hN : 0 ≤ N := hn.trans hnN
  have hnq := gridInteractionCount_nonneg hn
  have hNq := gridInteractionCount_nonneg hN
  have hq := gridInteractionCount_mono hn hnN
  have hδ1 : δ ≤ 1 := hδτ.trans hτ1
  have hdt : δ*τ ≤ δ := mul_le_of_le_one_right hδ hτ1
  have hdsq : δ^2 ≤ δ := by nlinarith
  have hdn : d*n ≤ d*N := mul_le_mul_of_nonneg_left hnN hd
  have hcq : c*gridInteractionCount n ≤ c*gridInteractionCount N :=
    mul_le_mul_of_nonneg_left hq hc
  have hfirst : d*n*(δ*τ)+c*gridInteractionCount n*δ^2+δ^2*t ≤
      (d*N+c*gridInteractionCount N+t)*δ := by
    calc
      _ ≤ (d*N)*δ+(c*gridInteractionCount N)*δ+δ*t := by
        apply add_le_add
        · exact add_le_add (mul_le_mul hdn hdt (mul_nonneg hδ hτ.le) (mul_nonneg hd hN))
            (mul_le_mul hcq hdsq (sq_nonneg δ) (mul_nonneg hc hNq))
        · exact mul_le_mul_of_nonneg_right hdsq ht
      _ = _ := by ring
  have han : a*n ≤ a*N := mul_le_mul_of_nonneg_left hnN ha
  have hbn : b*gridInteractionCount n ≤ b*gridInteractionCount N :=
    mul_le_mul_of_nonneg_left hq hb
  have hcubic : 2*(a*n)*(b*gridInteractionCount n)+(b*gridInteractionCount n)^2 ≤
      2*(a*N)*(b*gridInteractionCount N)+(b*gridInteractionCount N)^2 := by
    gcongr
  let A := d*N+c*gridInteractionCount N+t
  let B := D*(2*(a*N)*(b*gridInteractionCount N)+(b*gridInteractionCount N)^2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hv : 0 ≤ δ^3/τ := div_nonneg (pow_nonneg hδ 3) hτ.le
  calc
    _ = η*(d*n*(δ*τ)+c*gridInteractionCount n*δ^2+δ^2*t)+
        D*(2*(a*n)*(b*gridInteractionCount n)+(b*gridInteractionCount n)^2)*(δ^3/τ) := by ring
    _ ≤ η*(A*δ)+B*(δ^3/τ) := add_le_add
      (mul_le_mul_of_nonneg_left hfirst hη)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcubic hD) hv)
    _ = A*(δ*η)+B*(δ^3/τ) := by ring
    _ ≤ A*(δ*η+δ^3/τ)+B*(δ*η+δ^3/τ) := add_le_add
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hv) hA)
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (mul_nonneg hδ hη)) hB)
    _ = _ := by dsimp [A,B]; ring

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
