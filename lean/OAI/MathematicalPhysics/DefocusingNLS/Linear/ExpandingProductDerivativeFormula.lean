import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingOrderedPhysicalSymbol
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzPartialDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingMultiplication

namespace OAI

/-! # Exact Cartesian product rule for the normalized Fourier energy -/

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem expandingProduct_derivative_formula (a L : ℝ) (N : ℕ)
    (ha : 0 < a) (ha1 : a < 1) (hN : 8 < (N : ℝ)) (hL : 1 ≤ L)
    (j : Fin N → Fin 12) (q f : FourierL2) (qs fs : Finset (Fin N) → FourierL2)
    (hq : ∀ s n, expandingFourierCoefficient a N L (qs s) n =
      homogeneousPartialSymbol N j s (L⁻¹ • (n : E)) * expandingFourierCoefficient a N L q n)
    (hf : ∀ s n, expandingFourierCoefficient a N L (fs s) n =
      homogeneousPartialSymbol N j sᶜ (L⁻¹ • (n : E)) * expandingFourierCoefficient a N L f n) :
    expandingOrderedFourierEnergy a L N hL j (expandingProduct a N L ha ha1 hN hL q f) =
      ∑ s : Finset (Fin N), expandingPhysicalMassVector a N L ha ha1 hN hL
        (expandingProduct a N L ha ha1 hN hL (qs s) (fs s)) := by
  classical
  ext n
  change _ = (lp.evalCLM ℂ (fun _ : frequencyLattice => ℂ) 2 n) _
  rw [map_sum, expandingOrderedFourierEnergy_physical]
  change _ = ∑ s : Finset (Fin N), (expandingPhysicalMassVector a N L ha ha1 hN hL
    (expandingProduct a N L ha ha1 hN hL (qs s) (fs s))) n
  simp only [expandingPhysicalMassVector_apply, Complex.real_smul,
    expandingProduct_coefficient]
  push_cast
  let D : ℂ := (2 * Real.pi * L) ^ (6 : ℕ)
  have hs (s : Finset (Fin N)) : HasSum (fun m : frequencyLattice =>
      D * (expandingFourierCoefficient a N L (qs s) m *
        expandingFourierCoefficient a N L (fs s) (n - m)))
      (D * expandingProductCoefficient a N L (qs s) (fs s) n) :=
    (summable_expandingProductTerms a N L ha ha1 hN hL (qs s) (fs s) n).hasSum.mul_left D
  have hsum := hasSum_sum (s := Finset.univ) (fun s _ => hs s)
  have he (m : frequencyLattice) :
      (∑ s : Finset (Fin N), D * (expandingFourierCoefficient a N L (qs s) m *
        expandingFourierCoefficient a N L (fs s) (n - m))) =
      (D * homogeneousOrderedSymbol N j (L⁻¹ • (n : E))) *
        (expandingFourierCoefficient a N L q m * expandingFourierCoefficient a N L f (n - m)) := by
    simp_rw [hq, hf]
    have harg : L⁻¹ • (m : E) + L⁻¹ • ((n - m : frequencyLattice) : E) = L⁻¹ • (n : E) := by
      rw [← smul_add]
      congr 1
      change (m : E) + ((n : E) - (m : E)) = (n : E)
      abel
    calc
      _ = (D * ∑ s : Finset (Fin N),
          homogeneousPartialSymbol N j s (L⁻¹ • (m : E)) *
            homogeneousPartialSymbol N j sᶜ (L⁻¹ • ((n - m : frequencyLattice) : E))) *
          (expandingFourierCoefficient a N L q m * expandingFourierCoefficient a N L f (n - m)) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro s _
        ring
      _ = _ := by rw [← homogeneousOrderedSymbol_add, harg]
  have hfun : (fun m : frequencyLattice => ∑ s : Finset (Fin N),
      D * (expandingFourierCoefficient a N L (qs s) m *
        expandingFourierCoefficient a N L (fs s) (n - m))) =
      (fun m => (D * homogeneousOrderedSymbol N j (L⁻¹ • (n : E))) *
        (expandingFourierCoefficient a N L q m * expandingFourierCoefficient a N L f (n - m))) :=
    funext he
  rw [hfun] at hsum
  exact ((summable_expandingProductTerms a N L ha ha1 hN hL q f n).hasSum.mul_left
    (D * homogeneousOrderedSymbol N j (L⁻¹ • (n : E)))).unique hsum

end DefocusingNLS

end OAI
