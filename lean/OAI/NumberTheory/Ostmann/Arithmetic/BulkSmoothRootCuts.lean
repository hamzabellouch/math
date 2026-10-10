import OAI.NumberTheory.Ostmann.Arithmetic.BulkSmoothFactors
import OAI.NumberTheory.Ostmann.Arithmetic.SmoothPrimeAllRoots

namespace OAI

/-! # A complete finite root bound for the bulk-coordinate smooth factor -/

namespace Ostmann
open scoped Classical BigOperators SchwartzMap

/-- All cuts are constructed derivative roots of actual bulk polynomials.
Their number depends on degree, never on coefficient height or prime values. -/
theorem bulkSmoothFactors_root_cuts {σ : Type*} (value : σ → ℝ) (i : σ)
    {n : ℕ} (T : MovingSlotData σ n) (L R : Polynomial ℝ) (ψ : 𝓢(ℝ, ℂ))
    (X lo hi : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi) (φ : ℝ → ℝ)
    (G : ℕ → ℝ) (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hφ : ∀ x, |φ x| ≤ B) (hlip : ∀ x y, |φ x - φ y| ≤ D * |x - y|)
    (d r e : ℕ) (hsize : T.SizeLE d) (hregular : T.RegularLengthLE r)
    (hL : L.natDegree ≤ e) (hR : R.natDegree ≤ e) :
    ∃ S : Finset ℝ,
      S.card ≤ (2 ^ n + (T.bulkNodePolynomials value i L R).length) * (2 * (n * d + e) + r) ∧
      ∀ j z, z ∈ (bulkSmoothFactors value i T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip j).polynomial.derivative.roots → z ∈ S := by
  let F := bulkSmoothFactors value i T L R ψ X lo hi hlo hhi φ G B D hB hD hφ hlip
  let H := 2 * (n * d + e) + r
  let S := polynomialRootCuts (fun j => (F j).polynomial.derivative)
  have hd (j) : (F j).polynomial.natDegree ≤ H := by
    refine Fin.addCases ?_ ?_ j
    · intro j
      simp only [F, bulkSmoothFactors, Fin.append_left]
      exact bulkFourierFactors_degree value i T L R ψ X lo hi hlo hhi d r e hsize hregular hL hR j
    · intro j
      simp only [F, bulkSmoothFactors, Fin.append_right]
      have h := bulkNodeFactors_degree value i T L R φ G B D hB hD hφ hlip d e hsize hL hR j
      exact h.trans (by dsimp only [H]; omega)
  have hdr (j) : (F j).polynomial.derivative.natDegree ≤ H :=
    (Polynomial.natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans (hd j))
  refine ⟨S, ?_, ?_⟩
  · apply (polynomialRootCuts_card _).trans
    calc
      _ ≤ ∑ _j, H := Finset.sum_le_sum (fun j _ => hdr j)
      _ = _ := by simp [H]
  · intro j z hz
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Multiset.mem_toFinset.mpr hz⟩

end Ostmann

end OAI
