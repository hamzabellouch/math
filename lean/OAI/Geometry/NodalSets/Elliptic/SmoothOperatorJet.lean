import OAI.Geometry.NodalSets.Elliptic.SmoothJet
import OAI.Geometry.NodalSets.Waves.WaveEstimates

namespace OAI

namespace Yau.Jets
open MvPolynomial
open scoped ContDiff
noncomputable section

lemma smoothSecondOrder_contDiff {g : Fin 4 → Fin 4 → Coord → ℂ}
    {b : Fin 4 → Coord → ℂ} {f : Coord → ℂ}
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hb : ∀ i, ContDiff ℝ ∞ (b i))
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (smoothSecondOrder g b f) := by
  apply ContDiff.add
  · apply ContDiff.sum
    intro i _
    apply ContDiff.sum
    intro j _
    exact (hg i j).mul (coordPartial_contDiff (coordPartial_contDiff hf j) i)
  · apply ContDiff.sum
    intro i _
    exact (hb i).mul (coordPartial_contDiff hf i)

lemma smoothEikonal_contDiff {g : Fin 4 → Fin 4 → Coord → ℂ} {f : Coord → ℂ}
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (smoothEikonal g f) := by
  apply ContDiff.add _ contDiff_const
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact ((hg i j).mul (coordPartial_contDiff hf i)).mul (coordPartial_contDiff hf j)

theorem flat_secondOrder_coefficients {n : ℕ}
    {g G : Fin 4 → Fin 4 → Coord → ℂ} {b B : Fin 4 → Coord → ℂ} {f : Coord → ℂ}
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hG : ∀ i j, ContDiff ℝ ∞ (G i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (hB : ∀ i, ContDiff ℝ ∞ (B i))
    (hf : ContDiff ℝ ∞ f)
    (hgj : ∀ i j, FlatAt n (fun x ↦ g i j x - G i j x) 0)
    (hbj : ∀ i, FlatAt n (fun x ↦ b i x - B i x) 0) :
    FlatAt n (fun x ↦ smoothSecondOrder g b f x - smoothSecondOrder G B f x) 0 := by
  have he : (fun x ↦ smoothSecondOrder g b f x - smoothSecondOrder G B f x) =
      (fun x ↦ (∑ i, ∑ j, (g i j x - G i j x) * coordPartial i (coordPartial j f) x) +
        ∑ i, (b i x - B i x) * coordPartial i f x) := by
    funext x
    simp only [smoothSecondOrder, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he]
  apply FlatAt.add
  · exact ContDiff.sum (fun i _ ↦ ContDiff.sum (fun j _ ↦
      ((hg i j).sub (hG i j)).mul (coordPartial_contDiff (coordPartial_contDiff hf j) i)))
  · exact ContDiff.sum (fun i _ ↦ ((hb i).sub (hB i)).mul (coordPartial_contDiff hf i))
  · apply FlatAt.sum Finset.univ
    · intro i _
      exact ContDiff.sum (fun j _ ↦ ((hg i j).sub (hG i j)).mul
        (coordPartial_contDiff (coordPartial_contDiff hf j) i))
    · intro i _
      apply FlatAt.sum Finset.univ
      · intro j _
        exact ((hg i j).sub (hG i j)).mul (coordPartial_contDiff (coordPartial_contDiff hf j) i)
      · intro j _
        exact (hgj i j).mul ((hg i j).sub (hG i j))
          (coordPartial_contDiff (coordPartial_contDiff hf j) i)
  · apply FlatAt.sum Finset.univ
    · intro i _
      exact ((hb i).sub (hB i)).mul (coordPartial_contDiff hf i)
    · intro i _
      exact (hbj i).mul ((hb i).sub (hB i)) (coordPartial_contDiff hf i)

theorem flat_eikonal_coefficients {n : ℕ}
    {g G : Fin 4 → Fin 4 → Coord → ℂ} {f : Coord → ℂ}
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j)) (hG : ∀ i j, ContDiff ℝ ∞ (G i j))
    (hf : ContDiff ℝ ∞ f) (hgj : ∀ i j, FlatAt n (fun x ↦ g i j x - G i j x) 0) :
    FlatAt n (fun x ↦ smoothEikonal g f x - smoothEikonal G f x) 0 := by
  have he : (fun x ↦ smoothEikonal g f x - smoothEikonal G f x) =
      fun x ↦ ∑ i, ∑ j, (g i j x - G i j x) * coordPartial i f x * coordPartial j f x := by
    funext x
    simp only [smoothEikonal, sub_mul, Finset.sum_sub_distrib]
    ring
  rw [he]
  apply FlatAt.sum Finset.univ
  · intro i _
    exact ContDiff.sum (fun j _ ↦ (((hg i j).sub (hG i j)).mul
      (coordPartial_contDiff hf i)).mul (coordPartial_contDiff hf j))
  · intro i _
    apply FlatAt.sum Finset.univ
    · intro j _
      exact (((hg i j).sub (hG i j)).mul (coordPartial_contDiff hf i)).mul
        (coordPartial_contDiff hf j)
    · intro j _
      exact ((hgj i j).mul ((hg i j).sub (hG i j)) (coordPartial_contDiff hf i)).mul
        (((hg i j).sub (hG i j)).mul (coordPartial_contDiff hf i)) (coordPartial_contDiff hf j)

lemma flat_of_sub {n : ℕ} {f q : Coord → ℂ} (hf : ContDiff ℝ ∞ f)
    (hq : ContDiff ℝ ∞ q) (h : FlatAt n (fun x ↦ f x - q x) 0) (h' : FlatAt n q 0) :
    FlatAt n f 0 := by
  have he : f = fun x ↦ (f x - q x) + q x := by ext; ring
  rw [he]
  exact h.add (hf.sub hq) hq h'

theorem smooth_eikonal_flat {n : ℕ} {g : Fin 4 → Fin 4 → Coord → ℂ}
    (G : Fin 4 → Fin 4 → CPoly) (phi : CPoly)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hjet : ∀ i j, FlatAt n (fun x ↦ g i j x - reval (G i j) x) 0)
    (hpoly : ∀ k, k ≤ n → homogeneousComponent k (polynomialEikonal G phi) = 0) :
    FlatAt n (smoothEikonal g (reval phi)) 0 := by
  apply flat_of_sub (smoothEikonal_contDiff hg (reval_contDiff phi))
    (smoothEikonal_contDiff (fun i j ↦ reval_contDiff _) (reval_contDiff phi))
  · exact flat_eikonal_coefficients hg (fun i j ↦ reval_contDiff _) (reval_contDiff phi) hjet
  · rw [← reval_eikonal]
    exact flatAt_reval hpoly

theorem smooth_eikonal_derivative_bound {m l : ℕ} {g : Fin 4 → Fin 4 → Coord → ℂ}
    (G : Fin 4 → Fin 4 → CPoly) (phi : CPoly)
    (hg : ∀ i j, ContDiff ℝ ∞ (g i j))
    (hjet : ∀ i j, FlatAt m (fun x ↦ g i j x - reval (G i j) x) 0)
    (hpoly : ∀ k, k ≤ m → homogeneousComponent k (polynomialEikonal G phi) = 0)
    (hl : l ≤ m) (z : Coord) (C : ℝ)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ (m + 1) (smoothEikonal g (reval phi)) (t • z)‖ ≤ C) :
    ‖iteratedFDeriv ℝ l (smoothEikonal g (reval phi)) z‖ ≤
      C * ‖z‖ ^ (m + 1 - l) / ((m - l).factorial : ℝ) := by
  simpa using Yau.Waves.vanishing_jet_derivative_bound
    (smoothEikonal_contDiff hg (reval_contDiff phi)) hl 0 z C
    (smooth_eikonal_flat G phi hg hjet hpoly) (by simpa using hbound)

end
end Yau.Jets

end OAI
