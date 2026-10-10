import OAI.Combinatorics.Progressions.Geometry.UnconditionedSpatialWidthBudget

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem selectedResidue_anchored_trimmed_reference_compare {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (anchor : Option K × I → ℤ)
    (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hnoise : ∀ u ∈ rectangularWeightIndices 0 W 1, ∀ i,
      |integerPhysicalSite root (anchor + u) i| ≤ (R i : ℤ))
    (f : (I → ℤ) → ℂ) (hf : ∀ x ∈ integerBox N, ‖f x‖ ≤ 1) :
    ‖(𝔼 b ∈ trimmedIntegerBox N R,
        ∑' u, ((selectedResidueSmoothPMF modulus T W hW hZ u).toReal : ℂ) *
          f (b + integerPhysicalSite root (anchor + u))) - 𝔼 x ∈ integerBox N, f x‖ ≤
      2 * ∑ i, 2 * (R i : ℝ) / N i := by
  let p := selectedResidueFiniteLaw modulus T W hW hZ
  have h := p.translated_subset_mixture_compare (trimmedIntegerBox N R) (integerBox N)
    (trimmedIntegerBox_nonempty N R hR)
    (fun u b => b + integerPhysicalSite root (anchor + u.val))
    (fun _ _ _ _ _ he => add_right_cancel he)
    (fun u _ hb => trimmedIntegerBox_add_mem N R (fun i => (hR i).le) hb _
      (hnoise u.val u.property)) f hf
  have hdef := trimmedIntegerBox_card_deficit N R
    (fun i => lt_of_le_of_lt (Nat.zero_le _) (hR i)) (fun i => (hR i).le)
  have hbound := h.trans (mul_le_mul_of_nonneg_left hdef (by norm_num : (0 : ℝ) ≤ 2))
  dsimp only [p] at hbound
  have he (b : I → ℤ) := selectedResidueFiniteLaw_complexMean modulus T W hW hZ
    (fun u => f (b + integerPhysicalSite root (anchor + u)))
  simpa only [he] using hbound

theorem selectedResidue_anchored_trimmed_transfer {K I : Type*}
    [Fintype K] [Fintype I] [DecidableEq I]
    (root : K → ℤ) (anchor : Option K × I → ℤ)
    (N R : I → ℕ) (hR : ∀ i, 2 * R i < N i)
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hnoise : ∀ u ∈ rectangularWeightIndices 0 W 1, ∀ i,
      |integerPhysicalSite root (anchor + u) i| ≤ (R i : ℤ))
    (φ : (I → ℝ) → ℂ) (hφ : ∀ v, ‖φ v‖ ≤ 1)
    (L : (I → ℤ) → ℂ) {ε : ℝ}
    (hL : ∀ b ∈ trimmedIntegerBox N R,
      ‖L b - ∑' u, ((selectedResidueSmoothPMF modulus T W hW hZ u).toReal : ℂ) *
        φ (physicalAffineSite root ((integerBaseTranslation b + anchor) + u))‖ ≤ ε) :
    ‖(𝔼 b ∈ trimmedIntegerBox N R, L b) -
      𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))‖ ≤
      ε + 2 * ∑ i, 2 * (R i : ℝ) / N i := by
  let f := fun x : I → ℤ => φ (fun i => (x i : ℝ))
  have he (b : I → ℤ) (u : Option K × I → ℤ) :
      φ (physicalAffineSite root ((integerBaseTranslation b + anchor) + u)) =
        f (b + integerPhysicalSite root (anchor + u)) := by
    congr 1
    funext i
    rw [add_assoc]
    simp only [← integerPhysicalSite_cast_apply, integerPhysicalSite_baseTranslation_add,
      Pi.add_apply]
  have hlocal : ‖(𝔼 b ∈ trimmedIntegerBox N R, L b) -
      (𝔼 b ∈ trimmedIntegerBox N R,
        ∑' u, ((selectedResidueSmoothPMF modulus T W hW hZ u).toReal : ℂ) *
          f (b + integerPhysicalSite root (anchor + u)))‖ ≤ ε := by
    rw [← Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le (trimmedIntegerBox_nonempty N R hR)
    intro b hb
    simpa only [he] using hL b hb
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add hlocal
    (selectedResidue_anchored_trimmed_reference_compare root anchor N R hR modulus T W hW hZ
      hnoise f (fun x _ => hφ _)))

end Erdos3.BooleanCubeKernel

end

end OAI
