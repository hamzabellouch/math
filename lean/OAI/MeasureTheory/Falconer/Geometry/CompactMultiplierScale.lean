import OAI.MeasureTheory.Falconer.Angular.StationaryChartAmplitude

namespace OAI

namespace PlanarFalconer
open Set
open scoped ContDiff

 theorem compact_multiplier_uniform_derivatives {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) {K : Set ℝ} (hK : IsCompact K) (hs : tsupport w ⊆ K) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {f : ℝ → ℂ}, ContDiff ℝ ∞ f →
      ∀ {C D : ℝ}, 0 ≤ C → 1 ≤ D →
      (∀ k ≤ n, ∀ x, ‖iteratedDeriv k f x‖ ≤ C*D^k) →
      ∀ k ≤ n, ∀ x, ‖iteratedDeriv k (fun y => w y*f y) x‖ ≤ (A*C)*D^k := by
  choose A hA hbound using fun k => compact_weighted_composition_scale hw
    (contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)) hK k
  let B : ℝ := ∑ k ∈ Finset.range (n+1), A k
  refine ⟨B,Finset.sum_nonneg (fun k _ => hA k),?_⟩
  intro f hf C D hC hD hb k hk x
  have hkB : A k ≤ B := Finset.single_le_sum (fun l _ => hA l)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  by_cases hx : x ∈ K
  · have hh := hbound k f hf C D hC hD (fun l hl => hb l (hl.trans hk)) x hx
    change ‖iteratedDeriv k (fun y => w y*f y) x‖ ≤ A k*C*D^k at hh
    apply hh.trans
    gcongr
  · have he : iteratedDeriv k (fun y => w y*f y) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hx (hs (tsupport_mul_subset_left
        (complex_iteratedDeriv_tsupport _ k hh))))
    rw [he,norm_zero]
    have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ => hA k)
    positivity

end PlanarFalconer

end OAI
