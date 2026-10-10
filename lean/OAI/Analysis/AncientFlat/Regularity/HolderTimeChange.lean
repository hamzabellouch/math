import OAI.Analysis.AncientFlat.Regularity.CompactLocalHolder
import OAI.Analysis.AncientFlat.Regularity.HolderProducts

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff NNReal
namespace ParabolicInterior
open ParabolicLocalization
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [FiniteDimensional ℝ V] in
lemma compact_smooth_holder (α : ℝ) (hα : 0<α) (hα1 : α≤1)
    (K : Set (V × ℝ)) (hK : IsCompact K) (hKc : Convex ℝ K)
    (f : V × ℝ → E) (hf : ContDiffOn ℝ 1 f K) :
    ∃ C : ℝ, 0<C ∧ HolderBound α K f C := by
  obtain ⟨B0,hB0⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  let B := max B0 0
  have hB : 0≤B := le_max_right _ _
  have hBb (z) (hz : z∈K) : ‖f z‖≤B := (hB0 z hz).trans (le_max_left _ _)
  obtain ⟨L,hL⟩ := hf.exists_lipschitzOnWith (by norm_num) hKc hK
  refine ⟨2*B+L+1,by positivity,?_,?_⟩
  · intro p hp
    exact (hBb _ hp).trans (by linarith [L.coe_nonneg])
  · intro p hp q hq
    by_cases hd : pdist p q≤1
    · calc
        _ ≤ (L:ℝ)*‖p-q‖ := hL.norm_sub_le hp hq
        _ ≤ (L:ℝ)*pdist p q := mul_le_mul_of_nonneg_left (norm_pair_sub_le_pdist p q hd) L.coe_nonneg
        _ ≤ (L:ℝ)*pdist p q^α := mul_le_mul_of_nonneg_left
          (Real.self_le_rpow_of_le_one (pdist_nonneg _ _) hd hα1) L.coe_nonneg
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [L.coe_nonneg]) (Real.rpow_nonneg (pdist_nonneg _ _) _)
    · have hh : 1≤pdist p q^α := Real.one_le_rpow (le_of_not_ge hd) hα.le
      calc
        _ ≤ ‖f p‖+‖f q‖ := norm_sub_le _ _
        _ ≤ 2*B := by linarith [hBb _ hp,hBb _ hq]
        _ ≤ (2*B+L+1)*pdist p q^α := by nlinarith [L.coe_nonneg]
omit [FiniteDimensional ℝ V] [NormedSpace ℝ E] in
lemma separated_time_change (α ℓ H : ℝ) (hα : 0≤α) (hH : 0≤H)
    (I J : Set ℝ) (φ : ℝ → ℝ) (L : ℝ≥0) (hφ : LipschitzOnWith L φ J)
    (hmap : MapsTo φ J I) (g : ℝ → V → E)
    (hb : ∀ t∈I, ∀ x, ‖g t x‖≤H)
    (hh : ∀ t∈I, ∀ s∈I, ∀ x y, ‖g t x-g s y‖≤H*(‖x-y‖^α+|t-s|^(α/4))) :
    HolderBound α {p : V × ℝ | p.2∈J} (fun p => g (φ p.2) (ℓ • p.1))
      (H*(1+|ℓ|^α+(L:ℝ)^(α/4))) := by
  have hc : 0≤|ℓ|^α := Real.rpow_nonneg (abs_nonneg _) _
  have hL : 0≤(L:ℝ)^(α/4) := Real.rpow_nonneg L.coe_nonneg _
  refine ⟨fun p hp => (hb _ (hmap hp) _).trans (by nlinarith),?_⟩
  intro p hp q hq
  have hx : ‖ℓ • p.1-ℓ • q.1‖^α≤|ℓ|^α*pdist p q^α := by
    rw [←smul_sub,norm_smul,Real.norm_eq_abs,Real.mul_rpow (abs_nonneg _) (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _)
      (show ‖p.1-q.1‖≤pdist p q from le_add_of_nonneg_right (Real.rpow_nonneg (abs_nonneg _) _)) hα) hc
  have ht0 : |φ p.2-φ q.2|≤(L:ℝ)*|p.2-q.2| := by
    simpa only [Real.norm_eq_abs] using hφ.norm_sub_le hp hq
  have ht1 : |p.2-q.2|^(α/4)≤pdist p q^α := by
    rw [show α/4=(1/4:ℝ)*α by ring,Real.rpow_mul (abs_nonneg _)]
    exact Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _)
      (le_add_of_nonneg_left (norm_nonneg _)) hα
  have ht : |φ p.2-φ q.2|^(α/4)≤(L:ℝ)^(α/4)*pdist p q^α := by
    calc
      _ ≤ ((L:ℝ)*|p.2-q.2|)^(α/4) := Real.rpow_le_rpow (abs_nonneg _) ht0 (by positivity)
      _ = (L:ℝ)^(α/4)*|p.2-q.2|^(α/4) := Real.mul_rpow L.coe_nonneg (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left ht1 hL
  exact (hh _ (hmap hp) _ (hmap hq) _ _).trans
    ((mul_le_mul_of_nonneg_left (add_le_add hx ht) hH).trans (by nlinarith [mul_nonneg hH (Real.rpow_nonneg (pdist_nonneg p q) α)]))
end ParabolicInterior

end

end OAI
