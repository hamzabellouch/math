import OAI.Analysis.AncientFlat.Evolution.LowerOrderCore
import OAI.Analysis.AncientFlat.Regularity.HolderAlgebra

namespace OAI
noncomputable section
open Set Filter
open scoped ContDiff Laplacian
namespace ParabolicLowerOrder
open ParabolicInterior
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
lemma holder_clm_apply {α K L : ℝ} {Ω : Set (V × ℝ)}
    {c : V × ℝ → E →L[ℝ] F} {v : V × ℝ → E} (hK : 0≤K) (hL : 0≤L)
    (hc : HolderBound α Ω c K) (hv : HolderBound α Ω v L) :
    HolderBound α Ω (fun p => c p (v p)) (2*K*L) := by
  constructor
  · intro p hp
    exact ((c p).le_opNorm _).trans ((mul_le_mul (hc.1 p hp) (hv.1 p hp) (norm_nonneg _) hK).trans (by nlinarith))
  · intro p hp q hq
    have he : c p (v p)-c q (v q)=c p (v p-v q)+(c p-c q) (v q) := by simp only [map_sub,sub_apply]; abel
    rw [he]
    have h1 := ((c p).le_opNorm _).trans (mul_le_mul (hc.1 p hp) (hv.2 p hp q hq) (norm_nonneg _) hK)
    have h2 := ((c p-c q).le_opNorm _).trans (mul_le_mul (hc.2 p hp q hq) (hv.1 q hq) (norm_nonneg _) (mul_nonneg hK (Real.rpow_nonneg (pdist_nonneg p q) _)))
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))
omit [FiniteDimensional ℝ V] in
lemma lower_norm {K L : ℝ} {Ω : Set (V × ℝ)} (hK : 0≤K) (c : Coefficients V) (u : ℝ → V → ℂ)
    (hc : ∀ j, ∀ p∈Ω, ‖c j p‖≤K)
    (hu : ∀ j : Fin 3, ∀ p∈Ω, ‖iteratedFDeriv ℝ (j.val+1) (u p.2) p.1‖≤L) :
    ∀ p∈Ω, ‖spatialLower c u p‖≤3*K*L := by
  intro p hp
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j : Fin 3, K*L := Finset.sum_le_sum (fun j _ =>
      ((c j p).le_opNorm _).trans (mul_le_mul (hc j p hp) (hu j p hp) (norm_nonneg _) hK))
    _ = _ := by simp; ring
omit [FiniteDimensional ℝ V] in
lemma lower_holder {α K L : ℝ} {Ω : Set (V × ℝ)} (hK : 0≤K) (hL : 0≤L)
    (c : Coefficients V) (u : ℝ → V → ℂ) (hc : ∀ j, HolderBound α Ω (c j) K)
    (hu : ∀ j : Fin 3, HolderBound α Ω (fun p => iteratedFDeriv ℝ (j.val+1) (u p.2) p.1) L) :
    HolderBound α Ω (spatialLower c u) (6*K*L) := by
  have h j := holder_clm_apply hK hL (hc j) (hu j)
  constructor
  · intro p hp
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j : Fin 3, 2*K*L := Finset.sum_le_sum (fun j _ => (h j).1 p hp)
      _ = _ := by simp; ring
  · intro p hp q hq
    unfold spatialLower
    rw [←Finset.sum_sub_distrib]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ j : Fin 3, (2*K*L)*pdist p q^α := Finset.sum_le_sum (fun j _ => (h j).2 p hp q hq)
      _ = _ := by simp; ring
end ParabolicLowerOrder

end

end OAI
