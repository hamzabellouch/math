import OAI.Geometry.SurfaceImmersion.Whitney.OrderedCornerBridges

namespace OAI

/-! Consecutive ordered corner parameters leave genuine regular open
intervals of the original path between them. -/
noncomputable section
open Set
namespace ClosedSurfaceR4.FiniteOrderSmoothing

lemma not_mem_range_before_first {n : ℕ} (T : Fin (n+1) → ℝ) (hT : StrictMono T)
    {t : ℝ} (ht : t < T 0) : t ∉ range T := by
  rintro ⟨k,rfl⟩
  exact (not_lt_of_ge (hT.monotone (show (0:Fin (n+1)) ≤ k from bot_le))) ht

lemma not_mem_range_between_successive {n : ℕ} (T : Fin n → ℝ) (hT : StrictMono T)
    {i j : Fin n} (hij : j.val = i.val+1) {t : ℝ} (hi : T i < t) (hj : t < T j) :
    t ∉ range T := by
  rintro ⟨k,rfl⟩
  have hik := hT.lt_iff_lt.mp hi
  have hkj := hT.lt_iff_lt.mp hj
  change i.val < k.val at hik
  change k.val < j.val at hkj
  omega

lemma not_mem_range_after_last {n : ℕ} (T : Fin (n+1) → ℝ) (hT : StrictMono T)
    {t : ℝ} (ht : T (Fin.last n) < t) : t ∉ range T := by
  rintro ⟨k,rfl⟩
  have hk : k ≤ Fin.last n := k.le_last
  exact (not_lt_of_ge (hT.monotone hk)) ht

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
