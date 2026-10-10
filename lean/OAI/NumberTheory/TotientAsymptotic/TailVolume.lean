import OAI.NumberTheory.TotientAsymptotic.SimplexVolume
import OAI.NumberTheory.TotientAsymptotic.TailBounds

namespace OAI

/-! Exact finite-tail intersection volumes, before prime-box approximation. -/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace TotientAsymptotic

lemma prod_g_shifted (N : ℕ) :
    (∏ i : Fin N, g (i.val+1)) = ∏ i ∈ Finset.Icc 1 N, g i := by
  rw [Fin.prod_univ_eq_prod_range (fun i => g (i+1))]
  apply Finset.prod_bij (fun i _ => i+1)
  · intro i hi
    have := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr (by omega)
  · intro i _ j _ hij
    omega
  · intro j hj
    have := Finset.mem_Icc.mp hj
    refine ⟨j-1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i _
    rfl

def tailPrefixRegion (x : ℝ) (H : ℕ) (η : TailDatum H) :
    Set (Fin (R x H) → ℝ) :=
  prefixRegion (R x H) (B x) (D (m x) η)
    (fun i => D (m x-(i.val+1)) η)

def tailIntersection (x : ℝ) (H : ℕ) (T : Finset (TailDatum H)) :
    Set (Fin (R x H) → ℝ) :=
  {u | ∀ η ∈ T, u ∈ tailPrefixRegion x H η}

def tailBudget (x : ℝ) (H : ℕ) (T : Finset (TailDatum H)) : ℝ :=
  maxD (m x) T + ∑ i : Fin (R x H), g (i.val+1) * maxD (m x-(i.val+1)) T

lemma tailIntersection_eq (x : ℝ) (H : ℕ) (T : Finset (TailDatum H))
    (hT : T.Nonempty) :
    tailIntersection x H T = prefixRegion (R x H) (B x) (maxD (m x) T)
      (fun i => maxD (m x-(i.val+1)) T) := by
  unfold tailIntersection tailPrefixRegion
  rw [prefixRegion_intersection (R x H) (B x) T hT]
  simp only [maxD, dite_eq_left hT]

/-- The intersection-volume identity with the tail budget indexed by the prefix.
This form avoids a reversed-index convention in subsequent finite sums. -/
theorem volume_tailIntersection (x : ℝ) (H : ℕ) (T : Finset (TailDatum H))
    (hT : T.Nonempty) (hR : 0 < R x H) (hB : 0 < B x) :
    volume (tailIntersection x H T) =
      ENNReal.ofReal (G x (R x H) * (max (1-tailBudget x H T/B x) 0)^(R x H)) := by
  rw [tailIntersection_eq x H T hT, volume_prefixRegion_explicit _ hR]
  have hb : max (B x-tailBudget x H T) 0 =
      B x * max (1-tailBudget x H T/B x) 0 := by
    have he : B x * (1-tailBudget x H T/B x) = B x-tailBudget x H T := by
      field_simp
    rw [mul_max_of_nonneg _ _ hB.le, he, mul_zero]
  have he : B x - maxD (m x) T -
      ∑ i : Fin (R x H), g (i.val+1)*maxD (m x-(i.val+1)) T =
      B x-tailBudget x H T := by unfold tailBudget; ring
  rw [he, hb, mul_pow, prod_g_shifted]
  congr 1
  unfold G
  ring

end TotientAsymptotic

end

end OAI
