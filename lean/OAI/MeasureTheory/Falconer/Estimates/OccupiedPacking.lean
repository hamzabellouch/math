import OAI.MeasureTheory.Falconer.Geometry.ScaledDyadicPacking
import OAI.MeasureTheory.Falconer.Recursion.PrefixMass

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

noncomputable def occupiedCenterCells (Q : DyadicSquare) (ν : Measure Plane)
    (p : ℕ) (x : Plane) (r : ℝ) : Finset CellPath := by
  classical
  exact (dyadicPaths p).filter fun q => 0 < ν (Q.descendant q).carrier ∧
    (Q.descendant q).center ∈ ball x r

theorem occupied_center_count_le (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ν : Measure Plane) [IsFiniteMeasure ν] {g p : ℕ} (hgp : g ≤ p)
    (x : Plane) {r C₀ lo hi : ℝ} (hC₀ : 0 ≤ C₀) (hr : r ≤ C₀*(Q.side/(2:ℝ)^g))
    (hlo : 0 < lo) (hhi : 0 ≤ hi)
    (hfine : ∀ q ∈ dyadicPaths p, 0 < ν (Q.descendant q).carrier →
      lo ≤ (ν (Q.descendant q).carrier).toReal)
    (hcoarse : ∀ q ∈ dyadicPaths g, 0 < ν (Q.descendant q).carrier →
      (ν (Q.descendant q).carrier).toReal ≤ hi) :
    ((occupiedCenterCells Q ν p x r).card:ℝ) ≤ (4*(C₀+1)^2)*hi/lo := by
  classical
  let S := occupiedCenterCells Q ν p x r
  let T := S.image (List.take g)
  have hS : S ⊆ dyadicPaths p := Finset.filter_subset _ _
  have hT : T ⊆ dyadicPaths g := by
    intro c hc
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    have hl := (mem_dyadicPaths _ _).mp (hS hq)
    simp [mem_dyadicPaths,List.length_take,hl,hgp]
  have hpos {q : CellPath} (hq : q ∈ S) : 0 < ν (Q.descendant q).carrier :=
    (Finset.mem_filter.mp hq).2.1
  have hparent (q : CellPath) : (Q.descendant q).carrier ⊆ (Q.descendant (q.take g)).carrier :=
    Q.descendant_subset_take hQ q g
  have hTm : T ⊆ cellsMeeting Q g x r := by
    intro c hc
    have hc' := hT hc
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
    refine Finset.mem_filter.mpr ⟨hc',?_⟩
    refine ⟨(Q.descendant q).center,?_,(Finset.mem_filter.mp hq).2.2⟩
    exact hparent q ((Q.descendant q).center_mem (Q.descendant_side_pos hQ q))
  have hcard : (T.card:ℝ) ≤ 4*(C₀+1)^2 := by
    have hh : (T.card:ℝ) ≤ ((cellsMeeting Q g x r).card:ℝ) := by exact_mod_cast Finset.card_le_card hTm
    exact hh.trans (dyadic_scaled_ball_card_le Q hQ g x hC₀ hr)
  have hcover : leafUnion Q S ⊆ leafUnion Q T := by
    intro z hz
    obtain ⟨q,hq,hz⟩ := mem_iUnion₂.mp hz
    exact mem_iUnion₂.mpr ⟨q.take g,Finset.mem_image.mpr ⟨q,hq,rfl⟩,hparent q hz⟩
  have hsum : (S.card:ℝ)*lo ≤ (T.card:ℝ)*hi := by
    calc
      _ = ∑ _q ∈ S, lo := by simp
      _ ≤ ∑ q ∈ S, (ν (Q.descendant q).carrier).toReal :=
        Finset.sum_le_sum (fun q hq => hfine q (hS hq) (hpos hq))
      _ = (ν (leafUnion Q S)).toReal := (restriction_total_mass_real Q hQ ν hS).symm
      _ ≤ (ν (leafUnion Q T)).toReal := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hcover)
      _ = ∑ q ∈ T, (ν (Q.descendant q).carrier).toReal := restriction_total_mass_real Q hQ ν hT
      _ ≤ ∑ _q ∈ T, hi := by
        apply Finset.sum_le_sum
        intro c hc
        apply hcoarse c (hT hc)
        obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
        exact (hpos hq).trans_le (measure_mono (hparent q))
      _ = _ := by simp
  exact (le_div_iff₀ hlo).mpr (hsum.trans (mul_le_mul_of_nonneg_right hcard hhi))

end PlanarFalconer

end OAI
