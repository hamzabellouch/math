import OAI.MeasureTheory.Falconer.Estimates.PlanarPathCenters
import OAI.MeasureTheory.Falconer.Estimates.PlanarPrefixTruncation
import OAI.MeasureTheory.Falconer.Estimates.DyadicAncestors

namespace OAI

/-! Geometric realization of the endpoint cells inside their actual parent.
The local similarity preserves the number of cells and gives the separation
at the relative depth, as well as a bounded point chart. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem localPacketPoint_separated {δ Δ : ℝ} (hΔ : 0 < Δ) (y c : ℝ)
    (P : Finset (Space 2)) (hP : FiniteSeparatedAt δ P) :
    FiniteSeparatedAt (δ/Δ) (P.image (localPacketPoint Δ y c)) := by
  intro x hx z hz hxz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
  rw [localPacketPoint_dist hΔ]
  exact div_le_div_of_nonneg_right
    (hP p hp q hq (fun he => hxz (congrArg (localPacketPoint Δ y c) he))) hΔ.le

theorem local_prefix_centers_geometry {N a b : ℕ} (Q : DyadicCube 2)
    (hQ : Q.side = 1) (C : Finset (CellPath 2)) (hC : C ⊆ cubePaths 2 N)
    (hab : a ≤ b) (hbN : b ≤ N) (p₀ : CellPath 2) :
    let D := prefixChildren C a b p₀
    let P := D.image (fun q => (Q.descendant q).center)
    let Z := P.image (localPacketPoint (1/(2:ℝ)^a)
      ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1))
    Z.card = D.card ∧ InBoundedLineChart Z ∧
      FiniteSeparatedAt (1/(2:ℝ)^(b-a)) Z := by
  let D := prefixChildren C a b p₀
  let P := D.image (fun q => (Q.descendant q).center)
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hD : D ⊆ cubePaths 2 b :=
    (Finset.image_subset_image (Finset.filter_subset _ _)).trans
      (planar_prefix_image_take_cubePaths hC hbN)
  obtain ⟨_,_,_,_,hsep⟩ := planar_path_center_realization Q hQpos D hD
  have hcard : P.card = D.card := by
    apply Finset.card_image_iff.mpr
    intro q hq r hr he
    exact Q.center_injective_at_depth hQpos ((mem_cubePaths _ _ _).mp (hD hq))
      ((mem_cubePaths _ _ _).mp (hD hr)) he
  refine ⟨?_,?_,?_⟩
  · rw [Finset.card_image_of_injective _ (localPacketPoint_injective (by positivity) _ _)]
    exact hcard
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hu,hup⟩ := Finset.mem_filter.mp hu
    have hulen := (mem_cubePaths _ _ _).mp (hC hu)
    have hplen : p₀.length = a := by
      rw [← hup,List.length_take,hulen,Nat.min_eq_left (hab.trans hbN)]
    have htake : (u.take b).take a = p₀ := by
      simpa only [List.take_take,Nat.min_eq_left hab] using hup
    have hm := Q.center_mem_ancestor hQpos (u.take b) a
    rw [htake] at hm
    have hside : (Q.descendant p₀).side = 1/(2:ℝ)^a := by
      rw [Q.descendant_side,hplen,hQ]
    have hc (i : Fin 2) :
        |localPacketPoint (1/(2:ℝ)^a) ((Q.descendant p₀).center 0)
          ((Q.descendant p₀).center 1) (Q.descendant (u.take b)).center i| ≤ 1/2 := by
      have hh := (Q.descendant p₀).center_coordinate_bound hm i
      rw [hside] at hh
      fin_cases i
      · change |(Q.descendant (u.take b)).center 0-(Q.descendant p₀).center 0| ≤
          (1/(2:ℝ)^a)/2 at hh
        change |((Q.descendant (u.take b)).center 0-(Q.descendant p₀).center 0)/
          (1/(2:ℝ)^a)| ≤ 1/2
        rw [abs_div,abs_of_pos (by positivity : 0 < 1/(2:ℝ)^a)]
        exact (div_le_iff₀ (by positivity : 0 < 1/(2:ℝ)^a)).2 (by linarith only [hh])
      · change |(Q.descendant (u.take b)).center 1-(Q.descendant p₀).center 1| ≤
          (1/(2:ℝ)^a)/2 at hh
        change |((Q.descendant (u.take b)).center 1-(Q.descendant p₀).center 1)/
          (1/(2:ℝ)^a)| ≤ 1/2
        rw [abs_div,abs_of_pos (by positivity : 0 < 1/(2:ℝ)^a)]
        exact (div_le_iff₀ (by positivity : 0 < 1/(2:ℝ)^a)).2 (by linarith only [hh])
    exact ⟨(hc 0).trans (by norm_num),(hc 1).trans (by norm_num)⟩
  · have hh := localPacketPoint_separated (by positivity : 0 < 1/(2:ℝ)^a)
      ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1) P hsep
    have he : (Q.side/(2:ℝ)^b)/(1/(2:ℝ)^a) = 1/(2:ℝ)^(b-a) := by
      rw [hQ,show b = (b-a)+a by omega,pow_add]
      field_simp
      congr 1
      omega
    rw [he] at hh
    exact hh

end Falconer

end OAI
