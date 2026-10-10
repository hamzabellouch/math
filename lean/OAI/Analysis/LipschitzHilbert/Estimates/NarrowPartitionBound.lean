import OAI.Analysis.LipschitzHilbert.Estimates.NarrowPartitionReconstruction
import OAI.Analysis.LipschitzHilbert.Fourier.ProductPVLinear

namespace OAI

/-! A bound for the fixed narrow cutoff controls a finite partition of any
compact annulus. Its cost is independent of the common frequency dilation. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

private theorem list_sum_eLpNorm {α : Type*} (l : List α)
    (g : α → (ℝ×ℝ) → ℂ) (c : α → ℝ)
    (h : ∀ a∈l, 0≤c a ∧ MemLp (g a) 2 planeMeasure ∧
      eLpNorm (g a) 2 planeMeasure≤ENNReal.ofReal (c a)) :
    MemLp (l.map g).sum 2 planeMeasure ∧
      eLpNorm (l.map g).sum 2 planeMeasure≤ENNReal.ofReal (l.map c).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons,List.sum_cons]
    refine ⟨ha.2.1.add ht.1,?_⟩
    calc
      _ ≤ eLpNorm (g a) 2 planeMeasure+eLpNorm (as.map g).sum 2 planeMeasure :=
        eLpNorm_add_le (by norm_num)
      _ ≤ ENNReal.ofReal (c a)+ENNReal.ofReal (as.map c).sum := add_le_add ha.2.2 ht.2
      _ = _ := (ENNReal.ofReal_add ha.1 (List.sum_nonneg (by
        intro x hx
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
        exact (h b (List.mem_cons_of_mem _ hb)).1))).symm

def narrowPartitionCost (l : List NarrowWindow) : ℝ :=
  (l.map (fun q => verticalProjectionCost q.2)).sum

theorem narrowPartitionCost_nonneg (l : List NarrowWindow) : 0≤narrowPartitionCost l := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
  exact (verticalProjectionCost_pos q.2).le

theorem narrowPartition_PV_bound (l : List NarrowWindow) (K : Set ℝ)
    (habs : ∀ q∈l, 0<q.1 ∧ ∀ x, narrowBandProfile (q.1*x)*q.2 x=q.2 x)
    (hpartition : ∀ x∈K, (l.map (fun q => q.2 x)).sum=1)
    (u : (ℝ×ℝ) → ℝ) (R : ℝ) (hR : 0<R) (hRs : R≤1/4)
    (B : ℝ) (hB : 0≤B)
    (hband : ∀ w : ℝ, 0<w → ∀ g : SchwartzMap (ℝ×ℝ) ℂ,
      MemLp (productSlopePrincipalValue u R (schwartzVerticalProjection narrowBandProfile w 0 g))
        2 planeMeasure ∧
      eLpNorm (productSlopePrincipalValue u R (schwartzVerticalProjection narrowBandProfile w 0 g))
        2 planeMeasure≤ENNReal.ofReal (B*‖g.toLp 2 planeMeasure‖))
    (W : ℝ) (hW : 0<W) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (hsupport : ∀ omega, planarFourier f omega≠0 → W*omega.2∈K) :
    MemLp (productSlopePrincipalValue u R f) 2 planeMeasure ∧
      eLpNorm (productSlopePrincipalValue u R f) 2 planeMeasure≤
        ENNReal.ofReal ((B*narrowPartitionCost l)*‖f.toLp 2 planeMeasure‖) := by
  let g := fun q : NarrowWindow => schwartzVerticalProjection q.2 W 0 f
  have hpiece (q : NarrowWindow) (hq : q∈l) :
      MemLp (productSlopePrincipalValue u R (g q)) 2 planeMeasure ∧
        eLpNorm (productSlopePrincipalValue u R (g q)) 2 planeMeasure≤
          ENNReal.ofReal ((B*verticalProjectionCost q.2)*‖f.toLp 2 planeMeasure‖) := by
    have hh := hband (q.1*W) (mul_pos (habs q hq).1 hW) (g q)
    rw [narrowProjection_absorb q (habs q hq).2] at hh
    refine ⟨hh.1,hh.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hn := verticalSchwartzToL2_norm q.2 W hW f
    change ‖(g q).toLp 2 planeMeasure‖≤_ at hn
    nlinarith only [mul_le_mul_of_nonneg_left hn hB]
  have hs := list_sum_eLpNorm l (fun q => productSlopePrincipalValue u R (g q))
    (fun q => (B*verticalProjectionCost q.2)*‖f.toLp 2 planeMeasure‖) (fun q hq =>
      ⟨mul_nonneg (mul_nonneg hB (verticalProjectionCost_pos q.2).le) (norm_nonneg _),hpiece q hq⟩)
  have he : (l.map (fun q => productSlopePrincipalValue u R (g q))).sum=
      productSlopePrincipalValue u R f := by
    have hh := map_list_sum (productPVSchwartzLM u R hR hRs) (l.map g)
    change productSlopePrincipalValue u R (l.map g).sum=_ at hh
    rw [show (l.map g).sum=f from narrowPartition_reconstruction l K hpartition W f hsupport] at hh
    simpa only [List.map_map,Function.comp_def,productPVSchwartzLM_apply] using hh.symm
  rw [he] at hs
  have hc : (l.map (fun q => (B*verticalProjectionCost q.2)*‖f.toLp 2 planeMeasure‖)).sum=
      (B*narrowPartitionCost l)*‖f.toLp 2 planeMeasure‖ := by
    unfold narrowPartitionCost
    simp_rw [mul_assoc]
    rw [List.sum_map_mul_left,List.sum_map_mul_right]
  simpa only [hc] using hs

end LipschitzHilbert.PacketRepresentation

end

end OAI
