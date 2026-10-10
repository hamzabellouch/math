import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightRelativeConstants
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySmoothWeightSourceBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySymbolicEncoding
open Construction Characters.RationalHistory HistorySymbolicState HistorySymbolicSlots
open HistorySymbolicStep HistoryProductWindows
variable {ι : Type*}

theorem supported_frequency_exp_bound {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {h : History l} (hs : h.Supported V outside) :
    |(h.root.frequency : ℝ)| ≤ Real.exp (Real.log ((V l : ℝ) + 1)) := by
  rw [Real.exp_log (by positivity)]
  have hh : |(h.root.frequency : ℝ)| ≤ (V l : ℝ) := by
    have hnat : (h.root.frequency.natAbs : ℝ) ≤ (V l : ℝ) := by
      exact_mod_cast History.supported_root_frequency_bound hs
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hnat
  linarith

theorem pivot_relativeControl_of_source_windows
    (b k : ℕ) (tb G K : ℝ) (center : ℕ → ℝ) (x : ι → ℝ)
    {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (e : StateExpr a ι) (comp : Fin u.length → Expr ι)
    (hx : ∀ i, 0 < x i) (hsmall : StateSmallAtoms e)
    (hc : ∀ i, ∃ j, comp i = .atom j)
    (he : e.plus.RelativeControl x K ∧ e.minus.RelativeControl x K)
    (hplus : 0 < e.plus.realEval x) (hminus : 0 < e.minus.realEval x)
    (hP : 0 < (pivotExpr hs e comp).realEval x)
    (hPG : G - 1 ≤ Real.log ((pivotExpr hs e comp).realEval x))
    (hleft : Real.log (halfProduct e.plus hp (leftPart (splitSlots hs e)) x) ≤
      G + (2 : ℝ)^l * (2*tb + inheritedCenter b k l center) + inheritedWidth k l)
    (hright : Real.log (halfProduct e.minus hm (rightPart (splitSlots hs e)) x) ≤
      G + (2 : ℝ)^l * (2*tb + inheritedCenter b k l center) + inheritedWidth k l)
    (hremoved : (2 : ℝ)^l * removedCenter b k l center - removedWidth k l ≤
      Real.log (realProduct u comp x))
    (hK : Real.exp (sourceCancellationExponent V b k tb center l) ≤ K) :
    (pivotExpr hs e comp).RelativeControl x K := by
  have hs0 := History.supported_root_frequency_ne_zero hs
  have hsR : (a.frequency : ℝ) ≠ 0 := by exact_mod_cast hs0
  have hv0 := History.supported_root_frequency_ne_zero (History.supported_left hs)
  have hw0 := History.supported_root_frequency_ne_zero (History.supported_right hs)
  have hsmallpos : ∀ i, 0 < (e.small i).realEval x := by
    intro i
    obtain ⟨j, hj⟩ := hsmall i
    rw [hj]
    exact hx j
  have hcpos : ∀ i, 0 < (comp i).realEval x := by
    intro i
    obtain ⟨j, hj⟩ := hc i
    rw [hj]
    exact hx j
  have hu := realProduct_pos u comp x hcpos
  have hHl : 0 < halfProduct e.plus hp (leftPart (splitSlots hs e)) x :=
    mul_pos hplus (realProduct_pos _ _ _ (fun i => hsmallpos _))
  have hHr : 0 < halfProduct e.minus hm (rightPart (splitSlots hs e)) x :=
    mul_pos hminus (realProduct_pos _ _ _ (fun i => hsmallpos _))
  let P := (pivotExpr hs e comp).realEval x
  let N := (left.root.frequency : ℝ) * halfProduct e.minus hm (rightPart (splitSlots hs e)) x -
    (right.root.frequency : ℝ) * halfProduct e.plus hp (leftPart (splitSlots hs e)) x
  have hPeq : P = N / ((a.frequency : ℝ) * realProduct u comp x) := by
    simp only [P, N, pivotExpr, pivot_realEval, halfProduct, realProduct_eq_product_realEval]
  have hN : N = (a.frequency : ℝ) * realProduct u comp x * P := by
    rw [hPeq]
    field_simp
  have hN0 : N ≠ 0 := by
    rw [hN]
    exact mul_ne_zero (mul_ne_zero hsR hu.ne') hP.ne'
  have hv := supported_frequency_exp_bound (History.supported_left hs)
  have hw := supported_frequency_exp_bound (History.supported_right hs)
  have hratio (v : ℤ) (H : ℝ) (hH : 0 < H)
      (hv : |(v : ℝ)| ≤ Real.exp (Real.log ((V l : ℝ)+1)))
      (hHlog : Real.log H ≤ G+(2:ℝ)^l*(2*tb+inheritedCenter b k l center)+inheritedWidth k l) :
      |(v : ℝ)*H/N| ≤ K := by
    rw [hN]
    apply le_trans _ hK
    unfold sourceCancellationExponent
    apply pivot_numerator_ratio_le a.frequency v H (realProduct u comp x) P G
      ((2:ℝ)^l*removedCenter b k l center)
      ((2:ℝ)^l*(2*tb+inheritedCenter b k l center-removedCenter b k l center))
      (Real.log ((V l:ℝ)+1)) (inheritedWidth k l) (removedWidth k l)
      hs0 hH hu hP hv _ hremoved hPG
    convert hHlog using 1; ring
  have hrl := hratio left.root.frequency _ hHr hv hright
  have hrr := hratio right.root.frequency _ hHl hw hleft
  have hcontrol (f : Fin u.length → Expr ι) (hf : ∀i,∃j,f i=.atom j) :
      ∀ z ∈ List.ofFn f, z.RelativeControl x K := by
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    obtain ⟨j,hj⟩ := hf i
    rw [hj]
    exact (hx j).ne'
  have hhp : ∀ z ∈ List.ofFn (leftPart (splitSlots hs e)), z.RelativeControl x K := by
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    obtain ⟨j,hj⟩ := hsmall _
    change (e.small _).RelativeControl x K
    rw [hj]
    exact (hx j).ne'
  have hhm : ∀ z ∈ List.ofFn (rightPart (splitSlots hs e)), z.RelativeControl x K := by
    intro z hz
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz
    obtain ⟨j,hj⟩ := hsmall _
    change (e.small _).RelativeControl x K
    rw [hj]
    exact (hx j).ne'
  apply pivot_relativeControl a.frequency left.root.frequency right.root.frequency
    e.plus e.minus _ _ _ x K hs0 hv0 hw0 he.1 he.2 (hcontrol comp hc) hhp hhm
  · simpa only [N, halfProduct, realProduct_eq_product_realEval] using hN0
  · simpa only [N, halfProduct, realProduct_eq_product_realEval] using hrl
  · simpa only [N, halfProduct, realProduct_eq_product_realEval] using hrr

end Ostmann.Arithmetic.HistorySymbolicEncoding

end

end OAI
