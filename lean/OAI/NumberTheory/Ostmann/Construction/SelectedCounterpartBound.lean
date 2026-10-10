import OAI.NumberTheory.Ostmann.Construction.SelectedCounterpartWindows

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction

private theorem list_prod_unit_interval (xs : List ℝ)
    (h : ∀a∈xs,0≤a ∧ a≤1) : xs.prod≤1 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hx : ∀b∈xs,0≤b ∧ b≤1 := fun b hb => h b (List.mem_cons_of_mem a hb)
    have hp : 0≤xs.prod := List.prod_nonneg (fun b hb => (hx b hb).1)
    exact (mul_le_mul_of_nonneg_right (h a List.mem_cons_self).2 hp).trans
      (by simpa only [one_mul] using ih hx)

theorem counterpart_cell_product_bounds (G : ℝ) (center : ℕ→ℝ) (q : ℕ) (xs : List SmallSlot) :
    0≤Ostmann.smoothPartition (Real.log q-G)*
      ((xs.filter (fun z => decide (z.role≠.bulk))).map
        (fun z => Ostmann.smoothPartition (Real.log (z.value:ℝ)-center z.origin))).prod ∧
    Ostmann.smoothPartition (Real.log q-G)*
      ((xs.filter (fun z => decide (z.role≠.bulk))).map
        (fun z => Ostmann.smoothPartition (Real.log (z.value:ℝ)-center z.origin))).prod≤1 := by
  have hp : 0≤((xs.filter (fun z => decide (z.role≠.bulk))).map
        (fun z => Ostmann.smoothPartition (Real.log (z.value:ℝ)-center z.origin))).prod := by
    apply List.prod_nonneg
    intro a ha
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
    exact Ostmann.smoothPartition_nonneg _
  have hle : ((xs.filter (fun z => decide (z.role≠.bulk))).map
        (fun z => Ostmann.smoothPartition (Real.log (z.value:ℝ)-center z.origin))).prod≤1 := by
    apply list_prod_unit_interval
    intro a ha
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp ha
    exact ⟨Ostmann.smoothPartition_nonneg _,Ostmann.smoothPartition_le_one _⟩
  exact ⟨mul_nonneg (Ostmann.smoothPartition_nonneg _) hp,
    (mul_le_mul (Ostmann.smoothPartition_le_one _) hle hp zero_le_one).trans_eq (one_mul _)⟩

theorem remainingCounterpart_le (sources : SourceFamily) (T : List SourceSlot) (j : ℕ)
    (giant : PrimeSource) (A B G WH WU : ℝ) (center : ℕ→ℝ)
    (u : SourceAssignment sources (Template.extracted j T))
    (y : RemainingSample sources (Template.remainder j T) giant)
    (hH : |Real.log (remainingProduct sources (Template.remainder j T) giant y:ℝ)-A|≤WH)
    (hU : |Real.log (((assignedSlots sources (Template.extracted j T) u).map SmallSlot.value).prod:ℝ)-B|≤WU) :
    0≤remainingCounterpart sources T j giant A B G center u y ∧
      remainingCounterpart sources T j giant A B G center u y≤Real.exp (WH+WU) := by
  have hp : (0:ℝ)<remainingProduct sources (Template.remainder j T) giant y := by
    exact_mod_cast remainingProduct_pos sources _ giant y
  have hu : (0:ℝ)<((assignedSlots sources (Template.extracted j T) u).map SmallSlot.value).prod := by
    exact_mod_cast assignedSlots_product_pos sources _ u
  have h₁ : Real.exp A/(remainingProduct sources (Template.remainder j T) giant y:ℝ)≤Real.exp WH := by
    apply (Real.log_le_iff_le_exp (div_pos (Real.exp_pos _) hp)).mp
    rw [Real.log_div (Real.exp_pos _).ne' hp.ne',Real.log_exp]
    linarith [(abs_le.mp hH).1]
  have h₂ : (((assignedSlots sources (Template.extracted j T) u).map SmallSlot.value).prod:ℝ)/Real.exp B≤Real.exp WU := by
    apply (Real.log_le_iff_le_exp (div_pos hu (Real.exp_pos _))).mp
    rw [Real.log_div hu.ne' (Real.exp_pos _).ne',Real.log_exp]
    linarith [(abs_le.mp hU).2]
  have hc := counterpart_cell_product_bounds G center y.1.val (assignedSlots sources (Template.remainder j T) y.2)
  constructor
  · exact mul_nonneg (mul_nonneg (div_pos (Real.exp_pos _) hp).le (div_pos hu (Real.exp_pos _)).le) hc.1
  · calc
      _ ≤ (Real.exp WH*Real.exp WU)*1 :=
        mul_le_mul (mul_le_mul h₁ h₂ (div_pos hu (Real.exp_pos _)).le (Real.exp_pos _).le)
          hc.2 hc.1 (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le
      _ = _ := by rw [mul_one,Real.exp_add]

namespace InitialSourceChoice
open Conclusion Arithmetic.HistoryProductWindows
variable {d : Decomposition} {Bs BD Bz : ℝ} {k : ℕ} {L : ℝ} {E : Finset ℕ}
local notation "b₀" => (bulkSize k L/2)

theorem counterpart_bound_of_coefficient (C : InitialSourceChoice d Bs BD Bz k L E)
    (s l : ℕ) (hl : l<k) (X : ℝ) (outside : List ℕ) (p : ℕ)
    (u : SourceAssignment C.sources (Template.extracted (l+1)
      (Template.current (Template.initial (2*b₀) k) l)))
    (y : RemainingSample C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant) (v : ℤ)
    (hu : (assignmentPrior C.sources (Template.extracted (l+1)
      (Template.current (Template.initial (2*b₀) k) l))).mass u≠0)
    (hy : (remainingPrior C.sources (Template.remainder (l+1)
      (Template.current (Template.initial (2*b₀) k) l)) C.giant).mass y≠0)
    (hA : actualCoefficient C.sources (Template.initial (2*b₀) k) (frequencyBound Bs BD Bz k L)
      X C.giantCenter (residueTransform d) (Arithmetic.sourceStateBins b₀ s C.bulkBin C.spectatorBin)
      outside l (remainingState C.sources (Template.current (Template.initial (2*b₀) k) l)
        (l+1) C.giant p u y v)≠0) :
    let K := remainingCounterpart C.sources (Template.current (Template.initial (2*b₀) k) l)
      (l+1) C.giant ((C.giantCenter:ℝ)+C.compensationLogScale l+stepGap BD Bz k L l)
      (C.compensationLogScale l) C.giantCenter (C.cells.center b₀) u y
    0≤K ∧ K≤Real.exp (nominalInheritedWidth k l+nominalRemovedWidth k l) := by
  have hw := C.remaining_nominal_windows s l hl X outside p u y v hu hy hA
  exact remainingCounterpart_le C.sources _ (l+1) C.giant _ _ C.giantCenter
    (nominalInheritedWidth k l) (nominalRemovedWidth k l) (C.cells.center b₀) u y hw.1 hw.2

end InitialSourceChoice
end Ostmann.Construction

end

end OAI
