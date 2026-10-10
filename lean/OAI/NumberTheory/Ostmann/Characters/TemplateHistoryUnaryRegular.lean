import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryNorm

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem complex_character_regular_unary_transport {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (κ : ℂ) (hκ : ‖κ‖=1)
    (f s δ : ZMod p) (hf : f≠0) (hs : s≠0) (hδ : δ≠0) (ε t : ℤ) :
    (κ*χ f^(-ε))^t*χ (δ*f/s)^(t*ε) =
      (κ^t*χ δ^(t*ε))*χ s^(-(t*ε)) := by
  have hκ0 : κ≠0 := by intro he; simp [he] at hκ
  have hh := congrArg (fun z : ℂˣ => (z:ℂ))
    (character_regular_unary_transport χ (Units.mk0 κ hκ0)
      (Units.mk0 f hf) (Units.mk0 s hs) (Units.mk0 δ hδ) ε t)
  simpa only [Units.val_mul,Units.val_zpow_eq_zpow_val,MulChar.coe_toUnitHom,
    Units.val_div_eq_div_val,Units.val_mk0] using hh

theorem unaryPivotColumn_regular (k j : ℕ) (hj : j<k)
    (i : {i : (schedule k j).Slot // (schedule k j).IsCopied j i})
    (hi : (schedule k j).IsRegular j i.val) :
    unaryPivotColumn k j i.val=(rowSign k j i.val:ℤ) := by
  rw [unaryPivotColumn,dite_eq_left hj]
  apply graph_regular k j hj.le i.val hi
  intro he
  have hp : (schedule k j).IsPivot j i.val := he ▸ (pivotSlot k j hj).property
  exact pivot_not_copied _ _ _ hp i.property

theorem historyUnary_regular (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (κ : (schedule k 0).Constituent width → ℂ)
    (hκ : ∀ i, ‖κ i‖=1) (j : ℕ) (hj : j≤k) (s : ℤ)
    (t : HistoryReconstruction.Tree j) (ht : HistoryFrequencyUnits p j s t)
    (i : (schedule k j).Constituent width) (hi : (schedule k j).IsRegular j i.1) :
    historyUnary k width χ κ j s t i = historyRegularKappa k width χ κ j i *
      χ (s:ZMod p)^(-(rowSign k j i.1:ℤ)) := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    rcases i with ⟨i,a⟩
    obtain ⟨q,b,he,hq⟩ := step_regular_cases (schedule k j) j i hi
    subst i
    rw [historyUnary,ih (by omega) _ _ (ht.child b) _ hq,
      unaryPivotColumn_regular k j (by omega) q hq]
    have hsign : (copySign b:ZMod p)≠0 := by cases b <;> simp [copySign]
    have he : signedChildFrequency t.1.1 t.1.2 b=copySign b*unaryChildFrequency t b := by
      cases b <;> simp [signedChildFrequency,copySign,unaryChildFrequency]
    rw [he,Int.cast_mul]
    simpa only [historyRegularKappa,rowSign,Units.val_mul,copyUnit_coe] using
      complex_character_regular_unary_transport χ
        (historyRegularKappa k width χ κ j ⟨q.val,a⟩)
        (norm_historyRegularKappa k width χ κ hκ j _) _ _ _
        (ht.child b).root ht.1 hsign (rowSign k j q.val:ℤ) (copySign b)

theorem actualHistoryUnary_regular (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ≠1) (j : ℕ) (hj : j≤k) (s : ℤ)
    (t : HistoryReconstruction.Tree j) (ht : HistoryFrequencyUnits p j s t)
    (i : (schedule k j).Constituent width) (hi : (schedule k j).IsRegular j i.1) :
    actualHistoryUnary k width χ j s t i =
      historyRegularKappa k width χ (fun _ => initialKappa χ) j i *
        χ (s:ZMod p)^(-(rowSign k j i.1:ℤ)) :=
  historyUnary_regular k width χ _ (fun _ => norm_initialKappa χ hχ) j hj s t ht i hi

end Ostmann.Characters.Template

end

end OAI
