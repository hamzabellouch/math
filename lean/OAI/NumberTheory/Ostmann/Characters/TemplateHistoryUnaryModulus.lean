import OAI.NumberTheory.Ostmann.Characters.HistoryFrequencyLabelsModulus
import OAI.NumberTheory.Ostmann.Characters.TemplateHistoryUnaryRegular

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template

theorem historyFrequencyUnits_of_labels {p j : ℕ} {path : List Bool} {s : ℤ}
    {t : HistoryReconstruction.Tree j}
    (h : ∀ a f, (a,f)∈HistoryFrequencyLabels.labels j path s t → (f:ZMod p)≠0) :
    HistoryFrequencyUnits p j s t := by
  induction j generalizing path s with
  | zero => exact h path s (HistoryFrequencyLabels.root_mem_labels _ _ _ _)
  | succ j ih =>
    refine ⟨h path s (HistoryFrequencyLabels.root_mem_labels _ _ _ _),?_,?_⟩
    · apply ih
      intro a f hf
      exact h a f (List.mem_cons_of_mem _ (List.mem_append_left _ hf))
    · apply ih
      intro a f hf
      exact h a f (List.mem_cons_of_mem _ (List.mem_append_right _ hf))

theorem historyFrequencyUnits_of_modulus_coprime {p j : ℕ} [Fact p.Prime]
    (path : List Bool) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (hcop : p.Coprime (HistoryFrequencyLabels.modulus j path s t)) :
    HistoryFrequencyUnits p j s t := by
  apply historyFrequencyUnits_of_labels (path:=path)
  intro a f hf hz
  have hdZ : (p:ℤ)∣f := (ZMod.intCast_zmod_eq_zero_iff_dvd f p).mp hz
  have hdN : p∣f.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hdZ
  have hd := hdN.trans (HistoryFrequencyLabels.frequency_dvd_modulus hf)
  exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hcop) hd

theorem norm_supportedHistoryUnary_of_coprime (k : ℕ) (width : Role → ℕ) {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ≠1) (S : List Bool → Finset ℤ)
    (j : ℕ) (path : List Bool) (h : HistoryFrequencyLabels.SupportedHistory S j path)
    (hcop : p.Coprime (HistoryFrequencyLabels.modulus j path h.val.1 h.val.2))
    (i : (schedule k j).Constituent width) :
    ‖supportedHistoryUnary k width χ (fun _ => initialKappa χ) S j path h i‖=1 :=
  norm_actualHistoryUnary k width χ hχ j h.val.1 h.val.2
    (historyFrequencyUnits_of_modulus_coprime path h.val.1 h.val.2 hcop) i

theorem supportedHistoryUnary_regular_of_coprime (k : ℕ) (width : Role → ℕ)
    {p : ℕ} [Fact p.Prime] (χ : MulChar (ZMod p) ℂ) (hχ : χ≠1)
    (S : List Bool → Finset ℤ) (j : ℕ) (hj : j≤k) (path : List Bool)
    (h : HistoryFrequencyLabels.SupportedHistory S j path)
    (hcop : p.Coprime (HistoryFrequencyLabels.modulus j path h.val.1 h.val.2))
    (i : (schedule k j).Constituent width) (hi : (schedule k j).IsRegular j i.1) :
    supportedHistoryUnary k width χ (fun _ => initialKappa χ) S j path h i =
      historyRegularKappa k width χ (fun _ => initialKappa χ) j i *
        χ (h.val.1:ZMod p)^(-(rowSign k j i.1:ℤ)) :=
  actualHistoryUnary_regular k width χ hχ j hj h.val.1 h.val.2
    (historyFrequencyUnits_of_modulus_coprime path h.val.1 h.val.2 hcop) i hi

end Ostmann.Characters.Template

end

end OAI
