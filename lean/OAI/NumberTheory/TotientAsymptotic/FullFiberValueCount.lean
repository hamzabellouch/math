import OAI.NumberTheory.TotientAsymptotic.PublishedFiber

namespace OAI

/-! A full fiber with seed one gives an injective family of totient values. -/
noncomputable section
namespace TotientAsymptotic

lemma fullFiber_one_totient_injective {b c : ℕ} (hb : 0 < b) (hc : 0 < c)
    (hbfull : FullFiber 1 b) (hcfull : FullFiber 1 c)
    (he : b.totient=c.totient) : b=c := by
  obtain ⟨u,hu,_huφ,heu⟩ := (hcfull b).mp ⟨hb,by simpa only [one_mul] using he⟩
  obtain ⟨v,hv,_hvφ,hev⟩ := (hbfull c).mp ⟨hc,by simpa only [one_mul] using he.symm⟩
  have hcb : c ≤ b := by rw [heu]; exact Nat.le_mul_of_pos_right _ hu
  have hbc : b ≤ c := by rw [hev]; exact Nat.le_mul_of_pos_right _ hv
  exact Nat.le_antisymm hbc hcb

theorem fullFiber_one_card_le_V {x : ℝ} (S : Finset ℕ)
    (hS : ∀ b ∈ S,0 < b ∧ (b.totient:ℝ) ≤ x ∧ FullFiber 1 b) :
    (S.card:ℝ) ≤ V x := by
  classical
  have hinj : Set.InjOn Nat.totient (S : Set ℕ) := by
    intro b hb c hc he
    exact fullFiber_one_totient_injective (hS b hb).1 (hS c hc).1
      (hS b hb).2.2 (hS c hc).2.2 he
  have hsub : S.image Nat.totient ⊆ (Finset.Icc 1 ⌊x⌋₊).filter IsTotient := by
    intro v hv
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hbpos,hbx,_hbfull⟩ := hS b hb
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.totient_pos.mpr hbpos,?_⟩,b,hbpos,rfl⟩
    exact Nat.le_floor hbx
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj] at hc
  unfold V
  exact_mod_cast hc

end TotientAsymptotic

end

end OAI
