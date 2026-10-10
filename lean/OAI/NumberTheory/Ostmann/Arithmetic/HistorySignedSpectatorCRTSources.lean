import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepresentativeSourceSeparationSelected
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesPrecision
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorCRTBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedSpectatorCRT
open Construction HistorySignedDecode HistorySignedResidues
open HistoryRepresentativeSourceSeparation

theorem divisorProduct_coprime_outside {l : ℕ} (h : History l)
    {V : ℕ→ℕ} {outside : List ℕ} (hs : h.Supported V outside)
    (hf : ∀s∈h.frequencies,Nat.Coprime s.natAbs outside.prod) :
    Nat.Coprime (divisorProduct h).natAbs outside.prod := by
  induction h with
  | leaf a => simp [divisorProduct]
  | node a p u hp hm left right il ir =>
    have hu : Nat.Coprime (u.map SmallSlot.value).prod outside.prod := by
      apply Nat.coprime_list_prod_left_iff.mpr
      intro q hq
      obtain ⟨slot,hslot,rfl⟩ := List.mem_map.mp hq
      exact rootSlot_coprime_outside left (History.supported_left hs) slot
        ((History.supported_child_small hs).1.mem_iff.mpr (List.mem_append_left _ hslot))
    have ha := hf a.frequency (by simp [History.frequencies])
    have hl := il (History.supported_left hs)
      (fun s hmem=>hf s (by simp only [History.frequencies,List.mem_cons,List.mem_append]; exact Or.inr (Or.inl hmem)))
    have hr := ir (History.supported_right hs)
      (fun s hmem=>hf s (by simp only [History.frequencies,List.mem_cons,List.mem_append]; exact Or.inr (Or.inr hmem)))
    simpa only [divisorProduct,Int.natAbs_mul,Int.natAbs_natCast] using ((ha.mul_left hu).mul_left hl).mul_left hr

theorem pairedDivisorProduct_coprime_outside {l : ℕ} (h k : History l)
    {V : ℕ→ℕ} {outside : List ℕ} (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hp : PairAdmissible h k outside) :
    Nat.Coprime (pairedDivisorProduct h k).natAbs outside.prod := by
  have hf : Nat.Coprime (FrequencyPrecision.product (h.frequencies++k.frequencies)) outside.prod := by
    simpa only [pow_one] using (hp.2.2.2 1).2.2.2.1.symm
  have hall : ∀s∈h.frequencies++k.frequencies,Nat.Coprime s.natAbs outside.prod := by
    intro s hs'
    apply hf.of_dvd_left
    exact List.dvd_prod (List.mem_map.mpr ⟨s,hs',rfl⟩)
  simpa only [pairedDivisorProduct,Int.natAbs_mul] using
    (divisorProduct_coprime_outside h hs (fun s hm=>hall s (List.mem_append_left _ hm))).mul_left
    (divisorProduct_coprime_outside k ks (fun s hm=>hall s (List.mem_append_right _ hm)))

theorem pair_spectator_eq_mod_outside {l : ℕ} (h k : History l)
    {V : ℕ→ℕ} {outside : List ℕ} (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (g : (q:ℕ)→ZMod q→ℂ) (Xp Xm Yp Ym : ℤ)
    (hxi : (rebuild h Xp Xm).IntegralGuard) (kxi : (rebuild k Xp Xm).IntegralGuard)
    (hyi : (rebuild h Yp Ym).IntegralGuard) (kyi : (rebuild k Yp Ym).IntegralGuard)
    (hplus : Xp≡Yp [ZMOD (outside.prod:ℤ)]) (hminus : Xm≡Ym [ZMOD (outside.prod:ℤ)]) :
    HistorySignedSpectator.pairSpectator g outside (rebuild h Xp Xm) (rebuild k Xp Xm)=
      HistorySignedSpectator.pairSpectator g outside (rebuild h Yp Ym) (rebuild k Yp Ym) := by
  have hd := paired_divisorData h k hs ks
  have hc : Nat.Coprime (pairedDivisorProduct h k).natAbs (outside.prod:ℤ).natAbs := by
    simpa only [Int.natAbs_natCast] using pairedDivisorProduct_coprime_outside h k hs ks had
  apply HistorySignedSpectator.pairSpectator_eq_of_congruent (N := (outside.prod:ℤ)) g outside
    (fun q hq=>by exact_mod_cast List.dvd_prod hq)
  · exact rebuild_congruent_integral h _ _ Xp Xm Yp Ym hd.1 hc hxi hyi hplus hminus
  · exact rebuild_congruent_integral k _ _ Xp Xm Yp Ym hd.2 hc kxi kyi hplus hminus

end Ostmann.Arithmetic.HistorySignedSpectatorCRT

end

end OAI
