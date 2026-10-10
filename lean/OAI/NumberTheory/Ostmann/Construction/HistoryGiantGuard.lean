import OAI.NumberTheory.Ostmann.Construction.HistorySupportSplit

namespace OAI

noncomputable section
namespace Ostmann.Construction.History

theorem supported_frequency_bounds {V : ℕ → ℕ} {outside : List ℕ} {l : ℕ}
    {h : History l} (hs : h.Supported V outside) :
    ∀ s∈h.frequencies, s≠0 ∧ ∃ j≤l,s.natAbs≤V j := by
  induction h with
  | leaf a =>
    intro s hs'
    have heq : s=a.frequency := by simpa only [frequencies,List.mem_singleton] using hs'
    subst s
    exact ⟨supported_root_frequency_ne_zero hs,0,le_rfl,supported_root_frequency_bound hs⟩
  | @node l a p u hp hm left right ihl ihr =>
    intro s hs'
    simp only [frequencies,List.mem_cons,List.mem_append] at hs'
    rcases hs' with rfl | hs' | hs'
    · exact ⟨supported_root_frequency_ne_zero hs,l+1,le_rfl,supported_root_frequency_bound hs⟩
    · obtain ⟨hne,j,hjl,hj⟩ := ihl (supported_left hs) s hs'
      exact ⟨hne,j,by omega,hj⟩
    · obtain ⟨hne,j,hjl,hj⟩ := ihr (supported_right hs) s hs'
      exact ⟨hne,j,by omega,hj⟩

theorem prime_coprime_small_frequency {p : ℕ} (hp : Nat.Prime p) {s : ℤ}
    (hs : s≠0) (hsize : s.natAbs<p) : Nat.Coprime p s.natAbs := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hpos : 0<s.natAbs := Int.natAbs_pos.mpr hs
  exact (not_le_of_gt hsize) (Nat.le_of_dvd hpos hd)

theorem giantGuard_of_prime_bounds {V : ℕ → ℕ} {outside : List ℕ} {l : ℕ}
    {h : History l} (hs : h.Supported V outside) (a : State)
    (hp : Nat.Prime a.giantPlus) (hm : Nat.Prime a.giantMinus)
    (hV : ∀ j≤l,V j<a.giantPlus ∧ V j<a.giantMinus) : giantGuard a h := by
  intro s hmem
  obtain ⟨hs0,j,hjl,hj⟩ := supported_frequency_bounds hs s hmem
  exact ⟨prime_coprime_small_frequency hp hs0 (hj.trans_lt (hV j hjl).1),
    prime_coprime_small_frequency hm hs0 (hj.trans_lt (hV j hjl).2)⟩

theorem guardedWeight_eq_supportedWeight (V : ℕ → ℕ) (outside : List ℕ)
    (base : State → ℂ) (φ : ℝ → ℝ) (G : ℝ) {l : ℕ} (h : History l) (a : State)
    (hp : Nat.Prime a.giantPlus) (hm : Nat.Prime a.giantMinus)
    (hV : ∀ j≤l,V j<a.giantPlus ∧ V j<a.giantMinus) :
    guardedWeight a V outside base φ G h=h.supportedWeight V outside base φ G := by
  classical
  by_cases hs : h.Supported V outside
  · have hg := giantGuard_of_prime_bounds hs a hp hm hV
    simp only [guardedWeight,supportedWeight,hs,hg,and_self,ite_true]
  · simp only [guardedWeight,supportedWeight,hs,false_and,ite_false]

end Ostmann.Construction.History

end

end OAI
