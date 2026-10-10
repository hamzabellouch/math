import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorDiagramProduct

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedSpectatorDiagram
open Construction HistorySignedSpectatorCRT HistoryRepresentativeSourceSeparation

theorem exists_cast_zero_of_nonunit (outside : List ℕ)
    (hprime : ∀ q ∈ outside, q.Prime) (x : ZMod outside.prod) (hx : ¬ IsUnit x) :
    ∃ q ∈ outside, (ZMod.cast x : ZMod q) = 0 := by
  classical
  have hprod : 0 < outside.prod := List.prod_pos (fun q hq => (hprime q hq).pos)
  let : NeZero outside.prod := ⟨ne_of_gt hprod⟩
  by_contra h
  apply hx
  have hc : Nat.Coprime x.val outside.prod := by
    apply Nat.coprime_list_prod_right_iff.mpr
    intro q hq
    apply Nat.Coprime.symm
    apply (hprime q hq).coprime_iff_not_dvd.mpr
    intro hd
    apply h
    refine ⟨q,hq,?_⟩
    rw [ZMod.cast_eq_val]
    exact (ZMod.natCast_eq_zero_iff x.val q).mpr hd
  simpa only [ZMod.natCast_zmod_val] using
    (ZMod.isUnit_iff_coprime x.val outside.prod).mpr hc

theorem residuePairSpectator_zero_of_nonunit {l : ℕ} (h k : History l)
    {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hprime : ∀ q ∈ outside, q.Prime)
    (g : (q : ℕ) → ZMod q → ℂ) (hg : ∀ q ∈ outside, g q 0 = 0)
    (Xp Xm : ZMod outside.prod) (hx : ¬ IsUnit Xp ∨ ¬ IsUnit Xm) :
    residuePairSpectator g outside outside.prod h k (Xp,Xm) = 0 := by
  classical
  obtain ⟨q,hq,hzero⟩ : ∃ q ∈ outside,
      (ZMod.cast Xp : ZMod q) = 0 ∨ (ZMod.cast Xm : ZMod q) = 0 := by
    rcases hx with hx | hx
    · obtain ⟨q,hq,hz⟩ := exists_cast_zero_of_nonunit outside hprime Xp hx
      exact ⟨q,hq,Or.inl hz⟩
    · obtain ⟨q,hq,hz⟩ := exists_cast_zero_of_nonunit outside hprime Xm hx
      exact ⟨q,hq,Or.inr hz⟩
  let : Fact q.Prime := ⟨hprime q hq⟩
  rw [residuePairSpectator_eq_primeProduct_actual h k hs ks had]
  apply List.prod_eq_zero
  apply List.mem_map.mpr
  refine ⟨q,hq,?_⟩
  rw [primeSpectator_zero_of_giant q (g q) (hg q hq) _ h _ _ hzero,zero_mul]

theorem residuePairSpectator_zero_of_nonunit_left {l : ℕ} (h k : History l)
    {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hprime : ∀ q ∈ outside, q.Prime)
    (g : (q : ℕ) → ZMod q → ℂ) (hg : ∀ q ∈ outside, g q 0 = 0)
    (Xp Xm : ZMod outside.prod) (hx : ¬ IsUnit Xp) :
    residuePairSpectator g outside outside.prod h k (Xp,Xm) = 0 :=
  residuePairSpectator_zero_of_nonunit h k hs ks had hprime g hg Xp Xm (Or.inl hx)

theorem residuePairSpectator_zero_of_nonunit_right {l : ℕ} (h k : History l)
    {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (had : PairAdmissible h k outside) (hprime : ∀ q ∈ outside, q.Prime)
    (g : (q : ℕ) → ZMod q → ℂ) (hg : ∀ q ∈ outside, g q 0 = 0)
    (Xp Xm : ZMod outside.prod) (hx : ¬ IsUnit Xm) :
    residuePairSpectator g outside outside.prod h k (Xp,Xm) = 0 :=
  residuePairSpectator_zero_of_nonunit h k hs ks had hprime g hg Xp Xm (Or.inr hx)

end Ostmann.Arithmetic.HistorySignedSpectatorDiagram

end

end OAI
