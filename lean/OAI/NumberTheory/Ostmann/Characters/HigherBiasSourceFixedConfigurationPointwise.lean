import OAI.NumberTheory.Ostmann.Characters.HigherBiasSourceFixedConfigurationCells

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource
open Construction Preliminaries

def GoodTargetList {d : Decomposition} {Q : ℕ} {E : Finset (PrimeUpTo Q)}
    {δ : ℝ} (F : HigherBiasSourceFamily d Q E δ) (c U : ℝ) (k : ℕ)
    (n : ℤ) (T : ℝ) (l : List ℤ) : Prop :=
  (∃ a : ℝ,U ≤ a ∧ ∀ h∈l,Real.exp a < (h:ℝ) ∧ (h:ℝ)+1 ≤ Real.exp (a+1) ∧
    c/Real.exp a ≤ primeShellMass (boundedRawLogCell E h) ∧
    ∃ hp : 0 < primeShellMass (boundedRawLogCell E h),
      δ/4 ≤ ((primeShellPrior (boundedRawLogCell E h) hp).cmean
        (fun p => F.test p (n:ZMod p.val))).re) ∧
  |(l.sum:ℝ)-T| ≤ 6/c ∧ Real.exp ((1/10000:ℝ)*k)/6 ≤ (l.length:ℝ) ∧
  (l.length:ℝ) ≤ 2*Real.exp (2*((1/10000:ℝ)*k))

theorem selected_base_mean {d : Decomposition} {E : Finset ℕ} {δ L : ℝ}
    {k : ℕ} {α β ρ γ c0 : ℝ}
    (s : SelectedWordSource d E δ L k α β ρ γ c0) {n : ℤ} (hn : n∈s.endpoints)
    (i : Fin 3) (hp : 0 < primeShellMass (s.locations.base i)) :
    δ/2 ≤ ((primeShellPrior (s.locations.base i) hp).cmean
      (fun p => s.family.test p (n:ZMod p.val))).re := by
  have hh := s.shell_means n hn (firstTestIndex k i)
  simpa only [SourceLocations.tests,testedShellFamily_first] using hh

theorem exists_configuration_at_endpoint {d : Decomposition} {E : Finset ℕ} {δ L : ℝ}
    {k : ℕ} {α β ρ γ c0 c aMin BD : ℝ}
    (s : SelectedWordSource d E δ L k α β ρ γ c0)
    (hc : 0<c) (hc0 : 0<c0) (hproducer : GoodOriginalCellProducer c aMin c0 δ)
    (hband : ∀ p∈E,Real.log (Real.log p) ≤ β*L)
    (hsmin : aMin ≤ s.locations.s) (humin : aMin ≤ s.locations.u)
    (hsu : s.locations.s+1 ≤ s.locations.u) (hu0 : 0 ≤ s.locations.u)
    (hsmall : c0≤primeShellMass (s.locations.base 1))
    (htop : c0≤primeShellMass (s.locations.base 2))
    (hgap : ∀ j≤k,0≤InitialCharacterScale.gapSchedule BD k L j ∧
      InitialCharacterScale.gapSchedule BD k L j≤Real.exp s.locations.u/10)
    {n : ℤ} (hn : n∈s.endpoints)
    (htarget : ∀ T : ℝ,(1/10:ℝ)*2^k*Real.exp s.locations.u≤T →
      T≤600*4^k*Real.exp s.locations.u →
      ∃ l : List ℤ,GoodTargetList s.family c s.locations.U k n T l) :
    ∃ cfg : SourceConfiguration k,
      ConfigurationGeometry s c BD cfg ∧ ConfigurationGoodAt s c cfg n := by
  classical
  have hsp := hc0.trans_le hsmall
  have htp := hc0.trans_le htop
  obtain ⟨Is,hIs,hscells⟩ := hproducer d s.locations.Q s.locations.primes s.family
    s.locations.s n hsmin hsmall hsp (selected_base_mean s hn 1 hsp)
  obtain ⟨Ib,hIb,hbcells⟩ := hproducer d s.locations.Q s.locations.primes s.family
    s.locations.u n humin htop htp (selected_base_mean s hn 2 htp)
  have hIspos : 0<Is.card := by
    have hh : (0:ℝ)<Is.card := (mul_pos hc (Real.exp_pos _)).trans_le hIs
    exact_mod_cast hh
  have hIbpos : 0<Ib.card := by
    have hh : (0:ℝ)<Ib.card := (mul_pos hc (Real.exp_pos _)).trans_le hIb
    exact_mod_cast hh
  obtain ⟨a,ha⟩ := Finset.card_pos.mp hIspos
  obtain ⟨b,hb⟩ := Finset.card_pos.mp hIbpos
  have has := hscells a ha
  have hbs := hbcells b hb
  have hablo : 0≤(a:ℝ)+b := by linarith [Real.exp_pos s.locations.s,Real.exp_pos s.locations.u]
  have habhi : (a:ℝ)+b≤4*Real.exp s.locations.u := by
    have he := Real.exp_le_exp.mpr hsu
    have heb : Real.exp (s.locations.u+1) ≤ 3*Real.exp s.locations.u := by
      rw [Real.exp_add]
      nlinarith [Real.exp_one_lt_three,Real.exp_pos s.locations.u]
    linarith [has.2.1,hbs.2.1]
  let cfg0 : SourceConfiguration k := (repeatedAnchors k a b,fun _ => [])
  have ha0 : ∀ j<k,0≤configurationAnchorPair cfg0 j ∧
      configurationAnchorPair cfg0 j≤4*Real.exp s.locations.u := by
    intro j hj
    rw [configurationAnchorPair_repeated a b (fun _ => []) hj]
    exact ⟨hablo,habhi⟩
  have hX := higherSourceX_log_bounds k s.locations.u hu0
  have ht := HigherBiasSourceTargets.targets_bounds s.locations.k_pos
    (Real.exp_pos _) s.bin_lower s.bin_upper (configurationAnchorPair cfg0)
    (InitialCharacterScale.gapSchedule BD k L) ha0 hgap hX.2.1 hX.2.2
  have hex (j : Fin (k+1)) : ∃ l : List ℤ,GoodTargetList s.family c s.locations.U k n
      (configurationTarget (Real.log s.locations.X) s.J
        (InitialCharacterScale.gapSchedule BD k L) cfg0 j) l := by
    apply htarget
    · unfold configurationTarget
      split_ifs with hj
      · exact (ht.1 j.val hj).1
      · exact ht.2.1
    · unfold configurationTarget
      split_ifs with hj
      · exact (ht.1 j.val hj).2
      · exact ht.2.2
  choose lists hlists using hex
  let cfg : SourceConfiguration k := (repeatedAnchors k a b,lists)
  have hpair : configurationAnchorPair cfg=configurationAnchorPair cfg0 := rfl
  have htargeteq (j : Fin (k+1)) : configurationTarget (Real.log s.locations.X) s.J
      (InitialCharacterScale.gapSchedule BD k L) cfg j =
      configurationTarget (Real.log s.locations.X) s.J
        (InitialCharacterScale.gapSchedule BD k L) cfg0 j := rfl
  refine ⟨cfg,?_,?_⟩
  · exact {
      anchors := ⟨a,b,rfl,has.1,has.2.1,hbs.1,hbs.2.1⟩
      anchor_bound := by simpa only [hpair] using ha0
      length_lower := fun j => (hlists j).2.2.1
      length_upper := fun j => (hlists j).2.2.2
      target_error := fun j => by simpa only [htargeteq] using (hlists j).2.1
      list_entry_lower := by
        intro j i hi
        obtain ⟨z,hUz,hcells⟩ := (hlists j).1
        exact (Real.exp_le_exp.mpr hUz).trans (hcells i hi).1.le }
  · unfold ConfigurationGoodAt
    apply configCellIndices_property cfg (fun h : ℤ =>
      0 ≤ h ∧ (h:ℝ) ≤ Real.exp (β*L) ∧
      c/Real.exp (β*L) ≤ primeShellMass (boundedRawLogCell s.locations.primes h) ∧
      ∃ hp : 0 < primeShellMass (boundedRawLogCell s.locations.primes h),
        δ/4 ≤ ((primeShellPrior (boundedRawLogCell s.locations.primes h) hp).cmean
          (fun p => s.family.test p (n:ZMod p.val))).re)
    · intro i
      dsimp only [cfg,repeatedAnchors]
      split_ifs
      · exact good_cell_uniform s.family hc hband has.1 has.2.2.1 has.2.2.2
      · exact good_cell_uniform s.family hc hband hbs.1 hbs.2.2.1 hbs.2.2.2
    · intro j h hh
      obtain ⟨z,hUz,hz⟩ := (hlists j).1
      have hh' := hz h hh
      exact good_cell_uniform s.family hc hband hh'.1 hh'.2.2.1 hh'.2.2.2

end Ostmann.Characters.HigherBiasSource

end

end OAI
