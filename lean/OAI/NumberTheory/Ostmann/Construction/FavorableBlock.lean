import OAI.NumberTheory.Ostmann.Construction.FavorableBlockScale

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Construction
open Filter
open scoped BigOperators

theorem exists_favorable_log_block :
    ∀ᶠ L : ℝ in atTop, ∀ S : Finset ℕ,
      (∀p∈S,p.Prime ∧ (1/20:ℝ)*L≤Real.log (Real.log p) ∧
        Real.log (Real.log p)≤(9/10:ℝ)*L) →
      (3/20:ℝ)*L≤harmonicPrimeMass S →
      ∃ G : ℝ, ∃ P : Finset ℕ, P⊆S ∧
        Real.exp ((1/20:ℝ)*L)≤G ∧ G+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) ∧
        (∀p∈P,G≤Real.log p ∧ Real.log p<G+favorableBlockWidth L) ∧
        (1/10:ℝ)*favorableBlockWidth L<(∑p∈P,Real.log p/(p:ℝ)) := by
  filter_upwards [interiorFavorable_mass_eventually,
    eventually_ge_atTop (100+100*Real.log (2:ℝ))] with L hinterior hL
  have hlog2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have hL0 : 0≤L := by linarith
  have hgap : Real.log 2≤(1/100:ℝ)*L := by linarith
  have hgap' : Real.log 2≤(1/10:ℝ)*L := by linarith
  have hh : 0<favorableBlockWidth L := Real.exp_pos _
  intro S hS hmass
  have hinner := hinterior S hS hmass
  have hhar := favorableBlockCount_harmonic_le hL0 hgap'
  have hsmall : (1/10:ℝ)*(harmonic (favorableBlockCount L):ℝ)<
      harmonicPrimeMass (interiorFavorable S L) := by linarith
  obtain ⟨j,hj,hw⟩ := exists_logBlock_mass_gt (interiorFavorable S L)
    (favorableBlockWidth L) (1/10) (favorableBlockCount L) hh
    (fun p hp => interior_logBlockIndex hL0 hp) hsmall
  let P := logBlockPrimes (interiorFavorable S L) (favorableBlockWidth L) j
  have hne : P.Nonempty := by
    by_contra hn
    have he : P=∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hw₀ : logBlockMass (interiorFavorable S L) (favorableBlockWidth L) j=0 := by
      change (∑p∈P,Real.log p/(p:ℝ))=0
      rw [he,Finset.sum_empty]
    rw [hw₀] at hw
    linarith
  obtain ⟨p,hp⟩ := hne
  have hwin := favorableBlock_window_inside hL0 hgap hp
  refine ⟨(j:ℝ)*favorableBlockWidth L,P,?_,hwin.1,?_,?_,hw⟩
  · intro q hq
    exact (Finset.mem_inter.mp (Finset.mem_filter.mp hq).1).1
  · convert hwin.2 using 1
    ring
  · intro q hq
    exact ⟨logBlock_lower hh hq,by simpa only [add_mul,one_mul] using logBlock_upper hh hq⟩

theorem exists_nonsparse_log_block (d : Decomposition) :
    ∀ᶠ L : ℝ in atTop, ∀ δ : ℝ,
      (3/20:ℝ)*L≤(∑p∈Supply.nonsparsePrimes d δ L,(1:ℝ)/p) →
      ∃ G : ℝ, ∃ P : Finset ℕ, P⊆Supply.nonsparsePrimes d δ L ∧
        Real.exp ((1/20:ℝ)*L)≤G ∧ G+favorableBlockWidth L≤Real.exp ((9/10:ℝ)*L) ∧
        (∀p∈P,G≤Real.log p ∧ Real.log p<G+favorableBlockWidth L) ∧
        (1/10:ℝ)*favorableBlockWidth L<(∑p∈P,Real.log p/(p:ℝ)) := by
  filter_upwards [exists_favorable_log_block] with L hL
  intro δ hmass
  apply hL (Supply.nonsparsePrimes d δ L) _ hmass
  intro p hp
  have h := (Finset.mem_filter.mp hp).2
  exact ⟨h.1,h.2.1,h.2.2.1⟩

end Ostmann.Construction

end

end OAI
