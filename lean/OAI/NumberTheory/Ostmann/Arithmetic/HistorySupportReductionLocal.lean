import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReductionBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySupportReduction
open Construction
open HistorySupportDescent

theorem localTests_of_supported_node {V : ℕ → ℕ} {outside : List ℕ} {l : ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hs : (History.node a p u hp hm left right).Supported V outside)
    (hlarge : ∀b∈u,V (l+1)<b.value) :
    LocalTests outside a p u hp hm left.root.frequency right.root.frequency := by
  have hl := History.supported_left hs
  have hroot := rootData_of_supported hl
  obtain ⟨hlp,hrp,hlm,hrm⟩ := History.supported_child_giants hs
  obtain ⟨hls,hrs⟩ := History.supported_child_small hs
  have hlist := child_list_coprime_of_state hlp hlm hls (History.supported_root_coprime hl)
  simp only [List.cons_append,List.map_append,List.append_assoc] at hlist
  have hfirst := List.pairwise_cons.mp hlist
  have htail := (List.pairwise_cons.mp hfirst.2).2
  have huPair := (List.pairwise_append.mp htail).1
  have huPrime : ∀b∈u,Nat.Prime b.value := by
    intro b hb
    exact hroot.2.1 b (hls.mem_iff.mpr (List.mem_append_left hp hb))
  have hprime : ∀b∈u.map SmallSlot.value,Nat.Prime b := by
    intro b hb
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hb
    exact huPrime q hq
  have hnd : (u.map SmallSlot.value).Nodup := by
    apply List.Pairwise.imp_of_mem (p:=huPair)
    intro b c hb hc hbc heq
    subst c
    exact (hprime b hb).ne_one (by simpa only [Nat.Coprime,Nat.gcd_self] using hbc)
  have hpO : ∀q∈outside,Nat.Coprime p q := by
    intro q hq
    exact hfirst.1 q (by simp [hq])
  have huO : ∀b∈u,∀q∈outside,Nat.Coprime b.value q := by
    intro b hb q hq
    exact (List.pairwise_append.mp htail).2.2 b.value (List.mem_map.mpr ⟨b,hb,rfl⟩)
      q (List.mem_append_right _ hq)
  refine ⟨hnd,huPrime,?_,hpO,huO⟩
  intro b hb
  have hbp : Nat.Coprime p b.value := hfirst.1 b.value
    (List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map.mpr ⟨b,hb,rfl⟩)))
  have hbs : ¬(b.value:ℤ)∣a.frequency := by
    intro hd
    have he := Int.natAbs_le_of_dvd_ne_zero hd (History.supported_root_frequency_ne_zero hs)
    simp only [Int.natAbs_natCast] at he
    have hfreq := History.supported_root_frequency_bound hs
    exact (not_le_of_gt (hlarge b hb)) (he.trans hfreq)
  exact (compensation_square_test_iff huPair (List.mem_map.mpr ⟨b,hb,rfl⟩)
    (huPrime b hb) hbs (History.supported_reversal hs)).mpr hbp

theorem child_coprime_of_reduced_data {V : ℕ → ℕ} {outside : List ℕ} {l : ℕ}
    {a : State} {p : ℕ} {u hp hm : List SmallSlot} {left right : History l}
    (hparent : a.Coprime outside)
    (hrel : History.nodeRelations (l+1) a p u hp hm left.root right.root)
    (htests : LocalTests outside a p u hp hm left.root.frequency right.root.frequency)
    (hl : RootData V left) (hr : RootData V right)
    (hlg : ∀q∈left.root.small,V l<q.value) (hrg : ∀q∈right.root.small,V l<q.value) :
    left.root.Coprime outside ∧ right.root.Coprime outside := by
  obtain ⟨hpos,hrole,hperm,hlp,hrp,hlm,hrm,hls,hrs,hN⟩ := hrel
  obtain ⟨hnd,hprime,hsq,hpO,huO⟩ := htests
  have hv := inherited_frequency_unit hl hlg hlm hls
  have hw := inherited_frequency_unit hr hrg hrm hrs
  obtain ⟨hlc,hrc⟩ := child_lists_coprime a p u hp hm outside left.root.frequency right.root.frequency
    hparent hperm hv hw hN hnd hprime hsq hpO huO
  exact ⟨state_coprime_of_child_list hlp hlm hls hlc,
    state_coprime_of_child_list hrp hrm hrs hrc⟩

end Ostmann.Arithmetic.HistorySupportReduction

end

end OAI
