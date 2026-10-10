import OAI.NumberTheory.Jacobsthal.Paths.WrongOwnerBoxMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosTagEvent
open NumberTheoryLean ActualSourceTags ActualBinOwners FiniteFirstTag
open LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinLabels LogarithmicBinPartition
open PrimeChoiceBoxMass WrongOwnerBinMass ErdosInversePrimeBin ErdosInverseAlignment

attribute [local instance] Classical.propDecidable

noncomputable def patternBins {m : ℕ} (w top xi : ℝ) (pattern : Fin m → Fin (binCount w top xi)) :
    Fin m → Finset ℕ := fun i => primeBin (lower w top xi (pattern i)) (width w top xi (pattern i))
noncomputable def searchPositions {m : ℕ} (w top xi : ℝ)
    (pattern : Fin m → Fin (binCount w top xi)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => searchBin w (lower w top xi (pattern i)))

noncomputable def nearFull (eta R width : ℝ) (a : ℕ → ℤ) (q : ℚ) : Prop :=
  (1-eta)*((primeBin R width).card:ℝ) ≤ (((primeBin R width).filter (aligns a q)).card:ℝ)

theorem actual_choice_label {m : ℕ} {w top xi : ℝ} (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (pattern : Fin m → Fin (binCount w top xi)) (f : Fin m → ℕ)
    (hf : f ∈ choices (patternBins w top xi pattern)) (i : Fin m) :
    label (zero_lt_one.trans hw) htop hxi (f i)=pattern i := by
  have hp : f i ∈ primeBin (lower w top xi (pattern i)) (width w top xi (pattern i)) :=
    (Fintype.mem_piFinset.mp hf) i
  exact ((bin_mem_iff_label (zero_lt_one.trans hw) htop hxi (pattern i) (f i)).mp hp).2.2.2

theorem actual_choice_coordinate {m : ℕ} {w top xi : ℝ}
    (pattern : Fin m → Fin (binCount w top xi)) (f : Fin m → ℕ)
    (hf : f ∈ choices (patternBins w top xi pattern)) (i : Fin m) :
    f i ∈ primeBin (lower w top xi (pattern i)) (width w top xi (pattern i)) :=
  (Fintype.mem_piFinset.mp hf) i

theorem first_tag_coordinate {m : ℕ} {Y w top Cs eta xi : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi)
    (pattern : Fin m → Fin (binCount w top xi)) (f : Fin m → ℕ) (a : ℕ → ℤ)
    (hf : f ∈ choices (patternBins w top xi pattern))
    (t : Tag (binCount w top xi))
    (ht : sourceTag Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a (List.ofFn f)=some t) :
    ∃ i ∈ searchPositions w top xi pattern,pattern i=t.bin ∧
      owner Y w Cs eta (lower w top xi (pattern i)) (width w top xi (pattern i)) a=some t.rational ∧
      aligns a t.rational (f i) := by
  obtain ⟨pre,p,tail,heq,_hindex,hbin,_hp,hs,ho,ha,_hbefore⟩ :=
    sourceTag_witness Y w Cs eta (lower w top xi) (width w top xi)
      (label (zero_lt_one.trans hw) htop hxi) a (List.ofFn f) ht
  have hp : p ∈ List.ofFn f := by rw [heq]; simp
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hp
  have hl := actual_choice_label hw htop hxi pattern f hf i
  rw [← hi,hl] at hbin hs ho
  rw [← hi] at ha
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩,hbin.symm,ho,ha⟩

end ErdosTagEvent


end Erdos970

end OAI
