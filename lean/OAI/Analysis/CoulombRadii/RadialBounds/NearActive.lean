import Mathlib
import OAI.Analysis.CoulombRadii.Model

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom

theorem finite_max_near_active {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (f : ι → Position → ℝ) (hf : ∀ i∈s, Continuous (f i))
    {x₀ : Position} {O : Set Position} (hO : IsOpen O) (hx₀ : x₀∈O)
    {η : ℝ} (hη : 0<η) :
    ∃ t : Finset ι, ∃ ht : t.Nonempty, t⊆s ∧
      (∀ i∈s, i∈t ↔ s.sup' hs (fun j => f j x₀)-f i x₀≤η) ∧
      ∃ U : Set Position, x₀∈U ∧ IsOpen U ∧ U⊆O ∧
        (∀ x∈U, s.sup' hs (fun j => f j x)=t.sup' ht (fun j => f j x)) ∧
        (∀ i∈t, ∀ x∈U, s.sup' hs (fun j => f j x)-f i x<2*η) := by
  classical
  let M : Position → ℝ := fun x => s.sup' hs (fun j => f j x)
  have hM : Continuous M := Continuous.finset_sup'_apply hs hf
  obtain ⟨i₀,hi₀,hmax⟩ := Finset.exists_mem_eq_sup' hs (fun i => f i x₀)
  let t := s.filter (fun i => M x₀-f i x₀≤η)
  have hti₀ : i₀∈t := by
    simp only [t,Finset.mem_filter]
    exact ⟨hi₀,by dsimp only [M]; rw [hmax]; linarith⟩
  have ht : t.Nonempty := ⟨i₀,hti₀⟩
  have hts : t⊆s := Finset.filter_subset _ s
  let V : ι → Set Position := fun i => if i∈t then {x | M x-f i x<2*η}
    else {x | f i x<f i₀ x}
  have hV (i) (hi : i∈s) : IsOpen (V i) := by
    dsimp only [V]
    split_ifs
    · exact isOpen_lt (hM.sub (hf i hi)) continuous_const
    · exact isOpen_lt (hf i hi) (hf i₀ hi₀)
  have hxV (i) (hi : i∈s) : x₀∈V i := by
    dsimp only [V]
    split_ifs with hit
    · have hh := (Finset.mem_filter.mp hit).2
      change M x₀-f i x₀<2*η
      linarith
    · have hh : ¬M x₀-f i x₀≤η := by simpa only [t,Finset.mem_filter,hi,true_and] using hit
      change f i x₀<f i₀ x₀
      dsimp only [M] at hh
      rw [hmax] at hh
      linarith
  let U := O∩⋂ i∈s, V i
  refine ⟨t,ht,hts,?_,U,?_,?_,inter_subset_left,?_,?_⟩
  · intro i hi
    simp only [t,Finset.mem_filter,hi,true_and,M]
  · exact ⟨hx₀,mem_iInter₂.mpr (fun i hi => hxV i hi)⟩
  · exact hO.inter (isOpen_biInter_finset fun i hi => hV i hi)
  · intro x hx
    apply le_antisymm
    · apply Finset.sup'_le
      intro i hi
      by_cases hit : i∈t
      · exact Finset.le_sup' (fun j => f j x) hit
      · have hh := mem_iInter₂.mp hx.2 i hi
        have hh' : f i x<f i₀ x := by simpa only [V,ite_eq_right hit,mem_ofPred_eq] using hh
        exact hh'.le.trans (Finset.le_sup' (fun j => f j x) hti₀)
    · exact Finset.sup'_mono (fun j => f j x) hts ht
  · intro i hi x hx
    have hh := mem_iInter₂.mp hx.2 i (hts hi)
    simpa only [V,ite_eq_left hi,mem_ofPred_eq,M] using hh

end NeutralAtom
end

end

end OAI
