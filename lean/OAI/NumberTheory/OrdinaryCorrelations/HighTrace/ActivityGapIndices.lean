import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.Subpath

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}

lemma activity_gap_indices {n : ℕ} (A : Fin (n+1) → Prop) (h0 : A 0) (hn : A (Fin.last n))
    (i : Fin (n+1)) (hi : ¬A i) :
    ∃ a b : Fin (n+1), a.val+1<b.val ∧ A a ∧ A b ∧
      ∀ j : Fin (n+1),a < j → j < b → ¬A j := by
  let SL := univ.filter (fun j : Fin (n+1) => j ≤ i ∧ A j)
  let SR := univ.filter (fun j : Fin (n+1) => i ≤ j ∧ A j)
  have hl : SL.Nonempty := ⟨0,mem_filter.mpr ⟨mem_univ _,Fin.zero_le _,h0⟩⟩
  have hr : SR.Nonempty := ⟨Fin.last n,mem_filter.mpr ⟨mem_univ _,Fin.le_last _,hn⟩⟩
  let a := SL.max' hl
  let b := SR.min' hr
  have ha : a ≤ i ∧ A a := (mem_filter.mp (max'_mem SL hl)).2
  have hb : i ≤ b ∧ A b := (mem_filter.mp (min'_mem SR hr)).2
  have hai : a < i := lt_of_le_of_ne ha.1 (fun he => hi (he ▸ ha.2))
  have hib : i < b := lt_of_le_of_ne hb.1 (fun he => hi (he.symm ▸ hb.2))
  refine ⟨a,b,by have hai' := Fin.lt_def.mp hai; have hib' := Fin.lt_def.mp hib; omega,ha.2,hb.2,?_⟩
  intro j haj hjb hj
  by_cases hji : j ≤ i
  · have hjl : j ≤ a := le_max' SL j (mem_filter.mpr ⟨mem_univ _,hji,hj⟩)
    exact (not_lt_of_ge hjl) haj
  · have hrj : b ≤ j := min'_le SR j (mem_filter.mpr ⟨mem_univ _,(le_of_not_ge hji),hj⟩)
    exact (not_lt_of_ge hrj) hjb

namespace TreePath
variable {w : NumericalLine D h ℓ}

theorem all_active_of_no_gap (P : TreePath w L) (a : S.FixedResidues w.line)
    (H : Finset (Fin ℓ))
    (hcut : ∀ (Q : TreePath w L) (p : S.FixedIndex w.line),Q.IsGap a p → ∃ i,Q.edge i ∈ H)
    (hsurvive : ∀ i,P.edge i ∉ H) (p : S.FixedIndex w.line)
    (h0 : a p+(P.vertex 0 : ZMod (p.val:ℕ))=0)
    (hn : a p+(P.vertex (Fin.last P.length) : ZMod (p.val:ℕ))=0) :
    ∀ i,a p+(P.vertex i : ZMod (p.val:ℕ))=0 := by
  intro i
  by_contra hi
  obtain ⟨u,v,huv,hu,hv,hmid⟩ := activity_gap_indices
    (fun j => a p+(P.vertex j : ZMod (p.val:ℕ))=0) h0 hn i hi
  have hlt : u<v := by apply Fin.lt_def.mpr; omega
  let Q := P.subpath u v hlt
  have hg : Q.IsGap a p := by
    refine ⟨by dsimp [Q,subpath]; omega,?_,?_,?_⟩
    · simpa only [Q,subpath_start] using hu
    · simpa only [Q,subpath_finish] using hv
    · intro j hj0 hjl
      change a p+(P.vertex ⟨u.val+j.val,_⟩ : ZMod (p.val:ℕ))≠0
      apply hmid
      · apply Fin.lt_def.mpr; dsimp; omega
      · apply Fin.lt_def.mpr; dsimp [Q,subpath] at hjl ⊢; omega
  obtain ⟨j,hj⟩ := hcut Q p hg
  exact hsurvive ⟨u.val+j.val,by have := v.isLt; have := j.isLt; dsimp [Q,subpath] at *; omega⟩ hj

end TreePath
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
