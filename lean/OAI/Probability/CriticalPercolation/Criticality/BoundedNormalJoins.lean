import Mathlib
import OAI.Probability.CriticalPercolation.Growth.CosetBounded
import OAI.Probability.CriticalPercolation.Growth.CosetNormalClosure

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise

namespace CriticalPercolation.RelativeGrowth
variable {A : Type*} [Group A]

lemma conjugate_map_map (N : Subgroup A) (a b : A) :
    (N.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom=N.map (MulAut.conj (a*b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

lemma Bounded.conj {S : Set A} (h1 : (1:A)∈S) (hi : S⁻¹=S)
    (hg : Subgroup.closure S=⊤) {N : Subgroup A} (hN : Bounded S (N:Set A)) (g : A) :
    Bounded S (N.map (MulAut.conj g).toMonoidHom : Set A) := by
  have hh := ((bounded_singleton S h1 hi hg g).mul hN).mul (bounded_singleton S h1 hi hg g⁻¹)
  apply hh.mono
  rintro y ⟨x,hx,rfl⟩
  exact Set.mul_mem_mul (Set.mul_mem_mul (Set.mem_singleton g) hx) (Set.mem_singleton g⁻¹)

lemma normalized_conjugate (L N : Subgroup A) [L.Normal] (hN : L≤(Subgroup.normalizer (N:Set A))) (g : A) :
    L≤(Subgroup.normalizer ((N.map (MulAut.conj g).toMonoidHom):Set A)) := by
  have hh := (Subgroup.map_mono hN (f:=(MulAut.conj g).toMonoidHom)).trans (N.le_normalizer_map (MulAut.conj g).toMonoidHom)
  have he : L.map (MulAut.conj g).toMonoidHom=L := Subgroup.Normal.map_conj_eq L g
  rwa [he] at hh

lemma finite_normalized_join_bounded (S : Set A) (h1 : (1:A)∈S)
    (L : Subgroup A) (F : Set (Subgroup A)) (hf : F.Finite)
    (hle : ∀ N∈F, N≤L) (hnorm : ∀ N∈F, L≤(Subgroup.normalizer (N:Set A)))
    (hb : ∀ N∈F, Bounded S (N:Set A)) :
    Bounded S ((⨆ N∈F, N : Subgroup A) : Set A) := by
  induction F, hf using Set.Finite.induction_on with
  | empty => exact ⟨1,by simpa using h1⟩
  | @insert N F hN hF ih =>
    have hbF := ih (fun M hM => hle M (Set.mem_insert_of_mem _ hM))
      (fun M hM => hnorm M (Set.mem_insert_of_mem _ hM))
      (fun M hM => hb M (Set.mem_insert_of_mem _ hM))
    have hleF : (⨆ M∈F, M : Subgroup A)≤L := iSup_le (fun M => iSup_le (fun hM => hle M (Set.mem_insert_of_mem _ hM)))
    have hn : (⨆ M∈F, M : Subgroup A)≤(Subgroup.normalizer (N:Set A)) := hleF.trans (hnorm N (Set.mem_insert N F))
    rw [iSup_insert,Subgroup.coe_mul_of_right_le_normalizer_left N _ hn]
    exact (hb N (Set.mem_insert N F)).mul hbF

lemma conjugateStage_eq_join (S : Set A) (N : Subgroup A) (n : ℕ) :
    conjugateStage S (N:Set A) n=⨆ M∈((fun g => N.map (MulAut.conj g).toMonoidHom) '' S^n), M := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x ⟨g,hg,y,hy,rfl⟩
    have hh : N.map (MulAut.conj g).toMonoidHom ≤ ⨆ M∈((fun g => N.map (MulAut.conj g).toMonoidHom) '' S^n), M :=
      le_iSup_of_le _ (le_iSup_of_le ⟨g,hg,rfl⟩ le_rfl)
    exact hh (Subgroup.mem_map.mpr ⟨y,hy,rfl⟩)
  · apply iSup_le
    intro M
    apply iSup_le
    rintro ⟨g,hg,rfl⟩ x ⟨y,hy,rfl⟩
    exact Subgroup.subset_closure ⟨g,hg,y,hy,rfl⟩

end CriticalPercolation.RelativeGrowth
end
end

end OAI
