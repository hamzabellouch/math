import Mathlib
import OAI.Combinatorics.KMedian.Reduction.RationalLocalChoice
import OAI.Combinatorics.KMedian.Reduction.RationalCompletion
import OAI.Combinatorics.KMedian.Sparse.SparseDeletion
import OAI.Combinatorics.KMedian.Reduction.RationalThreshold
import OAI.Combinatorics.KMedian.Reduction.BadCenterBound

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def rationalRadii (I : Instance) (U : Finset (Fin I.n)) (t : Fin I.n) : ℚ :=
  rationalNearest I t (U.erase t)

def completionBranches (I : Instance) (F U : Finset (Fin I.n)) (δ : ℚ) (b : ℕ) :
    Finset (Finset (Fin I.n)) :=
  ((deletionChoices U b) ×ˢ (deletionChoices F b)).image
    (fun p => completionSet I F p.2 (U \ p.1) (rationalRadii I U) δ)

theorem completionBranches_card (I : Instance) (F U : Finset (Fin I.n)) (δ : ℚ) (b : ℕ) :
    (completionBranches I F U δ b).card ≤
      ((b+1)*(U.card+1)^b)*((b+1)*(F.card+1)^b) := by
  calc
    _ ≤ (deletionChoices U b).card*(deletionChoices F b).card := by
      exact (card_image_le (s:=(deletionChoices U b) ×ˢ (deletionChoices F b))
        (f:=fun p => completionSet I F p.2 (U \ p.1) (rationalRadii I U) δ)).trans_eq (card_product _ _)
    _ ≤ _ := Nat.mul_le_mul (card_deletionChoices U b) (card_deletionChoices F b)

variable {I : Instance}
local instance completionEnumerationPseudoMetric : PseudoMetricSpace (Fin I.n) := I.pseudoMetric

namespace Serving
variable {U O : Finset (Fin I.n)} {δ : ℝ}

theorem radius_rational (D : Serving (I:=I) U) (t : ↥U) :
    D.radius t=(rationalRadii I U t.val:ℝ) := by
  rw [rationalRadii,I.cast_rationalNearest]
  have ho : (D.other t).val ∈ U.erase t.val := mem_erase.mpr
    ⟨fun he => D.other_ne t (Subtype.ext he),(D.other t).property⟩
  apply le_antisymm
  · obtain ⟨u,hu,he⟩ := I.nearest_attained t (U.erase t.val) ⟨_,ho⟩
    rw [he]
    exact D.other_nearest t ⟨u,(mem_erase.mp hu).2⟩
      (fun he => (mem_erase.mp hu).1 (congrArg Subtype.val he))
  · exact I.nearest_le t ho

noncomputable def badSet (D : Serving (I:=I) U) (O : Finset (Fin I.n)) (δ : ℝ) :
    Finset (Fin I.n) := (D.bad O δ).image Subtype.val

theorem badSet_sub (D : Serving (I:=I) U) : D.badSet O δ ⊆ U := by
  intro i hi
  obtain ⟨t,_,rfl⟩ := mem_image.mp hi
  exact t.property

theorem badSet_card (D : Serving (I:=I) U) : (D.badSet O δ).card=(D.bad O δ).card :=
  card_image_of_injective _ Subtype.val_injective

theorem sdiff_badSet (D : Serving (I:=I) U) : U \ D.badSet O δ=D.good O δ := by
  ext i
  constructor
  · intro hi
    obtain ⟨hiU,hiH⟩ := mem_sdiff.mp hi
    refine mem_image.mpr ⟨⟨i,hiU⟩,mem_sdiff.mpr ⟨mem_univ _,?_⟩,rfl⟩
    intro hb
    exact hiH (mem_image_of_mem _ hb)
  · intro hi
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hi
    refine mem_sdiff.mpr ⟨t.property,?_⟩
    intro hb
    obtain ⟨u,hu,he⟩ := mem_image.mp hb
    have heq : u=t := Subtype.ext he
    rw [heq] at hu
    exact (mem_sdiff.mp ht).2 hu

end Serving

theorem completion_branch_exists (F O U : Finset (Fin I.n)) (hOF : O ⊆ F)
    (hO : O.Nonempty) (hk : O.card=I.k) (hUF : U ⊆ F) (hU : I.k < U.card)
    (α η : ℝ) (δ : ℚ) (c b : ℕ) (hc : 0 < c) (hδ : 0 < (δ:ℝ))
    (hsmall : (δ:ℝ) ≤ 1/6) (hη : 0 < η) (hC : 0 < cost I O)
    (hcost : cost I U ≤ α*cost I O)
    (hsp : Sparse (I:=I) F O ((δ:ℝ)*η/(2*c)))
    (hstuck : ∀ i ∈ U, η*cost I O/c ≤ cost I (U.erase i)-cost I U)
    (hb : 6*α*c/((δ:ℝ)*η) ≤ (b:ℝ)) :
    ∃ S ∈ completionBranches I F U δ b,
      S ⊆ F ∧ S.Nonempty ∧ S.card ≤ I.k ∧ cost I S ≤ (1+12*(δ:ℝ))*cost I O := by
  classical
  obtain ⟨D⟩ := serving_exists U hU
  have hbad : (D.bad O (δ:ℝ)).card ≤ b := by
    have hh := (D.bad_count hUF α (δ:ℝ) η c hc hδ hη hC hcost hsp
      (fun t => hstuck t.val t.property)).trans hb
    exact_mod_cast hh
  obtain ⟨C,hr⟩ := D.closeCenters_exists (δ:=(δ:ℝ)) hO
  have hbackup : C.backup.card ≤ b :=
    (D.backup_card_bound C hδ.le (by linarith) (by omega)).trans hbad
  have hBsub : C.backup ⊆ F := sdiff_subset.trans hOF
  have hH : D.badSet O (δ:ℝ) ∈ deletionChoices U b := by
    apply (mem_deletionChoices _ _ _).mpr
    exact ⟨D.badSet_sub,by rw [D.badSet_card]; exact hbad⟩
  have hB : C.backup ∈ deletionChoices F b := (mem_deletionChoices _ _ _).mpr ⟨hBsub,hbackup⟩
  have hrat : ∀ t, C.radius t=(rationalRadii I U t.val:ℝ) := fun t =>
    (hr t).trans (D.radius_rational _)
  let S := completionSet I F C.backup (D.good O (δ:ℝ)) (rationalRadii I U) δ
  have hspec := C.completionSet_spec hδ.le hsmall hO F hOF (rationalRadii I U) hrat
  refine ⟨S,?_,hspec.1,hspec.2.1,?_,hspec.2.2.2⟩
  · apply mem_image.mpr
    refine ⟨(D.badSet O (δ:ℝ),C.backup),mem_product.mpr ⟨hH,hB⟩,?_⟩
    simp only [D.sdiff_badSet,S]
  · exact hspec.2.2.1.trans_eq hk

end MetricKMedian.Reduction
end
end

end OAI
