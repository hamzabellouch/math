import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Blocks

namespace OAI

namespace BlueSubsetDP
variable {R Y L : Type*} [DecidableEq R] [DecidableEq Y] [DecidableEq L] [Fintype L]

omit [DecidableEq R] in

lemma best_le_designation (B T : Finset R) (F C : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (dest : R → Y) (hT : T ⊆ B) (hC : C ⊆ F)
    (hcard : T.card = Fintype.card L) (hinj : Set.InjOn label (↑T))
    (hdest : ∀ r ∈ T, dest r ∈ C) :
    best (blockCost B F label q) C.card Finset.univ ≤
      (∑ r ∈ T, q r (dest r) : ℝ) := by
  classical
  let map : ↥T → L := fun r => label r
  have hmap : Function.Injective map := by
    intro r s he
    exact Subtype.ext (hinj r.property s.property he)
  have hsur : Function.Surjective map :=
    (Fintype.bijective_iff_injective_and_card map).mpr ⟨hmap, by simpa using hcard⟩ |>.2
  let e : ↥T ≃ L := Equiv.ofBijective map ⟨hmap,hsur⟩
  let sel : L → R := fun l => (e.symm l).val
  let dst : L → Y := fun l => dest (sel l)
  have hs : ∀ l ∈ (Finset.univ : Finset L), sel l ∈ B ∧ label (sel l) = l := by
    intro l _
    exact ⟨hT (e.symm l).property,e.apply_symm_apply l⟩
  have hd : ∀ l ∈ (Finset.univ : Finset L), dst l ∈ F := by
    intro l _
    exact hC (hdest _ (e.symm l).property)
  have hc : (Finset.univ.image dst).card ≤ C.card := by
    apply Finset.card_le_card
    intro y hy
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hy
    exact hdest _ (e.symm l).property
  have hh := best_le_routing B F label q Finset.univ C.card sel dst hs hd hc
  have he : (∑ l : L, q (sel l) (dst l)) = ∑ r ∈ T, q r (dest r) := by
    change (∑ l : L, q (e.symm l).val (dest (e.symm l).val)) = _
    exact (e.symm.sum_comp (fun r : ↥T => q r.val (dest r.val))).trans
      (Finset.sum_coe_sort T (fun r => q r (dest r)))
  rwa [he] at hh

lemma designated_branch_witnesses [Nonempty R] [Nonempty Y]
    (B T : Finset R) (F C : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (dest : R → Y) (hT : T ⊆ B) (hC : C ⊆ F)
    (hcard : T.card = Fintype.card L) (hinj : Set.InjOn label (↑T))
    (hdest : ∀ r ∈ T, dest r ∈ C) :
    ∃ sel : L → R, ∃ dst : L → Y,
      (∀ l, sel l ∈ B ∧ label (sel l) = l ∧ dst l ∈ F) ∧
      Function.Injective sel ∧ (Finset.univ.image dst).card ≤ C.card ∧
      ((∑ l, q (sel l) (dst l) : ℝ) : WithTop ℝ) =
        best (blockCost B F label q) C.card Finset.univ ∧
      (∑ l, q (sel l) (dst l)) ≤ ∑ r ∈ T, q r (dest r) := by
  have hle := best_le_designation B T F C label q dest hT hC hcard hinj hdest
  have hfin : best (blockCost B F label q) C.card Finset.univ ≠ ⊤ := by
    exact ne_top_of_le_ne_top WithTop.coe_ne_top hle
  obtain ⟨sel,dst,hs,_,hc,hval⟩ := best_routing B F label q Finset.univ C.card hfin
  refine ⟨sel,dst,fun l => hs l (Finset.mem_univ l),?_,hc,hval,?_⟩
  · intro l l' he
    exact (hs l (Finset.mem_univ l)).2.1.symm.trans
      ((congrArg label he).trans (hs l' (Finset.mem_univ l')).2.1)
  · exact WithTop.coe_le_coe.mp (hval.le.trans hle)

end BlueSubsetDP
namespace BlueSubsetDP
variable {R Y L : Type*} [DecidableEq R] [DecidableEq Y] [DecidableEq L] [Fintype L]

structure Plan (B : Finset R) (F : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (c : ℕ) where
  sel : L → R
  dst : L → Y
  selection : ∀ l, sel l ∈ B ∧ label (sel l) = l ∧ dst l ∈ F
  selected_injective : Function.Injective sel
  destination_count : (Finset.univ.image dst).card ≤ c
  value_eq : ((∑ l, q (sel l) (dst l) : ℝ) : WithTop ℝ) =
    best (blockCost B F label q) c Finset.univ

lemma plan_exists [Nonempty R] [Nonempty Y]
    (B : Finset R) (F : Finset Y) (label : R → L) (q : R → Y → ℝ) (c : ℕ)
    (hfin : best (blockCost B F label q) c Finset.univ ≠ ⊤) :
    Nonempty (Plan B F label q c) := by
  obtain ⟨sel,dst,hs,_,hc,hval⟩ := best_routing B F label q Finset.univ c hfin
  refine ⟨⟨sel,dst,fun l => hs l (Finset.mem_univ l),?_,hc,hval⟩⟩
  intro l l' he
  exact (hs l (Finset.mem_univ l)).2.1.symm.trans
    ((congrArg label he).trans (hs l' (Finset.mem_univ l')).2.1)

noncomputable def computedPlan [Nonempty R] [Nonempty Y]
    (B : Finset R) (F : Finset Y) (label : R → L) (q : R → Y → ℝ) (c : ℕ) :
    Option (Plan B F label q c) :=
  if h : best (blockCost B F label q) c Finset.univ = ⊤ then none
  else some (Classical.choice (plan_exists B F label q c h))

lemma computedPlan_success [Nonempty R] [Nonempty Y]
    (B T : Finset R) (F C : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (dest : R → Y) (hT : T ⊆ B) (hC : C ⊆ F)
    (hcard : T.card = Fintype.card L) (hinj : Set.InjOn label (↑T))
    (hdest : ∀ r ∈ T, dest r ∈ C) :
    ∃ P : Plan B F label q C.card,
      computedPlan B F label q C.card = some P ∧
      (∑ l, q (P.sel l) (P.dst l)) ≤ ∑ r ∈ T, q r (dest r) := by
  have hle := best_le_designation B T F C label q dest hT hC hcard hinj hdest
  have hfin : best (blockCost B F label q) C.card Finset.univ ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hle
  simp only [computedPlan,dite_eq_right hfin]
  refine ⟨_,rfl,?_⟩
  exact WithTop.coe_le_coe.mp ((Classical.choice (plan_exists B F label q C.card hfin)).value_eq.le.trans hle)

end BlueSubsetDP

end OAI
