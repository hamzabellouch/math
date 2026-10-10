import Mathlib
import OAI.GroupTheory.FiniteType.OrderListChainsVertexSupport
import OAI.GroupTheory.FiniteType.TwistedBrinBasisFirstCut

namespace OAI

open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
noncomputable section
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits _root_.Representation _root_.OAI.Representation
open scoped MonoidalCategory
open _root_.CategoryTheory _root_.OAI.CategoryTheory CategoryTheory.Limits
attribute [instance] AddCommGroup.toIntModule
open Set Function
open scoped Pointwise
namespace OrderChains
section
open OrderListChains
variable (P : Type*) [Preorder P]
theorem exactIn_of_directed [Nonempty P]
    (hdir : ∀ x y : P, ∃ z, x ≤ z ∧ y ≤ z) (n : ℕ) : ExactIn P n := by
  classical
  have hfin (F : Finset P) : ∃ z : P, ∀ x ∈ F, x ≤ z := by
    induction F using Finset.induction_on with
    | empty => exact ⟨Classical.choice ‹Nonempty P›,by simp⟩
    | @insert x F hx ih =>
      obtain ⟨y,hy⟩ := ih
      obtain ⟨z,hxz,hyz⟩ := hdir x y
      exact ⟨z,fun a ha => (Finset.mem_insert.mp ha).elim (fun he => he ▸ hxz)
        (fun haF => (hy a haF).trans hyz)⟩
  intro c hc hn hd ha
  obtain ⟨z,hz⟩ := hfin (vertexSupport P c)
  have hcz : c ∈ carrier P z := fun s hs => ⟨hc hs,fun x hx =>
    hz x ((mem_vertexSupport P).mpr ⟨s,hs,hx⟩)⟩
  refine ⟨cone P z c,carrier_le_module P z (cone_carrier P z hcz),
    cone_mem_degreeModule P z hn,?_⟩
  rw [boundary_cone,hd,map_zero,K_apply,ha,zero_smul,sub_zero,sub_zero]
end

section
open OrderListChains
variable (P : Type*) [PartialOrder P]
theorem lower_filling_many (r : P → ℕ) (hr : StrictMono r) (h N : ℕ)
    (hne : ∀ a, h < r a → ∃ x, x < a)
    (hex : ∀ a, h < r a → ∀ k ≤ N, ExactSet P (Set.Iio a) k)
    {n : ℕ} (hnN : n ≤ N) (c : Chain P)
    (hc : c ∈ onSet P {x | r x ≤ h}) (hcn : Homogeneous P n c)
    (hcd : boundary P c = 0) (hca : augmentation P c = 0)
    (k : ℕ) (b : Chain P)
    (hb : b ∈ onSet P {x | r x ≤ h+k}) (hbn : Homogeneous P (n+1) b)
    (hbd : boundary P b = c) :
    ∃ b' : Chain P, b' ∈ onSet P {x | r x ≤ h} ∧
      Homogeneous P (n+1) b' ∧ boundary P b' = c := by
  induction k generalizing b with
  | zero => exact ⟨b,by simpa only [Nat.add_zero] using hb,hbn,hbd⟩
  | succ k ih =>
    obtain ⟨b',hb',hbn',hbd'⟩ := lower_filling P r hr (h+k) N
      (fun a ha => hne a (by omega))
      (fun a ha => hex a (by omega)) hnN c b
      (onSet_mono P (fun x hx => by change r x ≤ h+k; change r x ≤ h at hx; omega) hc)
      hcn hcd hca (by simpa only [Nat.add_assoc] using hb) hbn hbd
    exact ih b' hb' hbn' hbd'

theorem exactSet_sublevel (r : P → ℕ) (hr : StrictMono r) (h N : ℕ)
    (hne : ∀ a, h < r a → ∃ x, x < a)
    (hex : ∀ a, h < r a → ∀ k ≤ N, ExactSet P (Set.Iio a) k)
    {n : ℕ} (hnN : n ≤ N) (hall : ExactIn P n) :
    ExactSet P {x | r x ≤ h} n := by
  classical
  intro c hc hn hd ha
  obtain ⟨b,hb,hbn,hbd⟩ := hall c (onSet_le_module P _ hc) hn hd ha
  let k := (vertexSupport P b).sup r
  have hb' : b ∈ onSet P {x | r x ≤ h+k} := by
    intro s hs
    refine ⟨hb hs,fun x hx => ?_⟩
    have hxr : r x ≤ k := Finset.le_sup ((mem_vertexSupport P).mpr ⟨s,hs,hx⟩)
    change r x ≤ h+k
    omega
  exact lower_filling_many P r hr h N hne hex hnN c hc hn hd ha k b hb' hbn hbd
end

open OrderListChains
variable (P : Type*) [Preorder P]

theorem constant_of_exact_zero {U : Set P} (hU : ExactSet P U 0) {Y : Type*}
    (f : P → Y) (hf : ∀ x ∈ U, ∀ y ∈ U, x ≤ y → f x = f y)
    {x y : P} (hx : x ∈ U) (hy : y ∈ U) : f x = f y := by
  classical
  let ev : Chain P →ₗ[ℤ] (Y →₀ ℤ) :=
    Finsupp.linearCombination ℤ (fun s : Simplex P => Finsupp.single (f s.1) 1)
  have hev (z : P) : ev (vertex P z) = Finsupp.single (f z) 1 := by
    simp [ev,vertex,simplexVertex]
  have hvm (z : P) (hz : z ∈ U) : vertex P z ∈ onSet P U := by
    apply supported_single
    exact ⟨by simp [Descending,list,simplexVertex],by simpa [vertices,simplexVertex]⟩
  have hvn (z : P) : Homogeneous P 0 (vertex P z) := by
    apply supported_single
    rfl
  obtain ⟨b,hb,hbn,hbd⟩ := hU (vertex P x-vertex P y)
    ((onSet P U).sub_mem (hvm x hx) (hvm y hy)) (supported_sub P (hvn x) (hvn y))
    (by simp) (by simp)
  have he : ev (boundary P b) = 0 := by
    have hh := OrderBasedComplex.linear_eq_on_support (ev.comp (boundary P)) 0 b (by
      rintro ⟨a,l⟩ hs
      have hl : l.length = 1 := hbn (a,l) hs
      obtain ⟨d,hd⟩ := List.length_eq_one_iff.mp hl
      subst l
      have hds : d ≤ a := (hb hs).1.le_head P (Or.inr (by simp))
      have hda := hf d ((hb hs).2 (Or.inr (by simp))) a
        ((hb hs).2 (head_mem_vertices P _)) hds
      rw [LinearMap.comp_apply,LinearMap.zero_apply,single_cons]
      change ev (boundary P (cone P a (vertex P d))) = 0
      rw [boundary_cone,boundary_vertex,map_zero,sub_zero,K_apply,augmentation_vertex,one_smul,
        map_sub,hev,hev,hda,sub_self])
    exact hh
  rw [hbd,map_sub,hev,hev,sub_eq_zero] at he
  by_contra hn
  have hh := congrArg (fun t : Y →₀ ℤ => t (f x)) he
  simp [hn] at hh
end OrderChains

universe u v
namespace TwistedBrin.Basis
section
variable {A : Type v} [Group A] {S : Type u} (ρ : A →* Equiv.Perm S)
lemma firstCut_card {B C : Basis ρ} (h : CutRefines ρ B C) :
    Fintype.card (FirstCut ρ h) = ∑ b : B, (firstCuts ρ h b).card := by
  classical
  unfold FirstCut
  simp only [Fintype.card_sigma,Fintype.card_coe]

lemma firstCut_nonempty {B C : Basis ρ} (h : CutRefines ρ B C) (hne : B ≠ C) :
    Nonempty (FirstCut ρ h) := by
  classical
  by_contra hn
  have he : firstCuts ρ h = fun _ => ∅ := by
    funext b
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    exact hn ⟨⟨b,⟨s,hs⟩⟩⟩
  apply firstCore_ne ρ h hne
  change gridExpansion ρ B (firstCuts ρ h) = B
  rw [he,gridExpansion_empty]

lemma firstCut_rank_bound {B C : Basis ρ} (h : CutRefines ρ B C)
    (htop : firstCore ρ h = C) :
    rank ρ C + 1 ≤ rank ρ B + 2 ^ Fintype.card (FirstCut ρ h) := by
  rw [firstCut_card]
  have hh := grid_rank_bound ρ B (firstCuts ρ h)
  change rank ρ (firstCore ρ h) + 1 ≤ _ at hh
  simpa only [htop] using hh

theorem properCutInterval_exactIn {B C : Basis ρ} (h : CutRefines ρ B C)
    (hne : B ≠ C) {n : ℕ}
    (hrank : rank ρ B + 2 ^ (n+2) ≤ rank ρ C) :
    OrderChains.ExactIn (ProperCutInterval ρ B C) n := by
  classical
  apply OrderChains.exactIn_of_comparison _ (CutSelections.properToInterval h)
    (CutSelections.properOfInterval h)
  · intro D
    rw [CutSelections.proper_to_of]
    exact D.val.core_le
  · by_cases htop : firstCore ρ h = C
    · apply OrderChains.exactIn_of_orderIso (CutSelections.properBooleanBoundary h htop)
      apply SteinChains.properFace_exactIn
      have hb := firstCut_rank_bound ρ h htop
      have hp : 2 ^ (n+2) < 2 ^ Fintype.card (FirstCut ρ h) := by omega
      by_contra hn
      have hh := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega :
        Fintype.card (FirstCut ρ h) ≤ n+2)
      omega
    · apply OrderChains.exactIn_of_orderIso (CutSelections.properBooleanFaces h htop)
      let := firstCut_nonempty ρ h hne
      apply OrderChains.exactIn_of_top _ ⟨Finset.univ,Finset.univ_nonempty.ne_empty⟩
      intro F
      exact Finset.subset_univ _
end

section
universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

namespace Merge
variable {C : Basis ρ}
def endpoint (m : Merge ρ C) (q : Bool) : C := if q then m.second else m.first
lemma endpoint_injective (m : Merge ρ C) : Function.Injective m.endpoint := by
  intro i j he
  cases i <;> cases j <;> simp_all [endpoint, m.distinct, Ne.symm m.distinct]
end Merge

structure Matching (C : Basis ρ) (I : Type w) where
  edge : I → Merge ρ C
  endpoints_injective : Function.Injective (fun p : I × Bool => (edge p.1).endpoint p.2)

namespace Matching
variable {C : Basis ρ} {I : Type w} (M : Matching C I)

def Present (B : Basis ρ) (N : Finset I) : Prop :=
  ∀ i ∈ N, ∀ q : Bool, ((M.edge i).endpoint q).val ∈ B.pieces

abbrev Rest (B : Basis ρ) (N : Finset I) :=
  {b : B // ∀ i ∈ N, ∀ q : Bool, b.val ≠ ((M.edge i).endpoint q).val}
abbrev Roots (B : Basis ρ) (N : Finset I) := N ⊕ M.Rest B N

noncomputable def rootChart (B : Basis ρ) (N : Finset I) : M.Roots B N → LocalEmbedding ρ
  | Sum.inl i => (M.edge i.val).joined
  | Sum.inr b => chart ρ B b.val

lemma endpoint_eq {i j : I} {p q : Bool}
    (he : ((M.edge i).endpoint p).val = ((M.edge j).endpoint q).val) : i = j ∧ p = q := by
  have hh := M.endpoints_injective (a₁ := (i,p)) (a₂ := (j,q)) (Subtype.ext he)
  exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩

lemma range_joined (i : I) : Set.range (M.edge i).joined =
    ⋃ q : Bool, GermBrick.region ρ ((M.edge i).endpoint q).val := by
  rw [(M.edge i).range_joined]
  ext x
  simp [Merge.endpoint]

lemma rootPartition (B : Basis ρ) (N : Finset I) (h : M.Present B N) :
    ∀ x : Box S, ∃! r : M.Roots B N, x ∈ Set.range (M.rootChart B N r) := by
  classical
  intro x
  obtain ⟨b,hb,hu⟩ := B.partition x
  have hleft (i : N) : x ∈ Set.range (M.rootChart B N (Sum.inl i)) ↔
      ∃ q : Bool, b.val = ((M.edge i.val).endpoint q).val := by
    change x ∈ Set.range (M.edge i.val).joined ↔ _
    rw [M.range_joined]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨q,hq⟩
      exact ⟨q,congrArg Subtype.val ((hu ⟨_,h i.val i.property q⟩ hq).symm)⟩
    · rintro ⟨q,hq⟩
      exact ⟨q,hq ▸ hb⟩
  have hright (r : M.Rest B N) : x ∈ Set.range (M.rootChart B N (Sum.inr r)) ↔ r.val = b := by
    change x ∈ Set.range (chart ρ B r.val) ↔ _
    rw [chart_region]
    exact ⟨hu _,fun he => he.symm ▸ hb⟩
  by_cases ht : ∃ i : N, ∃ q : Bool, b.val = ((M.edge i.val).endpoint q).val
  · obtain ⟨i,q,hi⟩ := ht
    refine ⟨Sum.inl i,(hleft i).mpr ⟨q,hi⟩,?_⟩
    intro r hr
    cases r with
    | inl j =>
      obtain ⟨p,hj⟩ := (hleft j).mp hr
      exact congrArg Sum.inl (Subtype.ext (M.endpoint_eq (hj.symm.trans hi)).1)
    | inr r =>
      have he := (hright r).mp hr
      exact False.elim (r.property i.val i.property q ((congrArg Subtype.val he).trans hi))
  · have hr : ∀ i ∈ N, ∀ q : Bool, b.val ≠ ((M.edge i).endpoint q).val := by
      intro i hi q he
      exact ht ⟨⟨i,hi⟩,q,he⟩
    refine ⟨Sum.inr ⟨b,hr⟩,(hright _).mpr rfl,?_⟩
    intro r hh
    cases r with
    | inl i => exact False.elim (ht ⟨i,(hleft i).mp hh⟩)
    | inr r => exact congrArg Sum.inr (Subtype.ext ((hright r).mp hh))

noncomputable def contract (B : Basis ρ) (N : Finset I) (h : M.Present B N) : Basis ρ := by
  classical
  exact ofChartPartition ρ (M.rootChart B N) (M.rootPartition B N h)

lemma mem_contract (B : Basis ρ) (N : Finset I) (h : M.Present B N) (g : GermBrick ρ) :
    g ∈ (M.contract B N h).pieces ↔
      (∃ i ∈ N, g = GermBrick.mk ρ (M.edge i).joined) ∨
      (g ∈ B.pieces ∧ ∀ i ∈ N, ∀ q : Bool, g ≠ ((M.edge i).endpoint q).val) := by
  classical
  change g ∈ Finset.univ.image (fun r : M.Roots B N => GermBrick.mk ρ (M.rootChart B N r)) ↔ _
  rw [Finset.mem_image]
  constructor
  · rintro ⟨r,_,he⟩
    cases r with
    | inl i => exact Or.inl ⟨i.val,i.property,he.symm⟩
    | inr b =>
      have hb : b.val.val = g := (chart_germ ρ B b.val).symm.trans he
      exact Or.inr (hb ▸ ⟨b.val.property,b.property⟩)
  · rintro (⟨i,hi,he⟩ | ⟨hg,hr⟩)
    · exact ⟨Sum.inl ⟨i,hi⟩,Finset.mem_univ _,he.symm⟩
    · exact ⟨Sum.inr ⟨⟨g,hg⟩,hr⟩,Finset.mem_univ _,chart_germ ρ B ⟨g,hg⟩⟩

lemma contract_cutRefines (B : Basis ρ) (N : Finset I) (h : M.Present B N) :
    CutRefines ρ (M.contract B N h) B := by
  classical
  let P : M.Roots B N → Pattern S := Sum.elim (fun i => .split (M.edge i.val).coordinate .leaf .leaf)
    (fun _ => .leaf)
  apply cutRefines_ofChartPartition ρ (M.rootChart B N) (M.rootPartition B N h) B P
  intro r j
  cases r with
  | inl i =>
    cases j with
    | inl j =>
      simpa [P,Pattern.leafPrefix,Prefix.append_empty,rootChart,(M.edge i.val).left_eq,
        Merge.endpoint] using h i.val i.property false
    | inr j =>
      simpa [P,Pattern.leafPrefix,Prefix.append_empty,rootChart,(M.edge i.val).right_eq,
        Merge.endpoint] using h i.val i.property true
  | inr b =>
    simp [P,Pattern.leafPrefix,rootChart,LocalEmbedding.ofPrefix_empty,
      LocalEmbedding.comp_identity,chart_germ]

noncomputable def leafEquiv (B : Basis ρ) (N : Finset I) (h : M.Present B N) :
    (N × Bool) ⊕ M.Rest B N ≃ B := by
  classical
  let f : (N × Bool) ⊕ M.Rest B N → B := Sum.elim
    (fun p => ⟨((M.edge p.1.val).endpoint p.2).val,h _ p.1.property p.2⟩) (fun b => b.val)
  apply Equiv.ofBijective f
  constructor
  · intro i j he
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have hh := M.endpoint_eq (i := i.1.val) (j := j.1.val) (p := i.2) (q := j.2) (congrArg (fun b : B => b.val) he)
        exact congrArg Sum.inl (Prod.ext (Subtype.ext hh.1) hh.2)
      | inr j => exact False.elim (j.property _ i.1.property i.2 (congrArg Subtype.val he).symm)
    | inr i =>
      cases j with
      | inl j => exact False.elim (i.property _ j.1.property j.2 (congrArg Subtype.val he))
      | inr j => exact congrArg Sum.inr (Subtype.ext he)
  · intro b
    by_cases ht : ∃ i : N, ∃ q : Bool, b.val = ((M.edge i.val).endpoint q).val
    · obtain ⟨i,q,he⟩ := ht
      exact ⟨Sum.inl (i,q),Subtype.ext he.symm⟩
    · have hr : ∀ i ∈ N, ∀ q : Bool, b.val ≠ ((M.edge i).endpoint q).val := by
        intro i hi q he
        exact ht ⟨⟨i,hi⟩,q,he⟩
      exact ⟨Sum.inr ⟨b,hr⟩,rfl⟩

lemma rank_contract (B : Basis ρ) (N : Finset I) (h : M.Present B N) :
    rank ρ (M.contract B N h) + N.card = rank ρ B := by
  classical
  rw [contract,rank_ofChartPartition,rank_eq_card]
  have hc := Fintype.card_congr (M.leafEquiv B N h)
  simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_coe] at hc ⊢
  omega

end Matching
end

universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
namespace Matching
variable {C : Basis ρ} {I : Type w} (M : Matching C I)

lemma present_top (N : Finset I) : M.Present C N := fun i _ q => ((M.edge i).endpoint q).property

lemma present_mono {B D : Basis ρ} (hBD : CutRefines ρ B D) (hDC : CutRefines ρ D C)
    {N : Finset I} (h : M.Present B N) : M.Present D N := by
  intro i hi q
  let e : B := ⟨((M.edge i).endpoint q).val,h i hi q⟩
  let c := (M.edge i).endpoint q
  let d := ancestor ρ hDC.some.refines c
  have hcd := ancestor_restricts ρ hDC.some.refines c
  obtain ⟨e',he'⟩ := hBD.some.refines d
  have hee : e = e' := refines_ancestor_unique ρ (C := C)
    (GermBrick.restricts_refl ρ c.val) (GermBrick.restricts_trans ρ hcd he')
  have hdc : GermBrick.Restricts ρ d.val c.val := by
    have hh : e'.val = c.val := (congrArg Subtype.val hee).symm
    rwa [hh] at he'
  have hreg : GermBrick.region ρ c.val = GermBrick.region ρ d.val :=
    Set.Subset.antisymm (GermBrick.region_subset_of_restricts ρ hcd)
      (GermBrick.region_subset_of_restricts ρ hdc)
  have he := GermBrick.eq_of_restricts_of_region_eq ρ hcd hreg
  exact he.symm ▸ d.property

lemma contract_mono {B D : Basis ρ} (F : Forest ρ B D) (hDC : CutRefines ρ D C) {N K : Finset I}
    (hKN : K ⊆ N) (hB : M.Present B N) (hD : M.Present D K) :
    CutRefines ρ (M.contract B N hB) (M.contract D K hD) := by
  classical
  let P : M.Roots B N → Pattern S := Sum.elim
    (fun i => if i.val ∈ K then .leaf else .split (M.edge i.val).coordinate .leaf .leaf)
    (fun b => F.pattern b.val)
  apply cutRefines_ofChartPartition ρ (M.rootChart B N) (M.rootPartition B N hB)
    (M.contract D K hD) P
  intro r j
  cases r with
  | inl i =>
    by_cases hi : i.val ∈ K
    · have hp : P (Sum.inl i) = .leaf := by simp [P,hi]
      have hj : Pattern.leafPrefix (P (Sum.inl i)) j = Prefix.empty := by
        revert j
        rw [hp]
        intro j
        rfl
      rw [hj,LocalEmbedding.ofPrefix_empty,LocalEmbedding.comp_identity]
      exact (M.mem_contract D K hD _).mpr (Or.inl ⟨i.val,hi,rfl⟩)
    · have hj : ∃ q : Bool, GermBrick.mk ρ (LocalEmbedding.comp ρ
          (M.rootChart B N (Sum.inl i)) (LocalEmbedding.ofPrefix ρ
            (Pattern.leafPrefix (P (Sum.inl i)) j))) = ((M.edge i.val).endpoint q).val := by
        have hp : P (Sum.inl i) = .split (M.edge i.val).coordinate .leaf .leaf := by simp [P,hi]
        revert j
        rw [hp]
        intro j
        cases j with
        | inl j => exact ⟨false,by simpa [Pattern.leafPrefix,Prefix.append_empty,rootChart,Merge.endpoint]
            using (M.edge i.val).left_eq⟩
        | inr j => exact ⟨true,by simpa [Pattern.leafPrefix,Prefix.append_empty,rootChart,Merge.endpoint]
            using (M.edge i.val).right_eq⟩
      obtain ⟨q,hj⟩ := hj
      rw [hj]
      apply (M.mem_contract D K hD _).mpr
      refine Or.inr ⟨?_,?_⟩
      · exact M.present_mono ⟨F⟩ hDC hB i.val i.property q
      · intro k hk p he
        exact hi ((M.endpoint_eq he).1.symm ▸ hk)
  | inr b =>
    have hj : GermBrick.mk ρ (LocalEmbedding.comp ρ (M.rootChart B N (Sum.inr b))
        (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (P (Sum.inr b)) j))) =
        (F.leaves ⟨b.val,j⟩).val := F.chart_eq ⟨b.val,j⟩
    rw [hj]
    apply (M.mem_contract D K hD _).mpr
    refine Or.inr ⟨(F.leaves ⟨b.val,j⟩).property,?_⟩
    intro k hk q he
    have hrest : GermBrick.Restricts ρ (F.leaves ⟨b.val,j⟩).val b.val.val := by
      refine ⟨chart ρ B b.val,Pattern.leafPrefix (F.pattern b.val) j,
        (chart_germ ρ B b.val).symm,(F.chart_eq ⟨b.val,j⟩).symm⟩
    let e : B := ⟨((M.edge k).endpoint q).val,hB k (hKN hk) q⟩
    have heq : b.val = e := refines_ancestor_unique ρ (C := D) hrest (by
      rw [he]
      exact GermBrick.restricts_refl ρ e.val)
    exact b.property k (hKN hk) q (congrArg Subtype.val heq)
end Matching
end TwistedBrin.Basis

namespace TwistedBrin.Pattern
variable {S : Type u}
lemma card_leaves_ge_two {P : Pattern S} (h : P ≠ .leaf) :
    2 ≤ Fintype.card (Leaves P) := by
  cases P with
  | leaf => exact False.elim (h rfl)
  | split s P Q =>
    change 2 ≤ Fintype.card (Leaves P ⊕ Leaves Q)
    rw [Fintype.card_sum]
    have hP := Fintype.card_pos (α := Leaves P)
    have hQ := Fintype.card_pos (α := Leaves Q)
    omega
end TwistedBrin.Pattern

namespace TwistedBrin.Basis
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
namespace Forest
variable {B C : Basis ρ}

lemma leaf_root_eq (F : Forest ρ B C) (b : B) (h : F.pattern b = .leaf)
    (j : Pattern.Leaves (F.pattern b)) : (F.leaves ⟨b,j⟩).val = b.val := by
  rw [← F.chart_eq ⟨b,j⟩]
  change GermBrick.mk ρ (LocalEmbedding.comp ρ (chart ρ B b)
    (LocalEmbedding.ofPrefix ρ (Pattern.leafPrefix (F.pattern b) j))) = b.val
  have hp : Pattern.leafPrefix (F.pattern b) j = Prefix.empty := by
    revert j
    rw [h]
    intro j
    rfl
  rw [hp,LocalEmbedding.ofPrefix_empty,LocalEmbedding.comp_identity,chart_germ]

lemma lost_leaves_bound (F : Forest ρ B C) :
    letI := Classical.decEq (GermBrick ρ)
    (C.pieces \ B.pieces).card ≤ 2 * (rank ρ C - rank ρ B) := by
  classical
  let T : B → Finset (GermBrick ρ) := fun b =>
    if F.pattern b = .leaf then ∅ else
      Finset.univ.image (fun j : Pattern.Leaves (F.pattern b) => (F.leaves ⟨b,j⟩).val)
  have hsub : C.pieces \ B.pieces ⊆ Finset.univ.biUnion T := by
    intro c hc
    obtain ⟨hcC,hcB⟩ := Finset.mem_sdiff.mp hc
    obtain ⟨⟨b,j⟩,he⟩ := F.leaves.surjective ⟨c,hcC⟩
    have hn : F.pattern b ≠ .leaf := by
      intro hb
      have hh := F.leaf_root_eq b hb j
      have hcc : c = b.val := (congrArg Subtype.val he).symm.trans hh
      exact hcB (hcc ▸ b.property)
    apply Finset.mem_biUnion.mpr
    refine ⟨b,Finset.mem_univ _,?_⟩
    simp only [T,ite_eq_right hn]
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,congrArg Subtype.val he⟩
  have hcard (b : B) : (T b).card + 2 ≤ 2 * Fintype.card (Pattern.Leaves (F.pattern b)) := by
    by_cases hb : F.pattern b = .leaf
    · simp [T,hb,Pattern.Leaves]
    · have hle : (T b).card ≤ Fintype.card (Pattern.Leaves (F.pattern b)) := by
        simpa only [T,ite_eq_right hb,Finset.card_univ] using
          (Finset.card_image_le (s := (Finset.univ : Finset (Pattern.Leaves (F.pattern b))))
            (f := fun j => (F.leaves ⟨b,j⟩).val))
      have htwo := Pattern.card_leaves_ge_two hb
      omega
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset B)) (fun b _ => hcard b)
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  have hr : ∑ b : B, Fintype.card (Pattern.Leaves (F.pattern b)) = rank ρ C := by
    rw [rank_eq_card,← Fintype.card_sigma]
    exact Fintype.card_congr F.leaves
  rw [hr] at hsum
  have hi := (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hbcard : (∑ _b : B, 2) = 2 * rank ρ B := by simp [rank_eq_card, Nat.mul_comm]
  rw [hbcard] at hsum
  omega
end Forest
end TwistedBrin.Basis

end

end OAI
