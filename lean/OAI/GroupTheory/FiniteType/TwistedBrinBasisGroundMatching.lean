import Mathlib
import OAI.GroupTheory.FiniteType.OrderChainsExactInOfDirected

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
universe u v
namespace TwistedBrin.Basis
section
universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

noncomputable def groundMatching (C : Basis ρ) (s : S) (k : ℕ) (hk : 2*k ≤ rank ρ C) :
    Matching C (Fin k) := by
  classical
  have hc : Fintype.card (Fin k × Bool) ≤ Fintype.card C := by
    simpa [Fintype.card_prod,rank_eq_card,Nat.mul_comm] using hk
  let e : (Fin k × Bool) ↪ C := Classical.choice (Function.Embedding.nonempty_of_card_le hc)
  exact {
    edge := fun i => Merge.ofPair (ρ := ρ) (e (i,false)) (e (i,true))
      (fun he => Bool.false_ne_true (congrArg Prod.snd (e.injective he))) s
    endpoints_injective := by
      have h (p : Fin k × Bool) :
          (Merge.ofPair (ρ := ρ) (e (p.1,false)) (e (p.1,true))
            (fun he => Bool.false_ne_true (congrArg Prod.snd (e.injective he))) s).endpoint p.2 = e p := by
        rcases p with ⟨i,⟨⟩⟩ <;> rfl
      simpa only [h] using e.injective }

namespace Matching
variable {C : Basis ρ} {I : Type w} (M : Matching C I)

noncomputable def available (B : Basis ρ) (N : Finset I) : Finset I := by
  classical
  exact N.filter (fun i => ∀ q : Bool, ((M.edge i).endpoint q).val ∈ B.pieces)

lemma mem_available (B : Basis ρ) (N : Finset I) (i : I) :
    i ∈ M.available B N ↔ i ∈ N ∧ ∀ q : Bool, ((M.edge i).endpoint q).val ∈ B.pieces := by
  classical
  exact Finset.mem_filter

lemma available_present (B : Basis ρ) (N : Finset I) : M.Present B (M.available B N) :=
  fun i hi => ((M.mem_available B N i).mp hi).2

lemma available_mono {B D : Basis ρ} (hBD : CutRefines ρ B D) (hDC : CutRefines ρ D C)
    (N : Finset I) : M.available B N ⊆ M.available D N := by
  intro i hi
  exact (M.mem_available D N i).mpr ⟨((M.mem_available B N i).mp hi).1,
    M.present_mono hBD hDC (M.available_present B N) i hi⟩

lemma available_subset (B : Basis ρ) (N : Finset I) : M.available B N ⊆ N :=
  fun i hi => ((M.mem_available B N i).mp hi).1

lemma unavailable_bound {B : Basis ρ} (F : Forest ρ B C) (N : Finset I) :
    N.card - (M.available B N).card ≤ 2 * (rank ρ C - rank ρ B) := by
  classical
  let T := N \ M.available B N
  have hp (i : T) : ∃ q : Bool, ((M.edge i.val).endpoint q).val ∉ B.pieces := by
    have hi := Finset.mem_sdiff.mp i.property
    by_contra hn
    push Not at hn
    exact hi.2 ((M.mem_available B N i.val).mpr ⟨hi.1,hn⟩)
  let f : T → ↥(C.pieces \ B.pieces) := fun i =>
    ⟨((M.edge i.val).endpoint (hp i).choose).val,
      Finset.mem_sdiff.mpr ⟨((M.edge i.val).endpoint (hp i).choose).property,(hp i).choose_spec⟩⟩
  have hf : Function.Injective f := by
    intro i j hh
    apply Subtype.ext
    exact (M.endpoint_eq (congrArg (fun x : ↥(C.pieces \ B.pieces) => x.val) hh)).1
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hcard
  have he : T.card = N.card - (M.available B N).card :=
    Finset.card_sdiff_of_subset (M.available_subset B N)
  rw [he] at hcard
  exact hcard.trans F.lost_leaves_bound

lemma available_nonempty {B : Basis ρ} (hBC : CutRefines ρ B C) (N : Finset I)
    (hN : 2 * (rank ρ C - rank ρ B) < N.card) : (M.available B N).Nonempty := by
  have hb := M.unavailable_bound hBC.some N
  apply Finset.card_pos.mp
  omega

end Matching
end

universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}

structure CutDown (C : Basis ρ) where
  val : Basis ρ
  upper : CutRefines ρ val C
  ne : val ≠ C
namespace CutDown
variable {C : Basis ρ}
@[ext] lemma ext {B D : CutDown C} (h : B.val = D.val) : B = D := by
  cases B; cases D; simp_all
instance : PartialOrder (CutDown C) where
  le B D := CutRefines ρ B.val D.val
  le_refl B := cutRefines_refl ρ B.val
  le_trans _ _ _ := cutRefines_trans ρ
  le_antisymm _ _ h k := ext (cutRefines_antisymm ρ h k)
lemma rank_lt_top (B : CutDown C) : rank ρ B.val < rank ρ C :=
  (rank_strictMono ρ) (lt_of_le_of_ne (le_of_cutRefines ρ B.upper) B.ne)
lemma strictMono_rank : StrictMono (fun B : CutDown C => rank ρ B.val) := by
  intro B D h
  apply rank_strictMono ρ
  exact lt_of_le_of_ne (le_of_cutRefines ρ h.le) (fun he => h.ne (ext he))

noncomputable def upperInterval (B : CutDown C) : {D : CutDown C // B < D} ≃o
    ProperCutInterval ρ B.val C where
  toFun D := ⟨⟨D.val.val,D.property.le,D.val.upper⟩,
    (fun he => D.property.ne (ext he.symm)),D.val.ne⟩
  invFun D := ⟨⟨D.val.val,D.val.upper,D.property.2⟩,
    lt_of_le_of_ne D.val.lower (fun he => D.property.1 (congrArg CutDown.val he).symm)⟩
  left_inv _ := by apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; rfl
  map_rel_iff' := Iff.rfl

abbrev Near (C : Basis ρ) (m : ℕ) := {B : CutDown C // m ≤ rank ρ B.val}
def nearInclude (C : Basis ρ) (m : ℕ) : Near C m →o CutDown C := ⟨Subtype.val,fun _ _ h => h⟩

end CutDown

namespace Matching
variable {C : Basis ρ} {I : Type w} [Fintype I] (M : Matching C I)

structure Pair (m : ℕ) where
  base : CutDown.Near C m
  selected : Finset I
  nonempty : selected.Nonempty
  present : M.Present base.val.val selected

namespace Pair
variable {M} {m : ℕ}
omit [Fintype I] in
@[ext] lemma ext [Fintype I] {x y : M.Pair m} (h : x.base = y.base) (k : x.selected = y.selected) : x = y := by
  cases x; cases y; simp_all
instance : PartialOrder (M.Pair m) where
  le x y := x.base ≤ y.base ∧ y.selected ⊆ x.selected
  le_refl _ := ⟨le_rfl,Finset.Subset.refl _⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1,k.2.trans h.2⟩
  le_antisymm _ _ h k := ext (le_antisymm h.1 k.1) (Finset.Subset.antisymm k.2 h.2)
end Pair

def projectPair (m : ℕ) : M.Pair m →o CutDown.Near C m := ⟨Pair.base,fun _ _ h => h.1⟩

noncomputable def contractPair (m : ℕ) : M.Pair m →o CutDown C where
  toFun x := ⟨M.contract x.base.val.val x.selected x.present,
    cutRefines_trans ρ (M.contract_cutRefines _ _ _) x.base.val.upper,by
      intro he
      have hr := M.rank_contract x.base.val.val x.selected x.present
      have hp := Finset.card_pos.mpr x.nonempty
      have hb := x.base.val.rank_lt_top
      rw [he] at hr
      omega⟩
  monotone' := by
    intro x y h
    exact M.contract_mono h.1.some y.base.val.upper h.2 x.present y.present

lemma contractPair_le_base (m : ℕ) (x : M.Pair m) :
    M.contractPair m x ≤ x.base.val := M.contract_cutRefines _ _ x.present

abbrev GroundFaces := {N : OrderDual (Finset I) // N.Nonempty}

noncomputable def ground : GroundFaces (I := I) →o CutDown C where
  toFun N := ⟨M.contract C N.val (M.present_top N.val),M.contract_cutRefines _ _ _,by
    intro he
    have hr := M.rank_contract C N.val (M.present_top N.val)
    have hp := Finset.card_pos.mpr N.property
    rw [he] at hr
    omega⟩
  monotone' := by
    intro N K h
    exact M.contract_mono (Forest.refl C) (cutRefines_refl ρ C) h (M.present_top _) (M.present_top _)

def selectedPair (m : ℕ) : M.Pair m →o GroundFaces (I := I) :=
  ⟨fun x => ⟨x.selected,x.nonempty⟩,fun _ _ h => h.2⟩

lemma contractPair_le_ground (m : ℕ) (x : M.Pair m) :
    M.contractPair m x ≤ M.ground (M.selectedPair m x) :=
  M.contract_mono x.base.val.upper.some (cutRefines_refl ρ C) (Finset.Subset.refl _) x.present (M.present_top _)

abbrev AvailableFaces (B : CutDown C) :=
  {N : OrderDual (Finset I) // N.Nonempty ∧ (OrderDual.ofDual N) ⊆ M.available B.val Finset.univ}

noncomputable def fiberResolution (m : ℕ) (B : CutDown.Near C m) :
    {x : M.Pair m // M.projectPair m x ≤ B} →o M.AvailableFaces B.val where
  toFun x := ⟨x.val.selected,x.val.nonempty,by
    intro i hi
    apply (M.mem_available B.val.val Finset.univ i).mpr
    exact ⟨Finset.mem_univ _,M.present_mono x.property B.val.upper x.val.present i hi⟩⟩
  monotone' := fun _ _ h => h.2

noncomputable def fiberInclusion (m : ℕ) (B : CutDown.Near C m) :
    M.AvailableFaces B.val →o {x : M.Pair m // M.projectPair m x ≤ B} where
  toFun N := ⟨⟨B,N.val,N.property.1,fun i hi =>
    ((M.mem_available B.val.val Finset.univ i).mp (N.property.2 hi)).2⟩,le_rfl⟩
  monotone' := fun _ _ h => ⟨le_rfl,h⟩
lemma fiber_comparison (m : ℕ) (B : CutDown.Near C m)
    (x : {x : M.Pair m // M.projectPair m x ≤ B}) :
    x ≤ M.fiberInclusion m B (M.fiberResolution m B x) := ⟨x.property,Finset.Subset.refl _⟩

end Matching
end TwistedBrin.Basis

namespace TwistedBrin.Basis.Matching
open OrderListChains OrderChains
universe w
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
variable {C : Basis ρ} {I : Type w} [Fintype I] (M : Matching C I)

lemma fiber_exactIn (m : ℕ) (B : CutDown.Near C m)
    (hB : (M.available B.val.val Finset.univ).Nonempty) (n : ℕ) :
    ExactIn {x : M.Pair m // M.projectPair m x ≤ B} n := by
  classical
  apply exactIn_of_upper_comparison _ (M.fiberInclusion m B) (M.fiberResolution m B)
    (M.fiber_comparison m B)
  apply exactIn_of_bottom _ ⟨M.available B.val.val Finset.univ,hB,Finset.Subset.refl _⟩
  intro N
  exact N.property.2

lemma fiber_nonempty (m : ℕ) (B : CutDown.Near C m)
    (hB : (M.available B.val.val Finset.univ).Nonempty) :
    ∃ x : M.Pair m, M.projectPair m x ≤ B := by
  exact ⟨⟨B,M.available B.val.val Finset.univ,hB,M.available_present _ _⟩,le_rfl⟩

lemma ground_exactIn [Nonempty I] (n : ℕ) : ExactIn (GroundFaces (I := I)) n := by
  classical
  apply exactIn_of_bottom _ ⟨Finset.univ,Finset.univ_nonempty⟩
  intro N
  exact Finset.subset_univ _

theorem near_nullIn [Nonempty I] (m : ℕ)
    (hav : ∀ B : CutDown.Near C m, (M.available B.val.val Finset.univ).Nonempty)
    {n : ℕ} (c : Chain (CutDown.Near C m)) (hc : c ∈ module (CutDown.Near C m))
    (hn : Homogeneous _ n c) (hd : boundary _ c = 0) (ha : augmentation _ c = 0) :
    ∃ d : Chain (CutDown C), d ∈ module (CutDown C) ∧ Homogeneous _ (n+1) d ∧
      boundary _ d = mapChain _ (CutDown.nearInclude C m) c := by
  classical
  let P := CutDown.Near C m
  let Q := M.Pair m
  let D := CutDown C
  let G := GroundFaces (I := I)
  let a := CutDown.nearInclude C m
  let p := M.projectPair m
  let q := M.contractPair m
  let s := M.selectedPair m
  let g := M.ground
  let f := a.comp p
  let t := g.comp s
  obtain ⟨z,e,hz,hzn,hzd,hza,he,hen,hed⟩ := carrier_section P p n
    (fun B => M.fiber_nonempty m B (hav B))
    (fun B k _ => exactSet_of_subtype Q
      ⟨(M.fiber_nonempty m B (hav B)).choose,(M.fiber_nonempty m B (hav B)).choose_spec⟩
      (M.fiber_exactIn m B (hav B) k)) le_rfl c hc hn hd ha
  have hsz : mapChain Q s z ∈ module G := map_mem Q s hz
  have hszn : Homogeneous G n (mapChain Q s z) := map_degree Q s hzn
  have hszd : boundary G (mapChain Q s z) = 0 := by rw [boundary_mapChain,hzd,map_zero]
  have hsza : augmentation G (mapChain Q s z) = 0 := by rw [augmentation_mapChain,hza]
  obtain ⟨b,hb,hbn,hbd⟩ := ground_exactIn (I := I) n _ hsz hszn hszd hsza
  have hqf : ∀ x : Q, q x ≤ f x := M.contractPair_le_base m
  have hqt : ∀ x : Q, q x ≤ t x := M.contractPair_le_ground m
  have hHf := comparison_boundary Q q f z
  have hHt := comparison_boundary Q q t z
  rw [hzd,map_zero,add_zero] at hHf hHt
  refine ⟨mapChain P a e + mapChain G g b + comparison Q q t z - comparison Q q f z,
    (module D).sub_mem ((module D).add_mem
      ((module D).add_mem (map_mem P a he) (map_mem G g hb))
      (comparison_mem Q q t hqt hz)) (comparison_mem Q q f hqf hz),
    supported_sub D (supported_add D (supported_add D (map_degree P a hen)
      (map_degree G g hbn)) (comparison_degree Q q t hzn)) (comparison_degree Q q f hzn),?_⟩
  rw [map_sub,map_add,map_add,boundary_mapChain,boundary_mapChain,hed,hbd,hHt,hHf,
    map_sub,mapChain_comp,mapChain_comp]
  change mapChain P a c - mapChain Q f z + mapChain Q t z +
    (mapChain Q q z - mapChain Q t z) - (mapChain Q q z - mapChain Q f z) = _
  abel
end TwistedBrin.Basis.Matching

namespace TwistedBrin.Basis.CutDown
open OrderListChains OrderChains
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
variable {C : Basis ρ}
lemma upper_nonempty (B : CutDown C) (h : rank ρ B.val + 2 ≤ rank ρ C) :
    ∃ D : CutDown C, B < D := by
  obtain ⟨e,he⟩ := B.upper.some.exists_last_merge B.ne
  refine ⟨⟨e.lower,e.lower_cutRefines,e.lower_ne⟩,lt_of_le_of_ne he ?_⟩
  intro hBD
  have hr := e.rank_lower
  have hv := congrArg CutDown.val hBD
  dsimp at hv
  rw [← hv] at hr
  omega

theorem exactIn_high_rank [Nonempty S] (C : Basis ρ) (n : ℕ)
    (hC : 2 * (2 * 2^(n+2) + 1) ≤ rank ρ C) : ExactIn (CutDown C) n := by
  classical
  let L := 2^(n+2)
  let k := 2*L+1
  let m := rank ρ C - L
  have hk : 0 < k := by dsimp [k]; omega
  let : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  let M := groundMatching C (Classical.choice ‹Nonempty S›) k hC
  have hL : 2 ≤ L := by
    dsimp [L]
    have hh := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n+2)
    simpa using hh
  have hLm : L ≤ rank ρ C := by dsimp [L] at *; omega
  have hml : m + L = rank ρ C := Nat.sub_add_cancel hLm
  have hav (B : Near C m) : (M.available B.val.val Finset.univ).Nonempty := by
    apply M.available_nonempty B.val.upper
    simp only [Finset.card_univ,Fintype.card_fin]
    have hb := B.property
    dsimp [k]
    omega
  let e := M.edge ⟨0,hk⟩
  let u : Near C m := ⟨⟨e.lower,e.lower_cutRefines,e.lower_ne⟩,by
    have he := e.rank_lower
    change m ≤ rank ρ e.lower
    omega⟩
  intro c hc hn hd ha
  have hcU : c ∈ onSet (CutDown C) Set.univ := fun s hs => ⟨hc hs,Set.subset_univ _⟩
  obtain ⟨c',d,hc',hn',hd',ha',hdD,hdn,hdd⟩ := raise_rank (CutDown C)
    (fun B => rank ρ B.val) strictMono_rank Set.univ m n
    (fun B _ hB => by
      obtain ⟨D,hD⟩ := upper_nonempty B (by omega)
      exact ⟨D,Set.mem_univ _,hD⟩)
    (fun B _ hB j hj => by
      have hrj : rank ρ B.val + 2^(j+2) ≤ rank ρ C := by
        have hp := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.add_le_add_right hj 2)
        change 2^(j+2) ≤ L at hp
        omega
      have hx := properCutInterval_exactIn ρ B.upper B.ne hrj
      have hex : ExactIn {D : CutDown C // B < D} j :=
        exactIn_of_orderIso B.upperInterval hx
      obtain ⟨D,hD⟩ := upper_nonempty B (by omega)
      have hh := exactSet_of_subtype (CutDown C) ⟨D,hD⟩ hex
      have hset : {x : CutDown C | x ∈ Set.univ ∧ B < x} = {x | B < x} := by
        ext x
        simp only [Set.mem_ofPred_eq,Set.mem_univ,true_and]
      rw [hset]
      exact hh)
    le_rfl c hcU hn hd ha
  let U : Set (CutDown C) := {B | m ≤ rank ρ B.val}
  have hc'U : c' ∈ onSet (CutDown C) U :=
    onSet_mono _ (fun _ hx => hx.2) hc'
  let pr := project (CutDown C) U u
  have hpr := map_onSet (CutDown C) pr (U := U) (V := Set.univ) (fun _ _ => Set.mem_univ _)
    (fun x hx y hy hxy => by
      change (pr x).val ≤ (pr y).val
      change (project (CutDown C) U u x).val ≤ (project (CutDown C) U u y).val
      rw [project_val (CutDown C) (U := U) u hx,project_val (CutDown C) (U := U) u hy]
      exact hxy) hc'U
  have hprd : boundary (Near C m) (mapChain (CutDown C) pr c') = 0 := by
    change boundary U (mapChain (CutDown C) pr c') = 0
    rw [OrderListChains.boundary_mapChain,hd',map_zero]
  have hpra : augmentation (Near C m) (mapChain (CutDown C) pr c') = 0 := by
    change augmentation U (mapChain (CutDown C) pr c') = 0
    rw [OrderListChains.augmentation_mapChain,ha']
  obtain ⟨b,hb,hbn,hbd⟩ := M.near_nullIn m hav (mapChain _ pr c')
    (onSet_le_module _ _ hpr) (map_degree _ pr hn') hprd hpra
  have hbd' : boundary (CutDown C) b = c' := by
    rw [hbd]
    change mapChain U (fun x : U => x.val) (mapChain (CutDown C) pr c') = c'
    rw [OrderChains.mapChain_comp]
    have he := mapChain_eq_on (CutDown C) ((fun x : U => x.val) ∘ pr) id
      (c := c') (fun s hs x hx => project_val _ u ((hc'U hs).2 hx))
    rw [he,mapChain_id]
  refine ⟨d+b,(module _).add_mem (onSet_le_module _ _ hdD) hb,
    supported_add _ hdn hbn,?_⟩
  rw [map_add,hdd,hbd']
  abel
end TwistedBrin.Basis.CutDown

namespace TwistedBrin.Basis
open OrderListChains OrderChains
variable {A : Type v} [Group A] {S : Type u} {ρ : A →* Equiv.Perm S}
                                                                       
structure CutBasis (ρ : A →* Equiv.Perm S) where
  val : Basis ρ
namespace CutBasis
@[ext] lemma ext {B C : CutBasis ρ} (h : B.val = C.val) : B = C := by
  cases B; cases C; simp_all
instance : Nonempty (CutBasis ρ) := ⟨⟨trivial ρ⟩⟩
instance : PartialOrder (CutBasis ρ) where
  le B C := CutRefines ρ B.val C.val
  le_refl B := cutRefines_refl ρ B.val
  le_trans _ _ _ := cutRefines_trans ρ
  le_antisymm _ _ h k := ext (cutRefines_antisymm ρ h k)
lemma strictMono_rank : StrictMono (fun B : CutBasis ρ => rank ρ B.val) := by
  intro B C h
  apply rank_strictMono ρ
  exact lt_of_le_of_ne (le_of_cutRefines ρ h.le) (fun he => h.ne (ext he))
lemma directed (B C : CutBasis ρ) : ∃ D, B ≤ D ∧ C ≤ D := by
  obtain ⟨D,hBD,hCD⟩ := cut_directed ρ B.val C.val
  exact ⟨⟨D⟩,hBD,hCD⟩
noncomputable def lowerEquiv (C : CutBasis ρ) : Set.Iio C ≃o CutDown C.val where
  toFun B := ⟨B.val.val,(show B.val < C from B.property).le,
    fun he => (show B.val < C from B.property).ne (ext he)⟩
  invFun B := ⟨⟨B.val⟩,lt_of_le_of_ne B.upper (fun he => B.ne (congrArg CutBasis.val he))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl
lemma lower_nonempty [Nonempty S] (C : CutBasis ρ) (h : 2 ≤ rank ρ C.val) :
    ∃ B : CutBasis ρ, B < C := by
  let M := groundMatching C.val (Classical.choice ‹Nonempty S›) 1 (by simpa using h)
  let e := M.edge 0
  exact ⟨⟨e.lower⟩,lt_of_le_of_ne e.lower_cutRefines (fun he => e.lower_ne (congrArg CutBasis.val he))⟩
lemma lower_exactSet [Nonempty S] (C : CutBasis ρ) (n : ℕ)
    (h : 2*(2*2^(n+2)+1) ≤ rank ρ C.val) : ExactSet (CutBasis ρ) (Set.Iio C) n := by
  have ht : 2 ≤ rank ρ C.val := by omega
  obtain ⟨B,hB⟩ := lower_nonempty C ht
  exact exactSet_of_subtype (CutBasis ρ) ⟨B,hB⟩
    (exactIn_of_orderIso (lowerEquiv C) (CutDown.exactIn_high_rank C.val n h))

theorem sublevel_exact [Nonempty S] (n h : ℕ) (hh : 2*(2*2^(n+2)+1) ≤ h) :
    ExactSet (CutBasis ρ) {B | rank ρ B.val ≤ h} n := by
  apply exactSet_sublevel (CutBasis ρ) (fun B => rank ρ B.val) strictMono_rank h n
    (fun C hC => lower_nonempty C (by omega)) ?_ le_rfl
    (exactIn_of_directed (CutBasis ρ) directed n)
  intro C hC k hk
  apply lower_exactSet C k
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (Nat.add_le_add_right hk 2)
  omega
end CutBasis
end TwistedBrin.Basis

end

end OAI
