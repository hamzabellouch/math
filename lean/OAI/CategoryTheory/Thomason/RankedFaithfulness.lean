import Mathlib
import OAI.CategoryTheory.Thomason.LayeredWhiskers
import OAI.CategoryTheory.Thomason.RankedExchange

namespace OAI

/-! Ranked Faithfulness. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

lemma table_rank_split (n : ℕ) (s : ℤ) (x : Table K)
    (hx : truncate (n+1) false x = x) :
    ∃ l r : Table K, ∃ h : truncate n true l = truncate n false r,
      truncate (n+1) false l = l ∧ truncate (n+1) false r = r ∧
      (∀ b, A.coefficient b (n+1) (l.row (n+1) false) ≠ 0 → s < A.rank b) ∧
      (∀ b, A.coefficient b (n+1) (r.row (n+1) false) ≠ 0 → ¬s < A.rank b) ∧
      x = comp n l r h := by
  let c := A.cut (n+1) (x.row (n+1) false) (fun b => s < A.rank b)
  let d := A.cut (n+1) (x.row (n+1) false) (fun b => ¬s < A.rank b)
  have hp := (A.rank_cut_positive n s 0 0 (x.row n false) (x.row n true) _
    (K.positive n).zero_mem (K.positive n).zero_mem
    (x.positive n false) (x.positive n true) (x.positive (n+1) false)
    (by simp) (by simp) (by rw [sub_zero,zero_add,x.boundary])).1
  obtain ⟨l,r,h,hl,hr,hlt,hrt,he⟩ := split_top x hx c d
    (A.cut_positive _ _ (x.positive _ _) _) (A.cut_positive _ _ (x.positive _ _) _)
    (A.cut_add_complement _ _ _) hp
  refine ⟨l,r,h,hl,hr,?_,?_,he.symm⟩
  · intro b hb
    rw [hlt,A.coefficient_cut] at hb
    by_contra hn
    exact hb (ite_eq_right hn)
  · intro b hb
    rw [hrt,A.coefficient_cut] at hb
    by_contra hn
    exact hb (ite_eq_right (not_not_intro hn))

lemma rank_split (n : ℕ) (s : ℤ)
    (hinj : Function.Injective (F.onCells n))
    (hbij : Function.Bijective (F.onCells (n+1))) (x : C.Cell)
    (hx : C.source (n+1) x = x) :
    ∃ l r : C.Cell, C.source (n+1) l = l ∧ C.source (n+1) r = r ∧
      C.target n l = C.source n r ∧
      (∀ b, A.coefficient b (n+1) ((F.map l).row (n+1) false) ≠ 0 → s < A.rank b) ∧
      (∀ b, A.coefficient b (n+1) ((F.map r).row (n+1) false) ≠ 0 → ¬s < A.rank b) ∧
      x = C.join n l r := by
  obtain ⟨l,r,h,hl,hr,hlo,hro,he⟩ := A.table_rank_split n s (F.map x)
    ((F.map_source (n+1) x).symm.trans (congrArg F.map hx))
  obtain ⟨l',hl'⟩ := hbij.2 ⟨l,hl⟩
  obtain ⟨r',hr'⟩ := hbij.2 ⟨r,hr⟩
  have hfl : F.map l'.val = l := congrArg Subtype.val hl'
  have hfr : F.map r'.val = r := congrArg Subtype.val hr'
  have hm : C.target n l'.val = C.source n r'.val := by
    apply F.bounded_ext n hinj _ _ (C.source_target_self n _) (C.source_source_self n _)
    rw [F.map_target,F.map_source,hfl,hfr]
    exact h
  refine ⟨l'.val,r'.val,l'.property,r'.property,hm,?_,?_,?_⟩
  · simpa only [hfl] using hlo
  · simpa only [hfr] using hro
  · apply F.bounded_ext (n+1) hbij.1 _ _ hx
      (by rw [C.join_source_gt (n+1) n _ _ (Nat.lt_succ_self n) hm,l'.property,r'.property])
    rw [F.map_join n _ _ hm,hfl,hfr,K.nu.join_eq n l r h]
    exact he

lemma rank_split_unique (n : ℕ) (s : ℤ)
    (hinj : Function.Injective (F.onCells (n+1))) (l r l' r' : C.Cell)
    (hl : C.source (n+1) l = l) (hr : C.source (n+1) r = r)
    (hl' : C.source (n+1) l' = l') (hr' : C.source (n+1) r' = r')
    (h : C.target n l = C.source n r) (h' : C.target n l' = C.source n r')
    (hlo : ∀ b, A.coefficient b (n+1) ((F.map l).row (n+1) false) ≠ 0 → s < A.rank b)
    (hro : ∀ b, A.coefficient b (n+1) ((F.map r).row (n+1) false) ≠ 0 → ¬s < A.rank b)
    (hlo' : ∀ b, A.coefficient b (n+1) ((F.map l').row (n+1) false) ≠ 0 → s < A.rank b)
    (hro' : ∀ b, A.coefficient b (n+1) ((F.map r').row (n+1) false) ≠ 0 → ¬s < A.rank b)
    (he : C.join n l r = C.join n l' r') : l = l' ∧ r = r' := by
  have het := congrArg (fun x => (F.map x).row (n+1) false) he
  rw [top_row_join F (n+1) n (Nat.lt_succ_self n) l r h,
    top_row_join F (n+1) n (Nat.lt_succ_self n) l' r' h'] at het
  obtain ⟨hls,hrs⟩ := OrderedWhisker.split_unique (A := A) (n+1) s _ _ _ _ hlo hlo' hro hro' het
  have hf (x : C.Cell) (hx : C.source (n+1) x = x) : truncate (n+1) false (F.map x) = F.map x :=
    (F.map_source (n+1) x).symm.trans (congrArg F.map hx)
  constructor
  · apply F.bounded_ext (n+1) hinj l l' hl hl'
    apply top_and_source_ext n _ _ (hf l hl) (hf l' hl') hls
    have hh := congrArg (fun x => F.map (C.source n x)) he
    rw [C.join_source_le n n l r le_rfl h,C.join_source_le n n l' r' le_rfl h',
      F.map_source,F.map_source] at hh
    exact hh
  · apply F.bounded_ext (n+1) hinj r r' hr hr'
    apply top_and_target_ext n _ _ (hf r hr) (hf r' hr') hrs
    have hh := congrArg (fun x => F.map (C.target n x)) he
    rw [C.join_target_le n n l r le_rfl h,C.join_target_le n n l' r' le_rfl h',
      F.map_target,F.map_target] at hh
    exact hh
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

lemma support_add (p : ℕ) (P : A.Index → Prop) (x y : K.Chain p)
    (hx : ∀ b, A.coefficient b p x ≠ 0 → P b)
    (hy : ∀ b, A.coefficient b p y ≠ 0 → P b) :
    ∀ b, A.coefficient b p (x+y) ≠ 0 → P b := by
  intro b hb
  rw [map_add] at hb
  by_cases h : A.coefficient b p x = 0
  · exact hy b (by simpa only [h,zero_add] using hb)
  · exact hx b h

lemma layered_row_above (b : A.Index) {n : ℕ} {x : C.Cell}
    (hx : C.LayeredWhisker (fun z => F.map z = A.atom b) n x)
    (p : ℕ) (hp : n < p) (e : Bool) : (F.map x).row p e = (A.atom b).row p e := by
  induction n generalizing x with
  | zero => change F.map x = A.atom b at hx; rw [hx]
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,rfl⟩ := hx
    have hf (a : C.Cell) (ha : C.source (n+1) a = a) : (F.map a).row p e = 0 :=
      row_above_fixed (F.map a) ((F.map_source (n+1) a).symm.trans (congrArg F.map ha)) hp e
    have hpm : ¬p < n := by omega
    have hpn : p ≠ n := by omega
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]; exact hmr
    rw [F.map_join n _ r hlmr,K.nu.join_eq n _ _ (F.map_composable hlmr)]
    change (comp n (F.map (C.join n l m)) (F.map r) (F.map_composable hlmr)).row p e = _
    erw [comp_row]
    rw [ite_eq_right hpm,ite_eq_right hpn,F.map_join n l m hlm,
      K.nu.join_eq n _ _ (F.map_composable hlm)]
    change (comp n (F.map l) (F.map m) (F.map_composable hlm)).row p e + (F.map r).row p e = _
    erw [comp_row]
    rw [ite_eq_right hpm,ite_eq_right hpn,hf l hl,hf r hr,zero_add,add_zero]
    exact ih hm (by omega)

lemma layered_bounded (b : A.Index) (d : ℕ) (hb : A.dim b ≤ d)
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    {n : ℕ} (hn : n ≤ d) {x : C.Cell}
    (hx : C.LayeredWhisker (fun z => F.map z = A.atom b) n x) : C.source d x = x := by
  apply hx.row_bounded d (fun z hz => ?_) hn
  apply hreflect d z
  rw [hz]
  exact K.nu.source_fixed_upwards hb (A.bounded b)

lemma lower_single_ordered (n : ℕ)
    (hsmall : ∀ k, k ≤ n+1 → Function.Bijective (F.onCells k))
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    (b : A.Index) (hb : A.dim b = n+1) (x : C.Cell)
    (hx : C.source (n+1) x = x)
    (ht : (F.map x).row (n+1) false = A.basis (n+1) b) :
    A.OrderedWhisker F b n x := by
  have hf : truncate (n+1) false (F.map x) = F.map x :=
    (F.map_source (n+1) x).symm.trans (congrArg F.map hx)
  have hta : (F.map x).row (n+1) false = (A.atom b).row (n+1) false := by
    rw [ht,← hb,A.basis_own]
  have hay : A.OrderedWhisker (OmegaCategory.Functor.id K.nu) b n (F.map x) :=
    A.table_ordered_whisker b n (by omega) _
      (fun p hp e => NormalizedChains.rows_above_top_agree _ _ hf (hb ▸ A.bounded b) hta p (by omega) e)
  obtain ⟨a,ha⟩ := (hsmall (n+1) le_rfl).2 ⟨A.atom b,hb ▸ A.bounded b⟩
  obtain ⟨y,hy,he⟩ := OrderedWhisker.lift (A := A) (F := F) b n
    ⟨a.val,congrArg Subtype.val ha⟩ (fun k hk => hsmall k (by omega)) _ hay
  have hyb : C.source (n+1) y = y := hreflect (n+1) y (by rw [he]; exact hf)
  have hyx := F.bounded_ext (n+1) (hsmall (n+1) le_rfl).1 y x hyb hx he
  simpa only [hyx] using hy

theorem ordered_exchange (n : ℕ)
    (hsmall : ∀ k, k ≤ n → Function.Bijective (F.onCells k))
    (b c : A.Index) (hb : n < A.dim b) (hc : n < A.dim c)
    (hbc : A.rank b ≤ A.rank c) (x y : C.Cell)
    (hx : A.OrderedWhisker F b n x) (hy : A.OrderedWhisker F c n y)
    (h : C.target n x = C.source n y) :
    ∃ y' x' : C.Cell,
      C.LayeredWhisker (fun z => F.map z = A.atom c) n y' ∧
      C.LayeredWhisker (fun z => F.map z = A.atom b) n x' ∧
      C.target n y' = C.source n x' ∧ C.join n x y = C.join n y' x' := by
  cases n with
  | zero =>
    have he : truncate 0 true (A.atom b) = truncate 0 false (A.atom c) := by
      change F.map x = A.atom b at hx
      change F.map y = A.atom c at hy
      have hh := congrArg F.map h
      rw [F.map_target,F.map_source,hx,hy] at hh
      exact hh
    have hr : (A.atom b).row 0 true = (A.atom c).row 0 false := by
      have hh := congrArg (fun t : Table K => t.row 0 false) he
      simpa using hh
    have hm : A.mass 0 ((A.atom c).row 0 false) = 1 := by
      rw [← A.augmentation_eq_mass,(A.atom c).augmentation]
    obtain ⟨t,ht⟩ : ∃ t, A.coefficient t 0 ((A.atom c).row 0 false) ≠ 0 := by
      by_contra hn
      push Not at hn
      have hz : (A.atom c).row 0 false = 0 := A.ext 0 _ 0 (by simpa using hn)
      rw [hz,map_zero] at hm
      omega
    have ht' : A.coefficient t 0 ((A.atom b).row 0 true) ≠ 0 := by rwa [hr]
    have h₁ := A.ranked b 0 hb true t ht'
    have h₂ := A.ranked c 0 hc false t ht
    simp only [ite_true,Bool.false_eq_true,ite_false] at h₁ h₂
    omega
  | succ n =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,hlo,hro,rfl⟩ := hx
    obtain ⟨a,z,d,ha,hd,hz,haz,hzd,hao,hdo,rfl⟩ := hy
    obtain ⟨dH,dL,hdH,hdL,hdHL,hdHo,hdLo,heD⟩ :=
      A.rank_split F n (A.rank b) (hsmall n (by omega)).1 (hsmall (n+1) le_rfl) d hd
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]; exact hmr
    have hazd : C.target n (C.join n a z) = C.source n d := by
      rw [C.join_target_le n n a z le_rfl haz]; exact hzd
    have hzH : C.target n z = C.source n dH := by
      rw [heD,C.join_source_le n n dH dL le_rfl hdHL] at hzd; exact hzd
    have hazH : C.target n (C.join n a z) = C.source n dH := by
      rw [C.join_target_le n n a z le_rfl haz]; exact hzH
    let X := C.join n m r
    let Y := C.join n (C.join n a z) dH
    have hlX : C.target n l = C.source n X := by
      dsimp [X]; rw [C.join_source_le n n m r le_rfl hmr]; exact hlm
    have hYL : C.target n Y = C.source n dL := by
      dsimp [Y]; rw [C.join_target_le n n _ dH le_rfl hazH]; exact hdHL
    have hxform : C.join n (C.join n l m) r = C.join n l X :=
      C.join_assoc n l m r hlm hmr
    have hyform : C.join n (C.join n a z) d = C.join n Y dL := by
      rw [heD]
      exact (C.join_assoc n (C.join n a z) dH dL hazH hdHL).symm
    rw [hxform,hyform,C.join_target_gt (n+1) n l X (Nat.lt_succ_self n) hlX,
      C.join_source_gt (n+1) n Y dL (Nat.lt_succ_self n) hYL,
      C.target_eq_self_of_source_eq_self hl,hdL] at h
    have hlTX : C.target n l = C.source n (C.target (n+1) X) := by
      rw [C.source_target,ite_eq_left (Nat.lt_succ_self n)]; exact hlX
    have hSYL : C.target n (C.source (n+1) Y) = C.source n dL := by
      rw [C.target_source,ite_eq_left (Nat.lt_succ_self n)]; exact hYL
    have hf (t : C.Cell) (ht : C.source (n+1) t = t) :
        (F.map t).row (n+1) true = (F.map t).row (n+1) false :=
      (row_top_fixed (F.map t) ((F.map_source (n+1) t).symm.trans (congrArg F.map ht))).symm
    have hTX : ∀ t, A.coefficient t (n+1) ((F.map (C.target (n+1) X)).row (n+1) false) ≠ 0 →
        ¬ A.rank b < A.rank t := by
      rw [F.map_target]
      change ∀ t, A.coefficient t (n+1) ((truncate (n+1) true (F.map X)).row (n+1) false) ≠ 0 → _
      erw [truncate_row]
      simp only [lt_self_iff_false,ite_false,ite_true]
      dsimp [X]
      rw [F.map_join n m r hmr,K.nu.join_eq n _ _ (F.map_composable hmr)]
      change ∀ t, A.coefficient t (n+1) ((comp n (F.map m) (F.map r) (F.map_composable hmr)).row (n+1) true) ≠ 0 → _
      erw [comp_row]
      simp only [show ¬n+1 < n by omega,show n+1 ≠ n by omega,ite_false]
      rw [hm.row_above (n+1) (Nat.lt_succ_self n) true,hf r hr]
      apply A.support_add (n+1) _ _ _ ?_ hro
      intro t ht
      have hh := A.ranked b (n+1) hb true t ht
      simp only [ite_true] at hh
      omega
    have hSY : ∀ t, A.coefficient t (n+1) ((F.map (C.source (n+1) Y)).row (n+1) false) ≠ 0 →
        A.rank b < A.rank t := by
      rw [F.map_source]
      change ∀ t, A.coefficient t (n+1) ((truncate (n+1) false (F.map Y)).row (n+1) false) ≠ 0 → _
      erw [truncate_row]
      simp only [lt_self_iff_false,ite_false,ite_true]
      dsimp [Y]
      rw [top_row_join F (n+1) n (Nat.lt_succ_self n) _ dH hazH,
        top_row_join F (n+1) n (Nat.lt_succ_self n) a z haz,
        hz.row_above (n+1) (Nat.lt_succ_self n) false]
      apply A.support_add (n+1) _ _ _ (A.support_add (n+1) _ _ _ ?_ ?_) hdHo
      · intro t ht; exact hbc.trans_lt (hao t ht)
      · intro t ht
        have hh := A.ranked c (n+1) hc false t ht
        simp only [Bool.false_eq_true,ite_false] at hh
        exact hbc.trans_lt hh
    obtain ⟨hlY,hXL⟩ := A.rank_split_unique F n (A.rank b) (hsmall (n+1) le_rfl).1
      l (C.target (n+1) X) (C.source (n+1) Y) dL hl (C.source_target_self (n+1) X)
      (C.source_source_self (n+1) Y) hdL hlTX hSYL hlo hTX hSY hdLo h
    have hYX : C.target n Y = C.source n X := by
      rw [hlY,C.target_source,ite_eq_left (Nat.lt_succ_self n)] at hlX; exact hlX
    have hYS : C.target n Y = C.source n (C.source (n+1) X) := by
      rw [C.source_source,min_eq_left (Nat.le_succ n)]; exact hYX
    have hTYX : C.target n (C.target (n+1) Y) = C.source n X := by
      rw [C.target_target,min_eq_left (Nat.le_succ n)]; exact hYX
    have hTYm : C.target n (C.target (n+1) Y) = C.source n m := by
      rw [C.join_source_le n n m r le_rfl hmr] at hTYX; exact hTYX
    have hHS : C.target n dH = C.source n (C.source (n+1) X) := by
      dsimp [Y] at hYS
      rw [C.join_target_le n n _ dH le_rfl hazH] at hYS; exact hYS
    let y' := C.join n Y (C.source (n+1) X)
    let x' := C.join n (C.target (n+1) Y) X
    have hy' : C.LayeredWhisker (fun t => F.map t = A.atom c) (n+1) y' := by
      refine ⟨a,z,C.join n dH (C.source (n+1) X),ha,?_,hz.layered,haz,?_,?_⟩
      · rw [C.join_source_gt (n+1) n _ _ (Nat.lt_succ_self n) hHS,hdH,C.source_source_self]
      · rw [C.join_source_le n n _ _ le_rfl hHS]; exact hzH
      · exact C.join_assoc n (C.join n a z) dH (C.source (n+1) X) hazH hHS
    have hx' : C.LayeredWhisker (fun t => F.map t = A.atom b) (n+1) x' := by
      refine ⟨C.target (n+1) Y,m,r,C.source_target_self (n+1) Y,hr,hm.layered,hTYm,hmr,?_⟩
      exact (C.join_assoc n (C.target (n+1) Y) m r hTYm hmr).symm
    have hyx' : C.target (n+1) y' = C.source (n+1) x' := by
      dsimp [y',x']
      rw [C.join_target_gt (n+1) n _ _ (Nat.lt_succ_self n) hYS,
        C.join_source_gt (n+1) n _ _ (Nat.lt_succ_self n) hTYX,
        C.source_target_self,C.target_source_self]
    have he₁ := C.join_interchange n (n+1) (Nat.lt_succ_self n)
      (C.source (n+1) Y) Y X (C.target (n+1) X)
      (C.target_source_self (n+1) Y) (C.source_target_self (n+1) X).symm
      (by rw [C.target_source,ite_eq_left (Nat.lt_succ_self n)]; exact hYX)
      (by rw [C.source_target,ite_eq_left (Nat.lt_succ_self n)]; exact hYX)
    rw [C.join_left_unit (n+1) _ Y (C.source_source_self (n+1) Y)
      (C.target_source_self (n+1) Y),C.join_right_unit (n+1) X _
      (C.source_target_self (n+1) X) (C.source_target_self (n+1) X).symm] at he₁
    have he₂ := C.join_interchange n (n+1) (Nat.lt_succ_self n)
      Y (C.target (n+1) Y) (C.source (n+1) X) X
      (C.source_target_self (n+1) Y).symm (C.target_source_self (n+1) X) hYS hTYX
    rw [C.join_right_unit (n+1) Y _ (C.source_target_self (n+1) Y)
      (C.source_target_self (n+1) Y).symm,C.join_left_unit (n+1) _ X
      (C.source_source_self (n+1) X) (C.target_source_self (n+1) X)] at he₂
    refine ⟨y',x',hy',hx',hyx',?_⟩
    rw [hxform,hyform,hlY,← hXL]
    exact he₁.symm.trans he₂
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

namespace AtomPath
variable {A F} {n : ℕ}

lemma index_support {bs : List A.Index} {a : C.Cell} (ha : A.AtomPath F n bs a)
    (P : A.Index → Prop)
    (hs : ∀ c, A.coefficient c (n+1) ((F.map a).row (n+1) false) ≠ 0 → P c) :
    ∀ c ∈ bs, P c := by
  classical
  intro c hc
  apply hs c
  rw [ha.coefficient c]
  exact_mod_cast (ne_of_gt (List.count_pos_iff.mpr hc))

lemma move_low (n : ℕ)
    (hsmall : ∀ k, k ≤ n+1 → Function.Bijective (F.onCells k))
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    (b : A.Index) (hb : n < A.dim b)
    (hnorm : ∀ z, C.LayeredWhisker (fun t => F.map t = A.atom b) n z → A.OrderedWhisker F b n z)
    {bs : List A.Index} {a : C.Cell} (ha : A.AtomPath F n bs a)
    (hs : ∀ c ∈ bs, A.rank c ≤ A.rank b) (x : C.Cell)
    (hx : A.OrderedWhisker F b n x) (h : C.target n a = C.source n x) :
    ∃ y a' : C.Cell, A.OrderedWhisker F b n y ∧ C.source (n+1) a' = a' ∧
      (F.map a').row (n+1) false = (F.map a).row (n+1) false ∧
      C.target n y = C.source n a' ∧ C.join n a x = C.join n y a' := by
  induction ha generalizing x with
  | nil a ha =>
    refine ⟨x,C.target n x,hx,C.source_fixed_upwards (Nat.le_succ n) (C.source_target_self n x),?_,
      (C.source_target_self n x).symm,?_⟩
    · rw [top_row_lower F n a ha,top_row_lower F n _ (C.source_target_self n x)]
    · rw [C.join_left_unit n a x ha h,C.join_right_unit n x _ (C.source_target_self n x)
        (C.source_target_self n x).symm]
  | cons c hc z a bs hz ht hza ha ih =>
    have hax : C.target n a = C.source n x := by
      rw [C.join_target_le n n z a le_rfl hza] at h; exact h
    obtain ⟨y,a',hy,ha',hat,hya',he⟩ := ih (fun t ht => hs t (List.mem_cons_of_mem c ht)) x hx hax
    have hzy : C.target n z = C.source n y := by
      have hh := congrArg (C.source n) he
      rw [C.join_source_le n n a x le_rfl hax,C.join_source_le n n y a' le_rfl hya'] at hh
      exact hza.trans hh
    have hzo := A.lower_single_ordered F n hsmall hreflect c hc z hz.bounded ht
    obtain ⟨y',z',hy',hz',hyz',hez⟩ := A.ordered_exchange F n
      (fun k hk => hsmall k (by omega)) c b (by omega) hb (hs c (List.mem_cons_self)) z y hzo hy hzy
    have hz'b := A.layered_bounded F c (n+1) hc.le hreflect (Nat.le_succ n) hz'
    have hz't : (F.map z').row (n+1) false = (F.map z).row (n+1) false := by
      rw [A.layered_row_above F c hz' (n+1) (Nat.lt_succ_self n) false,ht,← hc,A.basis_own]
    have hz'a' : C.target n z' = C.source n a' := by
      have hh := congrArg (C.target n) hez
      rw [C.join_target_le n n z y le_rfl hzy,C.join_target_le n n y' z' le_rfl hyz'] at hh
      exact hh.symm.trans hya'
    have hym : C.target n y' = C.source n (C.join n z' a') := by
      rw [C.join_source_le n n z' a' le_rfl hz'a']; exact hyz'
    refine ⟨y',C.join n z' a',hnorm y' hy',?_,?_,hym,?_⟩
    · rw [C.join_source_gt (n+1) n z' a' (Nat.lt_succ_self n) hz'a',hz'b,ha']
    · rw [top_row_join F (n+1) n (Nat.lt_succ_self n) z' a' hz'a',
        top_row_join F (n+1) n (Nat.lt_succ_self n) z a hza,hz't,hat]
    · rw [C.join_assoc n z a x hza hax,he,← C.join_assoc n z y a' hzy hya',hez,
        C.join_assoc n y' z' a' hyz' hz'a']

lemma move_high (n : ℕ)
    (hsmall : ∀ k, k ≤ n+1 → Function.Bijective (F.onCells k))
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    (b : A.Index) (hb : n < A.dim b)
    (hnorm : ∀ z, C.LayeredWhisker (fun t => F.map t = A.atom b) n z → A.OrderedWhisker F b n z)
    {bs : List A.Index} {a : C.Cell} (ha : A.AtomPath F n bs a)
    (hs : ∀ c ∈ bs, A.rank b < A.rank c) (x : C.Cell)
    (hx : A.OrderedWhisker F b n x) (h : C.target n x = C.source n a) :
    ∃ a' y : C.Cell, C.source (n+1) a' = a' ∧ A.OrderedWhisker F b n y ∧
      (F.map a').row (n+1) false = (F.map a).row (n+1) false ∧
      C.target n a' = C.source n y ∧ C.join n x a = C.join n a' y := by
  induction ha generalizing x with
  | nil a ha =>
    refine ⟨C.source n x,x,C.source_fixed_upwards (Nat.le_succ n) (C.source_source_self n x),hx,?_,
      C.target_source_self n x,?_⟩
    · rw [top_row_lower F n a ha,top_row_lower F n _ (C.source_source_self n x)]
    · rw [C.join_right_unit n x a ha h,C.join_left_unit n _ x (C.source_source_self n x)
        (C.target_source_self n x)]
  | cons c hc z a bs hz ht hza ha ih =>
    have hxz : C.target n x = C.source n z := by
      rw [C.join_source_le n n z a le_rfl hza] at h; exact h
    have hzo := A.lower_single_ordered F n hsmall hreflect c hc z hz.bounded ht
    obtain ⟨z',x',hz',hx',hzx',hez⟩ := A.ordered_exchange F n
      (fun k hk => hsmall k (by omega)) b c hb (by omega) (hs c (List.mem_cons_self)).le x z hx hzo hxz
    have hz'b := A.layered_bounded F c (n+1) hc.le hreflect (Nat.le_succ n) hz'
    have hz't : (F.map z').row (n+1) false = (F.map z).row (n+1) false := by
      rw [A.layered_row_above F c hz' (n+1) (Nat.lt_succ_self n) false,ht,← hc,A.basis_own]
    have hx'a : C.target n x' = C.source n a := by
      have hh := congrArg (C.target n) hez
      rw [C.join_target_le n n x z le_rfl hxz,C.join_target_le n n z' x' le_rfl hzx'] at hh
      exact hh.symm.trans hza
    obtain ⟨a',y,ha',hy,hat,ha'y,he⟩ := ih (fun t ht => hs t (List.mem_cons_of_mem c ht)) x'
      (hnorm x' hx') hx'a
    have hz'a' : C.target n z' = C.source n a' := by
      have hh := congrArg (C.source n) he
      rw [C.join_source_le n n x' a le_rfl hx'a,C.join_source_le n n a' y le_rfl ha'y] at hh
      exact hzx'.trans hh
    have hmy : C.target n (C.join n z' a') = C.source n y := by
      rw [C.join_target_le n n z' a' le_rfl hz'a']; exact ha'y
    refine ⟨C.join n z' a',y,?_,hy,?_,hmy,?_⟩
    · rw [C.join_source_gt (n+1) n z' a' (Nat.lt_succ_self n) hz'a',hz'b,ha']
    · rw [top_row_join F (n+1) n (Nat.lt_succ_self n) z' a' hz'a',
        top_row_join F (n+1) n (Nat.lt_succ_self n) z a hza,hz't,hat]
    · rw [← C.join_assoc n x z a hxz hza,hez,C.join_assoc n z' x' a hzx' hx'a,he,
        ← C.join_assoc n z' a' y hz'a' ha'y]

end AtomPath
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

theorem layered_ordered (n : ℕ)
    (hsmall : ∀ k, k ≤ n → Function.Bijective (F.onCells k))
    (hgen : ∀ k, k < n → ∀ a : C.Cell, C.source (k+1) a = a →
      C.TopSequence k (A.TopGenerator F k) a)
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    (b : A.Index) (hb : n < A.dim b) (x : C.Cell)
    (hx : C.LayeredWhisker (fun t => F.map t = A.atom b) n x) :
    A.OrderedWhisker F b n x := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih =>
    have hnorm : ∀ z, C.LayeredWhisker (fun t => F.map t = A.atom b) n z →
        A.OrderedWhisker F b n z :=
      fun z hz => ih (fun k hk => hsmall k (by omega))
        (fun k hk => hgen k (by omega)) (by omega) z hz
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,rfl⟩ := hx
    obtain ⟨lH,lL,hlH,hlL,hlHL,hlHo,hlLo,heL⟩ :=
      A.rank_split F n (A.rank b) (hsmall n (by omega)).1 (hsmall (n+1) le_rfl) l hl
    have hLm : C.target n lL = C.source n m := by
      rw [heL,C.join_target_le n n lH lL le_rfl hlHL] at hlm; exact hlm
    obtain ⟨bs,hbs⟩ := A.topSequence_path F (hgen n (Nat.lt_succ_self n) lL hlL)
    have hbslo : ∀ c ∈ bs, A.rank c ≤ A.rank b :=
      hbs.index_support _ (fun c hc => le_of_not_gt (hlLo c hc))
    obtain ⟨m₁,aLow,hm₁,haLow,hatLow,hm₁a,heLow⟩ :=
      hbs.move_low n hsmall hreflect b (by omega) hnorm hbslo m (hnorm m hm) hLm
    have hHm₁ : C.target n lH = C.source n m₁ := by
      have hh := congrArg (C.source n) heLow
      rw [C.join_source_le n n lL m le_rfl hLm,
        C.join_source_le n n m₁ aLow le_rfl hm₁a] at hh
      exact hlHL.trans hh
    have haLowr : C.target n aLow = C.source n r := by
      have hh := congrArg (C.target n) heLow
      rw [C.join_target_le n n lL m le_rfl hLm,
        C.join_target_le n n m₁ aLow le_rfl hm₁a] at hh
      exact hh.symm.trans hmr
    have har : C.source (n+1) (C.join n aLow r) = C.join n aLow r := by
      rw [C.join_source_gt (n+1) n aLow r (Nat.lt_succ_self n) haLowr,haLow,hr]
    obtain ⟨rH,rL,hrH,hrL,hrHL,hrHo,hrLo,heR⟩ :=
      A.rank_split F n (A.rank b) (hsmall n (by omega)).1 (hsmall (n+1) le_rfl) _ har
    have hm₁H : C.target n m₁ = C.source n rH := by
      have hh := congrArg (C.source n) heR
      rw [C.join_source_le n n aLow r le_rfl haLowr,
        C.join_source_le n n rH rL le_rfl hrHL] at hh
      exact hm₁a.trans hh
    obtain ⟨cs,hcs⟩ := A.topSequence_path F (hgen n (Nat.lt_succ_self n) rH hrH)
    have hcshi : ∀ c ∈ cs, A.rank b < A.rank c := hcs.index_support _ hrHo
    obtain ⟨aHigh,m₂,haHigh,hm₂,hatHigh,ham₂,heHigh⟩ :=
      hcs.move_high n hsmall hreflect b (by omega) hnorm hcshi m₁ hm₁ hm₁H
    have hHaHigh : C.target n lH = C.source n aHigh := by
      have hh := congrArg (C.source n) heHigh
      rw [C.join_source_le n n m₁ rH le_rfl hm₁H,
        C.join_source_le n n aHigh m₂ le_rfl ham₂] at hh
      exact hHm₁.trans hh
    have hm₂L : C.target n m₂ = C.source n rL := by
      have hh := congrArg (C.target n) heHigh
      rw [C.join_target_le n n m₁ rH le_rfl hm₁H,
        C.join_target_le n n aHigh m₂ le_rfl ham₂] at hh
      exact hh.symm.trans hrHL
    refine ⟨C.join n lH aHigh,m₂,rL,?_,hrL,hm₂,?_,hm₂L,?_,hrLo,?_⟩
    · rw [C.join_source_gt (n+1) n lH aHigh (Nat.lt_succ_self n) hHaHigh,hlH,haHigh]
    · rw [C.join_target_le n n lH aHigh le_rfl hHaHigh]; exact ham₂
    · rw [top_row_join F (n+1) n (Nat.lt_succ_self n) lH aHigh hHaHigh,hatHigh]
      exact A.support_add (n+1) _ _ _ hlHo hrHo
    · have hHma : C.target n (C.join n lH m₁) = C.source n aLow := by
        rw [C.join_target_le n n lH m₁ le_rfl hHm₁]; exact hm₁a
      have hHmH : C.target n (C.join n lH m₁) = C.source n rH := by
        rw [C.join_target_le n n lH m₁ le_rfl hHm₁]; exact hm₁H
      rw [heL,C.join_assoc n lH lL m hlHL hLm,heLow,
        ← C.join_assoc n lH m₁ aLow hHm₁ hm₁a,
        C.join_assoc n (C.join n lH m₁) aLow r hHma haLowr,heR,
        ← C.join_assoc n (C.join n lH m₁) rH rL hHmH hrHL,
        C.join_assoc n lH m₁ rH hHm₁ hm₁H,heHigh,
        ← C.join_assoc n lH aHigh m₂ hHaHigh ham₂]
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory
variable {C : OmegaCategory.{u}}
lemma Whisker.mono {n : ℕ} {G H : C.Cell → Prop} {x : C.Cell}
    (hx : C.Whisker n G x) (h : ∀ z, G z → H z) : C.Whisker n H x := by
  induction hx with
  | generator z hz hd => exact .generator z (h z hz) hd
  | left k hk a z ha hm hz ih => exact .left k hk a z ha hm ih
  | right k hk z a ha hm hz ih => exact .right k hk z a ha hm ih
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

lemma basis_injective_on_dim (p : ℕ) (b c : A.Index)
    (hb : A.dim b = p) (hc : A.dim c = p) (he : A.basis p b = A.basis p c) : b = c := by
  classical
  by_contra hne
  have hh := congrArg (A.coefficient b p) he
  simp [A.coefficient_basis,hb,hc,Ne.symm hne] at hh

lemma whisker_atom_layered {n : ℕ} {x : C.Cell}
    (hx : C.Whisker n (A.TopGenerator F n) x) :
    ∃ b, A.dim b = n+1 ∧ C.LayeredWhisker (fun z => F.map z = A.atom b) n x := by
  induction hx with
  | generator x hx hd =>
    obtain ⟨b,hb,he⟩ := hx
    exact ⟨b,hb,LayeredWhisker.of_generator he n⟩
  | left k hk a x ha hm hx ih =>
    obtain ⟨b,hb,hh⟩ := ih
    exact ⟨b,hb,hh.left k hk a ha hm⟩
  | right k hk x a ha hm hx ih =>
    obtain ⟨b,hb,hh⟩ := ih
    exact ⟨b,hb,hh.right k hk a ha hm⟩

lemma whisker_layered_of_top (n : ℕ) (b : A.Index) (hb : A.dim b = n+1)
    (x : C.Cell) (hx : C.Whisker n (A.TopGenerator F n) x)
    (ht : (F.map x).row (n+1) false = A.basis (n+1) b) :
    C.LayeredWhisker (fun z => F.map z = A.atom b) n x := by
  obtain ⟨c,hc,hh⟩ := A.whisker_atom_layered F hx
  have htop : (F.map x).row (n+1) false = A.basis (n+1) c := by
    rw [A.layered_row_above F c hh (n+1) (Nat.lt_succ_self n) false,← hc,A.basis_own]
  have he := A.basis_injective_on_dim (n+1) c b hc hb (htop.symm.trans ht)
  simpa only [he] using hh

theorem whiskerFaithful (n : ℕ)
    (hsmall : ∀ k, k ≤ n → Function.Bijective (F.onCells k))
    (hgen : ∀ k, k < n → ∀ a : C.Cell, C.source (k+1) a = a →
      C.TopSequence k (A.TopGenerator F k) a)
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    (hatom : ∀ b (x y : C.Cell), F.map x = A.atom b → F.map y = A.atom b → x = y) :
    A.WhiskerFaithful F n := by
  intro x y hx hy he
  obtain ⟨b,hb,ht⟩ := A.whisker_top_basis F hx
  have hty : (F.map y).row (n+1) false = A.basis (n+1) b := by rw [← he]; exact ht
  have hx' := A.layered_ordered F n hsmall hgen hreflect b (by omega) x
    (A.whisker_layered_of_top F n b hb x hx ht)
  have hy' := A.layered_ordered F n hsmall hgen hreflect b (by omega) y
    (A.whisker_layered_of_top F n b hb y hy hty)
  exact OrderedWhisker.eq_of_map_eq b n (hatom b) (fun k hk => (hsmall k hk).1) x y hx' hy' he

theorem hasAdjacentExchange (n : ℕ)
    (hsmall : ∀ k, k ≤ n → Function.Bijective (F.onCells k))
    (hgen : ∀ k, k < n → ∀ a : C.Cell, C.source (k+1) a = a →
      C.TopSequence k (A.TopGenerator F k) a)
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x) :
    A.HasAdjacentExchange F n := by
  intro b c hb hc hbc x y hx hy ht hs hm
  have hx' := A.layered_ordered F n hsmall hgen hreflect b (by omega) x
    (A.whisker_layered_of_top F n b hb x hx ht)
  have hy' := A.layered_ordered F n hsmall hgen hreflect c (by omega) y
    (A.whisker_layered_of_top F n c hc y hy hs)
  obtain ⟨y',x',hy',hx',hm',he⟩ := A.ordered_exchange F n hsmall b c (by omega) (by omega)
    (A.rank_le_of_orderRank_le hbc.le) x y hx' hy' hm
  have hw (d : A.Index) (hd : A.dim d = n+1) (z : C.Cell)
      (hz : C.LayeredWhisker (fun t => F.map t = A.atom d) n z) :
      C.Whisker n (A.TopGenerator F n) z := by
    exact (hz.whisker n (fun t ht => hreflect (n+1) t (by rw [ht,← hd]; exact A.bounded d))
      le_rfl).mono (fun t ht => ⟨d,hd,ht⟩)
  refine ⟨y',x',hw c hc y' hy',hw b hb x' hx',?_,?_,hm',he⟩
  · rw [A.layered_row_above F c hy' (n+1) (Nat.lt_succ_self n) false,← hc,A.basis_own]
  · rw [A.layered_row_above F b hx' (n+1) (Nat.lt_succ_self n) false,← hb,A.basis_own]

theorem onCells_injective_step (n : ℕ)
    (hsmall : ∀ k, k ≤ n → Function.Bijective (F.onCells k))
    (hgen : ∀ k, k ≤ n → ∀ a : C.Cell, C.source (k+1) a = a →
      C.TopSequence k (A.TopGenerator F k) a)
    (hreflect : ∀ k x, truncate k false (F.map x) = F.map x → C.source k x = x)
    (hatom : ∀ b (x y : C.Cell), F.map x = A.atom b → F.map y = A.atom b → x = y) :
    Function.Injective (F.onCells (n+1)) :=
  A.onCells_injective_of_exchange F n (hsmall n le_rfl).1 (hgen n le_rfl)
    (A.whiskerFaithful F n hsmall (fun k hk => hgen k hk.le) hreflect hatom)
    (A.hasAdjacentExchange F n hsmall (fun k hk => hgen k hk.le) hreflect)
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory NormalizedChains

theorem chainComparison_finiteSimplex_onCells_bijective
    {N : ℕ} {P : Type u} [LinearOrder P] (e : Fin (N+1) ≃o P) (n : ℕ) :
    Function.Bijective ((chainComparison (NormalizedChains.complex P)).onCells n) := by
  let := Fintype.ofEquiv (Fin (N+1)) e.toEquiv
  induction n using Nat.strong_induction_on with
  | h n ih =>
    refine ⟨?_,chainComparison_finiteSimplex_surjective_of_lower_injective P n
      (fun k hk => (ih k hk).1)⟩
    cases n with
    | zero =>
      exact (chainComparison (NormalizedChains.complex P)).onCells_injective_mono (by omega : 0 ≤ 2)
        (chainComparison_poset_twocells_bijective P).1
    | succ n =>
      exact (Prism.Basis.ofOrderIso e).onCells_injective_step
        (chainComparison (NormalizedChains.complex P)) n (fun k hk => ih k (by omega))
        (fun k _ => tensor_top_sequence e k)
        (chainComparison_reflects_dimension (Prism.Basis.ofOrderIso e))
        (chainComparison_atom_fiber_subsingleton (Prism.Basis.ofOrderIso e))

theorem standardSimplexComparison_isIso (m : ℕ) :
    IsIso (chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3))))) := by
  apply chainComparison_finiteSimplex_isIso_of_injective
  apply (chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3))))).map_injective_of_onCells_injective
    (n := m+3)
    (tensor_truncated (NormalizedChains.table_truncated_of_card_le (n := m+2) (by simp)))
  exact (chainComparison_finiteSimplex_onCells_bijective
    (N := m+2) (finLiftOrderIso (m+3)) (m+3)).1
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason

theorem main : FullMain.{u} :=
  GrayRecursive.IntervalHom.fullMain_of_standardSimplexComparison_isIso
    GrayRecursive.IntervalHom.standardSimplexComparison_isIso
end Thomason

end

end OAI
