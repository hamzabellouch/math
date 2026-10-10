import Mathlib
import OAI.CategoryTheory.Thomason.TopSequences

namespace OAI

/-! Layered Whiskers. -/

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

variable (C : OmegaCategory.{u})

lemma join_distribute_left (k n : ℕ) (hk : k < n) (a l r : C.Cell)
    (hlr : C.target n l = C.source n r)
    (hal : C.target k a = C.source k l) :
    C.join k a (C.join n l r) =
      C.join n (C.join k a l) (C.join k (C.target n a) r) := by
  have htr : C.target k (C.target n a) = C.source k r := by
    have hh := congrArg (C.source k) hlr
    simp only [C.source_target, ite_eq_left hk, C.source_source, min_eq_left hk.le] at hh
    rw [C.target_target, min_eq_left hk.le]
    exact hal.trans hh
  have he := C.join_interchange k n hk a (C.target n a) l r
    (C.source_target_self n a).symm hlr hal htr
  rw [C.join_right_unit n a (C.target n a) (C.source_target_self n a)
    (C.source_target_self n a).symm] at he
  exact he

lemma join_distribute_right (k n : ℕ) (hk : k < n) (l r a : C.Cell)
    (hlr : C.target n l = C.source n r)
    (hra : C.target k r = C.source k a) :
    C.join k (C.join n l r) a =
      C.join n (C.join k l (C.source n a)) (C.join k r a) := by
  have hls : C.target k l = C.source k (C.source n a) := by
    have hh := congrArg (C.target k) hlr
    simp only [C.target_target, min_eq_left hk.le, C.target_source, ite_eq_left hk] at hh
    rw [C.source_source, min_eq_left hk.le]
    exact hh.trans hra
  have he := C.join_interchange k n hk l r (C.source n a) a
    hlr (C.target_source_self n a) hls hra
  rw [C.join_left_unit n (C.source n a) a (C.source_source_self n a)
    (C.target_source_self n a)] at he
  exact he

def LayeredWhisker (G : C.Cell → Prop) : ℕ → C.Cell → Prop
  | 0, x => G x
  | n+1, x => ∃ l m r : C.Cell,
      C.source (n+1) l = l ∧ C.source (n+1) r = r ∧
      LayeredWhisker G n m ∧ C.target n l = C.source n m ∧
      C.target n m = C.source n r ∧ x = C.join n (C.join n l m) r

variable {C}
namespace LayeredWhisker
variable {G : C.Cell → Prop}

lemma of_generator {b : C.Cell} (hb : G b) (n : ℕ) : C.LayeredWhisker G n b := by
  induction n with
  | zero => exact hb
  | succ n ih =>
    refine ⟨C.source n b,b,C.target n b,
      C.source_fixed_upwards (Nat.le_succ n) (C.source_source_self n b),
      C.source_fixed_upwards (Nat.le_succ n) (C.source_target_self n b),ih,
      C.target_source_self n b,(C.source_target_self n b).symm,?_⟩
    rw [C.join_left_unit n (C.source n b) b (C.source_source_self n b)
      (C.target_source_self n b), C.join_right_unit n b (C.target n b)
      (C.source_target_self n b) (C.source_target_self n b).symm]

lemma left {n : ℕ} {x : C.Cell} (hx : C.LayeredWhisker G n x)
    (k : ℕ) (hk : k < n) (a : C.Cell) (ha : C.source n a = a)
    (h : C.target k a = C.source k x) : C.LayeredWhisker G n (C.join k a x) := by
  induction n generalizing x k a with
  | zero => omega
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,rfl⟩ := hx
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]
      exact hmr
    by_cases hkn : k = n
    · subst k
      have hal : C.target n a = C.source n l := by
        rw [C.join_source_le n n _ r le_rfl hlmr,
          C.join_source_le n n l m le_rfl hlm] at h
        exact h
      refine ⟨C.join n a l,m,r,?_,hr,hm,?_,hmr,?_⟩
      · rw [C.join_source_gt (n+1) n a l (Nat.lt_succ_self n) hal,ha,hl]
      · rw [C.join_target_le n n a l le_rfl hal]
        exact hlm
      · rw [C.join_assoc n (C.join n a l) m r
          (by rw [C.join_target_le n n a l le_rfl hal]; exact hlm) hmr,
          C.join_assoc n a l (C.join n m r) hal
          (by rw [C.join_source_le n n m r le_rfl hmr]; exact hlm),
          C.join_assoc n l m r hlm hmr]
    · have hkn : k < n := by omega
      have hal : C.target k a = C.source k l := by
        rw [C.join_source_le k n _ r hkn.le hlmr,
          C.join_source_le k n l m hkn.le hlm] at h
        exact h
      have hm' : C.source k l = C.source k m := by
        have hh := congrArg (C.source k) hlm
        simpa only [C.source_target,ite_eq_left hkn,C.source_source,min_eq_left hkn.le] using hh
      have hr' : C.source k m = C.source k r := by
        have hh := congrArg (C.source k) hmr
        simpa only [C.source_target,ite_eq_left hkn,C.source_source,min_eq_left hkn.le] using hh
      have htm : C.target k (C.target n a) = C.source k m := by
        rw [C.target_target,min_eq_left hkn.le]
        exact hal.trans hm'
      have htr : C.target k (C.target n a) = C.source k r := htm.trans hr'
      have hai : C.target k a = C.source k (C.join n l m) := by
        rw [C.join_source_le k n l m hkn.le hlm]
        exact hal
      refine ⟨C.join k a l, C.join k (C.target n a) m,
        C.join k (C.target n a) r,?_,?_,
        ih hm k hkn (C.target n a) (C.source_target_self n a) htm,?_,?_,?_⟩
      · rw [C.join_source_gt (n+1) k a l (by omega) hal,ha,hl]
      · rw [C.join_source_gt (n+1) k (C.target n a) r (by omega) htr,
          C.source_fixed_upwards (Nat.le_succ n) (C.source_target_self n a),hr]
      · rw [C.join_target_gt n k a l hkn hal,
          C.join_source_gt n k (C.target n a) m hkn htm,
          C.source_target_self n a,hlm]
      · rw [C.join_target_gt n k (C.target n a) m hkn htm,
          C.join_source_gt n k (C.target n a) r hkn htr,
          C.source_target_self n a,C.target_target,min_self,hmr]
      · rw [C.join_distribute_left k n hkn a (C.join n l m) r hlmr hai,
          C.join_distribute_left k n hkn a l m hlm hal]

lemma right {n : ℕ} {x : C.Cell} (hx : C.LayeredWhisker G n x)
    (k : ℕ) (hk : k < n) (a : C.Cell) (ha : C.source n a = a)
    (h : C.target k x = C.source k a) : C.LayeredWhisker G n (C.join k x a) := by
  induction n generalizing x k a with
  | zero => omega
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,rfl⟩ := hx
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]
      exact hmr
    by_cases hkn : k = n
    · subst k
      have hra : C.target n r = C.source n a := by
        rw [C.join_target_le n n _ r le_rfl hlmr] at h
        exact h
      refine ⟨l,m,C.join n r a,hl,?_,hm,hlm,?_,?_⟩
      · rw [C.join_source_gt (n+1) n r a (Nat.lt_succ_self n) hra,hr,ha]
      · rw [C.join_source_le n n r a le_rfl hra]
        exact hmr
      · exact C.join_assoc n (C.join n l m) r a hlmr hra
    · have hkn : k < n := by omega
      have hra : C.target k r = C.source k a := by
        rw [C.join_target_le k n _ r hkn.le hlmr] at h
        exact h
      have hl' : C.target k l = C.target k m := by
        have hh := congrArg (C.target k) hlm
        simpa only [C.target_target,min_eq_left hkn.le,C.target_source,ite_eq_left hkn] using hh
      have hm' : C.target k m = C.target k r := by
        have hh := congrArg (C.target k) hmr
        simpa only [C.target_target,min_eq_left hkn.le,C.target_source,ite_eq_left hkn] using hh
      have hms : C.target k m = C.source k (C.source n a) := by
        rw [C.source_source,min_eq_left hkn.le]
        exact hm'.trans hra
      have hls : C.target k l = C.source k (C.source n a) := hl'.trans hms
      have his : C.target k (C.join n l m) = C.source k (C.source n a) := by
        rw [C.join_target_le k n l m hkn.le hlm]
        exact hms
      refine ⟨C.join k l (C.source n a), C.join k m (C.source n a),
        C.join k r a,?_,?_,
        ih hm k hkn (C.source n a) (C.source_source_self n a) hms,?_,?_,?_⟩
      · rw [C.join_source_gt (n+1) k l (C.source n a) (by omega) hls,hl,
          C.source_fixed_upwards (Nat.le_succ n) (C.source_source_self n a)]
      · rw [C.join_source_gt (n+1) k r a (by omega) hra,hr,ha]
      · rw [C.join_target_gt n k l (C.source n a) hkn hls,
          C.join_source_gt n k m (C.source n a) hkn hms,
          C.source_source_self n a,C.target_source_self n a,hlm]
      · rw [C.join_target_gt n k m (C.source n a) hkn hms,
          C.join_source_gt n k r a hkn hra,C.target_source_self n a,hmr]
      · rw [C.join_distribute_right k n hkn (C.join n l m) r a hlmr hra,
          C.join_whisker_right k n hkn l m (C.source n a)
            (C.source_source_self n a) hlm hls hms]

end LayeredWhisker

theorem Whisker.layered {n : ℕ} {G : C.Cell → Prop} {x : C.Cell}
    (hx : C.Whisker n G x) : C.LayeredWhisker G n x := by
  induction hx with
  | generator x hg hx => exact LayeredWhisker.of_generator hg n
  | left k hk a x ha h hx ih => exact ih.left k hk a ha h
  | right k hk x a ha h hx ih => exact ih.right k hk a ha h
end Thomason.OmegaCategory

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex
open OmegaCategory

namespace Table
variable {K : DirectedComplex.{u}}

lemma comp_left_cancel (n : ℕ) (x y z : Table K)
    (hxy : truncate n true x = truncate n false y)
    (hxz : truncate n true x = truncate n false z)
    (he : comp n x y hxy = comp n x z hxz) : y = z := by
  ext p e
  by_cases hp : p < n
  · exact (lower_rows_eq hxy hp e).symm.trans (lower_rows_eq hxz hp e)
  · by_cases hpn : p = n
    · subst p
      cases e
      · exact (matching_row_eq hxy).symm.trans (matching_row_eq hxz)
      · have hh := congrArg (fun t : Table K => t.row n true) he
        simpa only [comp_row,lt_self_iff_false,ite_false,ite_true] using hh
    · have hh := congrArg (fun t : Table K => t.row p e) he
      simp only [comp_row,ite_eq_right hp,ite_eq_right hpn] at hh
      exact add_left_cancel hh

lemma comp_right_cancel (n : ℕ) (x y z : Table K)
    (hxz : truncate n true x = truncate n false z)
    (hyz : truncate n true y = truncate n false z)
    (he : comp n x z hxz = comp n y z hyz) : x = y := by
  ext p e
  by_cases hp : p < n
  · exact (lower_rows_eq hxz hp e).trans (lower_rows_eq hyz hp e).symm
  · by_cases hpn : p = n
    · subst p
      cases e
      · have hh := congrArg (fun t : Table K => t.row n false) he
        simpa only [comp_row,lt_self_iff_false,ite_false,ite_true,Bool.false_eq_true] using hh
      · exact (matching_row_eq hxz).trans (matching_row_eq hyz).symm
    · have hh := congrArg (fun t : Table K => t.row p e) he
      simp only [comp_row,ite_eq_right hp,ite_eq_right hpn] at hh
      exact add_right_cancel hh

lemma join_left_cancel (n : ℕ) (x y z : Table K)
    (hxy : K.nu.target n x = K.nu.source n y)
    (hxz : K.nu.target n x = K.nu.source n z)
    (he : K.nu.join n x y = K.nu.join n x z) : y = z := by
  rw [K.nu.join_eq n x y hxy,K.nu.join_eq n x z hxz] at he
  exact comp_left_cancel n x y z hxy hxz he

lemma join_right_cancel (n : ℕ) (x y z : Table K)
    (hxz : K.nu.target n x = K.nu.source n z)
    (hyz : K.nu.target n y = K.nu.source n z)
    (he : K.nu.join n x z = K.nu.join n y z) : x = y := by
  rw [K.nu.join_eq n x z hxz,K.nu.join_eq n y z hyz] at he
  exact comp_right_cancel n x y z hxz hyz he

end Table

namespace RankedAtoms
open Table
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

lemma top_and_target_ext (n : ℕ) (x y : Table K)
    (hx : truncate (n+1) false x = x) (hy : truncate (n+1) false y = y)
    (ht : x.row (n+1) false = y.row (n+1) false)
    (hs : truncate n true x = truncate n true y) : x = y := by
  ext p e
  by_cases hp : n < p
  · exact NormalizedChains.rows_above_top_agree x y hx hy ht p (by omega) e
  · have hpn : p ≤ n := by omega
    by_cases he : p = n ∧ e = false
    · obtain ⟨he,rfl⟩ := he
      subst p
      have hright := congrArg (fun z : Table K => z.row n true) hs
      simp only [truncate_row,lt_self_iff_false,ite_false,ite_true] at hright
      have hd := congrArg (K.d n) ht
      rw [x.boundary,y.boundary,hright] at hd
      exact (sub_right_inj).mp hd
    · have h := congrArg (fun z : Table K => z.row p e) hs
      by_cases hpn' : p < n
      · simpa only [truncate_row,ite_eq_left hpn'] using h
      · have hp : p = n := by omega
        subst p
        have he' : e = true := by cases e <;> simp_all
        subst e
        simpa only [truncate_row,lt_self_iff_false,ite_false,ite_true] using h

def OrderedWhisker (b : A.Index) : ℕ → C.Cell → Prop
  | 0, x => F.map x = A.atom b
  | n+1, x => ∃ l m r : C.Cell,
      C.source (n+1) l = l ∧ C.source (n+1) r = r ∧
      OrderedWhisker b n m ∧ C.target n l = C.source n m ∧
      C.target n m = C.source n r ∧
      (∀ c, A.coefficient c (n+1) ((F.map l).row (n+1) false) ≠ 0 → A.rank b < A.rank c) ∧
      (∀ c, A.coefficient c (n+1) ((F.map r).row (n+1) false) ≠ 0 → ¬ A.rank b < A.rank c) ∧
      x = C.join n (C.join n l m) r

namespace OrderedWhisker
variable {A F}

lemma layered {b : A.Index} {n : ℕ} {x : C.Cell} (hx : A.OrderedWhisker F b n x) :
    C.LayeredWhisker (fun z => F.map z = A.atom b) n x := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,_,_,he⟩ := hx
    exact ⟨l,m,r,hl,hr,ih hm,hlm,hmr,he⟩

lemma row_above {b : A.Index} {n : ℕ} {x : C.Cell} (hx : A.OrderedWhisker F b n x)
    (p : ℕ) (hp : n < p) (e : Bool) : (F.map x).row p e = (A.atom b).row p e := by
  induction n generalizing x with
  | zero => change F.map x = A.atom b at hx; rw [hx]
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,_,_,rfl⟩ := hx
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

lemma of_atom {b : A.Index} {x : C.Cell} (hx : F.map x = A.atom b) (n : ℕ) :
    A.OrderedWhisker F b n x := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    refine ⟨C.source n x,x,C.target n x,
      C.source_fixed_upwards (Nat.le_succ n) (C.source_source_self n x),
      C.source_fixed_upwards (Nat.le_succ n) (C.source_target_self n x),ih,
      C.target_source_self n x,(C.source_target_self n x).symm,?_,?_,?_⟩
    · intro c hc
      rw [top_row_lower F n _ (C.source_source_self n x),map_zero] at hc
      exact False.elim (hc rfl)
    · intro c hc
      rw [top_row_lower F n _ (C.source_target_self n x),map_zero] at hc
      exact False.elim (hc rfl)
    · rw [C.join_left_unit n (C.source n x) x (C.source_source_self n x)
        (C.target_source_self n x),C.join_right_unit n x (C.target n x)
        (C.source_target_self n x) (C.source_target_self n x).symm]

lemma split_unique (p : ℕ) (r : ℤ) (l₁ l₂ r₁ r₂ : K.Chain p)
    (hl₁ : ∀ c, A.coefficient c p l₁ ≠ 0 → r < A.rank c)
    (hl₂ : ∀ c, A.coefficient c p l₂ ≠ 0 → r < A.rank c)
    (hr₁ : ∀ c, A.coefficient c p r₁ ≠ 0 → ¬ r < A.rank c)
    (hr₂ : ∀ c, A.coefficient c p r₂ ≠ 0 → ¬ r < A.rank c)
    (he : l₁ + r₁ = l₂ + r₂) : l₁ = l₂ ∧ r₁ = r₂ := by
  have hl : l₁ = l₂ := by
    apply A.ext p
    intro c
    have hh := congrArg (A.coefficient c p) he
    simp only [map_add] at hh
    by_cases hc : r < A.rank c
    · have h₁ : A.coefficient c p r₁ = 0 := by by_contra h; exact hr₁ c h hc
      have h₂ : A.coefficient c p r₂ = 0 := by by_contra h; exact hr₂ c h hc
      simpa only [h₁,h₂,add_zero] using hh
    · have h₁ : A.coefficient c p l₁ = 0 := by by_contra h; exact hc (hl₁ c h)
      have h₂ : A.coefficient c p l₂ = 0 := by by_contra h; exact hc (hl₂ c h)
      exact h₁.trans h₂.symm
  exact ⟨hl,add_left_cancel (hl ▸ he)⟩

theorem eq_of_map_eq (b : A.Index) (n : ℕ)
    (hatom : ∀ x y : C.Cell, F.map x = A.atom b → F.map y = A.atom b → x = y)
    (hsmall : ∀ k, k ≤ n → Function.Injective (F.onCells k))
    (x y : C.Cell) (hx : A.OrderedWhisker F b n x) (hy : A.OrderedWhisker F b n y)
    (he : F.map x = F.map y) : x = y := by
  induction n generalizing x y with
  | zero => exact hatom x y hx hy
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,hlo,hro,rfl⟩ := hx
    obtain ⟨l',m',r',hl',hr',hm',hlm',hmr',hlo',hro',rfl⟩ := hy
    have hfm := hm.row_above (n+1) (Nat.lt_succ_self n) false
    have hfm' := hm'.row_above (n+1) (Nat.lt_succ_self n) false
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]; exact hmr
    have hlmr' : C.target n (C.join n l' m') = C.source n r' := by
      rw [C.join_target_le n n l' m' le_rfl hlm']; exact hmr'
    have ht := congrArg (fun t : Table K => t.row (n+1) false) he
    rw [top_row_join F (n+1) n (Nat.lt_succ_self n) _ r hlmr,
      top_row_join F (n+1) n (Nat.lt_succ_self n) l m hlm,
      top_row_join F (n+1) n (Nat.lt_succ_self n) _ r' hlmr',
      top_row_join F (n+1) n (Nat.lt_succ_self n) l' m' hlm',hfm,hfm'] at ht
    have hsum : (F.map l).row (n+1) false + (F.map r).row (n+1) false =
        (F.map l').row (n+1) false + (F.map r').row (n+1) false := by
      have hh := congrArg (fun z => z - (A.atom b).row (n+1) false) ht
      convert hh using 1 <;> abel
    obtain ⟨hlt,hrt⟩ := split_unique (A := A) (n+1) (A.rank b) _ _ _ _ hlo hlo' hro hro' hsum
    have hf (z : C.Cell) (hz : C.source (n+1) z = z) : truncate (n+1) false (F.map z) = F.map z :=
      (F.map_source (n+1) z).symm.trans (congrArg F.map hz)
    have hle : F.map l = F.map l' := by
      apply top_and_source_ext n _ _ (hf l hl) (hf l' hl') hlt
      have hs := congrArg (K.nu.source n) he
      rw [← F.map_source,← F.map_source,
        C.join_source_le n n _ r le_rfl hlmr,C.join_source_le n n l m le_rfl hlm,
        C.join_source_le n n _ r' le_rfl hlmr',C.join_source_le n n l' m' le_rfl hlm',
        F.map_source,F.map_source] at hs
      exact hs
    have hre : F.map r = F.map r' := by
      apply top_and_target_ext n _ _ (hf r hr) (hf r' hr') hrt
      have hs := congrArg (K.nu.target n) he
      rw [← F.map_target,← F.map_target,
        C.join_target_le n n _ r le_rfl hlmr,C.join_target_le n n _ r' le_rfl hlmr',
        F.map_target,F.map_target] at hs
      exact hs
    have hll : l = l' := congrArg Subtype.val (hsmall (n+1) le_rfl
      (a₁ := ⟨l,hl⟩) (a₂ := ⟨l',hl'⟩) (Subtype.ext hle))
    have hrr : r = r' := congrArg Subtype.val (hsmall (n+1) le_rfl
      (a₁ := ⟨r,hr⟩) (a₂ := ⟨r',hr'⟩) (Subtype.ext hre))
    subst l'
    subst r'
    have hmm : F.map m = F.map m' := by
      rw [F.map_join n _ r hlmr,F.map_join n l m hlm,
        F.map_join n _ r hlmr',F.map_join n l m' hlm'] at he
      apply Table.join_left_cancel n (F.map l) _ _ (F.map_composable hlm) (F.map_composable hlm')
      apply Table.join_right_cancel n _ _ (F.map r)
        (by rw [← F.map_join n l m hlm]; exact F.map_composable hlmr)
        (by rw [← F.map_join n l m' hlm']; exact F.map_composable hlmr') he
    have hmm' : m = m' := ih (fun k hk => hsmall k (by omega)) m m' hm hm' hmm
    rw [hmm']

end OrderedWhisker
end RankedAtoms
end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex
open Table OmegaCategory

namespace Table
variable {K : DirectedComplex.{u}}

lemma factor_context_with_top (k : ℕ) (y : Table K) (c d : K.Chain (k+1))
    (hc : c ∈ K.positive (k+1)) (hd : d ∈ K.positive (k+1))
    (ht : ∀ b, y.row (k+1) b - c - d ∈ K.positive (k+1))
    (hs : y.row k false + K.d k c ∈ K.positive k)
    (he : y.row k true - K.d k d ∈ K.positive k) :
    ∃ (l r : Table K) (hlm : truncate k true l = truncate k false (removeContext k y c d ht hs he))
      (hmr : truncate k true (comp k l (removeContext k y c d ht hs he) hlm) = truncate k false r),
      truncate (k+1) false l = l ∧ truncate (k+1) false r = r ∧
      l.row (k+1) false = c ∧ r.row (k+1) false = d ∧
      comp k (comp k l (removeContext k y c d ht hs he) hlm) r hmr = y := by
  let m := removeContext k y c d ht hs he
  let s := truncate k false y
  have hsf : truncate k false s = s := by simp [s, truncate_truncate_same]
  have hs' : s.row k false + K.d k c ∈ K.positive k := by simpa [s] using hs
  let l := extendTop k s hsf c hc hs'
  have hlm : truncate k true l = truncate k false m := by
    ext p b
    rw [truncate_row, truncate_row]
    by_cases hp : p < k
    · simp only [ite_eq_left hp]
      change extensionRow k s c p b = removeContextRow k y c d p b
      rw [extensionRow_other k s c p b (by omega) (by omega),
        removeContextRow_other k y c d p b (by omega) (by omega)]
      simp [s, hp]
    · rw [ite_eq_right hp, ite_eq_right hp]
      by_cases heq : p = k
      · subst p
        simp only [ite_true]
        change extensionRow k s c k true = removeContextRow k y c d k false
        simp [s]
      · simp only [ite_eq_right heq]
  let t := truncate k true m
  have htf : truncate k false t = t := by simp [t, truncate_truncate]
  have htrow : t.row k false = y.row k true - K.d k d := by simp [t, m]
  have ht' : t.row k false + K.d k d ∈ K.positive k := by
    rw [htrow, sub_add_cancel]; exact y.positive k true
  let r := extendTop k t htf d hd ht'
  have hmr : truncate k true (comp k l m hlm) = truncate k false r := by
    rw [target_comp_le k k le_rfl, extendTop_source]
  refine ⟨l, r, hlm, hmr, extendTop_dimension k s hsf c hc hs',
    extendTop_dimension k t htf d hd ht', by simp [l], by simp [r], ?_⟩
  ext p b
  simp only [comp_row]
  by_cases hp : p < k
  · simp only [ite_eq_left hp]
    change extensionRow k s c p b = y.row p b
    rw [extensionRow_other k s c p b (by omega) (by omega)]
    simp [s, hp]
  · simp only [ite_eq_right hp]
    by_cases heq : p = k
    · subst p
      simp only [ite_true]
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        change extensionRow k s c k false = y.row k false
        simp [s]
      · simp only [ite_true]
        change extensionRow k t d k true = y.row k true
        simp only [extensionRow_middle, ite_true, htrow, sub_add_cancel]
    · simp only [ite_eq_right heq]
      by_cases hk : p = k+1
      · subst p
        change extensionRow k s c (k+1) b + removeContextRow k y c d (k+1) b +
          extensionRow k t d (k+1) b = y.row (k+1) b
        rw [extensionRow_top, extensionRow_top, removeContextRow_top]
        abel
      · change extensionRow k s c p b + removeContextRow k y c d p b +
          extensionRow k t d p b = y.row p b
        rw [extensionRow_other k s c p b heq hk, extensionRow_other k t d p b heq hk,
          removeContextRow_other k y c d p b heq hk]
        have hz₁ : s.row p b = 0 := by simp [s, hp, heq]
        have hz₂ : t.row p b = 0 := by simp [t, hp, heq]
        rw [hz₁, hz₂, zero_add, add_zero]

end Table

namespace RankedAtoms
variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

theorem table_ordered_whisker (b : A.Index) (n : ℕ) (hn : n < A.dim b)
    (y : Table K) (hy : ∀ p, n < p → ∀ e, y.row p e = (A.atom b).row p e) :
    A.OrderedWhisker (OmegaCategory.Functor.id K.nu) b n y := by
  induction n generalizing y with
  | zero =>
    change y = A.atom b
    obtain ⟨hz,hcommon⟩ := A.common_atom_context b 0 hn y (hy 1 (by omega) false)
    have haug : K.augmentation (y.row 0 false - (A.atom b).row 0 false) = 0 := by
      rw [map_sub,y.augmentation,(A.atom b).augmentation,sub_self]
    have hz₀ := A.positive_augmentation_zero _ hz haug
    ext p e
    cases p with
    | zero =>
      cases e
      · exact sub_eq_zero.mp hz₀
      · exact sub_eq_zero.mp (hcommon.trans hz₀)
    | succ p => exact hy (p+1) (by omega) e
  | succ n ih =>
    obtain ⟨hz,hcommon⟩ := A.common_atom_context b (n+1) hn y (hy (n+2) (by omega) false)
    let z := y.row (n+1) false - (A.atom b).row (n+1) false
    let c := A.cut (n+1) z (fun t => A.rank b < A.rank t)
    let d := A.cut (n+1) z (fun t => ¬ A.rank b < A.rank t)
    have hc : c ∈ K.positive (n+1) := A.cut_positive _ _ hz _
    have hd : d ∈ K.positive (n+1) := A.cut_positive _ _ hz _
    have hcd : c + d = z := A.cut_add_complement _ _ _
    have hrows (e : Bool) : y.row (n+1) e - c - d = (A.atom b).row (n+1) e := by
      have he : y.row (n+1) e - (A.atom b).row (n+1) e = z := by
        cases e
        · rfl
        · exact hcommon
      rw [sub_sub,hcd]
      exact sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp he).trans (add_comm _ _))
    have ht : ∀ e, y.row (n+1) e - c - d ∈ K.positive (n+1) := by
      intro e
      rw [hrows]
      exact (A.atom b).positive _ _
    have hdiff : y.row n true - y.row n false = (A.atom b).row n true -
        (A.atom b).row n false + K.d n z := by
      dsimp [z]
      rw [map_sub,y.boundary,(A.atom b).boundary]
      abel
    obtain ⟨hstart,hend⟩ := A.rank_cut_positive n (A.rank b) _ _ _ _ z
      ((A.atom b).positive n false) ((A.atom b).positive n true)
      (y.positive n false) (y.positive n true) hz
      (fun t ht => A.ranked b n (by omega) false t ht)
      (fun t ht => A.ranked b n (by omega) true t ht) hdiff
    let m := removeContext n y c d ht hstart hend
    have hm : A.OrderedWhisker (OmegaCategory.Functor.id K.nu) b n m := by
      apply ih (by omega) m
      intro p hp e
      change removeContextRow n y c d p e = (A.atom b).row p e
      by_cases hpn : p = n+1
      · subst p; rw [removeContextRow_top,hrows]
      · rw [removeContextRow_other n y c d p e (by omega) hpn]
        exact hy p (by omega) e
    obtain ⟨l,r,hlm,hmr,hl,hr,hlt,hrt,he⟩ := factor_context_with_top n y c d hc hd ht hstart hend
    have hmr' : K.nu.target n m = K.nu.source n r := by
      change truncate n true m = truncate n false r
      rw [target_comp_le n n le_rfl] at hmr
      exact hmr
    refine ⟨l,m,r,hl,hr,hm,hlm,hmr',?_,?_,?_⟩
    · intro t ht
      change A.coefficient t (n+1) (l.row (n+1) false) ≠ 0 at ht
      rw [hlt,A.coefficient_cut] at ht
      by_contra hh
      exact ht (ite_eq_right hh)
    · intro t ht
      change A.coefficient t (n+1) (r.row (n+1) false) ≠ 0 at ht
      rw [hrt,A.coefficient_cut] at ht
      by_contra hh
      exact ht (ite_eq_right (not_not_intro hh))
    · rw [K.nu.join_eq n l m hlm]
      rw [K.nu.join_eq n (K.nu.comp n l m hlm) r hmr]
      exact he.symm

namespace OrderedWhisker
variable {A F}

theorem lift (b : A.Index) (n : ℕ)
    (hatom : ∃ x : C.Cell, F.map x = A.atom b)
    (hsmall : ∀ k, k ≤ n → Function.Bijective (F.onCells k))
    (y : Table K) (hy : A.OrderedWhisker (OmegaCategory.Functor.id K.nu) b n y) :
    ∃ x : C.Cell, A.OrderedWhisker F b n x ∧ F.map x = y := by
  induction n generalizing y with
  | zero =>
    obtain ⟨x,hx⟩ := hatom
    exact ⟨x,hx,hx.trans hy.symm⟩
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,hlo,hro,rfl⟩ := hy
    obtain ⟨l',hl'⟩ := (hsmall (n+1) le_rfl).2 ⟨l,hl⟩
    obtain ⟨r',hr'⟩ := (hsmall (n+1) le_rfl).2 ⟨r,hr⟩
    have hfl : F.map l'.val = l := congrArg Subtype.val hl'
    have hfr : F.map r'.val = r := congrArg Subtype.val hr'
    obtain ⟨m',hm',hfm⟩ := ih (fun k hk => hsmall k (by omega)) m hm
    have hlm' : C.target n l'.val = C.source n m' := by
      apply congrArg Subtype.val ((hsmall n (Nat.le_succ n)).1
        (a₁ := ⟨C.target n l'.val,C.source_target_self n _⟩)
        (a₂ := ⟨C.source n m',C.source_source_self n _⟩) (Subtype.ext ?_))
      change F.map (C.target n l'.val) = F.map (C.source n m')
      rw [F.map_target,F.map_source,hfl,hfm]
      exact hlm
    have hmr' : C.target n m' = C.source n r'.val := by
      apply congrArg Subtype.val ((hsmall n (Nat.le_succ n)).1
        (a₁ := ⟨C.target n m',C.source_target_self n _⟩)
        (a₂ := ⟨C.source n r'.val,C.source_source_self n _⟩) (Subtype.ext ?_))
      change F.map (C.target n m') = F.map (C.source n r'.val)
      rw [F.map_target,F.map_source,hfm,hfr]
      exact hmr
    have hlmr' : C.target n (C.join n l'.val m') = C.source n r'.val := by
      rw [C.join_target_le n n l'.val m' le_rfl hlm']; exact hmr'
    refine ⟨C.join n (C.join n l'.val m') r'.val,?_,?_⟩
    · refine ⟨l'.val,m',r'.val,l'.property,r'.property,hm',hlm',hmr',?_,?_,rfl⟩
      · intro c hc
        rw [hfl] at hc
        exact hlo c hc
      · intro c hc
        rw [hfr] at hc
        exact hro c hc
    · rw [F.map_join n _ r'.val hlmr',F.map_join n l'.val m' hlm',hfl,hfm,hfr]

end OrderedWhisker

theorem unique_ordered_lift (b : A.Index) (n : ℕ) (hb : A.dim b = n+1)
    (hatom : ∃! x : C.Cell, F.map x = A.atom b)
    (hsmall : ∀ k, k ≤ n → Function.Bijective (F.onCells k))
    (y : Table K) (hy : truncate (n+1) false y = y)
    (ht : y.row (n+1) false = A.basis (n+1) b) :
    ∃! x : C.Cell, A.OrderedWhisker F b n x ∧ F.map x = y := by
  have htop : y.row (n+1) false = (A.atom b).row (n+1) false := by
    rw [ht,← hb,A.basis_own]
  have hyord := A.table_ordered_whisker b n (by omega) y (fun p hp e =>
    NormalizedChains.rows_above_top_agree y (A.atom b) hy (hb ▸ A.bounded b)
      htop p (by omega) e)
  obtain ⟨d,hd,hunique⟩ := hatom
  obtain ⟨x,hx,hfx⟩ := hyord.lift b n ⟨d,hd⟩ hsmall
  refine ⟨x,⟨hx,hfx⟩,?_⟩
  intro z hz
  exact OrderedWhisker.eq_of_map_eq b n
    (fun s t hs ht => (hunique s hs).trans (hunique t ht).symm)
    (fun k hk => (hsmall k hk).1) z x hz.1 hx (hz.2.trans hfx.symm)
end RankedAtoms
end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory
variable {C : OmegaCategory.{u}} {D : OmegaCategory.{v}}

lemma Functor.bounded_ext (F : Functor C D) (n : ℕ)
    (hinj : Function.Injective (F.onCells n)) (x y : C.Cell)
    (hx : C.source n x = x) (hy : C.source n y = y) (he : F.map x = F.map y) : x = y :=
  congrArg Subtype.val (hinj (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) (Subtype.ext he))

lemma LayeredWhisker.row_bounded {G : C.Cell → Prop} (d : ℕ)
    (hg : ∀ x, G x → C.source d x = x) {n : ℕ} (hn : n ≤ d) {x : C.Cell}
    (hx : C.LayeredWhisker G n x) : C.source d x = x := by
  induction n generalizing x with
  | zero => exact hg x hx
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,rfl⟩ := hx
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]; exact hmr
    rw [C.join_source_gt d n _ r (by omega) hlmr,
      C.join_source_gt d n l m (by omega) hlm,
      C.source_fixed_upwards hn hl,C.source_fixed_upwards hn hr,ih (by omega) hm]

lemma LayeredWhisker.whisker {G : C.Cell → Prop} (d : ℕ)
    (hg : ∀ x, G x → C.source (d+1) x = x) {n : ℕ} (hn : n ≤ d) {x : C.Cell}
    (hx : C.LayeredWhisker G n x) : C.Whisker d G x := by
  induction n generalizing x with
  | zero => exact .generator x hx (hg x hx)
  | succ n ih =>
    obtain ⟨l,m,r,hl,hr,hm,hlm,hmr,rfl⟩ := hx
    have hlmr : C.target n (C.join n l m) = C.source n r := by
      rw [C.join_target_le n n l m le_rfl hlm]; exact hmr
    exact .right n (by omega) _ r (C.source_fixed_upwards hn hr) hlmr
      (.left n (by omega) l m (C.source_fixed_upwards hn hl) hlm (ih (by omega) hm))

end Thomason.OmegaCategory

end

end OAI
