import Mathlib
import OAI.CategoryTheory.Thomason.TopSequences

namespace OAI

/-! Ranked Exchange. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory

variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

inductive AtomPath (n : ℕ) : List A.Index → C.Cell → Prop
  | nil (x) (hx : C.source n x = x) : AtomPath n [] x
  | cons (b : A.Index) (hb : A.dim b = n+1) (x y : C.Cell) (bs)
      (hx : C.Whisker n (A.TopGenerator F n) x)
      (ht : (F.map x).row (n+1) false = A.basis (n+1) b)
      (h : C.target n x = C.source n y) :
      AtomPath n bs y → AtomPath n (b::bs) (C.join n x y)

namespace AtomPath
variable {A F} {n : ℕ}

lemma bounded {bs : List A.Index} {x : C.Cell} (h : A.AtomPath F n bs x) :
    C.source (n+1) x = x := by
  induction h with
  | nil x hx => exact C.source_fixed_upwards (Nat.le_succ n) hx
  | cons b hb x y bs hx ht h hy ih =>
    rw [C.join_source_gt (n+1) n x y (Nat.lt_succ_self n) h,hx.bounded,ih]

lemma topSequence {bs : List A.Index} {x : C.Cell} (h : A.AtomPath F n bs x) :
    C.TopSequence n (A.TopGenerator F n) x := by
  induction h with
  | nil x hx => exact .lower x hx
  | cons b hb x y bs hx ht h hy ih => exact .compose _ _ h (.single x hx) ih

lemma append {bs cs : List A.Index} {x y : C.Cell}
    (hx : A.AtomPath F n bs x) (hy : A.AtomPath F n cs y)
    (h : C.target n x = C.source n y) : A.AtomPath F n (bs++cs) (C.join n x y) := by
  induction hx with
  | nil x hx =>
    rw [C.join_left_unit n x y hx h]
    exact hy
  | cons b hb z x bs hz ht hz_x hp ih =>
    have hx_y : C.target n x = C.source n y := by
      rw [C.join_target_le n n z x le_rfl hz_x] at h
      exact h
    rw [C.join_assoc n z x y hz_x hx_y]
    refine .cons b hb z (C.join n x y) (bs++cs) hz ht ?_ (ih hx_y)
    rw [C.join_source_le n n x y le_rfl hx_y]
    exact hz_x

lemma single {x : C.Cell} (hx : C.Whisker n (A.TopGenerator F n) x) :
    ∃ b, A.AtomPath F n [b] x := by
  obtain ⟨b,hb,ht⟩ := A.whisker_top_basis F hx
  refine ⟨b,?_⟩
  have h : C.target n x = C.source n (C.target n x) := (C.source_target_self n x).symm
  have hp := AtomPath.cons b hb x (C.target n x) [] hx ht h
    (AtomPath.nil (A := A) (F := F) (C.target n x) (C.source_target_self n x))
  rw [C.join_right_unit n x (C.target n x) (C.source_target_self n x) h] at hp
  exact hp

lemma coefficient {bs : List A.Index} {x : C.Cell} (h : A.AtomPath F n bs x)
    (b : A.Index) : A.coefficient b (n+1) ((F.map x).row (n+1) false) =
      (by classical exact (bs.count b : ℤ)) := by
  classical
  induction h with
  | nil x hx => rw [top_row_lower F n x hx,map_zero]; rfl
  | cons c hc x y cs hx ht h hp ih =>
    rw [top_row_join F (n+1) n (Nat.lt_succ_self n) x y h,map_add,ht,A.coefficient_basis,
      ite_eq_left hc,ih]
    by_cases he : c = b
    · subst c
      simp
      omega
    · simp [he]

lemma nodup {bs : List A.Index} {x : C.Cell} (h : A.AtomPath F n bs x) : bs.Nodup := by
  classical
  apply List.nodup_iff_count_le_one.mpr
  intro b
  have hm := A.top_coefficient_le_one (n+1) (F.map x)
    ((F.map_source (n+1) x).symm.trans (congrArg F.map h.bounded)) b
  rw [h.coefficient b] at hm
  omega

lemma perm_of_image_eq {bs cs : List A.Index} {x y : C.Cell}
    (hx : A.AtomPath F n bs x) (hy : A.AtomPath F n cs y) (he : F.map x = F.map y) :
    bs.Perm cs := by
  classical
  apply List.perm_iff_count.mpr
  intro b
  have h := congrArg (fun t : Table K => A.coefficient b (n+1) (t.row (n+1) false)) he
  rw [hx.coefficient b,hy.coefficient b] at h
  exact_mod_cast h

lemma dim_of_mem {bs : List A.Index} {x : C.Cell} (h : A.AtomPath F n bs x)
    (b : A.Index) (hb : b ∈ bs) : A.dim b = n+1 := by
  induction h with
  | nil x hx => simp at hb
  | cons c hc x y cs hx ht h hp ih =>
    rcases List.mem_cons.mp hb with he | he
    · simpa only [he] using hc
    · exact ih he

end AtomPath

lemma topSequence_path {n : ℕ} {x : C.Cell}
    (h : C.TopSequence n (A.TopGenerator F n) x) :
    ∃ bs : List A.Index, A.AtomPath F n bs x := by
  induction h with
  | lower x hx => exact ⟨[],.nil x hx⟩
  | single x hx =>
    obtain ⟨b,hb⟩ := AtomPath.single hx
    exact ⟨[b],hb⟩
  | compose x y h hx hy ihx ihy =>
    obtain ⟨bs,hbs⟩ := ihx
    obtain ⟨cs,hcs⟩ := ihy
    exact ⟨bs++cs,hbs.append hcs h⟩
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory NormalizedChains

theorem tensor_atom_path {N : ℕ} {P : Type u} [LinearOrder P] (e : Fin (N+1) ≃o P)
    (n : ℕ) (x : (tensorFunctor.obj (NormalizedChains.complex P).nu).Cell)
    (hx : (tensorFunctor.obj (NormalizedChains.complex P).nu).source (n+1) x = x) :
    ∃ bs : List (Prism.Basis.ofOrderIso e).Index,
      (Prism.Basis.ofOrderIso e).AtomPath (chainComparison (NormalizedChains.complex P)) n bs x ∧
        bs.Nodup := by
  obtain ⟨bs,hbs⟩ := (Prism.Basis.ofOrderIso e).topSequence_path
    (chainComparison (NormalizedChains.complex P)) (tensor_top_sequence e n x hx)
  exact ⟨bs,hbs,hbs.nodup⟩
end Thomason.GrayRecursive.IntervalHom

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory

variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)

def orderRank (b : A.Index) : ℤ :=
  (Fintype.card A.Index : ℤ) * A.rank b + (Fintype.equivFin A.Index b).val

lemma orderRank_strict {b c : A.Index} (h : A.rank b < A.rank c) :
    A.orderRank b < A.orderRank c := by
  have hb : ((Fintype.equivFin A.Index b).val : ℤ) < Fintype.card A.Index := by
    exact_mod_cast (Fintype.equivFin A.Index b).isLt
  have hc : (0 : ℤ) ≤ (Fintype.equivFin A.Index c).val := Int.natCast_nonneg _
  have hn : (0 : ℤ) ≤ Fintype.card A.Index := Int.natCast_nonneg _
  have hm := mul_le_mul_of_nonneg_left (Int.add_one_le_iff.mpr h) hn
  dsimp [orderRank]
  nlinarith

lemma orderRank_injective : Function.Injective A.orderRank := by
  intro b c h
  have hr : A.rank b = A.rank c := by
    have hbc : ¬ A.rank b < A.rank c := fun hn => (ne_of_lt (A.orderRank_strict hn)) h
    have hcb : ¬ A.rank c < A.rank b := fun hn => (ne_of_lt (A.orderRank_strict hn)) h.symm
    omega
  have hf : (Fintype.equivFin A.Index b).val = (Fintype.equivFin A.Index c).val := by
    dsimp [orderRank] at h
    rw [hr] at h
    exact_mod_cast add_left_cancel h
  exact (Fintype.equivFin A.Index).injective (Fin.ext hf)

lemma rank_le_of_orderRank_le {b c : A.Index} (h : A.orderRank b ≤ A.orderRank c) :
    A.rank b ≤ A.rank c := by
  by_contra hn
  exact (not_lt_of_ge h) (A.orderRank_strict (lt_of_not_ge hn))

lemma table_topSequence (n : ℕ) (x : Table K) (hx : truncate (n+1) false x = x) :
    K.nu.TopSequence n (A.TopGenerator (OmegaCategory.Functor.id K.nu) n) x := by
  have hh := A.bounded_pasting (n+1) x hx
  clear hx
  induction hh with
  | atom b hb =>
    by_cases he : A.dim b ≤ n
    · exact .lower _ (K.nu.source_fixed_upwards he (A.bounded b))
    · exact .single _ (.generator _ ⟨b,by omega,rfl⟩
        (K.nu.source_fixed_upwards hb (A.bounded b)))
  | compose k hk x y h hx hy ihx ihy => exact ihx.comp ihy k (by omega) h

lemma table_single_whisker (n : ℕ) (b : A.Index) (hb : A.dim b = n+1)
    (x : Table K) (hx : truncate (n+1) false x = x)
    (ht : x.row (n+1) false = A.basis (n+1) b) :
    K.nu.Whisker n (A.TopGenerator (OmegaCategory.Functor.id K.nu) n) x :=
  A.topSequence_single (OmegaCategory.Functor.id K.nu) hb (fun _ h => h)
    (A.table_topSequence n x hx) ht

namespace AtomPath
variable {A}

lemma mass {C : OmegaCategory.{w}} {F : OmegaCategory.Functor C K.nu}
    {n : ℕ} {bs : List A.Index} {x : C.Cell} (h : A.AtomPath F n bs x) :
    A.mass (n+1) ((F.map x).row (n+1) false) = bs.length := by
  induction h with
  | nil x hx => rw [top_row_lower F n x hx,map_zero]; rfl
  | cons b hb x y bs hx ht h hy ih =>
    rw [top_row_join F (n+1) n (Nat.lt_succ_self n) x y h,map_add,ht,A.mass_basis _ _ hb,ih]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    omega

lemma sorted_list_unique {C : OmegaCategory.{w}} {F : OmegaCategory.Functor C K.nu}
    {n : ℕ} {bs cs : List A.Index} {x y : C.Cell}
    (hx : A.AtomPath F n bs x) (hy : A.AtomPath F n cs y)
    (hbs : bs.Pairwise (fun b c => A.orderRank c < A.orderRank b))
    (hcs : cs.Pairwise (fun b c => A.orderRank c < A.orderRank b))
    (he : F.map x = F.map y) : bs = cs := by
  exact List.Perm.eq_of_pairwise
    (fun b c _ _ hbc hcb => A.orderRank_injective (le_antisymm hcb hbc))
    (hbs.imp fun h => h.le) (hcs.imp fun h => h.le)
    (hx.perm_of_image_eq hy he)

end AtomPath

theorem table_sorted_atomPath (n : ℕ) (y : Table K) (hy : truncate (n+1) false y = y) :
    ∃ bs : List A.Index,
      A.AtomPath (OmegaCategory.Functor.id K.nu) n bs y ∧
        bs.Pairwise (fun b c => A.orderRank c < A.orderRank b) := by
  classical
  generalize hm : (A.mass (n+1) (y.row (n+1) false)).toNat = m
  induction m using Nat.strong_induction_on generalizing y with
  | h m ih =>
    let z := y.row (n+1) false
    have hz : z ∈ K.positive (n+1) := y.positive (n+1) false
    by_cases he : z = 0
    · refine ⟨[],?_,by simp⟩
      apply AtomPath.nil
      exact fixed_of_top_zero hy he
    let S := Finset.univ.filter (fun b => A.coefficient b (n+1) z ≠ 0)
    have hs : S.Nonempty := by
      by_contra hn
      apply he
      apply A.ext (n+1)
      intro b
      rw [map_zero]
      by_contra hb
      exact hn ⟨b,by simp [S,hb]⟩
    obtain ⟨b,hb,hmax⟩ := Finset.exists_max_image S A.orderRank hs
    have hb' : A.coefficient b (n+1) z ≠ 0 := (Finset.mem_filter.mp hb).2
    have hp : 0 < A.coefficient b (n+1) z :=
      lt_of_le_of_ne ((A.positive (n+1) z).mp hz b) (Ne.symm hb')
    have hd := A.homogeneous b (n+1) z hb'
    have hrem := A.peel_remainder (n+1) z hz b hp
    have hfinal : y.row n false + K.d n z ∈ K.positive n := by
      change y.row n false + K.d n (y.row (n+1) false) ∈ _
      rw [y.boundary]
      convert y.positive n true using 1
      abel
    have hpos := A.peel_positive n z (y.row n false) hz (y.positive n false) hfinal b hp
      (fun c hc => A.rank_le_of_orderRank_le (hmax c (by simp [S,hc])))
    obtain ⟨x,w,hxw,hx,hw,hxt,hwt,heq⟩ :=
      split_top y hy (A.basis (n+1) b) (z - A.basis (n+1) b)
        (A.basis_positive (n+1) b) hrem (by dsimp [z]; abel) hpos
    have hlt : (A.mass (n+1) (w.row (n+1) false)).toNat < m := by
      rw [hwt,map_sub,A.mass_basis (n+1) b hd,← hm]
      change (A.mass (n+1) z - 1).toNat < (A.mass (n+1) z).toNat
      rw [Int.toNat_lt_toNat (A.mass_pos (n+1) z hz b hp)]
      omega
    obtain ⟨bs,hbs,hsorted⟩ := ih _ hlt w hw rfl
    have hpath : A.AtomPath (OmegaCategory.Functor.id K.nu) n (b::bs) y := by
      rw [← heq]
      change A.AtomPath (OmegaCategory.Functor.id K.nu) n (b::bs) (K.nu.comp n x w hxw)
      rw [← K.nu.join_eq n x w hxw]
      exact AtomPath.cons (A := A) (F := OmegaCategory.Functor.id K.nu) b hd x w bs
        (A.table_single_whisker n b hd x hx hxt) hxt hxw hbs
    refine ⟨b::bs,hpath,List.pairwise_cons.mpr ⟨?_,hsorted⟩⟩
    intro c hc
    have hcount : 0 < bs.count c := List.count_pos_iff.mpr hc
    have hcoeff : 0 < A.coefficient c (n+1) (w.row (n+1) false) := by
      have he := hbs.coefficient c
      change A.coefficient c (n+1) (w.row (n+1) false) = _ at he
      rw [he]
      exact_mod_cast hcount
    have hcz : A.coefficient c (n+1) z ≠ 0 := by
      rw [hwt,map_sub] at hcoeff
      have hcb := (A.positive (n+1) _).mp (A.basis_positive (n+1) b) c
      omega
    have hm := hmax c (by simp [S,hcz])
    have hcb : c ≠ b := by
      intro he
      subst c
      exact (List.nodup_cons.mp hpath.nodup).1 hc
    exact lt_of_le_of_ne hm (fun he => hcb (A.orderRank_injective he))
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory

variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

def WhiskerFaithful (n : ℕ) : Prop :=
  ∀ x y : C.Cell, C.Whisker n (A.TopGenerator F n) x →
    C.Whisker n (A.TopGenerator F n) y → F.map x = F.map y → x = y

def HasAdjacentExchange (n : ℕ) : Prop :=
  ∀ (b c : A.Index), A.dim b = n+1 → A.dim c = n+1 →
    A.orderRank b < A.orderRank c →
    ∀ (x y : C.Cell), C.Whisker n (A.TopGenerator F n) x →
      C.Whisker n (A.TopGenerator F n) y →
      (F.map x).row (n+1) false = A.basis (n+1) b →
      (F.map y).row (n+1) false = A.basis (n+1) c →
      C.target n x = C.source n y →
      ∃ x' y' : C.Cell,
        C.Whisker n (A.TopGenerator F n) x' ∧
        C.Whisker n (A.TopGenerator F n) y' ∧
        (F.map x').row (n+1) false = A.basis (n+1) c ∧
        (F.map y').row (n+1) false = A.basis (n+1) b ∧
        C.target n x' = C.source n y' ∧ C.join n x y = C.join n x' y'

namespace AtomPath
variable {A F} {n : ℕ}

lemma eq_of_same_list
    (hn : ∀ x y : C.Cell, C.source n x = x → C.source n y = y → F.map x = F.map y → x = y)
    (hw : A.WhiskerFaithful F n)
    {bs : List A.Index} {x y : C.Cell}
    (hx : A.AtomPath F n bs x) (hy : A.AtomPath F n bs y)
    (he : F.map x = F.map y) : x = y := by
  induction hx generalizing y with
  | nil x hx =>
    cases hy with
    | nil y hy => exact hn x y hx hy he
  | cons b hb x z bs hx ht h hz ih =>
    cases hy with
    | cons _ _ y w _ hy hs h' hw' =>
      have hf (a : C.Cell) (ha : C.source (n+1) a = a) :
          truncate (n+1) false (F.map a) = F.map a :=
        (F.map_source (n+1) a).symm.trans (congrArg F.map ha)
      have hsource : truncate n false (F.map x) = truncate n false (F.map y) := by
        have h₀ := congrArg (fun t : Table K => truncate n false t) he
        change K.nu.source n _ = K.nu.source n _ at h₀
        rw [← F.map_source,← F.map_source,
          C.join_source_le n n x z le_rfl h,C.join_source_le n n y w le_rfl h',
          F.map_source,F.map_source] at h₀
        exact h₀
      have hhead : F.map x = F.map y :=
        top_and_source_ext n _ _ (hf x hx.bounded) (hf y hy.bounded) (ht.trans hs.symm) hsource
      have hxy : x = y := hw x y hx hy hhead
      subst y
      have htail : F.map z = F.map w := by
        apply top_and_source_ext n _ _ (hf z hz.bounded) (hf w hw'.bounded)
        · have ht₀ := congrArg (fun t : Table K => t.row (n+1) false) he
          rw [top_row_join F (n+1) n (Nat.lt_succ_self n) x z h,
            top_row_join F (n+1) n (Nat.lt_succ_self n) x w h'] at ht₀
          exact add_left_cancel ht₀
        · change K.nu.source n _ = K.nu.source n _
          rw [← F.map_source,← F.map_source,← h,← h']
      rw [ih hw' htail]

lemma eq_of_sorted
    (hn : ∀ x y : C.Cell, C.source n x = x → C.source n y = y → F.map x = F.map y → x = y)
    (hw : A.WhiskerFaithful F n)
    {bs cs : List A.Index} {x y : C.Cell}
    (hx : A.AtomPath F n bs x) (hy : A.AtomPath F n cs y)
    (hbs : bs.Pairwise (fun b c => A.orderRank c < A.orderRank b))
    (hcs : cs.Pairwise (fun b c => A.orderRank c < A.orderRank b))
    (he : F.map x = F.map y) : x = y := by
  have hh := hx.sorted_list_unique hy hbs hcs he
  subst cs
  exact hx.eq_of_same_list hn hw hy he

lemma insert_sorted (hex : A.HasAdjacentExchange F n)
    {bs : List A.Index} {y : C.Cell} (hy : A.AtomPath F n bs y)
    (hbs : bs.Pairwise (fun b c => A.orderRank c < A.orderRank b))
    (b : A.Index) (hb : A.dim b = n+1) (x : C.Cell)
    (hx : C.Whisker n (A.TopGenerator F n) x)
    (ht : (F.map x).row (n+1) false = A.basis (n+1) b)
    (h : C.target n x = C.source n y) :
    ∃ cs : List A.Index, A.AtomPath F n cs (C.join n x y) ∧
      cs.Pairwise (fun b c => A.orderRank c < A.orderRank b) := by
  induction hy generalizing b x with
  | nil y hy =>
    exact ⟨[b],.cons b hb x y [] hx ht h (.nil y hy),by simp⟩
  | cons c hc y z bs hy hs hyz hz ih =>
    obtain ⟨hcbs,hbs'⟩ := List.pairwise_cons.mp hbs
    have hxy : C.target n x = C.source n y := by
      rw [C.join_source_le n n y z le_rfl hyz] at h
      exact h
    by_cases hbc : A.orderRank c < A.orderRank b
    · refine ⟨b::c::bs,.cons b hb x (C.join n y z) (c::bs) hx ht h
        (.cons c hc y z bs hy hs hyz hz),List.pairwise_cons.mpr ⟨?_,hbs⟩⟩
      intro t hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · exact hbc
      · exact (hcbs t hmem).trans hbc
    · have hne : b ≠ c := by
        have hp := AtomPath.cons (A := A) (F := F) b hb x (C.join n y z) (c::bs) hx ht h
          (.cons c hc y z bs hy hs hyz hz)
        have hn := (List.nodup_cons.mp hp.nodup).1
        intro heq
        apply hn
        simp [heq]
      have hlt : A.orderRank b < A.orderRank c := by
        have hh : A.orderRank b ≠ A.orderRank c := fun heq => hne (A.orderRank_injective heq)
        omega
      obtain ⟨y',x',hy',hx',hty',htx',hyx',heq⟩ := hex b c hb hc hlt x y hx hy ht hs hxy
      have hxz : C.target n x' = C.source n z := by
        have ht₀ := congrArg (C.target n) heq
        rw [C.join_target_le n n x y le_rfl hxy,
          C.join_target_le n n y' x' le_rfl hyx'] at ht₀
        exact ht₀.symm.trans hyz
      obtain ⟨cs,hcs,hsorted⟩ := ih hbs' b hb x' hx' htx' hxz
      have hm : C.target n y' = C.source n (C.join n x' z) := by
        rw [C.join_source_le n n x' z le_rfl hxz]
        exact hyx'
      have hperm : cs.Perm (b::bs) := hcs.perm_of_image_eq
        (.cons b hb x' z bs hx' htx' hxz hz) rfl
      have hsame : C.join n x (C.join n y z) = C.join n y' (C.join n x' z) := by
        rw [← C.join_assoc n x y z hxy hyz,heq,C.join_assoc n y' x' z hyx' hxz]
      refine ⟨c::cs,?_,List.pairwise_cons.mpr ⟨?_,hsorted⟩⟩
      · rw [hsame]
        exact .cons c hc y' (C.join n x' z) cs hy' hty' hm hcs
      · intro t hmem
        have hh := hperm.mem_iff.mp hmem
        rcases List.mem_cons.mp hh with rfl | hh
        · exact hlt
        · exact hcbs t hh

lemma sorted (hex : A.HasAdjacentExchange F n)
    {bs : List A.Index} {x : C.Cell} (hx : A.AtomPath F n bs x) :
    ∃ cs : List A.Index, A.AtomPath F n cs x ∧
      cs.Pairwise (fun b c => A.orderRank c < A.orderRank b) := by
  induction hx with
  | nil x hx => exact ⟨[],.nil x hx,by simp⟩
  | cons b hb x y bs hx ht h hy ih =>
    obtain ⟨cs,hcs,hs⟩ := ih
    exact hcs.insert_sorted hex hs b hb x hx ht h

lemma eq_of_exchange
    (hn : ∀ x y : C.Cell, C.source n x = x → C.source n y = y → F.map x = F.map y → x = y)
    (hw : A.WhiskerFaithful F n) (hex : A.HasAdjacentExchange F n)
    {bs cs : List A.Index} {x y : C.Cell}
    (hx : A.AtomPath F n bs x) (hy : A.AtomPath F n cs y)
    (he : F.map x = F.map y) : x = y := by
  obtain ⟨bs,hbs,hs⟩ := hx.sorted hex
  obtain ⟨cs,hcs,ht⟩ := hy.sorted hex
  exact hbs.eq_of_sorted hn hw hcs hs ht he

end AtomPath

lemma onCells_injective_of_exchange (n : ℕ)
    (hn : Function.Injective (F.onCells n))
    (hgen : ∀ x : C.Cell, C.source (n+1) x = x →
      C.TopSequence n (A.TopGenerator F n) x)
    (hw : A.WhiskerFaithful F n) (hex : A.HasAdjacentExchange F n) :
    Function.Injective (F.onCells (n+1)) := by
  intro x y he
  obtain ⟨bs,hbs⟩ := A.topSequence_path F (hgen x.val x.property)
  obtain ⟨cs,hcs⟩ := A.topSequence_path F (hgen y.val y.property)
  apply Subtype.ext
  apply hbs.eq_of_exchange ?_ hw hex hcs (congrArg Subtype.val he)
  intro a b ha hb he
  exact congrArg Subtype.val (hn (a₁ := ⟨a,ha⟩) (a₂ := ⟨b,hb⟩) (Subtype.ext he))
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

lemma of_single (b : A.Index) (hb : A.dim b = n+1) {x : C.Cell}
    (hx : C.Whisker n (A.TopGenerator F n) x)
    (ht : (F.map x).row (n+1) false = A.basis (n+1) b) :
    A.AtomPath F n [b] x := by
  have h : C.target n x = C.source n (C.target n x) := (C.source_target_self n x).symm
  have hp := AtomPath.cons b hb x (C.target n x) [] hx ht h
    (AtomPath.nil (A := A) (F := F) (C.target n x) (C.source_target_self n x))
  rw [C.join_right_unit n x (C.target n x) (C.source_target_self n x) h] at hp
  exact hp

lemma nil_bounded {x : C.Cell} (hx : A.AtomPath F n [] x) : C.source n x = x := by
  cases hx with
  | nil x hx => exact hx

lemma view_cons {b : A.Index} {bs : List A.Index} {x : C.Cell}
    (hx : A.AtomPath F n (b::bs) x) :
    A.dim b = n+1 ∧ ∃ y z : C.Cell,
      C.Whisker n (A.TopGenerator F n) y ∧
      (F.map y).row (n+1) false = A.basis (n+1) b ∧
      C.target n y = C.source n z ∧ A.AtomPath F n bs z ∧ x = C.join n y z := by
  cases hx with
  | cons b hb x y bs hx ht h hy => exact ⟨hb,x,y,hx,ht,h,hy,rfl⟩

lemma singleton_data {b : A.Index} {x : C.Cell} (hx : A.AtomPath F n [b] x) :
    A.dim b = n+1 ∧ C.Whisker n (A.TopGenerator F n) x ∧
      (F.map x).row (n+1) false = A.basis (n+1) b := by
  obtain ⟨hb,y,z,hy,ht,hyz,hz,rfl⟩ := hx.view_cons
  rw [C.join_right_unit n y z hz.nil_bounded hyz]
  exact ⟨hb,hy,ht⟩

end AtomPath

lemma table_whiskerFaithful (n : ℕ) : A.WhiskerFaithful (OmegaCategory.Functor.id K.nu) n := by
  intro x y _ _ h
  exact h

lemma table_hasAdjacentExchange (n : ℕ) : A.HasAdjacentExchange (OmegaCategory.Functor.id K.nu) n := by
  intro b c hb hc hbc x y hx hy ht hs h
  have hp := (AtomPath.of_single b hb hx ht).append (AtomPath.of_single c hc hy hs) h
  obtain ⟨cs,q,hq⟩ := A.table_sorted_atomPath n (K.nu.join n x y) hp.bounded
  have hperm : cs.Perm [b,c] := q.perm_of_image_eq hp rfl
  have he : cs = [c,b] := by
    rcases List.perm_pair.mp hperm with he | he
    · rw [he] at hq
      have hh := (List.pairwise_cons.mp hq).1 c (by simp)
      omega
    · exact he
  rw [he] at q
  obtain ⟨_,x',y',hx',ht',h',hy',heq⟩ := q.view_cons
  obtain ⟨_,hy',hs'⟩ := hy'.singleton_data
  exact ⟨x',y',hx',hy',ht',hs',h',heq⟩
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.RankedAtoms
open Table OmegaCategory

variable {K : DirectedComplex.{u}} (A : RankedAtoms.{u,v} K)
variable {C : OmegaCategory.{w}} (F : OmegaCategory.Functor C K.nu)

def TwoAtomFaithful (n : ℕ) : Prop :=
  ∀ (x y : C.Cells (n+1)), A.mass (n+1) ((F.map x.val).row (n+1) false) ≤ 2 →
    F.map x.val = F.map y.val → x = y

lemma whiskerFaithful_of_twoAtomFaithful {n : ℕ} (hh : A.TwoAtomFaithful F n) :
    A.WhiskerFaithful F n := by
  intro x y hx hy he
  obtain ⟨b,hb,ht⟩ := A.whisker_top_basis F hx
  have hm : A.mass (n+1) ((F.map x).row (n+1) false) ≤ 2 := by
    rw [ht,A.mass_basis _ _ hb]
    norm_num
  exact congrArg Subtype.val (hh ⟨x,hx.bounded⟩ ⟨y,hy.bounded⟩ hm he)

lemma hasAdjacentExchange_of_twoAtomFaithful (n : ℕ)
    (hn : Function.Injective (F.onCells n))
    (hsur : Function.Surjective (F.onCells (n+1)))
    (hgen : ∀ x : C.Cell, C.source (n+1) x = x →
      C.TopSequence n (A.TopGenerator F n) x)
    (hreflect : ∀ x : C.Cell, truncate n false (F.map x) = F.map x → C.source n x = x)
    (hh : A.TwoAtomFaithful F n) : A.HasAdjacentExchange F n := by
  intro b c hb hc hbc x y hx hy ht hs h
  have hf (z : C.Cell) (hz : C.source (n+1) z = z) :
      truncate (n+1) false (F.map z) = F.map z :=
    (F.map_source (n+1) z).symm.trans (congrArg F.map hz)
  have hxy := F.map_composable h
  have htx := A.table_single_whisker n b hb (F.map x) (hf x hx.bounded) ht
  have hty := A.table_single_whisker n c hc (F.map y) (hf y hy.bounded) hs
  obtain ⟨a,d,ha,hd,hat,hdt,had,hval⟩ :=
    A.table_hasAdjacentExchange n b c hb hc hbc (F.map x) (F.map y) htx hty ht hs hxy
  obtain ⟨a',ha'⟩ := hsur ⟨a,ha.bounded⟩
  obtain ⟨d',hd'⟩ := hsur ⟨d,hd.bounded⟩
  have hfa : F.map a'.val = a := congrArg Subtype.val ha'
  have hfd : F.map d'.val = d := congrArg Subtype.val hd'
  have hma : (F.map a'.val).row (n+1) false = A.basis (n+1) c := by
    change a.row (n+1) false = _ at hat
    rw [hfa]
    exact hat
  have hmd : (F.map d'.val).row (n+1) false = A.basis (n+1) b := by
    change d.row (n+1) false = _ at hdt
    rw [hfd]
    exact hdt
  have hwa : C.Whisker n (A.TopGenerator F n) a'.val :=
    A.topSequence_single F hc hreflect (hgen a'.val a'.property) hma
  have hwd : C.Whisker n (A.TopGenerator F n) d'.val :=
    A.topSequence_single F hb hreflect (hgen d'.val d'.property) hmd
  have hm : C.target n a'.val = C.source n d'.val := by
    apply congrArg Subtype.val (hn (a₁ := ⟨C.target n a'.val,C.source_target_self n _⟩)
      (a₂ := ⟨C.source n d'.val,C.source_source_self n _⟩) (Subtype.ext ?_))
    change F.map (C.target n _) = F.map (C.source n _)
    rw [F.map_target,F.map_source,hfa,hfd]
    exact had
  refine ⟨a'.val,d'.val,hwa,hwd,hma,hmd,hm,?_⟩
  have hp := (AtomPath.of_single b hb hx ht).append (AtomPath.of_single c hc hy hs) h
  have hp' := (AtomPath.of_single c hc hwa hma).append (AtomPath.of_single b hb hwd hmd) hm
  apply congrArg Subtype.val (hh ⟨C.join n x y,hp.bounded⟩
    ⟨C.join n a'.val d'.val,hp'.bounded⟩ ?_ ?_)
  · have he := hp.mass
    norm_num at he
    exact he.le
  · change F.map (C.join n x y) = F.map (C.join n a'.val d'.val)
    rw [F.map_join n x y h,F.map_join n a'.val d'.val hm,hfa,hfd]
    exact hval

lemma onCells_injective_of_twoAtomFaithful (n : ℕ)
    (hn : Function.Injective (F.onCells n))
    (hsur : Function.Surjective (F.onCells (n+1)))
    (hgen : ∀ x : C.Cell, C.source (n+1) x = x →
      C.TopSequence n (A.TopGenerator F n) x)
    (hreflect : ∀ x : C.Cell, truncate n false (F.map x) = F.map x → C.source n x = x)
    (hh : A.TwoAtomFaithful F n) : Function.Injective (F.onCells (n+1)) :=
  A.onCells_injective_of_exchange F n hn hgen (A.whiskerFaithful_of_twoAtomFaithful F hh)
    (A.hasAdjacentExchange_of_twoAtomFaithful F n hn hsur hgen hreflect hh)
end Thomason.DirectedComplex.RankedAtoms

end

noncomputable section
universe u v w z


namespace Thomason.GrayRecursive.IntervalHom
open CategoryTheory DirectedComplex Table OmegaCategory NormalizedChains

lemma chainComparison_onCells_injective_of_twoAtomFaithful
    {N : ℕ} {P : Type u} [LinearOrder P] (e : Fin (N+1) ≃o P) (n : ℕ)
    (h : ∀ k, 2 ≤ k → k < n →
      (Prism.Basis.ofOrderIso e).TwoAtomFaithful (chainComparison (NormalizedChains.complex P)) k) :
    Function.Injective ((chainComparison (NormalizedChains.complex P)).onCells n) := by
  let := Fintype.ofEquiv (Fin (N+1)) e.toEquiv
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 2
    · exact (chainComparison (NormalizedChains.complex P)).onCells_injective_mono hn
        (chainComparison_poset_twocells_bijective P).1
    have hex : ∃ k, n = k+1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    obtain ⟨k,rfl⟩ := hex
    have hk : 2 ≤ k := by omega
    have hlow (j : ℕ) (hj : j < k+1) :
        Function.Injective ((chainComparison (NormalizedChains.complex P)).onCells j) :=
      ih j hj (fun t ht htj => h t ht (htj.trans hj))
    exact (Prism.Basis.ofOrderIso e).onCells_injective_of_twoAtomFaithful
      (chainComparison (NormalizedChains.complex P)) k
      (hlow k (Nat.lt_succ_self k))
      (chainComparison_finiteSimplex_surjective_of_lower_injective P (k+1) hlow)
      (tensor_top_sequence e k)
      (chainComparison_reflects_dimension (Prism.Basis.ofOrderIso e) k)
      (h k hk (Nat.lt_succ_self k))

def finLiftOrderIso (k : ℕ) : Fin k ≃o ULift.{u} (Fin k) where
  toEquiv := Equiv.ulift.symm
  map_rel_iff' := Iff.rfl

def standardPrismBasis (m : ℕ) :
    RankedAtoms (NormalizedChains.complex (ULift.{u} (Fin (m+3)))).cylinder :=
  Prism.Basis.ofOrderIso (N := m+2) (finLiftOrderIso (m+3))

theorem fullMain_of_standard_twoAtomFaithful
    (h : ∀ m k : ℕ, 2 ≤ k → k ≤ m+2 →
      (standardPrismBasis.{u} m).TwoAtomFaithful
        (chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3))))) k) :
    FullMain.{u} := by
  apply fullMain_of_standardSimplexComparison_isIso
  intro m
  apply chainComparison_finiteSimplex_isIso_of_injective
  apply (chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3))))).map_injective_of_onCells_injective
    (n := m+3)
    (tensor_truncated (NormalizedChains.table_truncated_of_card_le (n := m+2) (by simp)))
  apply chainComparison_onCells_injective_of_twoAtomFaithful
    (N := m+2) (finLiftOrderIso (m+3)) (m+3)
  intro k hk hm
  exact h m k hk (by omega)

lemma chainComparison_onCells_injective_of_local_exchange
    {N : ℕ} {P : Type u} [LinearOrder P] (e : Fin (N+1) ≃o P) (n : ℕ)
    (h : ∀ k, 2 ≤ k → k < n →
      (Prism.Basis.ofOrderIso e).WhiskerFaithful (chainComparison (NormalizedChains.complex P)) k ∧
      (Prism.Basis.ofOrderIso e).HasAdjacentExchange (chainComparison (NormalizedChains.complex P)) k) :
    Function.Injective ((chainComparison (NormalizedChains.complex P)).onCells n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 2
    · exact (chainComparison (NormalizedChains.complex P)).onCells_injective_mono hn
        (chainComparison_poset_twocells_bijective P).1
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
    obtain ⟨hw,he⟩ := h k (by omega) (Nat.lt_succ_self k)
    exact (Prism.Basis.ofOrderIso e).onCells_injective_of_exchange
      (chainComparison (NormalizedChains.complex P)) k
      (ih k (Nat.lt_succ_self k) (fun t ht htj => h t ht (by omega)))
      (tensor_top_sequence e k) hw he

theorem fullMain_of_standard_local_exchange
    (h : ∀ m k : ℕ, 2 ≤ k → k ≤ m+2 →
      (standardPrismBasis.{u} m).WhiskerFaithful
        (chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3))))) k ∧
      (standardPrismBasis.{u} m).HasAdjacentExchange
        (chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3))))) k) :
    FullMain.{u} := by
  apply fullMain_of_standardSimplexComparison_isIso
  intro m
  apply chainComparison_finiteSimplex_isIso_of_injective
  apply (chainComparison (NormalizedChains.complex (ULift.{u} (Fin (m+3))))).map_injective_of_onCells_injective
    (n := m+3)
    (tensor_truncated (NormalizedChains.table_truncated_of_card_le (n := m+2) (by simp)))
  apply chainComparison_onCells_injective_of_local_exchange
    (N := m+2) (finLiftOrderIso (m+3)) (m+3)
  intro k hk hm
  exact h m k hk (by omega)
end Thomason.GrayRecursive.IntervalHom

end

end OAI
