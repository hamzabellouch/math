import Mathlib
import OAI.Algebra.GroupRing.GraphQuotient

namespace OAI

noncomputable section

namespace TorsionFreeZeroDivisors.SeparatorLevels

section
open scoped BigOperators
variable {V : Type*} [Fintype V]

/-- Canonical finite vertex level profile; its mass is not an extra assumption. -/
def profile (level : V → ℤ) (z : ℤ) : ℕ :=
  (Finset.univ.filter (fun v=>level v=z)).card

theorem profile_mass (level : V → ℤ) (s : Finset ℤ) :
    ∑ z ∈ s,profile level z ≤ Fintype.card V := by
  classical
  unfold profile
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

theorem select_vertices (level : V → ℤ) (center : ℤ) :
    ∃ kL kR : ℕ,
      (profile level (center-kL) + profile level (center+kR) + 2*(kL+kR) : ℝ) ≤
        2*Real.sqrt 2*Real.sqrt (Fintype.card V) :=
  select (profile level) _ center (profile_mass level)

/-- A median genuine BFS level, including the empty graph and repeated levels. -/
theorem exists_median (level : V → ℕ) :
    ∃ center : ℕ,
      2*(Finset.univ.filter (fun v=>level v<center)).card ≤ Fintype.card V ∧
      2*(Finset.univ.filter (fun v=>center<level v)).card ≤ Fintype.card V := by
  classical
  let P := fun k => Fintype.card V ≤
    2*(Finset.univ.filter (fun v=>level v≤k)).card
  have hex : ∃ k,P k := by
    refine ⟨Finset.univ.sup level,?_⟩
    have hh : ∀ v,level v ≤ Finset.univ.sup level :=
      fun v=>Finset.le_sup (Finset.mem_univ v)
    simp only [P,Finset.filter_true_of_mem (fun v _ => hh v),Finset.card_univ]
    omega
  let center := Nat.find hex
  have hc : P center := Nat.find_spec hex
  refine ⟨center,?_,?_⟩
  · cases he : center with
    | zero => simp only [Nat.not_lt_zero,Finset.filter_false,Finset.card_empty,mul_zero]
              exact Nat.zero_le _
    | succ k =>
      have hk : k < Nat.find hex := by change k<center;omega
      have hp := Nat.find_min hex hk
      change ¬ P k at hp
      simp only [Nat.lt_succ_iff]
      dsimp [P] at hp
      omega
  · have hparts : (Finset.univ.filter (fun v=>level v≤center)).card+
        (Finset.univ.filter (fun v=>center<level v)).card=Fintype.card V := by
      have hh := Finset.card_filter_add_card_filter_not
        (s:=Finset.univ) (p:=fun v=>level v≤center)
      simpa only [not_le,Finset.card_univ] using hh
    dsimp [P] at hc
    omega

/-- The selected levels are literal finite graph levels, and both exterior
regions already satisfy the stronger half-size bound. -/
theorem selected_levels (level : V → ℕ) :
    ∃ center kL kR : ℕ,
      (profile (fun v=>(level v:ℤ)) ((center:ℤ)-kL) +
       profile (fun v=>(level v:ℤ)) ((center:ℤ)+kR) + 2*(kL+kR) : ℝ) ≤
        2*Real.sqrt 2*Real.sqrt (Fintype.card V) ∧
      2*(Finset.univ.filter (fun v=>(level v:ℤ)<(center:ℤ)-kL)).card ≤ Fintype.card V ∧
      2*(Finset.univ.filter (fun v=>(center:ℤ)+kR<(level v:ℤ))).card ≤ Fintype.card V := by
  classical
  obtain ⟨center,hcl,hcr⟩ := exists_median level
  obtain ⟨kL,kR,hk⟩ := select_vertices (fun v=>(level v:ℤ)) center
  refine ⟨center,kL,kR,hk,?_,?_⟩
  · have hs : (Finset.univ.filter (fun v=>(level v:ℤ)<(center:ℤ)-kL))⊆
        (Finset.univ.filter (fun v=>level v<center)) := by
      intro v hv
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
      omega
    have hh := Finset.card_le_card hs
    omega
  · have hs : (Finset.univ.filter (fun v=>(center:ℤ)+kR<(level v:ℤ)))⊆
        (Finset.univ.filter (fun v=>center<level v)) := by
      intro v hv
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
      omega
    have hh := Finset.card_le_card hs
    omega

omit [Fintype V] in
/-- A single removed level prevents an edge from passing across it. -/
theorem below_closed {R : V → V → Prop} (level : V → ℤ)
    (hstep : ∀ x y,R x y → level y ≤ level x+1) {b : ℤ} {x y : V}
    (hx : level x<b) (hy : level y≠b) (hxy : R x y) : level y<b := by
  have hh := hstep x y hxy
  omega

omit [Fintype V] in
theorem above_closed {R : V → V → Prop} (level : V → ℤ)
    (hstep : ∀ x y,R x y → level x ≤ level y+1) {b : ℤ} {x y : V}
    (hx : b<level x) (hy : level y≠b) (hxy : R x y) : b<level y := by
  have hh := hstep x y hxy
  omega

omit [Fintype V] in
theorem band_closed {R : V → V → Prop} (level : V → ℤ)
    (hstep : ∀ x y,R x y → level y ≤ level x+1 ∧ level x ≤ level y+1)
    {lo hi : ℤ} {x y : V} (hx : lo<level x ∧ level x<hi)
    (hyl : level y≠lo) (hyh : level y≠hi) (hxy : R x y) :
    lo<level y ∧ level y<hi :=
  ⟨above_closed level (fun x y h=>(hstep x y h).2) hx.1 hyl hxy,
   below_closed level (fun x y h=>(hstep x y h).1) hx.2 hyh hxy⟩

end

variable {V : Type*} (G : SimpleGraph V) (root : V)

theorem bfs_step (hconn : G.Connected) {x y : V} (hxy : G.Adj x y) :
    (G.dist root y:ℤ) ≤ (G.dist root x:ℤ)+1 ∧
    (G.dist root x:ℤ) ≤ (G.dist root y:ℤ)+1 := by
  have h₁ := hconn.dist_triangle (u:=root) (v:=x) (w:=y)
  have h₂ := hconn.dist_triangle (u:=root) (v:=y) (w:=x)
  rw [G.dist_eq_one_iff_adj.mpr hxy] at h₁
  rw [G.dist_eq_one_iff_adj.mpr hxy.symm] at h₂
  exact ⟨by exact_mod_cast h₁,by exact_mod_cast h₂⟩

end TorsionFreeZeroDivisors.SeparatorLevels

namespace TorsionFreeZeroDivisors.RecursiveSeparator
open scoped Classical
variable {V I : Type} [DecidableEq V] [Fintype I] [DecidableEq I]
    (R : V→V→Prop) (S remove : Finset V) (label : V→I)

def Split.of_fibers (hsub : remove⊆S)
    (hclosed : ∀ x∈S\remove,∀ y∈S\remove,R x y→label x=label y)
    (hsize : ∀ i,3*((S\remove).filter (fun x=>label x=i)).card≤2*S.card)
    (hcost : (remove.card:ℝ)≤2*Real.sqrt 2*Real.sqrt S.card) : Split R S where
  remove := remove
  parts := Finset.univ.image (fun i=>(S\remove).filter (fun x=>label x=i))
  remove_subset := hsub
  cover := by
    ext x
    simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and,id_eq]
    constructor
    · rintro ⟨b,⟨i,rfl⟩,hx⟩
      exact (Finset.mem_filter.mp hx).1
    · intro hx
      exact ⟨(S\remove).filter (fun y=>label y=label x),⟨label x,rfl⟩,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩
  disjoint := by
    intro b hb c hc hbc
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hc
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hi := (Finset.mem_filter.mp hx).2
    have hj := (Finset.mem_filter.mp hy).2
    have he : i=j := hi.symm.trans hj
    exact hbc (by rw [he])
  closed := by
    intro b hb x hx y hy hxy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hx,hi⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hy,(hclosed x hx y hy hxy).symm.trans hi⟩
  size := by
    intro b hb
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hb
    exact hsize i
  cost := hcost
end TorsionFreeZeroDivisors.RecursiveSeparator

namespace TorsionFreeZeroDivisors.PlanarMap
open scoped Classical
open SeparatorLevels
variable {V : Type} [Fintype V] {G : SimpleGraph V}

theorem Model.connected_split (M : Model G) (hc : G.Connected) :
    Nonempty (RecursiveSeparator.Split G.Adj Finset.univ) := by
  classical
  have : Nonempty V := hc.nonempty
  let root := Classical.ofNonempty (α:=V)
  let level : V→ℕ := fun v=>G.dist v root
  obtain ⟨center,kL,kR,hcost,hbelow,habove⟩ := selected_levels level
  let L : ℤ := (center:ℤ)-kL
  let U : ℤ := (center:ℤ)+kR
  have hLU : L≤U := by dsimp [L,U];omega
  let A := Finset.univ.filter (fun v=>L<(level v:ℤ) ∧ (level v:ℤ)<U)
  have hA (v : V) : v∈A↔L<(level v:ℤ) ∧ (level v:ℤ)<U := by simp only [A,Finset.mem_filter,Finset.mem_univ,true_and]
  have hex : ∃ cut side : Finset V,cut⊆A ∧ cut.card≤2*(kL+kR) ∧
      3*(A.filter (fun v=>v∉cut ∧ v∈side)).card≤2*A.card ∧
      3*(A.filter (fun v=>v∉cut ∧ v∉side)).card≤2*A.card ∧
      ∀ v∈A,∀ w∈A,v∉cut→w∉cut→G.Adj v w→(v∈side↔w∈side) := by
    by_cases hk : kL≤center
    · obtain ⟨C,D,hs,hcC,h₁,h₂,hsep⟩ := M.annular_separator hc root (center-kL) (center+kR) A (by
        intro v hv
        have hh := (hA v).mp hv
        change center-kL<level v ∧ level v≤center+kR
        dsimp [L,U] at hh
        omega)
      refine ⟨C,D,hs,?_,h₁,h₂,hsep⟩
      have he : center+kR-(center-kL)=kL+kR := by omega
      rwa [he] at hcC
    · obtain ⟨C,D,hs,hcC,h₁,h₂,hsep⟩ := M.ball_separator hc root (center+kR) A (by
        intro v hv
        have hh := (hA v).mp hv
        change level v≤center+kR
        dsimp [U] at hh
        omega)
      exact ⟨C,D,hs,by omega,h₁,h₂,hsep⟩
  obtain ⟨C,D,hCA,hC,h₁,h₂,hsep⟩ := hex
  let low := Finset.univ.filter (fun v=>(level v:ℤ)<L)
  let high := Finset.univ.filter (fun v=>U<(level v:ℤ))
  let eL := Finset.univ.filter (fun v=>(level v:ℤ)=L)
  let eU := Finset.univ.filter (fun v=>(level v:ℤ)=U)
  let remove := eL∪eU∪C
  have hremove (v : V) : v∈remove↔(level v:ℤ)=L ∨ (level v:ℤ)=U ∨ v∈C := by
    simp only [remove,eL,eU,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,or_assoc]
  have hnone {v : V} (hv : v∈Finset.univ\remove) : (level v:ℤ)≠L ∧ (level v:ℤ)≠U ∧ v∉C := by
    have hh := (Finset.mem_sdiff.mp hv).2
    simpa only [hremove,not_or] using hh
  let label : V→Fin 4 := fun v=>if (level v:ℤ)<L then 0 else if U<(level v:ℤ) then 1 else if v∈D then 2 else 3
  have hl0 {v : V} (hv : label v=0) : (level v:ℤ)<L := by
    dsimp [label] at hv
    split_ifs at hv with h₀ h₁ h₂ <;> simp_all
  have hl1 {v : V} (hv : label v=1) : U<(level v:ℤ) := by
    dsimp [label] at hv
    split_ifs at hv with h₀ h₁ h₂ <;> simp_all
  have hl2 {v : V} (hv : label v=2) : ¬(level v:ℤ)<L ∧ ¬U<(level v:ℤ) ∧ v∈D := by
    dsimp [label] at hv
    split_ifs at hv with h₀ h₁ h₂ <;> simp_all
  have hl3 {v : V} (hv : label v=3) : ¬(level v:ℤ)<L ∧ ¬U<(level v:ℤ) ∧ v∉D := by
    dsimp [label] at hv
    split_ifs at hv with h₀ h₁ h₂ <;> simp_all
  have hglobal : A.card≤Fintype.card V := Finset.card_le_univ _
  have hsize (i : Fin 4) : 3*((Finset.univ\remove).filter (fun v=>label v=i)).card≤2*(Finset.univ : Finset V).card := by
    rw [Finset.card_univ]
    fin_cases i
    · change 3*((Finset.univ\remove).filter (fun v=>label v=(0:Fin 4))).card≤2*Fintype.card V
      have hs : (Finset.univ\remove).filter (fun v=>label v=0)⊆low := by
        intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl0 (Finset.mem_filter.mp hv).2⟩
      have hh := Finset.card_le_card hs
      change 2*low.card≤Fintype.card V at hbelow
      omega
    · change 3*((Finset.univ\remove).filter (fun v=>label v=(1:Fin 4))).card≤2*Fintype.card V
      have hs : (Finset.univ\remove).filter (fun v=>label v=1)⊆high := by
        intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl1 (Finset.mem_filter.mp hv).2⟩
      have hh := Finset.card_le_card hs
      change 2*high.card≤Fintype.card V at habove
      omega
    · change 3*((Finset.univ\remove).filter (fun v=>label v=(2:Fin 4))).card≤2*Fintype.card V
      have hs : (Finset.univ\remove).filter (fun v=>label v=2)⊆A.filter (fun v=>v∉C ∧ v∈D) := by
        intro v hv
        obtain ⟨hr,he⟩ := Finset.mem_filter.mp hv
        have hn := hnone hr
        have hd := hl2 he
        exact Finset.mem_filter.mpr ⟨(hA v).mpr (by omega),hn.2.2,hd.2.2⟩
      have hh := Finset.card_le_card hs
      omega
    · change 3*((Finset.univ\remove).filter (fun v=>label v=(3:Fin 4))).card≤2*Fintype.card V
      have hs : (Finset.univ\remove).filter (fun v=>label v=3)⊆A.filter (fun v=>v∉C ∧ v∉D) := by
        intro v hv
        obtain ⟨hr,he⟩ := Finset.mem_filter.mp hv
        have hn := hnone hr
        have hd := hl3 he
        exact Finset.mem_filter.mpr ⟨(hA v).mpr (by omega),hn.2.2,hd.2.2⟩
      have hh := Finset.card_le_card hs
      omega
  have hclosed : ∀ v∈Finset.univ\remove,∀ w∈Finset.univ\remove,G.Adj v w→label v=label w := by
    intro v hv w hw he
    have hnV := hnone hv
    have hnW := hnone hw
    have hstep : (level w:ℤ)≤(level v:ℤ)+1 ∧ (level v:ℤ)≤(level w:ℤ)+1 := by
      have h := bfs_step G root hc he
      simpa only [SimpleGraph.dist_comm,level] using h
    by_cases hL : (level v:ℤ)<L
    · have hwL : (level w:ℤ)<L := by omega
      simp only [label,ite_eq_left hL,ite_eq_left hwL]
    · by_cases hU : U<(level v:ℤ)
      · have hwU : U<(level w:ℤ) := by omega
        have hwL : ¬(level w:ℤ)<L := by omega
        simp only [label,ite_eq_right hL,ite_eq_right hwL,ite_eq_left hU,ite_eq_left hwU]
      · have hvA : v∈A := (hA v).mpr (by omega)
        have hwA : w∈A := (hA w).mpr (by omega)
        have hwL : ¬(level w:ℤ)<L := by have := (hA w).mp hwA;omega
        have hwU : ¬U<(level w:ℤ) := by have := (hA w).mp hwA;omega
        have hd := hsep v hvA w hwA hnV.2.2 hnW.2.2 he
        simp only [label,ite_eq_right hL,ite_eq_right hU,ite_eq_right hwL,ite_eq_right hwU,hd]
  have hrCost : (remove.card:ℝ)≤2*Real.sqrt 2*Real.sqrt (Finset.univ : Finset V).card := by
    have hcn : remove.card≤eL.card+eU.card+C.card :=
      (Finset.card_union_le (eL∪eU) C).trans (Nat.add_le_add_right (Finset.card_union_le eL eU) _)
    have hbound : remove.card≤eL.card+eU.card+2*(kL+kR) := by omega
    have hre : (remove.card:ℝ)≤(eL.card:ℝ)+eU.card+2*(kL+kR) := by exact_mod_cast hbound
    rw [Finset.card_univ]
    exact hre.trans hcost
  exact ⟨RecursiveSeparator.Split.of_fibers G.Adj Finset.univ remove label
    (Finset.subset_univ _) hclosed hsize hrCost⟩

end TorsionFreeZeroDivisors.PlanarMap

namespace TorsionFreeZeroDivisors.RecursiveSeparator.Split
open scoped Classical
variable {V W : Type} [DecidableEq V] [DecidableEq W]
    {R : V→V→Prop} {Q : W→W→Prop} {S : Finset V}

def map (P : Split R S) (f : V ↪ W) (hR : ∀ v w,Q (f v) (f w)→R v w) :
    Split Q (S.map f) where
  remove := P.remove.map f
  parts := P.parts.image (fun b=>b.map f)
  remove_subset := Finset.map_subset_map.mpr P.remove_subset
  cover := by
    rw [←Finset.map_sdiff]
    ext x
    constructor
    · intro hx
      obtain ⟨b,hb,hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hb
      subst b
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
      refine Finset.mem_map.mpr ⟨v,?_,rfl⟩
      rw [←P.cover]
      exact Finset.mem_biUnion.mpr ⟨c,hc,hv⟩
    · intro hx
      obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
      rw [←P.cover] at hv
      obtain ⟨b,hb,hv⟩ := Finset.mem_biUnion.mp hv
      exact Finset.mem_biUnion.mpr ⟨b.map f,Finset.mem_image.mpr ⟨b,hb,rfl⟩,
        Finset.mem_map.mpr ⟨v,hv,rfl⟩⟩
  disjoint := by
    intro b hb c hc hbc
    obtain ⟨d,hd,he⟩ := Finset.mem_image.mp hb
    subst b
    obtain ⟨e,he,hf⟩ := Finset.mem_image.mp hc
    subst c
    exact (Finset.disjoint_map f).mpr (P.disjoint hd he (fun h=>hbc (congrArg (fun b=>b.map f) h)))
  closed := by
    intro b hb x hx y hy hxy
    obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hb
    subst b
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
    rw [←Finset.map_sdiff] at hy
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hy
    exact Finset.mem_map.mpr ⟨w,P.closed c hc v hv w hw (hR v w hxy),rfl⟩
  size := by
    intro b hb
    obtain ⟨c,hc,he⟩ := Finset.mem_image.mp hb
    subst b
    simpa only [Finset.card_map] using P.size c hc
  cost := by simpa only [Finset.card_map] using P.cost
end TorsionFreeZeroDivisors.RecursiveSeparator.Split

end

end OAI
