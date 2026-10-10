import Mathlib
import OAI.Combinatorics.KServer.RankProportions
import OAI.Combinatorics.KServer.Rounding

namespace OAI

/-! A literal finite complete-prefix tree, numbered parent-before-child. The
unused words are retained, as required for an unconditioned finite key tape. -/
noncomputable section
open scoped BigOperators
namespace KServer.PrefixTree
variable (A:Type) [Fintype A] (L:ℕ)

abbrev Vertex := (j:Fin (L+1)) × (Fin j.val→A)

def root : Vertex A L := ⟨0,Fin.elim0⟩
instance : Nonempty (Vertex A L) := ⟨root A L⟩

def code (v:Vertex A L) : Lex (ℕ×ℕ) :=
  toLex (v.1.val,(Fintype.equivFin (Fin v.1.val→A) v.2).val)

lemma code_injective : Function.Injective (code A L) := by
  rintro ⟨j,f⟩ ⟨j',g⟩ h
  have hj:j=j':=Fin.ext (congrArg (fun p:Lex (ℕ×ℕ)=>(ofLex p).1) h)
  subst j'
  have hf:(Fintype.equivFin (Fin j.val→A) f).val=(Fintype.equivFin (Fin j.val→A) g).val :=
    congrArg (fun p:Lex (ℕ×ℕ)=>(ofLex p).2) h
  have he:f=g:=(Fintype.equivFin _).injective (Fin.ext hf)
  subst g
  rfl

instance : LinearOrder (Vertex A L) := LinearOrder.lift' (code A L) (code_injective A L)

lemma root_le (v:Vertex A L) : root A L≤v := by
  by_cases hj:v.1.val=0
  · have he:v=root A L:=by
      rcases v with ⟨j,f⟩
      have hj':j=0:=Fin.ext hj
      subst j
      congr
      exact funext (fun i=>Fin.elim0 i)
    rw [he]
  · change code A L (root A L)≤code A L v
    exact Prod.Lex.toLex_le_toLex.mpr (Or.inl (Nat.pos_of_ne_zero hj))

instance : NeZero (Fintype.card (Vertex A L)) := ⟨Nat.ne_of_gt Fintype.card_pos⟩

def numbering : Fin (Fintype.card (Vertex A L)) ≃o Vertex A L :=
  Fintype.orderIsoFinOfCardEq _ rfl

lemma numbering_zero : numbering A L 0=root A L := by
  apply le_antisymm
  · rw [←(numbering A L).apply_symm_apply (root A L)]
    apply (numbering A L).monotone
    exact Fin.zero_le _
  · exact root_le A L _

def parent (v:Vertex A L) : Vertex A L :=
  if h:v.1.val=0 then root A L
  else ⟨⟨v.1.val-1,by omega⟩,fun i=>v.2 ⟨i.val,by have hi : i.val<v.1.val-1 := i.isLt; omega⟩⟩

omit [Fintype A] in
lemma parent_root : parent A L (root A L)=root A L := by simp [parent,root]

lemma parent_lt {v:Vertex A L} (hv:v≠root A L) : parent A L v<v := by
  have hj:v.1.val≠0:=by
    intro h
    apply hv
    rcases v with ⟨j,f⟩
    have hj:j=0:=Fin.ext h
    subst j
    congr
    exact funext (fun i=>Fin.elim0 i)
  change code A L (parent A L v)<code A L v
  rw [parent,dite_eq_right hj]
  apply Prod.Lex.toLex_lt_toLex.mpr
  left
  dsimp only [code]
  omega

def tree : TreeRounding.Tree (Fintype.card (Vertex A L)) where
  parent v := (numbering A L).symm (parent A L (numbering A L v))
  root := by rw [numbering_zero,parent_root,←numbering_zero]; exact (numbering A L).symm_apply_apply 0
  lower v hv := by
    have h:(numbering A L v)≠root A L:=by
      intro he
      apply hv
      apply (numbering A L).injective
      rw [he,numbering_zero]
    have hp:=parent_lt A L h
    have he: (numbering A L).symm (parent A L (numbering A L v))<v :=by
      simpa only [(numbering A L).symm_apply_apply] using (numbering A L).symm.strictMono hp
    exact he

end KServer.PrefixTree

end


/-! Literal cells and hidden labeled counts in the retained complete-prefix
hierarchy.  Empty words/nodes are not removed. Child counts partition the
parent exactly, including repeated physical server locations. -/
noncomputable section
open scoped BigOperators
open Finset
namespace KServer.HierarchyCounts
attribute [local instance] Classical.propDecidable Classical.decEq
variable {A Y Ω : Type} [Fintype A] [Fintype Ω] {k d : ℕ}

def hit (maps : ℕ → Y → A) (word : Fin d → A) (y : Y) : Prop :=
  ∀ i, maps i.val y=word i

def count (maps : ℕ → Y → A) (word : Fin d → A) (q : Fin k → Y) : ℕ :=
  (univ.filter fun l => hit maps word (q l)).card

omit [Fintype A] in
lemma count_le (maps : ℕ → Y → A) (word : Fin d → A) (q : Fin k → Y) :
    count maps word q ≤ k := by
  exact (card_filter_le _ _).trans_eq (card_univ.trans (Fintype.card_fin k))

omit [Fintype A] in
lemma hit_zero (maps : ℕ → Y → A) (word : Fin 0 → A) (y : Y) : hit maps word y :=
  fun i => Fin.elim0 i

omit [Fintype A] in
lemma count_zero (maps : ℕ → Y → A) (word : Fin 0 → A) (q : Fin k → Y) :
    count maps word q=k := by simp [count,hit_zero]

omit [Fintype A] in
lemma hit_snoc (maps : ℕ → Y → A) (word : Fin d → A) (a : A) (y : Y) :
    hit maps (Fin.snoc word a) y ↔ hit maps word y ∧ maps d y=a := by
  constructor
  · intro h
    exact ⟨fun i=>by simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using h i.castSucc,
      by simpa only [Fin.snoc_last,Fin.val_last] using h (Fin.last d)⟩
  · rintro ⟨h,ha⟩ i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · simpa using ha
    · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using h j

lemma count_sum (maps : ℕ → Y → A) (word : Fin d → A) (q : Fin k → Y) :
    (∑ a : A, count maps (Fin.snoc word a) q)=count maps word q := by
  simp only [count,card_filter,hit_snoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  by_cases h : hit maps word (q l)
  · simp [h]
  · simp [h]

open RankTracking PosteriorRanks

lemma positive_mass {w : Ω → ℝ} (hw : ∀ ρ,0≤w ρ) (H : Ω → ℕ) (ω : Ω)
    (hω : 0<w ω) : 0<PosteriorRanks.mass w H (H ω) := by
  exact hω.trans_le (single_le_sum (fun ρ _=>hw ρ) (by simp [fiber]))

/-- The actual conditional distribution on the true prefix fiber. -/
def conditional (w : Ω → ℝ) (H : Ω → ℕ) (ω ρ : Ω) : ℝ :=
  if H ρ=H ω then w ρ/PosteriorRanks.mass w H (H ω) else 0

lemma conditional_nonneg {w : Ω → ℝ} (hw : ∀ ω,0≤w ω) (H : Ω → ℕ) (ω ρ : Ω) :
    0≤conditional w H ω ρ := by
  unfold conditional
  split_ifs
  · exact div_nonneg (hw ρ) (mass_nonneg hw H (H ω))
  · rfl

lemma conditional_sum (w : Ω → ℝ) (H : Ω → ℕ) (ω : Ω)
    (hm : PosteriorRanks.mass w H (H ω)≠0) : (∑ ρ,conditional w H ω ρ)=1 := by
  unfold conditional
  rw [←sum_filter,←sum_div]
  exact div_self hm

lemma conditional_rank (w : Ω → ℝ) (H : Ω → ℕ) (ω : Ω) (N : Ω → ℕ) (a : ℕ) :
    RankOrder.countRank (conditional w H ω) N a=posterior w H (PosteriorRanks.rank N a) ω := by
  unfold RankOrder.countRank conditional posterior numerator PosteriorRanks.rank
  simp only [ite_mul,zero_mul,div_mul_eq_mul_div]
  rw [←sum_filter,←sum_div]
  rfl

/-- The actual posterior lower bounds simultaneously satisfy both source
superadditivities, even though the labeled counts are arbitrarily dependent. -/
theorem compatible (w : Ω → ℝ) (hw : ∀ ω,0≤w ω) (H : Ω → ℕ) (ω : Ω)
    (hω : 0<w ω) (maps : Ω → ℕ → Y → A) (word : Fin d → A) (q : Ω → Fin k → Y)
    {z : ℝ} (hz : z∈Set.Icc 0 (1/100:ℝ)) :
    (∑ a : A, CompatibleBounds.L k (conditional w H ω)
      (fun ρ=>count (maps ρ) (Fin.snoc word a) (q ρ)) z) ≤
      CompatibleBounds.L k (conditional w H ω) (fun ρ=>count (maps ρ) word (q ρ)) z ∧
    (∑ a : A, CompatibleBounds.M k (conditional w H ω)
      (fun ρ=>count (maps ρ) (Fin.snoc word a) (q ρ))) ≤
      CompatibleBounds.M k (conditional w H ω) (fun ρ=>count (maps ρ) word (q ρ)) ∧
    CompatibleBounds.M k (conditional w H ω) (fun ρ=>count (maps ρ) word (q ρ)) ≤
      ∑ ρ,conditional w H ω ρ*count (maps ρ) word (q ρ) := by
  have hb:=CompatibleBounds.compatible_bounds (conditional w H ω) (conditional_nonneg hw H ω)
    (conditional_sum w H ω (positive_mass hw H ω hω).ne')
    (fun ρ a=>count (maps ρ) (Fin.snoc word a) (q ρ))
    (fun ρ=>by rw [count_sum]; exact count_le _ _ _) hz
  simpa only [count_sum] using hb

lemma conditional_adapted (w : Ω → ℝ) (H : Ω → ℕ) (ρ : Ω) :
    Adapted H (fun ω=>conditional w H ω ρ) := by
  intro ω ω' hh
  simp only [conditional,hh]

lemma rank_adapted (w : Ω → ℝ) (H : Ω → ℕ) (N : Ω → ℕ) (a : ℕ) :
    Adapted H (fun ω=>RankOrder.countRank (conditional w H ω) N a) := by
  simp_rw [conditional_rank]
  exact posterior_adapted w H _

end KServer.HierarchyCounts

end

end OAI
