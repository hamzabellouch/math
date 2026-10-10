import OAI.Combinatorics.HadwigerCounterexample.PrimalChannelTests
import OAI.Combinatorics.HadwigerCounterexample.CellPruning

namespace OAI

/-! # Unary Records -/

noncomputable section
namespace HadwigerCounterexample
open Matrix LinearMap Module Submodule Finset
open scoped BigOperators
variable {p : Shape} {n N : ℕ}

/-- records of x indexed by opposite pin plan signs -/
abbrev Ledger {p : Shape} {n} (f : Plan p n) :=
  ∀ z, Mat (Fin (dim (f z))) (JointIdx p n)

instance fintypeLedger (f : Plan p n) : Fintype (Ledger f) := by
  classical
  letI (z : Place p) : Fintype (Mat (Fin (dim (f z))) (JointIdx p n)) := inferInstance
  exact inferInstance

theorem ledger_dim (f : Plan p n) :
    dim (Ledger f)=planRank f*Fintype.card (JointIdx p n) := by
  unfold Ledger dim planRank
  rw [finrank_pi_fintype,Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => (dim_mat _ _).trans (by simp)

def entries (f : Pin p n N) (x : UnitType p n N) : Ledger f.sp :=
  fun z => (pack (f.sp z))ᵀ * (f.target z)ᵀ * images x (flipZ p z)

theorem entries_val (f : Pin p n N) {x y : UnitType p n N} (h : f.agree y)
    (z) : entries f x z= (pack (f.sp z))ᵀ * actual p y x z := by
  have he := Pin.agree_pack.mp h z
  unfold entries actual
  rw [← transpose_mul,← he,transpose_mul,Matrix.mul_assoc]

theorem entries_rows (f : Pin p n N) {x y x' y' : UnitType p n N}
    (h : f.agree y) (h' : f.agree y') (hg : entries f x=entries f x') :
    rowAgree f.sp (actual p y x) (actual p y' x') := by
  intro z u hu v
  have he : (pack (f.sp z))ᵀ * actual p y x z= (pack (f.sp z))ᵀ * actual p y' x' z := by
    rw [←entries_val f h, ←entries_val f h',hg]
  obtain ⟨r,rfl⟩ := (pack_mem_iff ..).mp hu
  have hE (P : Mat (JointIdx p n) (JointIdx p n)) :
      evmat P (pack (f.sp z) *ᵥ r) v=evmat ((pack (f.sp z))ᵀ * P) r v := by
    unfold evmat
    rw [←Matrix.mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_comm]
  rw [hE,hE,he]

theorem rowAgree_step {a : Plan p n} {X Y Z}
    (h : rowAgree a X Y) (he : rowAgree a Z Y) :
    rowAgree a X Z := fun z u hu v => (h z u hu v).trans (he z u hu v).symm

variable {I : Type} [Fintype I]
namespace Volley
variable (v w : Volley p n I)

/-- Deterministic realization promise at two orientations. Can be required
only if both accept the specific parameter pair and their keys agree. -/
def promised (t : Tagging p I) (m : Mixer p n)
    (a b : Plan p n) (x y : UnitType p n N) :=
  v.legal t ∧ w.legal t ∧ v.roleMatch w t ∧
    ∃ Q : Cross p n, v.realized w t m Q ∧ w.realized v t m (reciprocal p Q) ∧
    rowAgree (v.frozen a t) Q (actual p x y) ∧
    rowAgree (w.frozen b t) (reciprocal p Q) (actual p y x)

private theorem carried_heavy {T : Type} [Fintype T] {w : Wgt T} {p : T→Prop}
    (x) (hx : onW w p x ≠ 0) : p x :=
  Classical.byContradiction fun h => hx (normW_carried (subW_carried w p) x h)

set_option maxHeartbeats 800000 in
theorem record_hit {t : Tagging p I} (m : Mixer p n)
    {a b : Pin p n N} {μ δ : Wgt (UnitType p n N)}
    (U V : UnitType p n N → Prop) (u : Keys (p:=p) t N)
    (ha : ∀ x, U x → a.agree x ∧ (∀ i,frameLaw m (onSide x i)) ∧ v.keys t x=u)
    (hb : ∀ x, V x → b.agree x ∧ (∀ i,frameLaw m (onSide x i)) ∧ w.keys t x=u)
    {ζ : ℝ} {q : ℕ}
    (h : ∀ x,U x → ∀ y,V y → v.promised w t m a.sp b.sp x y)
    (hv : v.avoids a.sp q) (hw : w.avoids b.sp q)
    (hz : ζ ≤ 0.004) (hK : ζ*(kslots p I) ≤ 0.004)
    (hμ : SubLaw μ) (hδ : SubLaw δ)
    (hA : a.clear ζ μ) (hB : b.clear ζ δ)
    (hN : 100 ≤ N) (hT : (dim (CheckGram p n) : ℝ) ≤ 0.01*N)
    (L : ℝ)
    (hLf : bp (dim (Ledger (v.frozen a.sp t))) ≤ L)
    (hLg : bp (dim (Ledger (w.frozen b.sp t))) ≤ L) :
    hit N * (pr μ U * pr δ V) ≤ pr (pairW μ δ) (fun x => U x.1 ∧ V x.2 ∧
      (rawHoles m).conflict x.1 x.2) +
      (hit N*tau N (kslots p I)*L)*(pr μ U+pr δ V) := by
  classical
  let k := kslots p I
  obtain ⟨x0,hx⟩ :
      ∃ x0 : UnitType p n N,∀ x,U x → (Pin.make (v.frozen a.sp t) x0).agree x := by
    by_cases he : ∃ x,U x
    · obtain ⟨x0,hx0⟩ := he
      exact ⟨x0,fun x hx => key_pin t (ha x0 hx0).1 (ha x hx).1
        ((ha x0 hx0).2.2.trans (ha x hx).2.2.symm)⟩
    exact ⟨0,fun x h => (he ⟨x,h⟩).elim⟩
  let f := Pin.make (v.frozen a.sp t) x0
  obtain ⟨y0,hy⟩ :
      ∃ y0 : UnitType p n N,∀ y,V y → (Pin.make (w.frozen b.sp t) y0).agree y := by
    by_cases he : ∃ y,V y
    · obtain ⟨y0,hy0⟩ := he
      exact ⟨y0,fun y hy => key_pin t (hb y0 hy0).1 (hb y hy).1
        ((hb y0 hy0).2.2.trans (hb y hy).2.2.symm)⟩
    exact ⟨0,fun y h => (he ⟨y,h⟩).elim⟩
  let g := Pin.make (w.frozen b.sp t) y0
  apply prune_pairs μ δ hμ hδ U V (entries g) (entries f)
    (fun x => (rawHoles m).conflict x.1 x.2) (hit N) (tau N k)
    (bp_pos _).le (bp_pos _) _ _
  · intro i j hi hj
    let F := memberC U (entries g) i
    let G := memberC V (entries f) j
    let α := onW μ F
    let β := onW δ G
    change tau N k≤pr μ F at hi
    change tau N k≤pr δ G at hj
    have hL (v : Volley p n I) {a} (h : v.avoids a q) :
        planRank (v.frozen a t)=planRank a+k := by
      unfold k
      rw [← v.key_slots (t:=t) h]; exact (plan_add_rank a (v.keyPlan t)).symm
    obtain ⟨hα,hF⟩ := in_clear (f:=f) hz hK hμ hA le_sup_left (hL v hv)
      F (fun x h => hx x h.1) hi
    obtain ⟨hβ,hG⟩ := in_clear (f:=g) hz hK hδ hB le_sup_left (hL w hw)
      G (fun x h => hy x h.1) hj
    obtain ⟨x,xX,_⟩ := exists_of_pr_pos hμ.nz (lt_of_lt_of_le (bp_pos _) hi)
    obtain ⟨y,yY,_⟩ := exists_of_pr_pos hδ.nz (lt_of_lt_of_le (bp_pos _) hj)
    have h1 x (h : α x≠0) : F x := carried_heavy _ h
    have h2 y (h : β y≠0) : G y := carried_heavy _ h
    obtain ⟨hr,ht,hL,Q,hZ,hI,hQ,hQ'⟩ := h x xX.1 y yY.1
    have he x' (hs : α x'≠0) y' (hs' : β y'≠0) :
        rowAgree f.sp (actual p x' y') Q ∧
        rowAgree g.sp (actual p y' x') (reciprocal p Q) := by
      have ha := h1 x' hs
      have hb := h2 y' hs'
      exact ⟨rowAgree_step (entries_rows f (hx x' ha.1) (hx x xX.1) (hb.2.trans yY.2.symm)) hQ,
        rowAgree_step (entries_rows g (hy y' hb.1) (hy y yY.1) (ha.2.trans xX.2.symm)) hQ'⟩
    refine (gram_hit Q hα hβ hF hG he hN hT).trans (pr_on_mono (pairW_law hα hβ).nz ?_)
    rintro ⟨x,y⟩ hxy heq
    obtain ⟨_,hx,hX⟩ := ha x (h1 x (left_ne_zero_of_mul hxy)).1
    obtain ⟨_,hy,hY⟩ := hb y (h2 y (right_ne_zero_of_mul hxy)).1
    have he : scalarBlocks p (actual p x y) = scalarBlocks p Q := congrArg Prod.fst heq
    have he' : scalarBlocks p (actual p y x) = scalarBlocks p (reciprocal p Q) := by
      rw [← reciprocal_actual x y]; exact congrArg Prod.snd heq
    apply v.realized_conflicts w m x y hr ht hx hy (hX.trans hY.symm) hL
    · intro i j μ hμ; rw [contract_scalars _ _ he]; exact hZ i j _ hμ
    · intro i j μ hμ; rw [contract_scalars _ _ he']; exact hI i j _ hμ
  · rw [card_space]; exact hLg
  rw [card_space]; exact hLf
end Volley
end HadwigerCounterexample

end

end OAI
