import Mathlib
import OAI.Combinatorics.MatchingCount.Arithmetic.ArithmeticSize
import OAI.Combinatorics.MatchingCount.Machines.CoinTM1Finite
import OAI.Combinatorics.MatchingCount.Tapes.PhysicalAlphabet
import OAI.Combinatorics.MatchingCount.Tapes.CoinSupport

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream SafeTrace
open scoped Classical

variable {K Λ σ : Type} {Γ : K → Type} [DecidableEq K] [Fintype K]
  [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
abbrev Alpha (K : Type) (Γ : K → Type) := TM2to1.Γ' K Γ
abbrev L1 (K : Type) (Γ : K → Type) (Λ σ : Type) := TM2to1.Λ' K Γ Λ σ
abbrev L2 (K : Type) (Γ : K → Type) (Λ σ : Type) := TM1to1.Λ' (Alpha K Γ) (L1 K Γ Λ σ) σ
abbrev Q (K : Type) (Γ : K → Type) (Λ σ : Type) := CoinTM1.State Bool (L2 K Γ Λ σ) σ

noncomputable def height (S : ∀ k,List (Γ k)) : ℕ := Finset.univ.sup (fun k=>(S k).length)
omit [DecidableEq K] [∀ k,Fintype (Γ k)] in
lemma height_bound (S : ∀ k,List (Γ k)) : StackCost.StackBound S (height S) :=
  fun k=>Finset.le_sup (f:=fun k=>(S k).length) (Finset.mem_univ k)
noncomputable def stackCfg (c : TM2.Cfg Γ Λ σ) : TM1.Cfg (Alpha K Γ) (L1 K Γ Λ σ) σ :=
  ⟨c.l.map TM2to1.Λ'.normal,c.var,Tape.mk₁ (StackWords.word c.stk (height c.stk))⟩
omit [DecidableEq K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
  [Inhabited σ] [Fintype σ] in
lemma stackCfg_spec [DecidableEq K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
    [Inhabited σ] [Fintype σ] (c : TM2.Cfg Γ Λ σ) : TM2to1.TrCfg c (stackCfg c) := by
  rcases c with ⟨l,v,S⟩
  have h:=TM2to1.TrCfg.mk (Λ:=Λ) (σ:=σ) (q:=l) (v:=v)
    (ListBlank.mk (StackWords.rows S (height S))) (StackWords.rows_projection S _ (height_bound S))
  convert h using 1
  simp only [stackCfg,Tape.mk₁,Tape.mk₂,StackWords.word_blank]
  rfl
omit [DecidableEq K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
  [Inhabited σ] [Fintype σ] in
lemma stackCfg_unique [DecidableEq K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
    [Inhabited σ] [Fintype σ] {c : TM2.Cfg Γ Λ σ}
    {a : TM1.Cfg (Alpha K Γ) (L1 K Γ Λ σ) σ} (h : TM2to1.TrCfg c a) : a=stackCfg c := by
  rcases h with ⟨L,hL⟩
  rename_i l v S
  rw [StackWords.unique_rows S (height S) (height_bound S) L hL]
  simp only [stackCfg,Tape.mk₁,Tape.mk₂,StackWords.word_blank]
  rfl

variable (M : Λ → TM2.Stmt Γ Λ σ) (coin : CoinTM1.Coins Λ)
noncomputable def program1 := TM2to1.tr M
noncomputable def enc := FixedEncoding.enc (Alpha K Γ)
noncomputable def dec := FixedEncoding.dec (Alpha K Γ)
lemma enc0 : enc (K:=K) (Γ:=Γ) default=List.Vector.replicate (Fintype.card (Alpha K Γ)) false :=
  FixedEncoding.blank (Alpha K Γ)
lemma encdec (a : Alpha K Γ) : dec (enc a)=a := FixedEncoding.left_inverse _ a
noncomputable def program2 := TM1to1.tr (enc (K:=K) (Γ:=Γ)) dec (program1 M)
noncomputable def support1 := TM2to1.trSupp M Finset.univ
noncomputable def support2 := TM1to1.trSupp (program1 M) (support1 M)
noncomputable def coin2 := CoinAlphabet.coins (Γ:=Alpha K Γ) (σ:=σ) (CoinStack.coins (Γ:=Γ) (σ:=σ) coin)
noncomputable def table := CoinTM1.table (program2 M) (coin2 coin)
noncomputable def states := CoinTM1.states (program2 M) (support2 M)
omit [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited σ] [Fintype σ] in
lemma supports1 [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited σ] [Fintype σ] :
    TM1.Supports (program1 M) (support1 M) :=
  TM2to1.tr_supports M (StackComposition.supports_univ M)
lemma supports2 : TM1.Supports (program2 M) (support2 M) :=
  TM1to1.tr_supports enc dec (program1 M) (supports1 M)
omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
lemma coin2_supported [Inhabited Λ] [Inhabited σ] [Fintype σ] :
    ∀ l∈support2 M,∀ f,coin2 coin l=some f→∀ b,f b∈support2 M :=
  CoinAlphabet.coins_supported (program1 M) (support1 M) _
    (CoinStack.coins_supported M Finset.univ coin (fun _ _ _ _ _=>Finset.mem_univ _))
lemma table_supported : PhysicalPost.Supported (table M coin) (states M) :=
  CoinTM1.table_supported (program2 M) (support2 M) (supports2 M) (coin2 coin) (coin2_supported M coin)
noncomputable def cfg (c : TM2.Cfg Γ Λ σ) : PhysicalPost.Cfg Bool (Q K Γ Λ σ) :=
  CoinTM1.trCfg (TM1to1.trCfg enc enc0 (stackCfg c))

noncomputable def accesses : ℕ := Finset.univ.sup (fun l=>StackCost.accesses (M l))
omit [DecidableEq K] [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited Λ]
  [Inhabited σ] [Fintype σ] in
lemma accesses_bound (l : Λ) : StackCost.accesses (M l)≤accesses M :=
  Finset.le_sup (f:=fun l=>StackCost.accesses (M l)) (Finset.mem_univ l)
noncomputable def overhead : ℕ :=
  (AlphabetCost.supportedWrites (program1 M) (support1 M)+1)*
    SupportedCompiler.cost (program2 M) (support2 M)

theorem deterministic (c : TM2.Cfg Γ Λ σ) (hc : ∀ l,c.l=some l→coin l=none)
    (H : ℕ) (hH : StackCost.StackBound c.stk H) :
    ∃ k,k≤overhead M*(1+2*accesses M*(H+accesses M+1)) ∧ ∀ b : Stream,
      PhysicalPost.execute (table M coin) k (cfg c) b=cfg (advance (TM2.step M) c) := by
  obtain ⟨i,a,hi,ha,hpath⟩:=CoinStack.one_step_path M (fun l=>coin l=none)
    (accesses M) (accesses_bound M) (stackCfg_spec c) hc H hH
  have hc1 : (stackCfg c).l∈(support1 M).insertNone :=
    CoinStack.cfg_supported M Finset.univ (stackCfg_spec c) (by simp)
  obtain ⟨j,hj,hpath2⟩:=CoinAlphabet.path_supported enc dec enc0 encdec (program1 M)
    (support1 M) (supports1 M) hpath hc1
  have hc2 : (TM1to1.trCfg enc enc0 (stackCfg c)).l∈(support2 M).insertNone :=
    CoinAlphabet.cfg_supported (program1 M) (support1 M) enc enc0 (stackCfg c) hc1
  have hh:=hpath2.with_support (supports2 M) (fun l hl=>Finset.some_mem_insertNone.mp (hl ▸ hc2))
  obtain ⟨k,hk,he⟩:=hh.physical (coin2 coin)
    (fun l hl=>CoinAlphabet.coins_none (by
      cases l with
      | normal l => exact CoinStack.coins_none hl.1
      | write a q => trivial))
    (SupportedCompiler.cost (program2 M) (support2 M)) (fun l hl=>SupportedCompiler.cost_le _ _ hl.2)
  refine ⟨k,?_,fun b=>?_⟩
  · calc
      k≤(i*(AlphabetCost.supportedWrites (program1 M) (support1 M)+1))*
          SupportedCompiler.cost (program2 M) (support2 M) := hk.trans (Nat.mul_le_mul_right _ hj)
      _=overhead M*i := by unfold overhead; ring
      _≤overhead M*(1+2*accesses M*(H+accesses M+1)) := Nat.mul_le_mul_left _ hi
  · rw [stackCfg_unique ha] at he
    exact he b

omit [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ] in
lemma random [Inhabited Λ] [Fintype Λ] [Inhabited σ] [Fintype σ]
    (l : Λ) (v : σ) (S : ∀ k,List (Γ k)) (f : Bool → Λ) (hf : coin l=some f) (b : Bool) :
    PhysicalPost.tick (table M coin) (cfg ⟨some l,v,S⟩) b=cfg ⟨some (f b),v,S⟩ := by
  apply CoinTM1.coin_tick
  simp only [coin2,CoinAlphabet.coins,CoinStack.coins,hf,Option.map_some]

noncomputable def initialState : Q K Γ Λ σ :=
  (.inl (.normal (.normal default)),default)
lemma initialState_mem : initialState (K:=K) (Γ:=Γ) (Λ:=Λ) (σ:=σ)∈states M := by
  apply CoinTM1.state_mem
  apply CoinTM1.node_entry
  apply (CoinAlphabet.normal_mem _ _ _).mpr
  exact (CoinStack.normal_mem M Finset.univ default).mpr (Finset.mem_univ default)

noncomputable def machine : RandomMachine := PhysicalPost.restrictedMachine
  (PhysicalPost.liftBool (table M coin)) (states M)
  (PhysicalPost.liftBool_supported _ _ (table_supported M coin))
  initialState (initialState_mem M)
end MatchingFPRAS.OnlineStack

end OAI
