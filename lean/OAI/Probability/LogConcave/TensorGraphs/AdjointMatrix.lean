import Mathlib
import OAI.Probability.LogConcave.TensorGraphs.Inside
import OAI.Probability.LogConcave.JetEstimates.PolySmooth

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open Function MeasureTheory Set Filter
open scoped Topology NNReal

namespace LogConcaveSampling.AdjointRemoval
open MeasureTheory
open scoped RealInnerProductSpace NNReal

lemma regular_of_polySmooth {d : ℕ} {P : Type*}
    {H : Point d → ℝ} {f : P → Point d → ℝ} (b : P → Point d) {K : ℝ≥0}
    (hH : PolySmooth H) (ht : HasGaussianLowerTail H)
    (hL : LipschitzWith K (gradient H)) (hf : ∀p,PolySmooth (f p)) :
    Regular H b f K := by
  refine ⟨hH.smooth,ht,hL,fun p => (hf p).smooth,
    fun p l => ((hf p).jet b l).polyC1,?_⟩
  intro h
  exact (((hH.directional (b h.second)).directional (b h.first)).jet b h.extra).polyC1

end LogConcaveSampling.AdjointRemoval

namespace LogConcaveSampling.TraceWords
open MeasureTheory Matrix
open scoped RealInnerProductSpace NNReal

variable {d : ℕ} {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    [DecidableEq I] [DecidableEq J]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in

theorem integral_word_expansion
    {H : Point d → ℝ} {F : I → J → K → Point d → ℝ}
    (b : K → Point d) {L : ℝ≥0} (hH : PolySmooth H)
    (ht : HasGaussianLowerTail H) (hL : LipschitzWith L (gradient H))
    (hF : ∀i j k,PolySmooth (F i j k)) (w : List (I×J)) :
    (∫x,eval ((fun i j => tensorAdjoint H b (F i j) x) : Matrix I J ℝ) w ∂gibbs H)=
      ((AdjointRemoval.expand w.length AdjointRemoval.initial).map (fun S =>
        ∑a : Fin w.length → K,∫x,
          (∏p : Fin w.length,JetCalculus.jet (fun q => b (a q)) (S.derivatives p)
            (F (w.get p).1 (w.get p).2 (a p)) x)*
          (S.hessians.map (fun h => AdjointRemoval.hessian H (fun q => b (a q)) h x)).prod
          ∂gibbs H)).sum := by
  have he (x : Point d) := eval_eq_prod_get
    ((fun i j => tensorAdjoint H b (F i j) x) : Matrix I J ℝ) w
  simp_rw [he]
  have hr (a : Fin w.length → K) : AdjointRemoval.Regular H (fun p => b (a p))
      (fun p => F (w.get p).1 (w.get p).2 (a p)) L :=
    AdjointRemoval.regular_of_polySmooth _ hH ht hL (fun p => hF _ _ _)
  simpa only [Fintype.card_fin] using
    AdjointRemoval.tensor_actual_adjoint_expansion_branch_first hr

def adjointMatrix (H : Point d → ℝ) (b : K → Point d)
    (F : I → J → K → Point d → ℝ) (x : Point d) : Matrix I J ℝ :=
  fun i j => tensorAdjoint H b (F i j) x

omit [DecidableEq J] in

theorem integral_trace_expansion
    {H : Point d → ℝ} {F : I → J → K → Point d → ℝ}
    (b : K → Point d) {L : ℝ≥0} (hH : PolySmooth H)
    (ht : HasGaussianLowerTail H) (hL : LipschitzWith L (gradient H))
    (hF : ∀i j k,PolySmooth (F i j k)) (s : ℕ) :
    (∫x,((adjointMatrix H b F x*(adjointMatrix H b F x).transpose)^s).trace ∂gibbs H)=
    ((closed (I:=I) (J:=J) s).map (fun w =>
      ((AdjointRemoval.expand w.length AdjointRemoval.initial).map (fun S =>
        ∑a : Fin w.length → K,∫x,
          (∏p : Fin w.length,JetCalculus.jet (fun q => b (a q)) (S.derivatives p)
            (F (w.get p).1 (w.get p).2 (a p)) x)*
          (S.hessians.map (fun h => AdjointRemoval.hessian H (fun q => b (a q)) h x)).prod
          ∂gibbs H)).sum)).sum := by
  have hw (w : List (I×J)) : Integrable
      (fun x => eval ((fun i j => tensorAdjoint H b (F i j) x) : Matrix I J ℝ) w) (gibbs H) := by
    have he (x : Point d) := eval_eq_prod_get
      ((fun i j => tensorAdjoint H b (F i j) x) : Matrix I J ℝ) w
    simp_rw [he]
    exact (PolySmooth.prod Finset.univ (fun p _ =>
      hH.tensorAdjoint (hF (w.get p).1 (w.get p).2) b)).integrable hH.smooth.continuous ht
  have hsum (T : List (List (I×J))) : Integrable
      (fun x => (T.map (eval ((fun i j => tensorAdjoint H b (F i j) x) : Matrix I J ℝ))).sum) (gibbs H) := by
    induction T with
    | nil => simp
    | cons w T ih =>
      change Integrable (fun x => eval ((fun i j => tensorAdjoint H b (F i j) x) : Matrix I J ℝ) w+
        (T.map (eval ((fun i j => tensorAdjoint H b (F i j) x) : Matrix I J ℝ))).sum) (gibbs H)
      exact (hw w).add ih
  simp_rw [trace_power]
  have hl (T : List (List (I×J))) :
      (∫x,(T.map (eval ((fun i j => tensorAdjoint H b (F i j) x) : Matrix I J ℝ))).sum ∂gibbs H)=
        (T.map (fun w => ∫x,eval ((fun i j => tensorAdjoint H b (F i j) x) : Matrix I J ℝ) w ∂gibbs H)).sum := by
    induction T with
    | nil => simp
    | cons w T ih =>
      simp only [List.map_cons,List.sum_cons]
      rw [integral_add (hw w) (hsum T),ih]
  change (∫x,((closed (I:=I) (J:=J) s).map
    (eval ((fun i j => tensorAdjoint H b (F i j) x) : Matrix I J ℝ))).sum ∂gibbs H)=_
  rw [hl]
  simp_rw [integral_word_expansion b hH ht hL hF]
end LogConcaveSampling.TraceWords
namespace LogConcaveSampling.AdjointRemoval
variable {P : Type*} [Fintype P] [DecidableEq P]

def Hessian.tokens (h : Hessian P) : Multiset P :=
  h.first::ₘh.second::ₘ(h.extra : Multiset P)

def State.tokens (S : State P) : Multiset P :=
  S.pending.val+(∑p,(S.derivatives p : Multiset P))+
    (S.hessians.map Hessian.tokens).sum

lemma initial_tokens : (initial (P:=P)).tokens=Finset.univ.val := by
  simp [State.tokens,initial]

lemma hitPrimary_tokens (S : State P) {i j : P} (hi : i∈S.pending) :
    (hitPrimary S i j).tokens=S.tokens := by
  have he : (∑k,(Function.update S.derivatives j (i::S.derivatives j) k : Multiset P))=
      i::ₘ(∑k,(S.derivatives k : Multiset P)) := by
    have hl : (fun k => (Function.update S.derivatives j (i::S.derivatives j) k : Multiset P))=
        Function.update (fun k => (S.derivatives k : Multiset P)) j (i::ₘ(S.derivatives j : Multiset P)) := by
      funext k
      by_cases hk : k=j
      · subst k; simp
      · simp [Function.update_of_ne hk]
    rw [hl,Finset.sum_update_of_mem (Finset.mem_univ j),Finset.sdiff_singleton_eq_erase]
    rw [←Finset.add_sum_erase Finset.univ (fun k => (S.derivatives k : Multiset P)) (Finset.mem_univ j)]
    simp only [Multiset.cons_add]
  have hp : i::ₘ(S.pending.erase i).val=S.pending.val := by
    exact Multiset.cons_erase hi
  simp only [State.tokens,hitPrimary,he]
  rw [Multiset.add_cons,←Multiset.cons_add,hp]

lemma pair_tokens (S : State P) {i j : P} (hi : i∈S.pending) (hj : j∈S.pending) (hij : i≠j) :
    (pair S i j).tokens=S.tokens := by
  have hj' : j∈S.pending.erase i := Finset.mem_erase.mpr ⟨hij.symm,hj⟩
  have hp : i::ₘj::ₘ((S.pending.erase i).erase j).val=S.pending.val := by
    rw [show j::ₘ((S.pending.erase i).erase j).val=(S.pending.erase i).val from Multiset.cons_erase hj']
    exact Multiset.cons_erase hi
  simp only [State.tokens,pair,Multiset.map_cons,Multiset.sum_cons,Hessian.tokens,Multiset.coe_nil]
  rw [Multiset.cons_add,Multiset.cons_add,zero_add,Multiset.add_cons,Multiset.add_cons,
    ←Multiset.cons_add,←Multiset.cons_add,←Multiset.cons_add,←Multiset.cons_add,hp]

lemma hitHessian_tokens (S : State P) {i : P} (hi : i∈S.pending)
    {h : Hessian P} (hh : h∈S.hessians) : (hitHessian S i h).tokens=S.tokens := by
  have hm := congrArg (fun t : Multiset (Hessian P) => (t.map Hessian.tokens).sum)
    (Multiset.cons_erase hh)
  simp only [Multiset.map_cons,Multiset.sum_cons] at hm
  have hp : i::ₘ(S.pending.erase i).val=S.pending.val := Multiset.cons_erase hi
  have hh' : (h.hit i).tokens=i::ₘh.tokens := by
    simp only [Hessian.tokens,Hessian.hit,←Multiset.cons_coe]
    rw [Multiset.cons_swap h.second i,Multiset.cons_swap h.first i]
  simp only [State.tokens,hitHessian,Multiset.map_cons,Multiset.sum_cons,hh']
  rw [Multiset.cons_add,hm,Multiset.add_cons,←Multiset.cons_add,←Multiset.cons_add,hp]

lemma Step.tokens {S T : State P} (h : Step S T) : T.tokens=S.tokens := by
  cases h with
  | primary i j hi hij => exact hitPrimary_tokens S hi
  | pair i j hi hj hij => exact pair_tokens S hi hj hij
  | hessian i h hi hh => exact hitHessian_tokens S hi hh

theorem mem_expand_tokens {n : ℕ} {S : State P}
    (hS : S∈expand n initial) : S.tokens=Finset.univ.val := by
  have hr := mem_expand_reachable hS
  clear hS
  have he : S.tokens=(initial (P:=P)).tokens := by
    induction hr with
    | refl => rfl
    | tail hr ht ih => exact ht.tokens.trans ih
  exact he.trans initial_tokens

theorem terminal_ports {S : State P} (hS : S∈expand (Fintype.card P) initial) :
    (∑p,(S.derivatives p : Multiset P))+(S.hessians.map Hessian.tokens).sum=Finset.univ.val := by
  have he := mem_expand_tokens hS
  have ht := mem_expand_terminal (by simp [initial]) hS
  simpa only [State.tokens,ht,Finset.empty_val,zero_add] using he
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
variable {P : Type*} [Fintype P] [DecidableEq P]

abbrev TargetVertex (S : State P) := P ⊕ S.hessians

def ports (S : State P) : TargetVertex S → Multiset P
  | Sum.inl p => (S.derivatives p : Multiset P)
  | Sum.inr h => (h : Hessian P).tokens

lemma sum_ports (S : State P) : (∑v,ports S v)=
    (∑p,(S.derivatives p : Multiset P))+(S.hessians.map Hessian.tokens).sum := by
  rw [Fintype.sum_sum_type]
  congr 1
  change (Finset.univ.val.map (fun h : S.hessians => (h : Hessian P).tokens)).sum=_
  rw [Multiset.map_univ]

abbrev Port (S : State P) := (v : TargetVertex S) × ports S v

def portLabel (S : State P) (p : Port S) : P := p.2

theorem portLabel_bijective {S : State P} (hS : S∈expand (Fintype.card P) initial) :
    Function.Bijective (portLabel S) := by
  have hs : (∑v,ports S v)=Finset.univ.val := (sum_ports S).trans (terminal_ports hS)
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  constructor
  · intro i
    have hi : i∈∑v,ports S v := by rw [hs]; exact Finset.mem_univ i
    obtain ⟨v,_,hv⟩ := Multiset.mem_sum.mp hi
    refine ⟨⟨v,(ports S v).mkToType i ⟨0,Multiset.count_pos.mpr hv⟩⟩,rfl⟩
  · simp only [Port,Fintype.card_sigma,Multiset.card_coe]
    rw [←Multiset.card_sum,hs]
    rfl

noncomputable def portEquiv {S : State P} (hS : S∈expand (Fintype.card P) initial) :
    Port S ≃ P := Equiv.ofBijective (portLabel S) (portLabel_bijective hS)

noncomputable def destination {S : State P} (hS : S∈expand (Fintype.card P) initial)
    (i : P) : TargetVertex S := ((portEquiv hS).symm i).1

lemma destination_label {S : State P} (hS : S∈expand (Fintype.card P) initial)
    (p : Port S) : destination hS (portLabel S p)=p.1 := by
  exact congrArg Sigma.fst ((portEquiv hS).symm_apply_apply p)

lemma label_mem_destination {S : State P} (hS : S∈expand (Fintype.card P) initial)
    (i : P) : i∈ports S (destination hS i) := by
  have hp := @Multiset.coe_mem P _ (ports S (destination hS i)) (((portEquiv hS).symm i).2)
  change portLabel S ((portEquiv hS).symm i)∈_ at hp
  change portEquiv hS ((portEquiv hS).symm i)∈_ at hp
  simpa only [Equiv.apply_symm_apply] using hp

lemma destination_primary_ne {S : State P} (hS : S∈expand (Fintype.card P) initial)
    {i j : P} (h : destination hS i=Sum.inl j) : i≠j := by
  have hi := label_mem_destination hS i
  rw [h] at hi
  exact (reachable_good (mem_expand_reachable hS)).1 j i hi

theorem hessian_distinguished_neighbors {S : State P}
    (hS : S∈expand (Fintype.card P) initial) (h : S.hessians) :
    destination hS (h : Hessian P).first=Sum.inr h ∧
    destination hS (h : Hessian P).second=Sum.inr h ∧
    (h : Hessian P).first≠(h : Hessian P).second := by
  have hf : (h : Hessian P).first∈ports S (Sum.inr h) := by
    simp [ports,Hessian.tokens]
  have hs : (h : Hessian P).second∈ports S (Sum.inr h) := by
    simp [ports,Hessian.tokens]
  have lift (i : P) (hi : i∈ports S (Sum.inr h)) : destination hS i=Sum.inr h := by
    let p : Port S := ⟨Sum.inr h,(ports S (Sum.inr h)).mkToType i ⟨0,Multiset.count_pos.mpr hi⟩⟩
    exact destination_label hS p
  exact ⟨lift _ hf,lift _ hs,(reachable_good (mem_expand_reachable hS)).2 h Multiset.coe_mem⟩
end LogConcaveSampling.AdjointRemoval
namespace LogConcaveSampling.AdjointRemoval
variable {n : ℕ} {S : State (Fin (n+1))}

def Adjacent (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    (u v : TargetVertex S) : Prop :=
  (∃k : Fin n,(u=Sum.inl k.castSucc ∧ v=Sum.inl k.succ) ∨
    (v=Sum.inl k.castSucc ∧ u=Sum.inl k.succ)) ∨
  (∃i : Fin (n+1),(u=Sum.inl i ∧ v=destination hS i) ∨
    (v=Sum.inl i ∧ u=destination hS i))

lemma adjacent_ne (hS : S∈expand (Fintype.card (Fin (n+1))) initial)
    {u v : TargetVertex S} (h : Adjacent hS u v) : u≠v := by
  intro he
  rcases h with ⟨k,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩ | ⟨i,(⟨rfl,rfl⟩|⟨rfl,rfl⟩)⟩
  · have hh : k.castSucc=k.succ := Sum.inl.inj he
    have hv := congrArg Fin.val hh
    simp only [Fin.val_castSucc,Fin.val_succ] at hv
    omega
  · have hh : k.succ=k.castSucc := Sum.inl.inj he
    have hv := congrArg Fin.val hh
    simp only [Fin.val_castSucc,Fin.val_succ] at hv
    omega
  · exact destination_primary_ne hS he.symm rfl
  · exact destination_primary_ne hS he rfl

theorem actual_removal_graph_order
    (hS : S∈expand (Fintype.card (Fin (n+1))) initial) :
    ∃ key : TargetVertex S → ℕ, Function.Injective key ∧
      (∀u v,Adjacent hS u v → key u≠key v) ∧
      ∀v : TargetVertex S,
        (v=Sum.inl 0 ∨ ∃u,Adjacent hS u v ∧ key u<key v) ∧
        (v=Sum.inl (Fin.last n) ∨ ∃w,Adjacent hS v w ∧ key v<key w) := by
  let left (h : S.hessians) : Fin (n+1) := min (h : Hessian (Fin (n+1))).first (h : Hessian (Fin (n+1))).second
  let right (h : S.hessians) : Fin (n+1) := max (h : Hessian (Fin (n+1))).first (h : Hessian (Fin (n+1))).second
  have hp (h : S.hessians) : left h<right h := by
    have hh := (hessian_distinguished_neighbors hS h).2.2
    exact min_lt_max.mpr hh
  have hchain (k : Fin n) : Adjacent hS (Sum.inl k.castSucc) (Sum.inl k.succ) :=
    Or.inl ⟨k,Or.inl ⟨rfl,rfl⟩⟩
  have hleft (h : S.hessians) : Adjacent hS (Sum.inl (left h)) (Sum.inr h) := by
    obtain ⟨hf,hs,_⟩ := hessian_distinguished_neighbors hS h
    refine Or.inr ⟨left h,Or.inl ⟨rfl,?_⟩⟩
    cases min_choice (h : Hessian (Fin (n+1))).first (h : Hessian (Fin (n+1))).second with
    | inl he => exact (he ▸ hf).symm
    | inr he => exact (he ▸ hs).symm
  have hright (h : S.hessians) : Adjacent hS (Sum.inr h) (Sum.inl (right h)) := by
    obtain ⟨hf,hs,_⟩ := hessian_distinguished_neighbors hS h
    refine Or.inr ⟨right h,Or.inr ⟨rfl,?_⟩⟩
    cases max_choice (h : Hessian (Fin (n+1))).first (h : Hessian (Fin (n+1))).second with
    | inl he => exact (he ▸ hf).symm
    | inr he => exact (he ▸ hs).symm
  obtain ⟨key,hkey,horder⟩ := TraceOpening.ordered_nontrivial_splits left right hp
    (Adjacent hS) hchain hleft hright
  exact ⟨key,hkey,fun u v huv hEq => adjacent_ne hS huv (hkey hEq),horder⟩
end LogConcaveSampling.AdjointRemoval

end UpperProof
end
end
end

end OAI
