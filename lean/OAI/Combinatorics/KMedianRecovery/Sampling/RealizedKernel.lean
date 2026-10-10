import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplingRate
import OAI.Combinatorics.KMedianRecovery.Sampling.InverseCDF

namespace OAI

namespace MetricKMedianRecovery.Guided.Realized
open FiniteSampling
variable {S A Ω : Type*} [Fintype A] [Fintype Ω]

structure Draw (p : Kernel S A) where
  run : S→Ω→A
  law : ∀ s (g : A→ℝ), average (fun ω=>g (run s ω))=∑ a,p.weight s a*g a
noncomputable def actions (f : S→A→S) (p : Kernel S A) (r : Draw (Ω:=Ω) p) :
    (n : ℕ)→S→(Fin n→Ω)→(Fin n→A)
  | 0,_,_=>Fin.elim0
  | n+1,s,bits=>let a:=r.run s (bits 0); Fin.cons a (actions f p r n (f s a) (Fin.tail bits))
theorem actions_average (f : S→A→S) (p : Kernel S A) (r : Draw (Ω:=Ω) p)
    (n : ℕ) (s : S) (g : (Fin n→A)→ℝ) :
    average (fun bits=>g (actions f p r n s bits))=
      ∑ a : Fin n→A,pathWeight f p.weight n s a*g a := by
  classical
  induction n generalizing s with
  | zero=>
    simp only [actions,average_const,pathWeight,one_mul,Fintype.sum_unique]
    congr 1
  | succ n ih=>
    rw [average_fin_succ,sum_fin_succ]
    simp only [actions,Fin.cons_zero,Fin.tail_cons,pathWeight]
    conv_lhs=>
      arg 1; ext bits
      rw [ih (f s (r.run s bits)) (fun seed=>g (Fin.cons (r.run s bits) seed))]
    rw [r.law s (fun a=>∑ seed : Fin n→A,pathWeight f p.weight n (f s a) seed*g (Fin.cons a seed))]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro seed _
    ring
lemma actions_probability (f : S→A→S) (p : Kernel S A) (r : Draw (Ω:=Ω) p)
    (n : ℕ) (s : S) (E : (Fin n→A)→Prop) :
    probability (fun bits=>E (actions f p r n s bits))=eventMass f p.weight n s E := by
  classical
  unfold probability
  rw [actions_average f p r n s (fun a=>if E a then 1 else 0)]
  simp only [eventMass,mul_ite,mul_one,mul_zero]
noncomputable def canonical [DecidableEq A] (p : Kernel S A) (b : ℕ) (d : A)
    (as : List A) (h : as.Perm Finset.univ.toList) : Draw (Ω:=Fin b→Bool) (FixedDyadic.kernel p b d) where
  run s := Dyadic.Canonical.draw (p.weight s) b d as
  law s g := Dyadic.Canonical.draw_average (p.weight s) (p.nonneg s) (p.total s) b d as h g
lemma canonical_law [DecidableEq A] (f : S→A→S) (p : Kernel S A) (b : ℕ) (d : A)
    (as : List A) (h : as.Perm Finset.univ.toList) (n : ℕ) (s : S) (g : (Fin n→A)→ℝ) :
    average (fun bits=>g (actions f (FixedDyadic.kernel p b d) (canonical p b d as h) n s bits))=
      average (fun bits=>g (FixedDyadic.actions f p b d n s bits)) := by
  rw [actions_average,FixedDyadic.actions_average]
end MetricKMedianRecovery.Guided.Realized

namespace MetricKMedianRecovery.BitMachine.BinaryDyadic
open FiniteSampling
lemma zipIdx_ofFn_nat {n : ℕ} (f : Fin n→ℕ) :
    ((List.ofFn f).zipIdx).map (fun wi=>(wi.2,wi.1))=List.ofFn (fun i=>(i.val,f i)) := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp
lemma finEnum_perm (n : ℕ) : (List.ofFn (id : Fin n→Fin n)).Perm Finset.univ.toList := by
  apply (List.perm_ext_iff_of_nodup (List.nodup_ofFn.mpr Function.injective_id) (Finset.nodup_toList _)).mpr
  intro i
  simp
lemma canonical_run {n : ℕ} (p : Fin n→ℚ) (d : Fin n) (b : ℕ) (s : Fin b→Bool) :
    run (pack b d.val (List.ofFn p) (List.ofFn s))=
      (Dyadic.Canonical.draw (fun i=>(p i:ℝ)) b d (List.ofFn id) s).val.bits := by
  rw [run_pack]
  simp only [List.map_ofFn,Function.comp_def]
  have hh:=Dyadic.Canonical.select_relabel Fin.val d
    (Dyadic.Canonical.list (fun i=>(p i:ℝ)) b (List.ofFn id)) (Categorical.uniformBits b s).val
  simp only [Dyadic.Canonical.list,List.map_ofFn,Function.comp_def,id_eq,rawCount_cast] at hh
  rw [←zipIdx_ofFn_nat (fun i=>⌊p i*(2:ℚ)^b⌋₊),Dyadic.Canonical.select_index] at hh
  simpa only [Dyadic.Canonical.draw,Dyadic.Canonical.list,List.map_ofFn,Function.comp_def,id_eq,rawCount_cast] using congrArg Nat.bits hh
lemma canonical_average {n : ℕ} (p : Fin n→ℚ) (hp : ∀ i,0≤p i) (ht : ∑ i,p i=1)
    (d : Fin n) (b : ℕ) (g : Fin n→ℝ) :
    average (fun s=>g (Dyadic.Canonical.draw (fun i=>(p i:ℝ)) b d (List.ofFn id) s))=
      ∑ i,Dyadic.weight (fun i=>(p i:ℝ)) b d i*g i := by
  apply Dyadic.Canonical.draw_average _ _ _ _ _ _ (finEnum_perm n)
  · intro i;exact_mod_cast hp i
  · exact_mod_cast ht
end MetricKMedianRecovery.BitMachine.BinaryDyadic

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
def entries (M E J : ℕ) : List (Entry M E J) :=
  (List.ofFn (fun i : Fin M=>Sum.inl i))++
    (List.ofFn (fun i : Fin (E+1)=>Sum.inr (Sum.inl i)))++
    (List.ofFn (fun i : Fin J=>Sum.inr (Sum.inr i)))
lemma mem_entries (M E J : ℕ) (e : Entry M E J) : e∈entries M E J := by
  rcases e with i | (i | i) <;> simp only [entries,List.mem_append,List.mem_ofFn]
  · exact Or.inl (Or.inl ⟨i,rfl⟩)
  · exact Or.inl (Or.inr ⟨i,rfl⟩)
  · exact Or.inr ⟨i,rfl⟩
lemma entries_nodup (M E J : ℕ) : (entries M E J).Nodup := by
  simp only [entries,List.nodup_append,List.nodup_ofFn]
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · exact fun a b h=>Sum.inl.inj h
  · exact fun a b h=>Sum.inl.inj (Sum.inr.inj h)
  · simp only [List.mem_ofFn]; rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩ h; cases h
  · exact fun a b h=>Sum.inr.inj (Sum.inr.inj h)
  · simp only [List.mem_append,List.mem_ofFn]
    rintro _ (⟨a,rfl⟩|⟨a,rfl⟩) _ ⟨b,rfl⟩ h <;> cases h

def clients (D : Finset (Fin n)) : List D := D.attach.sort (·≤·)
lemma clients_nodup (D : Finset (Fin n)) : (clients D).Nodup := Finset.sort_nodup _ _
lemma mem_clients (D : Finset (Fin n)) (w : D) : w∈clients D := by simp [clients]
def actions (D : Finset (Fin n)) (M E J : ℕ) : List (Action D M E J) :=
  Sum.inl () :: ((clients D).map (fun w=>Sum.inr (Sum.inl w))++
    ((clients D).product (entries M E J)).map (fun z=>Sum.inr (Sum.inr z)))
lemma actions_nodup (D : Finset (Fin n)) (M E J : ℕ) : (actions D M E J).Nodup := by
  simp only [actions,List.nodup_cons,List.mem_append,List.mem_map,List.nodup_append]
  refine ⟨?_,?_,?_,?_⟩
  · simp
  · exact (clients_nodup D).map (fun a b h=>Sum.inl.inj (Sum.inr.inj h))
  · exact ((clients_nodup D).product (entries_nodup M E J)).map (fun a b h=>Sum.inr.inj (Sum.inr.inj h))
  · rintro _ ⟨w,hw,rfl⟩ _ ⟨z,hz,rfl⟩ h
    cases h
lemma mem_actions (D : Finset (Fin n)) (M E J : ℕ) (a : Action D M E J) : a∈actions D M E J := by
  rcases a with u | (w | ⟨w,e⟩)
  · cases u; simp [actions]
  · simp only [actions,List.mem_cons,List.mem_append,List.mem_map]
    exact Or.inr (Or.inl ⟨w,mem_clients D w,rfl⟩)
  · simp only [actions,List.mem_cons,List.mem_append,List.mem_map]
    exact Or.inr (Or.inr ⟨(w,e),List.mem_product.mpr ⟨mem_clients D w,mem_entries M E J e⟩,rfl⟩)
lemma actions_perm (D : Finset (Fin n)) (M E J : ℕ) : (actions D M E J).Perm Finset.univ.toList := by
  apply (List.perm_ext_iff_of_nodup (actions_nodup D M E J) (Finset.nodup_toList _)).mpr
  simp only [mem_actions,Finset.mem_toList,Finset.mem_univ,implies_true]
def entryCode (M E J : ℕ) : Entry M E J→List Bool
  | .inl i=>BinaryMenu.code 0 i.val
  | .inr (.inl i)=>BinaryMenu.code 1 i.val
  | .inr (.inr i)=>BinaryMenu.code 2 i.val
lemma entry_weight (M E J : ℕ) (e : Entry M E J) :
    BinaryMenu.weight (pairBits (BinaryMenu.weights M E J,entryCode M E J e))=menuWeight M E J e := by
  rcases e with i | (i | i) <;> norm_num [entryCode,BinaryMenu.weight_pair,menuWeight]
def actionCode (D : Finset (Fin n)) (M E J : ℕ) : Action D M E J→List Bool
  | .inl _=>WordList.encode [(0:ℕ).bits,[],[]]
  | .inr (.inl w)=>WordList.encode [(1:ℕ).bits,w.val.val.bits,[]]
  | .inr (.inr (w,e))=>WordList.encode [(2:ℕ).bits,w.val.val.bits,entryCode M E J e]
end MetricKMedianRecovery.RationalSampling

end OAI
