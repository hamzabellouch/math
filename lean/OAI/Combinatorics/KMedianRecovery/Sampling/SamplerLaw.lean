import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.SamplingPotential

namespace OAI

namespace MetricKMedianRecovery.Guided.Realized
open FiniteSampling
variable {S A Ω : Type*} [Fintype A] [Fintype Ω]
lemma adaptive_actions (f : S→A→S) (p : Kernel S A) (r : Draw (Ω:=Ω) p)
    (n : ℕ) (s : S) (bits : Fin n→Ω) :
    adaptiveRun f n s (actions f p r n s bits)=
      adaptiveRun (fun s bit=>f s (r.run s bit)) n s bits := by
  induction n generalizing s with
  | zero=>rfl
  | succ n ih=>simpa only [actions,adaptiveRun,Fin.cons_zero,Fin.tail_cons] using ih (f s (r.run s (bits 0))) (Fin.tail bits)
lemma adaptive_list {S Ω : Type*} (f : S→Ω→S) (n : ℕ) (s : S) (bits : Fin n→Ω) :
    adaptiveRun f n s bits=(List.ofFn bits).foldl f s := by
  induction n generalizing s with
  | zero=>rfl
  | succ n ih=>simpa only [adaptiveRun,List.ofFn_succ,List.foldl_cons,Fin.tail_def] using ih (f s (bits 0)) (Fin.tail bits)
end MetricKMedianRecovery.Guided.Realized
namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine Guided FiniteSampling
variable {n : ℕ} [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
lemma next_real (D F S : Finset (Fin n)) (hD : D.Nonempty) (Δ P κ : ℚ) (m M E J b : ℕ)
    (s : Option (State n)) (seed : Fin b→Bool) :
    (next δ D F S Δ P κ m M E J b s seed).map State.real=
      Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J (s.map State.real)
        (Dyadic.Canonical.draw (Sampling.transitionWeight D S (Δ:ℝ) M E J (s.map State.real)) b (Sum.inl ()) (actions D M E J) seed) := by
  rw [next,update_real δ hδ D F S hD]
  congr 1
  congr 1
  funext a
  exact transitionWeight_cast δ hδ D S Δ M E J s a
lemma adaptive_real (D F S : Finset (Fin n)) (hD : D.Nonempty) (Δ P κ : ℚ) (m M E J b t : ℕ)
    (s : Option (State n)) (seed : Fin t→Fin b→Bool) :
    (adaptiveRun (next δ D F S Δ P κ m M E J b) t s seed).map State.real=
      adaptiveRun (fun s bit=>Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J s
        (Dyadic.Canonical.draw (Sampling.transitionWeight D S (Δ:ℝ) M E J s) b (Sum.inl ()) (actions D M E J) bit)) t (s.map State.real) seed := by
  induction t generalizing s with
  | zero=>rfl
  | succ t ih=>rw [adaptiveRun,adaptiveRun,ih,next_real δ hδ D F S hD]
lemma canonical_average (D F S : Finset (Fin n)) (hD : D.Nonempty) (Δ P κ : ℚ) (m M E J b t : ℕ)
    (hM : 0<M) (hJ : 0<J) (s : Option (State n)) (g : Option (Sampling.State (Fin n))→ℝ) :
    average (fun seed : Fin t→Fin b→Bool=>g (((List.ofFn seed).foldl (next δ D F S Δ P κ m M E J b) s).map State.real))=
      average (fun seed=>g (adaptiveRun (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J) t (s.map State.real)
        (FixedDyadic.actions (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J)
          (actualKernel D S (Δ:ℝ) M E J hM hJ) b (Sum.inl ()) t (s.map State.real) seed))) := by
  let f:=Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J
  let p:=actualKernel D S (Δ:ℝ) M E J hM hJ
  have he (seed : Fin t→Fin b→Bool) :
      ((List.ofFn seed).foldl (next δ D F S Δ P κ m M E J b) s).map State.real=
      adaptiveRun f t (s.map State.real) (Realized.actions f (FixedDyadic.kernel p b (Sum.inl ()))
        (Realized.canonical p b (Sum.inl ()) (actions D M E J) (actions_perm D M E J)) t (s.map State.real) seed) := by
    rw [←Realized.adaptive_list,adaptive_real δ hδ D F S hD,Realized.adaptive_actions]
    rfl
  simp only [he]
  exact Realized.canonical_law f p b (Sum.inl ()) (actions D M E J) (actions_perm D M E J) t (s.map State.real)
    (fun as=>g (adaptiveRun f t (s.map State.real) as))
end MetricKMedianRecovery.RationalSampling

namespace MetricKMedianRecovery.Guided
variable {S T A : Type*}
lemma states_map (h : S→T) (f : S→A→S) (g : T→A→T)
    (hf : ∀ s a,h (f s a)=g (h s) a) (n : ℕ) (s : S) (seed : Fin n→A) (i : Fin (n+1)) :
    h (states f n s seed i)=states g n (h s) seed i := by
  induction n generalizing s with
  | zero=>rfl
  | succ n ih=>
    refine Fin.cases ?_ (fun j=>?_) i
    · rfl
    · simpa only [states,Fin.cases_succ,hf] using ih (f s (seed 0)) (Fin.tail seed) j
lemma states_list (f : S→A→S) (n : ℕ) (s : S) (seed : Fin n→A) (i : Fin (n+1)) :
    states f n s seed i=((List.ofFn seed).take i.val).foldl f s := by
  induction n generalizing s with
  | zero=>simp only [List.ofFn_zero,List.take_nil,List.foldl_nil];rfl
  | succ n ih=>
    refine Fin.cases ?_ (fun j=>?_) i
    · simp only [states,Fin.cases_zero,Fin.val_zero,List.take_zero,List.foldl_nil]
    · simpa only [states,Fin.cases_succ,List.ofFn_succ,Fin.val_succ,List.take_succ_cons,List.foldl_cons,Fin.tail_def]
        using ih (f s (seed 0)) (Fin.tail seed) j
end MetricKMedianRecovery.Guided
namespace MetricKMedianRecovery.Guided.Realized
variable {S A Ω : Type*} [Fintype A] [Fintype Ω]
lemma states_actions (f : S→A→S) (p : Kernel S A) (r : Draw (Ω:=Ω) p)
    (n : ℕ) (s : S) (bits : Fin n→Ω) (i : Fin (n+1)) :
    states f n s (actions f p r n s bits) i=
      states (fun s bit=>f s (r.run s bit)) n s bits i := by
  induction n generalizing s with
  | zero=>rfl
  | succ n ih=>
    refine Fin.cases ?_ (fun j=>?_) i
    · rfl
    · simpa only [actions,states,Fin.cases_succ,Fin.cons_zero,Fin.tail_cons]
        using ih (f s (r.run s (bits 0))) (Fin.tail bits) j
end MetricKMedianRecovery.Guided.Realized
namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine Guided FiniteSampling
variable {n : ℕ} [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
lemma trace_average (D F S : Finset (Fin n)) (hD : D.Nonempty) (Δ P κ : ℚ) (m M E J b t : ℕ)
    (hM : 0<M) (hJ : 0<J) (s : Option (State n)) (G : (Fin (t+1)→Option (Sampling.State (Fin n)))→ℝ) :
    average (fun seed : Fin t→Fin b→Bool=>G (fun i=>(((List.ofFn seed).take i.val).foldl
      (next δ D F S Δ P κ m M E J b) s).map State.real))=
      average (fun seed=>G (states (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J) t (s.map State.real)
        (FixedDyadic.actions (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J)
          (actualKernel D S (Δ:ℝ) M E J hM hJ) b (Sum.inl ()) t (s.map State.real) seed))) := by
  let f:=Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J
  let p:=actualKernel D S (Δ:ℝ) M E J hM hJ
  let r:=Realized.canonical p b (Sum.inl ()) (actions D M E J) (actions_perm D M E J)
  have he (seed : Fin t→Fin b→Bool) :
      (fun i:Fin (t+1)=>(((List.ofFn seed).take i.val).foldl (next δ D F S Δ P κ m M E J b) s).map State.real)=
        states f t (s.map State.real) (Realized.actions f (FixedDyadic.kernel p b (Sum.inl ())) r t (s.map State.real) seed) := by
    funext i
    rw [←states_list,Realized.states_actions]
    exact states_map (Option.map State.real) _ _ (next_real δ hδ D F S hD Δ P κ m M E J b) t s seed i
  simp only [he]
  exact Realized.canonical_law f p b (Sum.inl ()) (actions D M E J) (actions_perm D M E J) t (s.map State.real)
    (fun as=>G (states f t (s.map State.real) as))
lemma trace_probability (D F S : Finset (Fin n)) (hD : D.Nonempty) (Δ P κ : ℚ) (m M E J b t : ℕ)
    (hM : 0<M) (hJ : 0<J) (s : Option (State n)) (G : (Fin (t+1)→Option (Sampling.State (Fin n)))→Prop) :
    probability (fun seed : Fin t→Fin b→Bool=>G (fun i=>(((List.ofFn seed).take i.val).foldl
      (next δ D F S Δ P κ m M E J b) s).map State.real))=
      probability (fun seed=>G (states (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J) t (s.map State.real)
        (FixedDyadic.actions (Sampling.update D F S hD (Δ:ℝ) (P:ℝ) (κ:ℝ) m M E J)
          (actualKernel D S (Δ:ℝ) M E J hM hJ) b (Sum.inl ()) t (s.map State.real) seed))) := by
  classical
  exact trace_average δ hδ D F S hD Δ P κ m M E J b t hM hJ s (fun z=>if G z then 1 else 0)
end MetricKMedianRecovery.RationalSampling

end OAI
