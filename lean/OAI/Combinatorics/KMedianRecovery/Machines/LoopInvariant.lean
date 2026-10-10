import Mathlib
import OAI.Combinatorics.KMedianRecovery.Machines.ResolveResources
import OAI.Combinatorics.KMedianRecovery.Machines.CorrectionSize

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [LinearOrder V] {d : ℕ}
structure Frame (V : Type*) where
  q : ℕ
  n : ℕ
  out : Outcome V

def transition (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k : ℕ) (f : Frame V) : Frame V :=
  match f.out,f.n with
  | .inr s,n+1=>⟨f.q+1,n,step loc distance F v M N precision f.q n k s⟩
  | _,_=>f

def Frame.value (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k : ℕ) (f : Frame V) : Output V :=
  match f.out with
  | .inl o=>o
  | .inr s=>run loc distance F v M N precision k f.q f.n s

lemma transition_value (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k : ℕ) (f : Frame V) :
    (transition loc distance F v M N precision k f).value loc distance F v M N precision k=
      f.value loc distance F v M N precision k := by
  rcases f with ⟨q,n,o⟩
  cases o with
  | inl o=>rfl
  | inr s=>
    cases n with
    | zero=>rfl
    | succ n=>
      rfl
lemma iterate_value (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k j : ℕ) (f : Frame V) :
    ((transition loc distance F v M N precision k)^[j] f).value loc distance F v M N precision k=
      f.value loc distance F v M N precision k := by
  induction j with
  | zero=>rfl
  | succ j ih=>rw [Function.iterate_succ_apply',transition_value,ih]

def Frame.Stopped (f : Frame V) : Prop := match f.out with
  | .inl _=>True
  | .inr _=>f.n=0
lemma iterate_stopped (loc : Fin d→V) (distance : V→Fin d→ℚ) (F : Finset V)
    (v M : ℚ) (N precision k j : ℕ) (f : Frame V) (hn : f.n≤j) :
    ((transition loc distance F v M N precision k)^[j] f).Stopped := by
  induction j generalizing f with
  | zero=>
    rcases f with ⟨q,n,o⟩
    cases o <;> simp only [Function.iterate_zero_apply,Frame.Stopped]
    exact Nat.eq_zero_of_le_zero hn
  | succ j ih=>
    rcases f with ⟨q,n,o⟩
    cases o with
    | inl o=>
      rw [Function.iterate_fixed (show transition loc distance F v M N precision k ⟨q,n,.inl o⟩=⟨q,n,.inl o⟩ from rfl)]
      trivial
    | inr s=>
      cases n with
      | zero=>
        rw [Function.iterate_fixed (show transition loc distance F v M N precision k ⟨q,0,.inr s⟩=⟨q,0,.inr s⟩ from rfl)]
        rfl
      | succ n=>
        rw [Function.iterate_succ_apply]
        exact ih _ (by simpa only [transition] using Nat.le_of_succ_le_succ hn)

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

def Frame.Valid (loc : Fin d→V) (F : Finset V) (v eta lo hi : ℝ) (total k h p : ℕ) (f : Frame V) : Prop :=
  f.q+f.n=total ∧ match f.out with
  | .inl o=>o.Correct loc F v eta lo hi total k ∧ o.Resources F f.q h p
  | .inr s=>Certified loc F v eta lo hi f.q f.n k s ∧ s.Resources F f.q h p ∧ s.correction.Keys f.q

lemma transition_valid (loc : Fin d→V) (distance : V→Fin d→ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v M : ℚ) (eta lo hi : ℝ) (N precision total k H p : ℕ)
    (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hhi : hi≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) (hfar : Height (20*N*M) H)
    (f : Frame V) (hf : f.Valid loc F v eta lo hi total k (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p) :
    (transition loc distance F v M N precision k f).Valid loc F v eta lo hi total k
      (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p := by
  rcases f with ⟨q,n,o⟩
  cases o with
  | inl o=>exact hf
  | inr s=>
    cases n with
    | zero=>exact hf
    | succ n=>
      obtain ⟨hn,hc,hr,hkey⟩:=hf
      change q+(n+1)=total at hn
      have hs:=step_correct loc distance hmetric F v M eta lo hi N precision q n k s hc
        hF hM hN hv hv1 hlo heta hhi hprecision hdiam
      have hb:=step_resources loc distance F v M N precision q n k H p s hr hfar
      have hk:=step_keys loc distance F v M N precision q n k s hkey
      refine ⟨by dsimp only [transition]; omega,?_⟩
      dsimp only [transition]
      cases he : step loc distance F v M N precision q n k s with
      | inl o=>
        rw [he] at hs hb
        exact ⟨by simpa only [Outcome.Correct,hn] using hs,hb⟩
      | inr s=>
        rw [he] at hs hb hk
        exact ⟨hs,hb,hk⟩
lemma valid_stopped_output {loc : Fin d→V} {F : Finset V} {v eta lo hi : ℝ} {total k h p : ℕ}
    {f : Frame V} (hf : f.Valid loc F v eta lo hi total k h p) (hs : f.Stopped) :
    ∃ o,f.out=.inl o := by
  rcases f with ⟨q,n,o⟩
  cases o with
  | inl o=>exact ⟨o,rfl⟩
  | inr s=>
    change n=0 at hs
    subst n
    exact hf.2.1.zero_false.elim
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
