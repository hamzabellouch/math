import Mathlib
import OAI.Combinatorics.UniformKServer.EpochExpectation
import OAI.Combinatorics.UniformKServer.EpochFinite

namespace OAI

noncomputable section
                                     
section

namespace UniformKServer.TapeController
open EpochShadow EpochExpectation

abbrev Tape (k M b : ℕ) := Fin (horizon k M) → Fin b → Bool

structure State (n k M R b : ℕ) where
  localState : {s : EpochControl.State n k // EpochControl.Bounded M s}
  completed : Fin R
  tape : Option (Tape k M b)

instance {n k M R b : ℕ} : Finite (State n k M R b) := by
  let f : State n k M R b → {s : EpochControl.State n k // EpochControl.Bounded M s} ×
      Fin R × Option (Tape k M b) := fun s => (s.localState,s.completed,s.tape)
  apply Finite.of_injective f
  intro a b h
  cases a;cases b
  simp_all [f]

def initial {n k M R b : ℕ} (hR : 0<R) (u : Configuration n k) : State n k M R b :=
  ⟨⟨EpochControl.initial u,EpochControl.bounded_initial M u⟩,⟨0,hR⟩,none⟩

def boundary {n k M R b : ℕ} (s : State n k M R b) (r : Fin n) : Prop :=
  k<(insert r s.localState.val.seen).card ∧ s.completed.val+1=R

instance {n k M R b : ℕ} (s : State n k M R b) (r : Fin n) : Decidable (boundary s r) :=
  inferInstanceAs (Decidable (_ ∧ _))

def chosen {n k M R b : ℕ} (s : State n k M R b) (fresh : Tape k M b) : Tape k M b :=
  s.tape.getD fresh

def choose {n k M R b : ℕ} (hk : 0<k)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (s : State n k M R b) (r : Fin n) (fresh : Tape k M b) : Fin k :=
  EpochControl.label hk (selector N hN (extend (chosen s fresh))) s.localState.val r

def step {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (u : Configuration n k)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (s : State n k M R b) (r : Fin n) (fresh : Tape k M b) : State n k M R b :=
  if hb : boundary s r then initial hR u else
    ⟨EpochControl.boundedStep hk M (selector N hN (extend (chosen s fresh))) s.localState r,
      ⟨s.completed.val+if k<(insert r s.localState.val.seen).card then 1 else 0,by
        have hc := s.completed.isLt
        split_ifs with h
        · have hn : ¬boundary s r := hb
          unfold boundary at hn
          omega
        · omega⟩,some (chosen s fresh)⟩

theorem step_seen {n k : ℕ} (hk : 0<k) (M : ℕ) (T : Selector n k)
    (s : EpochControl.State n k) (r : Fin n) :
    (EpochControl.step hk M T s r).seen=bookStep (k:=k) s.seen r := by
  unfold EpochControl.step
  split_ifs with ht hc
  · simp only [EpochControl.asRaw,Fallback.rawStep,Fallback.isEndpoint,bookStep]
    split_ifs with h <;> simp [h]
  · rfl
  · rfl

noncomputable def expected {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (d : RationalMetric n)
    (u : Configuration n k) (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b) :
    (s : State n k M R b) → Configuration n k → List (Fin n) → ℝ
  | _,_,[] => 0
  | z,s,r::w => BitSampling.mean (fun coins : Tape k M b =>
      (d.distance (s (choose hk N hN z r coins)) r : ℝ)+
        expected hk hR d u N hN (step hk hR u N hN z r coins)
          (serve s r (choose hk N hN z r coins)) w)

def loaded {n k M R b : ℕ} (s : State n k M R b) (coins : Tape k M b) : State n k M R b :=
  {s with tape:=some coins}

theorem step_loaded {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (u : Configuration n k)
    (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (s : State n k M R b) (r : Fin n) (coins fresh : Tape k M b) :
    step hk hR u N hN (loaded s coins) r fresh=step hk hR u N hN (loaded s coins) r coins := by
  unfold step
  split_ifs <;> rfl

theorem loaded_cons {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (d : RationalMetric n)
    (u : Configuration n k) (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (z : State n k M R b) (s : Configuration n k) (r : Fin n) (w : List (Fin n))
    (coins : Tape k M b) :
    expected hk hR d u N hN (loaded z coins) s (r::w)=
      (d.distance (s (choose hk N hN (loaded z coins) r coins)) r : ℝ)+
        expected hk hR d u N hN (step hk hR u N hN (loaded z coins) r coins)
          (serve s r (choose hk N hN (loaded z coins) r coins)) w := by
  rw [expected]
  have he : ∀fresh,choose hk N hN (loaded z coins) r fresh=
      choose hk N hN (loaded z coins) r coins := fun _ => rfl
  simp_rw [he,step_loaded]
  exact BitSampling.mean_const (A:=Tape k M b) _

theorem fresh_mean {n k M R b : ℕ} (hk : 0<k) (hR : 0<R) (d : RationalMetric n)
    (u : Configuration n k) (N : BState n k → Fin n → Fin k → ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (z : State n k M R b) (hz : z.tape=none) (s : Configuration n k) (w : List (Fin n)) :
    expected hk hR d u N hN z s w=
      BitSampling.mean (fun coins : Tape k M b => expected hk hR d u N hN (loaded z coins) s w) := by
  cases w with
  | nil => simp [expected,BitSampling.mean_const]
  | cons r w =>
    rw [expected]
    congr 1
    funext coins
    rw [loaded_cons]
    have hl : choose hk N hN z r coins=choose hk N hN (loaded z coins) r coins := by
      simp [choose,chosen,loaded,hz]
    rw [hl]
    congr 2
    have hb : boundary (loaded z coins) r=boundary z r := rfl
    by_cases h : boundary z r
    · simp only [step,hb,dite_eq_left h]
    · have hn : ¬boundary (loaded z coins) r := h
      simp only [step,dite_eq_right h,dite_eq_right hn]
      simp only [loaded,chosen,hz,Option.getD_none,Option.getD_some]
      rfl

end UniformKServer.TapeController

end


end

end OAI
