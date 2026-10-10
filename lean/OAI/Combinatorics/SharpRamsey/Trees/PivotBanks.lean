import Mathlib
import OAI.Combinatorics.SharpRamsey.Selection.ScheduledBanks
import OAI.Combinatorics.SharpRamsey.Trees.PivotCaps

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables
  ReadyTests PivotGeometry ProjectiveDuality
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

structure Input (n : ℕ) (A : Finset (Projectivization K V))
    (B : Finset (Projectivization K (Module.Dual K V))) (b : ℝ) where
  U : Finset (Projectivization K V)
  UT : Finset (Projectivization K (Module.Dual K V))
  W : Finset (Projectivization K V)
  nonemptyA : A.Nonempty
  nonemptyB : B.Nonempty
  trimA : (9/10:ℝ)*A.card ≤ (A∩U).card
  trimB : (9/10:ℝ)*B.card ≤ (B∩UT).card
  source_nonempty : ((A∩U)∩W).Nonempty
  source_fraction : (A.card:ℝ) ≤ 2*((A∩U)∩W).card
  proposal_ratio : (W.card:ℝ) ≤ exp (b+log 1000000)*((A∩U)∩W).card
  product : (Nat.card K:ℝ)^(n+3)*exp (-b) ≤ (A.card:ℝ)*B.card
  sparse : (incidenceCount A B:ℝ) ≤ (A.card:ℝ)*B.card/(40000*Nat.card K)

variable {n : ℕ} {A : Finset (Projectivization K V)}
  {B : Finset (Projectivization K (Module.Dual K V))} {b : ℝ}

def Input.firstCall (d : Input n A B b) : Call A :=
  ReadyTests.firstCall A d.U d.W B d.UT b d.nonemptyB d.trimB
    d.source_nonempty d.source_fraction d.proposal_ratio d.sparse

abbrev FirstBank (b : ℝ) := Bank (P:=Projectivization K V)
  (Q:=Projectivization K (Module.Dual K V)) (Nat.card K) (b+log 1000000)
abbrev SecondBank (b : ℝ) := Bank (P:=Projectivization K (Module.Dual K V))
  (Q:=Projectivization K (Module.Dual K (Module.Dual K V))) (Nat.card K) (b+log 1000000)

abbrev Input.FirstRow (d : Input n A B b) :=
  Fin (length (Nat.card K) d.firstCall.address) → Projectivization K V

omit [Finite K] [FiniteDimensional K V]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))] in
lemma Input.first_valid (d : Input n A B b) (z : FirstBank (K:=K) (V:=V) b)
    (r : d.FirstRow) (hr : d.firstCall.bankRow (b+log 1000000) n z=some r) :
    d.firstCall.accept n r := by
  exact PublicTables.first_valid _ _ _ _ hr

def Input.secondCall (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (r : d.FirstRow) (hr : d.firstCall.accept n r) : Call B := by
  have hi : firstIndex (d.firstCall.accept n) 1 (r,PUnit.unit)=some 0 := by
    simp only [firstIndex, ite_eq_left hr]
  exact ReadyTests.secondCall hdim A d.U d.W B d.UT d.nonemptyA d.nonemptyB
    d.trimA d.trimB b d.product d.sparse
    (h:=length (Nat.card K) d.firstCall.address) (m:=1) (r,PUnit.unit) 0 hi

lemma Input.second_overhead (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (r : d.FirstRow) (hr : d.firstCall.accept n r) :
    (d.secondCall hdim r hr).overhead=b+log 1000000 := rfl

def Input.next (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) : Option (Call B) :=
  match hr : d.firstCall.bankRow (b+log 1000000) n z with
  | none => none
  | some r => some (d.secondCall hdim r (d.first_valid z r hr))

lemma Input.next_none (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) :
    d.next hdim z=none ↔ d.firstCall.bankRow (b+log 1000000) n z=none := by
  unfold Input.next
  split <;> simp_all

lemma Input.next_overhead (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (c : Call B) (hc : d.next hdim z=some c) :
    c.overhead=b+log 1000000 := by
  unfold Input.next at hc
  split at hc
  · cases hc
  · cases Option.some.inj hc
    rfl

def Input.failure (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) : ℝ :=
  (d.next hdim z).elim 1 (fun c => if c.bankRow (b+log 1000000) n w=none then 1 else 0)

def Input.secondLoss (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (y : Projectivization K (Module.Dual K (Module.Dual K V)))
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) : ℝ :=
  (d.next hdim z).elim 0 (fun c => (c.bankRow (b+log 1000000) n w).elim 0
    (fun r => if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K) r y then 1 else 0))

theorem Input.failure_bound (d : Input n A B b) (hdim : Module.finrank K V=n+3) :
    (∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      ∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w * d.failure hdim z w) ≤
      2*exp (-(Nat.card K:ℝ)) := by
  let e := exp (-(Nat.card K:ℝ))
  have he : 0≤e := (exp_pos _).le
  have hf := d.firstCall.bank_failure_bound (b+log 1000000) rfl hdim
  have hlocal (z : FirstBank (K:=K) (V:=V) b) :
      (∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w * d.failure hdim z w) ≤
      (if d.firstCall.bankRow (b+log 1000000) n z=none then 1 else 0)+e := by
    unfold Input.failure
    cases hc : d.next hdim z with
    | none =>
      have hr := (d.next_none hdim z).mp hc
      simp only [Option.elim_none, mul_one, ite_eq_left hr, PublicTables.Law.total]
      linarith
    | some c =>
      have hr : d.firstCall.bankRow (b+log 1000000) n z≠none := by
        intro hr
        rw [(d.next_none hdim z).mpr hr] at hc
        cases hc
      simp only [Option.elim_some, ite_eq_right hr, zero_add]
      exact c.bank_failure_bound (b+log 1000000) (d.next_overhead hdim z c hc)
        (Subspace.dual_finrank_eq.trans hdim)
  calc
    _ ≤ ∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      ((if d.firstCall.bankRow (b+log 1000000) n z=none then 1 else 0)+e) := by
        apply sum_le_sum
        intro z _
        exact mul_le_mul_of_nonneg_left (hlocal z) ((bankLaw _ _).nonneg z)
    _ = (∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      (if d.firstCall.bankRow (b+log 1000000) n z=none then 1 else 0))+e := by
        simp only [mul_add, sum_add_distrib, ←sum_mul, PublicTables.Law.total, one_mul]
    _ ≤ _ := by dsimp only [e]; linarith

 theorem Input.second_loss_bound (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (y : Projectivization K (Module.Dual K (Module.Dual K V))) :
    (∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      ∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w * d.secondLoss hdim y z w) ≤
      12*(Nat.card K:ℝ)*(∑ x, SupportMixtures.kernel B x * (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  let E := 12*(Nat.card K:ℝ)*(∑ x, SupportMixtures.kernel B x * (if SharpLogRamsey.Incidence.Incident x y then 1 else 0))
  have hE : 0≤E := by
    dsimp only [E]
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun x _ => mul_nonneg (SupportMixtures.kernel_nonneg _ _) (by split_ifs <;> norm_num))
  have hlocal (z : FirstBank (K:=K) (V:=V) b) :
      (∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w * d.secondLoss hdim y z w) ≤ E := by
    unfold Input.secondLoss
    cases hc : d.next hdim z with
    | none => simpa only [Option.elim_none, mul_zero, sum_const_zero] using hE
    | some c =>
      simp only [Option.elim_some]
      exact c.bank_loss_bound (b+log 1000000) (d.next_overhead hdim z c hc)
        (Subspace.dual_finrank_eq.trans hdim) y
  calc
    _ ≤ ∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z * E := by
      apply sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (hlocal z) ((bankLaw _ _).nonneg z)
    _ = E := by rw [←sum_mul, PublicTables.Law.total, one_mul]

end
end SharpLogRamsey.ActualPivot

end

end OAI
