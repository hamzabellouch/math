import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.PivotCalls

namespace OAI

section
namespace SharpLogRamsey.ScheduledBanks
open Finset Real Validation PublicTables
open scoped Classical BigOperators
noncomputable section
variable (P Q : Type*) [Fintype P] [Fintype Q]

abbrev Address := {W : Finset P // W.Nonempty} × Finset Q × Fin (Fintype.card Q+1)

variable {P Q}
def length (q : ℝ) (a : Address P Q) : ℕ :=
  scheduleLength q a.2.1.card a.2.2.val

def cutoff (q b : ℝ) (a : Address P Q) : ℕ := scheduleCutoff q b (length q a)

abbrev At (q b : ℝ) (a : Address P Q) := Table (Fin (length q a) → P) (cutoff q b a)

abbrev Bank (q b : ℝ) := ∀ a : Address P Q, At q b a

def atLaw (q b : ℝ) (a : Address P Q) : Law (At q b a) where
  mass := tableWeight (rowLaw a.1.1 a.1.2 (length q a)) (cutoff q b a)
  nonneg := tableWeight_nonneg _ _
  total := tableWeight_total _ _

def bankLaw (q b : ℝ) : Law (Bank (P:=P) (Q:=Q) q b) := piLaw (atLaw q b)

theorem integral (q b : ℝ) (a : Address P Q)
    (A : (Fin (length q a) → P) → Prop) (f : (Fin (length q a) → P) → ℝ) :
    (∑ z, (bankLaw q b).mass z * outcome A f (cutoff q b a) (z a)) =
      PublicTables.integral (rowLaw a.1.1 a.1.2 (length q a)) A f (cutoff q b a) := by
  rw [show bankLaw (P:=P) (Q:=Q) q b = piLaw (atLaw q b) from rfl]
  rw [family_integral (atLaw q b) a (fun _ z => outcome A f (cutoff q b a) z)]
  change (∑ s, (outsideLaw (atLaw q b) a).mass s *
    PublicTables.integral (rowLaw a.1.1 a.1.2 (length q a)) A f (cutoff q b a)) = _
  rw [←sum_mul, (outsideLaw (atLaw q b) a).total, one_mul]

end
end SharpLogRamsey.ScheduledBanks

namespace SharpLogRamsey.ReadyTests
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]

def Call.address {S : Finset (Projectivization K V)} (c : Call S) :
    Address (Projectivization K V) (Projectivization K (Module.Dual K V)) :=
  ((⟨c.proposal, c.source_nonempty.mono c.source_proposal⟩), c.domain,
    ⟨c.target.card, Nat.lt_succ_of_le (card_le_univ _)⟩)

def Call.accept {S : Finset (Projectivization K V)} (c : Call S) (n : ℕ) :
    (Fin (length (Nat.card K) c.address) → Projectivization K V) → Prop :=
  implementAccept c.source
    (GoodCap SharpLogRamsey.Incidence.Incident (Nat.card K) c.domain c.target
      (2000*(Nat.card K:ℝ)^(n+3)/S.card))

def Call.bankRow {S : Finset (Projectivization K V)} (c : Call S)
    (b : ℝ) (n : ℕ)
    (z : Bank (P:=Projectivization K V) (Q:=Projectivization K (Module.Dual K V)) (Nat.card K) b) :
    Option (Fin (length (Nat.card K) c.address) → Projectivization K V) :=
  first (c.accept n) (cutoff (Nat.card K) b c.address) (z c.address)

def Call.bankIndex {S : Finset (Projectivization K V)} (c : Call S)
    (b : ℝ) (n : ℕ)
    (z : Bank (P:=Projectivization K V) (Q:=Projectivization K (Module.Dual K V)) (Nat.card K) b) :
    Option (Fin (cutoff (Nat.card K) b c.address)) :=
  firstIndex (c.accept n) (cutoff (Nat.card K) b c.address) (z c.address)

omit [Finite K] [FiniteDimensional K V] in
theorem Call.bank_loss_eq {S : Finset (Projectivization K V)} (c : Call S)
    (b : ℝ) (hb : c.overhead = b) (n : ℕ)
    (y : Projectivization K (Module.Dual K V)) :
    (∑ z, (bankLaw (Nat.card K) b).mass z *
      (c.bankRow b n z).elim 0 (fun row => if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K) row y then 1 else 0)) =
    c.loss n y := by
  have h := ScheduledBanks.integral (Nat.card K) b c.address (c.accept n)
    (fun row => if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K) row y then 1 else 0)
  convert h using 1
  · rfl
  · simp only [Call.loss, Call.accept, Call.address, length, cutoff, hb]
    rfl

omit [Finite K] [FiniteDimensional K V] in
 theorem Call.bank_production_eq {S : Finset (Projectivization K V)} (c : Call S)
    (b : ℝ) (hb : c.overhead = b) (n : ℕ) :
    (∑ z, (bankLaw (Nat.card K) b).mass z * (c.bankRow b n z).elim 0 (fun _ => 1)) =
      c.production n := by
  have h := ScheduledBanks.integral (Nat.card K) b c.address (c.accept n) (fun _ => 1)
  convert h using 1
  · rfl
  · simp only [Call.production, Call.accept, Call.address, length, cutoff, hb]
    rfl

 theorem Call.bank_loss_bound {S : Finset (Projectivization K V)} (c : Call S)
    (b : ℝ) (hb : c.overhead=b) {n : ℕ} (hdim : Module.finrank K V=n+3)
    (y : Projectivization K (Module.Dual K V)) :
    (∑ z, (bankLaw (Nat.card K) b).mass z *
      (c.bankRow b n z).elim 0 (fun row => if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K) row y then 1 else 0)) ≤
    12*(Nat.card K:ℝ)*(∑ x, SupportMixtures.kernel S x * (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  rw [c.bank_loss_eq b hb n y]
  exact c.loss_bound hdim y

 theorem Call.bank_failure_bound {S : Finset (Projectivization K V)} (c : Call S)
    (b : ℝ) (hb : c.overhead=b) {n : ℕ} (hdim : Module.finrank K V=n+3) :
    (∑ z, (bankLaw (Nat.card K) b).mass z * (if c.bankRow b n z = none then 1 else 0)) ≤
      exp (-(Nat.card K:ℝ)) := by
  have he (z) : (if c.bankRow b n z = none then (1:ℝ) else 0) =
      1-(c.bankRow b n z).elim 0 (fun _=>1) := by cases c.bankRow b n z <;> simp
  simp_rw [he, mul_sub, mul_one]
  rw [sum_sub_distrib, (bankLaw (P:=Projectivization K V)
    (Q:=Projectivization K (Module.Dual K V)) (Nat.card K) b).total,
    c.bank_production_eq b hb n]
  exact c.failure_bound hdim

end
end SharpLogRamsey.ReadyTests

end

end OAI
