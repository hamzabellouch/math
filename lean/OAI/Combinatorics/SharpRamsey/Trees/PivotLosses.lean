import Mathlib
import OAI.Combinatorics.SharpRamsey.Trees.PivotDecoder

namespace OAI

section
namespace SharpLogRamsey.ActualPivot
open Finset Real Incidence Validation Selection ScheduledBanks PublicTables
  ReadyTests PivotGeometry ProjectiveDuality TreeDecoder
open scoped Classical BigOperators
noncomputable section
variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
  [Fintype (Projectivization K V)] [Fintype (Projectivization K (Module.Dual K V))]
  [Fintype (Projectivization K (Module.Dual K (Module.Dual K V)))]

def mask (b : ℝ) (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) :
    CapReader (Projectivization K V) (Projectivization K (Module.Dual K V))
      (Code (K:=K) (V:=V) b) := fun _ c=>read b z w (univ,univ) c

omit [Finite K] in
lemma read_mask_first (b : ℝ) (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (c : Code (K:=K) (V:=V) b) :
    (read b z w U c).1=U.1∩(mask b z w U c).1 := by
  ext x
  simp [read,mask,primalCap]

omit [Finite K] in
lemma read_mask_second (b : ℝ) (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b)
    (U : Domains (Projectivization K V) (Projectivization K (Module.Dual K V)))
    (c : Code (K:=K) (V:=V) b) :
    (read b z w U c).2=U.2∩(mask b z w U c).2 := by
  ext x
  simp [read,mask,cap]

variable {n : ℕ} {A : Finset (Projectivization K V)}
  {B : Finset (Projectivization K (Module.Dual K V))} {b : ℝ}

def Input.dualLoss (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (y : Projectivization K (Module.Dual K V))
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) : ℝ :=
  (d.choose hdim z w).elim 0 (fun c=>if y∉(mask b z w (d.U,d.UT) c).2 then 1 else 0)

def Input.primalLoss (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (x : Projectivization K V)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) : ℝ :=
  (d.choose hdim z w).elim 0 (fun c=>if x∉(mask b z w (d.U,d.UT) c).1 then 1 else 0)

lemma Input.dual_loss_le (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (y : Projectivization K (Module.Dual K V))
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) :
    d.dualLoss hdim y z w ≤ (d.firstCall.bankRow (b+log 1000000) n z).elim 0
      (fun r=>if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K) r y then 1 else 0) := by
  unfold Input.dualLoss
  rw [d.firstRow_eq]
  cases hi : d.firstCall.bankIndex (b+log 1000000) n z with
  | none => rw [d.choose_first_fail hdim z w hi]; simp
  | some i =>
    rw [d.choose_of_index hdim z w i hi]
    let c := d.secondCall hdim (rowAt _ (z d.firstCall.address) i) (index_valid _ _ _ i hi)
    change ((c.bankIndex (b+log 1000000) n w).map _).elim _ _ ≤ _
    cases c.bankIndex (b+log 1000000) n w <;> simp [mask,read,cap]
    split_ifs <;> norm_num

lemma Input.primal_loss_eq (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (x : Projectivization K V)
    (z : FirstBank (K:=K) (V:=V) b) (w : SecondBank (K:=K) (V:=V) b) :
    d.primalLoss hdim x z w=d.secondLoss hdim (bidual x) z w := by
  unfold Input.primalLoss Input.secondLoss
  cases hi : d.firstCall.bankIndex (b+log 1000000) n z with
  | none =>
    have hr : d.firstCall.bankRow (b+log 1000000) n z=none := by
      rw [d.firstRow_eq,hi,Option.map_none]
    rw [d.choose_first_fail hdim z w hi,(d.next_none hdim z).mpr hr]
    rfl
  | some i =>
    rw [d.choose_of_index hdim z w i hi,d.next_of_index hdim z i hi]
    let c := d.secondCall hdim (rowAt _ (z d.firstCall.address) i) (index_valid _ _ _ i hi)
    change ((c.bankIndex (b+log 1000000) n w).map _).elim _ _ =
      (c.bankRow (b+log 1000000) n w).elim _ _
    have hr : c.bankRow (b+log 1000000) n w =
        (c.bankIndex (b+log 1000000) n w).map (rowAt _ (w c.address)) :=
      (reconstruct_first _ _ _).symm
    rw [hr]
    cases c.bankIndex (b+log 1000000) n w <;> simp [mask,read,primalCap]
    rfl

theorem Input.dual_loss_bound (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (y : Projectivization K (Module.Dual K V)) :
    (∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      ∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w * d.dualLoss hdim y z w) ≤
      12*(Nat.card K:ℝ)*(∑ x, SupportMixtures.kernel A x *
        (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  apply le_trans _ (d.firstCall.bank_loss_bound (b+log 1000000) rfl hdim y)
  apply sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ ((bankLaw _ _).nonneg z)
  calc
    _ ≤ ∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w *
      (d.firstCall.bankRow (b+log 1000000) n z).elim 0
        (fun r=>if ¬pass SharpLogRamsey.Incidence.Incident (Nat.card K) r y then 1 else 0) := by
      apply sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_left (d.dual_loss_le hdim y z w) ((bankLaw _ _).nonneg w)
    _ = _ := by rw [←sum_mul,PublicTables.Law.total,one_mul]

theorem Input.primal_loss_bound (d : Input n A B b) (hdim : Module.finrank K V=n+3)
    (x : Projectivization K V) :
    (∑ z, (bankLaw (Nat.card K) (b+log 1000000)).mass z *
      ∑ w, (bankLaw (Nat.card K) (b+log 1000000)).mass w * d.primalLoss hdim x z w) ≤
      12*(Nat.card K:ℝ)*(∑ y, SupportMixtures.kernel B y *
        (if SharpLogRamsey.Incidence.Incident x y then 1 else 0)) := by
  simp_rw [d.primal_loss_eq hdim]
  simpa only [ProjectiveDuality.incident_bidual] using d.second_loss_bound hdim (bidual x)

end
end SharpLogRamsey.ActualPivot

end

end OAI
