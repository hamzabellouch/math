import OAI.Analysis.FourierLLogL.Procedure.Fisher
import OAI.Analysis.FourierLLogL.Edges.Fringe

/-! # Complete spatial wires reading every bit to leaf -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section
namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal

variable {J M j : ℕ} {s : Scene M} {f : Grid M → ℝ}
open scoped Classical

namespace Fork
/-- dry, single-bit price -/
def pitch (q : Fork M) := log 2 - q.probs.entropy
def whistle (q : Fork M) (b : Bool) := log (2*q.probs b)

lemma pitch_nonneg (q : Fork M) : 0 ≤ q.pitch := by
  unfold pitch; have h := entropy_le_log_card q.probs; simpa [sub_nonneg] using h

lemma pitch_eq (q : Fork M) : q.pitch=q.probs.Ex q.whistle := by
  unfold pitch entropy crossE whistle; rw [Ex_neg,sub_neg_eq_add]
  conv_lhs => lhs; rw [← Ex_const q.probs (log 2)]
  rw [← Ex_add]
  exact Ex_congr_mem _ fun i hi => (Real.log_mul (by norm_num) hi.ne').symm

lemma whistle_high (q : Fork M) (b : Bool) :
    max (q.whistle b) 0 ^2 ≤ 4*q.pitch := by
  let x := q.probs
  have H := bit_cost x
  unfold pitch whistle
  change max (log (2*x b)) 0 ^2 ≤ 4*(log 2-x.entropy)
  apply le_trans (b:=(x false-x true)^2) _ H
  by_cases hi : x b=0
  · simp [hi,sq_nonneg]
  have he := log_le_sub_one_of_pos (mul_pos (by norm_num : (0:ℝ)<2)
    ((x.nonneg b).lt_of_ne (Ne.symm hi)))
  have hj : x true+x false=1 := by simpa [Fintype.sum_bool] using x.total
  rw [max_def]
  split_ifs with h
  · simp [sq_nonneg]
  cases b
  · have hE : 2*x false-1=x false-x true := by linarith
    rw [hE] at he; nlinarith
  · have hE : 2*x true-1= -(x false-x true) := by linarith
    rw [hE] at he; nlinarith

end Fork

structure Pulse (M : ℕ) where
  scene : Scene M
  active : Bool
  chosen : Bool

namespace Pulse
def signal (e : Pulse M) := (step e.scene).pitch
def realized (e : Pulse M) := (step e.scene).whistle e.chosen
lemma signal_nonneg (e : Pulse M) : 0 ≤ e.signal := pitch_nonneg _
end Pulse

/-- Generic membership fork, same spatial node both children. -/
structure TossUp (s : Scene M) where
  coord : Grid M → Bool
  dst : Bool → Scene M

def TossUp.snip {s : Scene M} (t : TossUp s) : Fork M := ⟨s,t.dst,t.coord⟩

inductive Wire (M : ℕ) : Scene M → Type
| term (s : Scene M) : Wire M s
| stay (s : Scene M) (v : Pace) (t : Wire M (s.pace v)) : Wire M s
| spot (s : Scene M) (t : TossUp s) (k : ∀ b : Bool, Wire M (t.dst b)) : Wire M s
| link (s : Scene M) (activeStep : Bool) (k : ∀ b : Bool, Wire M (s.smaller b)) : Wire M s

namespace Wire
inductive Part where
| jump | no

def ReadyAt (s : Scene M) : Prop := s.here.ok M ∧ 0 ≤ s.wage

/-- valid with active prefix -/
def Valid {s : Scene M} (t : Wire M s) (a : Bool) : Prop :=
    match t with
    | .term s => ReadyAt s ∧ s.here.lev=M
    | .stay s _ k => ReadyAt s ∧ k.Valid a
    | .spot s u k =>
      ReadyAt s ∧ (∀ b, (u.dst b).here=s.here) ∧ (0 < s.mass → u.snip.TrueLaw) ∧
        ∀ b, (k b).Valid a
    | .link s v k =>
      ReadyAt s ∧ s.here.lev < M ∧ (v=true → a=true) ∧ ∀ b, (k b).Valid v

lemma Valid.atSrc {s : Scene M} {t : Wire M s} {a : Bool} (h : t.Valid a) :
    ReadyAt s := by cases t <;> exact h.1

def read {s : Scene M} (t : Wire M s) (x : Grid M) : List (Pulse M) :=
    match t with
    | .term _ => []
    | .stay _ _ k => k.read x
    | .spot _ u k => (k (u.coord x)).read x
    | .link s v k =>
      let b := (step s).bit x
      ⟨s,v,b⟩ :: (k b).read x

def expenditure {s : Scene M} (t : Wire M s) (f : Pulse M → ℝ) :=
    s.actor.Ex fun x => ((t.read x).map f).sum

lemma linkEx {s : Scene M} (v : Bool) (k : ∀ b, Wire M (s.smaller b))
    (t : List (Pulse M) → Grid M → ℝ) (h : (step s).TrueLaw) :
    s.actor.Ex (fun x => t ((Wire.link s v k).read x) x) = (step s).probs.Ex (fun b =>
      (s.smaller b).actor.Ex fun x => t (⟨s,v,b⟩::(k b).read x) x) := by
  let f := fun (b : Bool) x => t (⟨s,v,b⟩::(k b).read x) x
  exact (expect_bit h f).symm

lemma spotEx {s : Scene M} (u : TossUp s) (k : ∀ b, Wire M (u.dst b)) (t : List (Pulse M) → Grid M → ℝ)
    (h : u.snip.TrueLaw) :
    s.actor.Ex (fun x => t ((Wire.spot s u k).read x) x) = u.snip.probs.Ex (fun b =>
      (u.dst b).actor.Ex fun x => t ((k b).read x) x) := by
  let f := fun (b : Bool) x => t ((k b).read x) x
  exact (expect_bit h f).symm

lemma fee_stay {s : Scene M} (v : Pace) (k : Wire M (s.pace v)) (f : Pulse M → ℝ) :
    (Wire.stay s v k).expenditure f = k.expenditure f := by cases v <;> rfl

lemma fee_spot {s : Scene M} (u : TossUp s) (k : ∀ b, Wire M (u.dst b)) (f : Pulse M → ℝ)
    (h : u.snip.TrueLaw) :
    (Wire.spot s u k).expenditure f = u.snip.probs.Ex (fun b => (k b).expenditure f) :=
  spotEx u k (fun l _ => (l.map f).sum) h

lemma fee_link {s : Scene M} (v : Bool) (k : ∀ b, Wire M (s.smaller b)) (f : Pulse M → ℝ)
    (h : (step s).TrueLaw) :
    (Wire.link s v k).expenditure f = (step s).probs.Ex (fun b => f ⟨s,v,b⟩+(k b).expenditure f) := by
  have hh := linkEx v k (fun l _ => (l.map f).sum) h
  simp_rw [List.map_cons,List.sum_cons,Ex_add,Ex_const] at hh
  unfold expenditure
  rw [hh, Ex_add]


end Wire
end FourierLLogL.Dyadic.Procedure

end OAI
