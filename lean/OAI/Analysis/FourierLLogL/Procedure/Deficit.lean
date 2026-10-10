import OAI.Analysis.FourierLLogL.Procedure.Fork
import OAI.Analysis.FourierLLogL.Finite.Signal

/-! # Conditional entropy on a fork with a fixed input signal -/
open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure
open Law Node Real Period Compress.Params Thermal Fund Scene Fork
variable {M J j : ℕ} {s : Scene M} {f : Grid M → ℝ}
variable {α : Type} [Fintype α]
open scoped Classical

/-- Remaining number of bits in nats -/
def levels (s : Scene M) := ((M-s.here.lev:ℕ):ℝ)*log 2
def deficit (s : Scene M) (k : Grid M → Law α) :=
    levels s - s.actor.privateH k
def sideH (v : Fork M) (k : Grid M → Law α) :=
    (v.src.actor.withNext k).Hcond (fun i => v.bit i.1) Prod.snd


lemma cap_entropy (s : Scene M) (hp : s.here.ok M) (hh : 0 ≤ s.wage) (hm : 0 < s.mass) :
    s.actor.entropy ≤ levels s := by
  apply le_trans (entropy_le_log_size _ (s.here.group M) ?_)
  · rw [group_card hp.1 hp.2,wid]; push_cast; rw [log_pow]
    exact le_rfl
  intro i hi
  exact (mem_group _ _).mpr (piece_support hp (actor_def hp hh hm) i hi)

lemma deficit_nonneg (s : Scene M) (hp : s.here.ok M) (hh : 0 ≤ s.wage) (hm : 0 < s.mass)
    (k : Grid M → Law α) : 0 ≤ deficit s k :=
  sub_nonneg.mpr ((privateH_le _ _).trans (cap_entropy _ hp hh hm))

lemma levels_child (s : Scene M) (hb : s.here.lev < M) (b : Bool) :
    levels (s.smaller b) = levels s - log 2 := by
  unfold levels
  have He : M - s.here.lev = M - (s.smaller b).here.lev +1 := by
    have H : (s.smaller b).here.lev = s.here.lev+1 := by cases b <;> rfl
    omega
  rw [He]; push_cast; ring

lemma conditioned_balance (k : Grid M → Law α) (v : Fork M) (h : v.TrueLaw) :
    v.probs.Ex (fun b => (v.dst b).actor.privateH k) + sideH v k =
      v.src.actor.privateH k := by
  have hi (b) (hi : 0 < v.probs b) :
      v.src.actor.after v.bit b=(v.dst b).actor := by
    apply Law.ext; intro x
    apply mul_left_cancel₀ hi.ne'
    rw [local_law h]
    exact send_mul_after _ _ _ _
  have He := det_channel v.src.actor v.bit k
  rw [← He]
  unfold sideH
  congr 1
  exact Ex_congr_mem _ (fun x hx => by rw [hi x hx])

lemma old_entropy_cost (v : Fork M) (k : Grid M → Law α) :
    sideH v k ≤ v.probs.entropy := by
  let P := v.src.actor.withNext k; let B : Grid M × α → Bool := fun x => v.bit x.1
  have he : P.send B = v.probs := by
    have HH := send_send P Prod.fst v.bit
    rw [send_fst_withNext v.src.actor k] at HH
    exact HH.symm
  apply le_trans (Hcond_le_H P B Prod.snd); rw [Law.H,he]

/-- Observation mass relative to s.norm. -/
def hist (s : Scene M) (k : Grid M → Law α) (i : α) :=
    ∑ x : Grid M, wt s.here s.wage s.norm x*k x i
def diff (s : Scene M) (k : Grid M → Law α) (i : α) :=
    (hist (s.smaller false) k i - hist (s.smaller true) k i)/2

def fisher (s : Scene M) (k : Grid M → Law α) :=
    ∑ i : α, (diff s k i)^2 / hist s k i

lemma hist_special (s : Scene M) (i : Grid M) (A : Form M) :
    hist s (channel A) i = Mz s.here s.wage s.norm A i := rfl

lemma hist_source (k : Grid M → Law α) (s : Scene M) (hp : s.here.ok M)
    (hh : 0 ≤ s.wage) (i : α) :
    hist s k i = (s.mass / s.norm) * s.actor.through k i := by
  rw [through_apply]
  unfold hist wt Ex; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x hx => by rw [← mass_actor hp hh]; ring

lemma bit_cost (Q : Law Bool) :
    (Q false-Q true)^2 ≤ 4*(log 2-Q.entropy) := by
  have H := tv_sq_le_kl (P:=Q) (Q:=uniform Bool)
    (fun i hi => by rw [uniform_apply]; positivity)
  have Ht : Q true + Q false = 1 := by simpa only [Fintype.sum_bool] using Q.total
  unfold tv kl crossE at H
  simp_rw [Fintype.sum_bool, uniform_apply,Fintype.card_bool, Nat.cast_ofNat, Ex_const,
    Real.log_inv] at H
  rw [show Q false-2⁻¹= -(Q true-2⁻¹) by linarith,abs_neg] at H
  rw [show Q false = 1-Q true by linarith]
  nlinarith [sq_abs (Q true-2⁻¹)]

lemma bit_def (s : Scene M) (k : Grid M → Law α) (hp : s.here.valid)
    (he : s.here.lev < M) (hh : 0 ≤ s.wage) (hm : 0 < s.mass) (hn : 0 < s.norm) :
    s.norm/s.mass * fisher s k ≤ 4*(log 2-sideH (step s) k) := by
  let v := step s
  have HV : v.TrueLaw := step_true hp he hh hm
  let R := s.actor.withNext k
  let P := R.send Prod.snd
  let z := fun x : Grid M × α => v.bit x.1
  let Q (i) := (R.after Prod.snd i).send z
  have H0 b i :
      v.probs b * ((s.smaller b).actor.through k) i = R.send (fun x => (z x,x.2)) (b,i) := by
    let C := fun x : Grid M × α => (z x,x.2)
    rw [through_apply, Ex,Finset.mul_sum]
    simp_rw [← mul_assoc]
    rw [send_apply,prob_eq,Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x hx => ?_
    change (v.probs b*(v.dst b).actor x)*k x i = ∑ y, if C (x,y)=(b,i) then R (x,y) else 0
    rw [local_law HV]
    by_cases h : v.bit x=b
    · rw [ite_eq_left h]
      simp [C,z,h,R,withNext_apply]

      exact Or.inl rfl
    rw [ite_eq_right h]; simp [C,z,h]
  have HH (b i) : hist (s.smaller b) k i =
      (s.mass/s.norm)*(2*P i*Q i b) := by
    rw [hist_source k (s.smaller b) (child_ok _ hp he b) hh,step_mass HV]
    have HC := H0 b i
    rw [joint_after R z Prod.snd] at HC
    change _ = P i*Q i b at HC
    change 2*v.probs b*s.mass/s.norm*((s.smaller b).actor.through k i) = _
    rw [mul_assoc (a:=2) (b:=P i),← HC]; ring
  have hP (i) :
      hist s k i = s.mass/s.norm*P i := by rw [hist_source _ _ ⟨hp,he.le⟩ hh]; unfold P R; rw [send_snd_withNext]
  have ht i : s.norm/s.mass*((diff s k i)^2 / hist s k i) = P i*(Q i false-Q i true)^2 := by
    unfold diff; rw [HH,HH,hP]
    rcases eq_or_lt_of_le (P.nonneg i) with He|He
    · simp [← He]
    field_simp
  let F (i : α) := log 2-(Q i).entropy
  calc
    _ = P.Ex fun i => (Q i false-Q i true)^2 := by rw [fisher,Finset.mul_sum]; simp_rw [ht]; rfl
    _ ≤ P.Ex fun i => 4*F i := Ex_mono _ (fun i => bit_cost _)
    _ = _ := by
      unfold F sideH; rw [Ex_lmul, Ex_sub (f:=fun i => log 2),Ex_const,Hcond_after]
      rfl

lemma space_deficit (s : Scene M) (k : Grid M → Law α) (hp : s.here.valid)
    (he : s.here.lev < M) (hh : 0 ≤ s.wage) (hm : 0 < s.mass) (hn : 0 < s.norm) :
    (step s).probs.Ex (fun b => deficit (s.smaller b) k) +
      (1/4:ℝ)*(s.norm/s.mass)*fisher s k ≤ deficit s k := by
  let v := step s
  have H := conditioned_balance k v (step_true hp he hh hm)
  have HH := bit_def s k hp he hh hm hn
  unfold deficit
  simp_rw [levels_child s he, Ex_sub (f:=fun _ => levels s - log 2),Ex_const]
  change (step s).probs.Ex (fun b => (s.smaller b).actor.privateH k)+sideH (step s) k=s.actor.privateH k at H
  dsimp only [step] at *
  rw [mul_assoc]
  linarith

lemma member_deficit (s : Scene M) (k : Grid M → Law α) (u : Update j M s.here)
    (H : (toss s u).TrueLaw) :
    let v := toss s u
    v.probs.Ex (fun b => deficit (v.dst b) k) ≤ deficit s k + v.probs.entropy := by
  intro v
  have he := conditioned_balance k v H
  have hV : ∀ b, levels (v.dst b)=levels s := by intro b; cases b <;> rfl
  unfold deficit
  simp_rw [hV,Ex_sub (f:=fun _ => levels s),Ex_const]
  change _+_ = s.actor.privateH k at he
  linarith [old_entropy_cost v k]

end FourierLLogL.Dyadic.Procedure

end OAI
