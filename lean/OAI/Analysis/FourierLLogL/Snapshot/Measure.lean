import OAI.Analysis.FourierLLogL.Capture.Dual
import OAI.Analysis.FourierLLogL.Capture.Curve

open Function Set Filter
open scoped Topology BigOperators ComplexConjugate
noncomputable section

namespace OAI

namespace FourierLLogL.Dyadic.Procedure.Snapshot
open Law Node Real Period Compress.Params Thermal Fund Scene Fork Road Event Journal Wire Pulse Thread Capture
variable {M : ℕ}
open scoped Classical

abbrev RingN (e M : ℕ) := Grid (min e M)
def shade (e : ℕ) (x s : Grid M) : RingN e M :=
    down (min_le_right e M) (s*x)
def shine (e M : ℕ) (z : RingN e M) : ℂ :=
    chi 1 (raise (min_le_right e M) z)

lemma shade_close (e : ℕ) (x s : Grid M) : ‖chi s x-shine e M (shade e x s)‖ ≤ 8*side e := by
  let p := s*x
  let r := raise (min_le_right e M) (shade e x s)
  have HE : chi s x=chi 1 p := by unfold chi p; rw [one_mul]
  have hp : ‖chi 1 p-chi 1 r‖ = ‖1-chi 1 (p-r)‖ := by
    rw [show chi 1 p-chi 1 r = (chi 1 (p-r)-1)*chi 1 r by
      rw [sub_mul,← chi_add,sub_add_cancel,one_mul],norm_mul,norm_chi,mul_one,norm_sub_rev]
  have hi : Dyadic.diam (p-r) ≤ side e := by
    let b := min e M
    have hV : rad (p-r) ≤ 2^(M-b)-1 := snap_dist _ p
    rcases le_total e M with he|he
    · have hh : side M*(2:ℝ)^(M-e)=side e := (descale (p:=⟨e,0⟩) he).symm
      rw [show b=e from min_eq_left he] at hV
      unfold Dyadic.diam; rw [←hh]
      exact mul_le_mul_of_nonneg_left (by linarith) (side_pos _).le
    rw [show b=M from min_eq_right he] at hV
    rw [Nat.sub_self,pow_zero,sub_self] at hV
    unfold Dyadic.diam; have H := hV.antisymm (rad_nonneg _)
    rw [H,mul_zero]; exact (side_pos _).le
  rw [HE]; change ‖chi 1 p-chi 1 r‖ ≤ _
  rw [hp]
  have HH := norm_phase_sq (1:Grid M) (p-r)
  nlinarith [(cost_diam (p-r)).2,side_pos e,diam_nonneg (p-r)]

abbrev TileN (e : ℕ) (d : Finset (Grid M)) := d → RingN e M

def tiles (e : ℕ) (d : Finset (Grid M)) (x : Grid M) : TileN e d :=
    fun i => shade e x i

abbrev Dome (e : ℕ) (d : Finset (Grid M)) := Grid M × TileN e d

def sight (s : Scene M) (b : Bool) (d : Finset (Grid M)) (e : ℕ) (x : Grid M) :
    Law (Dome e d) := (channel (optic s b) x).send (fun y => (y,tiles e d x))


private lemma see_as_H (s : Scene M) (b : Bool) (d : Finset (Grid M)) (e : ℕ) :
    let P := tracker s b
    s.actor.privateH (sight s b d e) =
      P.Hcond Prod.fst (fun i => (i.2, tiles e d i.1)) := by
  intro P
  let g : Grid M × Grid M → Grid M × Dome e d :=
    fun i => (i.1,i.2,tiles e d i.1)
  have H : s.actor.withNext (sight s b d e) = P.send g := by
    apply ext_of_Ex; intro f
    simp_rw [P,tracker,Ex_send,Ex_withNext,sight,Ex_send]
    rfl
  rw [privateH,H,Hcond_send]

lemma sight_budget (s : Scene M) (b : Bool) (d : Finset (Grid M)) (e : ℕ) :
    let v := deficit s (channel (optic s b))
    v ≤ deficit s (sight s b d e) ∧ deficit s (sight s b d e) ≤ v+d.card*e := by
  unfold deficit; intro v
  let P := tracker s b
  let X : Grid M × Grid M → TileN e d := fun i => tiles e d i.1
  let g := fun i : Grid M × Grid M => (i.2,X i)
  change v ≤ levels s-_ ∧ _
  rw [see_as_H]
  have H1 : s.actor.privateH (channel (optic s b))=P.Hcond Prod.fst Prod.snd := rfl
  change levels s-_≤levels s-P.Hcond _ g ∧ levels s-P.Hcond _ g ≤ levels s-_+_
  rw [H1]
  have H := Hcond_antitone P Prod.fst (Y:=g) (Z:=Prod.snd) (fun i j hi => congrArg Prod.fst hi)
  refine ⟨by linarith [H],?_⟩
  have hX := P.H_card X
  have HX : P.H X ≤ (d.card:ℝ)*e := by
    apply hX.trans
    simp only [TileN,RingN,Grid,Fintype.card_fun,Fintype.card_coe,ZMod.card]
    push_cast; rw [Real.log_pow,Real.log_pow]
    gcongr
    have he : (min e M:ℕ) ≤ e := by omega
    have hi : ((min e M:ℕ):ℝ) ≤ e := by exact_mod_cast he
    nlinarith [log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),
      Nat.cast_nonneg (α:=ℝ) (min e M)]
  have h₂ :
      P.Hcond Prod.fst Prod.snd = P.Hcond (fun i => (i.1,X i)) Prod.snd := by
    unfold Hcond; congr 1; apply H_partition; simp [X]
  rw [h₂, Hcond_chain]
  have H₃ : P.Hcond Prod.fst (fun i => (X i,i.2)) = P.Hcond Prod.fst g :=
      P.Hcond_right_partition _ (by simp [g,and_comm])
  rw [H₃]
  linarith [Hcond_le_H P X Prod.snd]


private def switch (n : ℤ) (z : ℂ) :=
    if n=0 then 1 else if n=1 then z else conj z
theorem painted (u : Grid M) (d : Finset (Grid M)) (h : enclosed d 1 u) (e : ℕ) :
    ∃ f : TileN e d → ℂ, (∀ i, ‖f i‖=1) ∧
      ∀ x, ‖chi u x-f (tiles e d x)‖ ≤ d.card*(8*side e) := by
  obtain ⟨v,hv,rfl⟩ := h
  let F (i : TileN e d) := ∏ x : d, switch (v x) (shine e M (i x))
  have Hs (i : ℤ) (z : ℂ) (h : ‖z‖=1) : ‖switch i z‖=1 := by unfold switch; split_ifs <;> simp [h]
  refine ⟨F,?_,?_⟩
  · intro i; unfold F; rw [Complex.norm_prod]
    exact (Finset.prod_eq_one fun j _ => Hs _ _ (norm_chi _ _))
  intro x
  have h1 (i : d) :
      chi (v i • (i.val)) x = switch (v i.val) (chi (i.val) x) := by
    have hx := abs_le.mp (hv i.val i.property)
    have hh : v i.val = -1 ∨ v i.val=0 ∨ v i.val=1 := by omega
    rcases hh with H|H|H <;> simp [H,switch,chi_zero_left,chi_neg']
  have hx : chi (∑ i∈d,v i • i) x = ∏ i : d, switch (v i) (chi (i:Grid M) x) := by
    simp_rw [← h1]; rw [← Finset.sum_attach d,chi_comm,←phaseChar_apply]
    have H := Compress.char_sum (phaseChar x) (fun i : d => (v i.val) • i.val)
    change (phaseChar x) (∑ i : d, v i.val • i.val) = _
    rw [H]; exact Finset.prod_congr rfl fun i _ => chi_comm x _
  let p (i : d) := switch (v i) (chi (i:Grid M) x)
  let q (i : d) := switch (v i) (shine e M (tiles e d x i))
  have hp i : ‖p i‖=1 := Hs _ _ (norm_chi _ _)
  have hq i : ‖q i‖=1 := Hs _ _ (norm_chi _ _)
  have hh (S : Finset d) :
      ‖∏ i∈S,p i - ∏ i∈S,q i‖ ≤ S.card * (8*side e) := by
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      let a := ∏ y∈t,p y
      let b := ∏ y∈t,q y
      rw [Finset.prod_insert hi,Finset.prod_insert hi]
      change ‖p i*a-q i*b‖ ≤ _
      have he : ‖p i-q i‖ ≤ 8*side e := by
        unfold p q tiles switch
        split_ifs
        · simp; exact side_pos e |>.le
        · exact shade_close _ _ _
        · rw [← map_sub,Complex.norm_conj]
          exact shade_close _ _ _
      have hA : ‖a‖=1 := by unfold a; rw [Complex.norm_prod]; exact Finset.prod_eq_one (fun i _ => hp i)
      rw [show p i*a-q i*b=(p i-q i)*a+q i*(a-b) by ring]
      apply le_trans (norm_add_le _ _)
      rw [norm_mul,norm_mul,hA,hq,mul_one,one_mul,Finset.card_insert_of_notMem hi]; push_cast
      change ‖a-b‖ ≤ _ at ih
      nlinarith
  rw [hx]
  simpa only [Finset.card_univ,Fintype.card_coe] using hh Finset.univ

end FourierLLogL.Dyadic.Procedure.Snapshot

end OAI
