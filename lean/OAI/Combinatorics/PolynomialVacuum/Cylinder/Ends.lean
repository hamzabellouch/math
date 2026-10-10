import OAI.Combinatorics.PolynomialVacuum.Cylinder.Lift
import OAI.Combinatorics.PolynomialVacuum.Cylinder.Indicator

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

noncomputable def totalAt (k : Fin 3) : (Edge M →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom fun e => if e.2=k then AddMonoidHom.id ℤ else 0
@[simp] theorem totalAt_single (k : Fin 3) (e : Edge M) (a : ℤ) :
    totalAt k (Finsupp.single e a)=if e.2=k then a else 0 := by
  simp [totalAt]; split_ifs <;> rfl

noncomputable def columnTotal (q : Edge M →₀ ℤ) (i : ZMod M) : ℤ :=
  (column q i 2).sum fun _ a => a

lemma prefix_full (f : ℤ →₀ ℤ) (j : ℤ) (h : ∀ k∈f.support,k<j) :
    finitePrefix j f=f.sum (fun _ a => a) := by
  simp only [finitePrefix,Finsupp.liftAddHom_apply,Finsupp.sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [h k hk]

lemma potential_top_eq (q : Edge M →₀ ℤ) (i : ZMod M) (j : ℤ)
    (hj : (flowRadius q : ℤ)<j) : potential q (i,j) = -columnTotal q (i+1) := by
  unfold potential columnTotal
  rw [prefix_full]
  intro k hk
  have he : ((i+1,k),2)∈q.support := by simpa only [Finsupp.mem_support_iff,column_apply] using hk
  exact lt_of_le_of_lt (flow_support_height q _ he).2 hj

noncomputable def topValue (q : Edge M →₀ ℤ) : ℤ :=
  potential q (0,(flowRadius q : ℤ)+1)

lemma potential_top_constant [NeZero M] (q : Edge M →₀ ℤ) (hq : Conserved q) (i : ZMod M) (j : ℤ)
    (hj : (flowRadius q : ℤ)<j) : potential q (i,j)=topValue q := by
  have hstep (z : ZMod M) : potential q (z+1,j)=potential q (z,j) := by
    have hz : q ((z+1,j),0)=0 := by
      by_contra hn
      have hh := (flow_support_height q _ (Finsupp.mem_support_iff.mpr hn)).2
      change j≤(flowRadius q : ℤ) at hh
      omega
    have hh := (potential_gradient q hq (z+1) j).1
    simp only [add_sub_cancel_right,hz] at hh
    omega
  have hn (n : ℕ) : potential q ((n : ZMod M),j)=potential q (0,j) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.cast_add,Nat.cast_one,hstep,ih]
  calc
    potential q (i,j)=potential q (0,j) := by simpa using hn i.val
    _ = topValue q := by
      rw [potential_top_eq q _ j hj]
      unfold topValue
      rw [potential_top_eq q _ _ (by omega)]

lemma totalAt_eq_sum_columns [NeZero M] (q : Edge M →₀ ℤ) :
    totalAt 2 q=∑ i : ZMod M,columnTotal q i := by
  induction q using Finsupp.induction_linear with
  | zero =>
    have hz (i : ZMod M) : column (0 : Edge M →₀ ℤ) i 2=0 := by ext j; rfl
    simp [columnTotal,hz]
  | add q r hq hr =>
    have hc (i : ZMod M) : columnTotal (q+r) i=columnTotal q i+columnTotal r i := by
      unfold columnTotal
      have he : column (q+r) i 2=column q i 2+column r i 2 := by ext j; rfl
      rw [he,Finsupp.sum_add_index] <;> simp
    simp only [map_add,hq,hr,hc,Finset.sum_add_distrib]
  | single e a =>
    have hc (i : ZMod M) : columnTotal (Finsupp.single e a) i = if e.1.1=i ∧ e.2=2 then a else 0 := by
      unfold columnTotal
      by_cases h : e.1.1=i ∧ e.2=2
      · have he : column (Finsupp.single e a) i 2=Finsupp.single e.1.2 a := by
          ext j
          rcases e with ⟨⟨x,y⟩,k⟩
          rcases h with ⟨rfl,rfl⟩
          simp [Finsupp.single_apply]
        rw [he]
        simp [h]
      · have he : column (Finsupp.single e a) i 2=0 := by
          ext j
          simp only [column_apply,Finsupp.single_apply,Finsupp.zero_apply]
          split_ifs with he
          · have hh := Prod.mk.inj he
            exact False.elim (h ⟨(Prod.mk.inj hh.1).1,hh.2⟩)
          · rfl
        simp [he,h]
    simp only [totalAt_single,hc]
    by_cases hk : e.2=2
    · simp [hk,eq_comm]
    · simp [hk]

 
theorem totalAt_topValue [NeZero M] (q : Edge M →₀ ℤ) (hq : Conserved q) :
    totalAt 2 q=-(M : ℤ)*topValue q := by
  rw [totalAt_eq_sum_columns]
  have hc (i : ZMod M) : columnTotal q i= -topValue q := by
    have h1 := potential_top_eq q (i-1) ((flowRadius q : ℤ)+1) (by omega)
    have h2 := potential_top_constant q hq (i-1) ((flowRadius q : ℤ)+1) (by omega)
    simp only [sub_add_cancel] at h1
    omega
  simp only [hc,Finset.sum_const,Finset.card_univ,ZMod.card, nsmul_eq_mul]
  ring

def coord (v : PlaneVertex) : ℤ := match v with | .up i _ => i | .down i _ => i

lemma totalAt_dart_project (v : PlaneVertex) (k : Fin 3) :
    totalAt (M:=M) 2 (dartFlow (projectVertex M v,k))=
      coord v-coord (PolynomialVacuumBridge.Corridor.neighbor v k) := by
  cases v <;> fin_cases k <;>
    simp [dartFlow,edgeOf,dartSign,projectVertex,coord,PolynomialVacuumBridge.Corridor.neighbor]

lemma totalAt_word_project (g : PlaneGerm) (w : List Bool) :
    totalAt (M:=M) 2 (wordFlow (projectGerm M g) w)=
      coord g.1-coord (PolynomialVacuumBridge.Corridor.terminalGerm g w).1 := by
  induction w generalizing g with
  | nil => simp [wordFlow,PolynomialVacuumBridge.Corridor.terminalGerm]
  | cons b w ih =>
    rw [wordFlow,map_add]
    have hd := totalAt_dart_project (M:=M) g.1 (PolynomialVacuumBridge.Corridor.outgoingSlot g b)
    change totalAt 2 (dartFlow ((projectGerm M g).1,outgoingSlot (projectGerm M g) b))=_ at hd
    rw [hd,← project_advance,ih]
    simp only [PolynomialVacuumBridge.Corridor.terminalGerm,PolynomialVacuumBridge.Corridor.advance]
    omega

theorem winding_eq_topValue [NeZero M] (g : PlaneGerm) (w : List Bool) (d : ℤ)
    (hc : PolynomialVacuumBridge.Corridor.terminalGerm g w=translateGerm d g)
    (hd : (d : ZMod M)=0) :
    d=(M : ℤ)*topValue (wordFlow (projectGerm M g) w) := by
  have hclosed : terminalGerm (projectGerm M g) w=projectGerm M g := by
    rw [← project_terminal,hc]
    simp [projectGerm,translateGerm,project_translate d hd]
  have h1 := totalAt_topValue (wordFlow (projectGerm M g) w) (closed_word_conserved _ _ hclosed)
  have h2 := totalAt_word_project (M:=M) g w
  rw [hc] at h2
  have ht : coord (translateGerm d g).1=coord g.1+d := by rcases g with ⟨v,k⟩; cases v <;> rfl
  rw [ht] at h2
  nlinarith

end PolynomialVacuumCylinder

end OAI
