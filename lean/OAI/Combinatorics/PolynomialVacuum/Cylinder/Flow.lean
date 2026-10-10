import OAI.Combinatorics.PolynomialVacuum.Pairing.PairingTarget

namespace OAI

namespace PolynomialVacuumCylinder
open Classical

@[simp] theorem neighbor_neighbor {L : ℕ} (v : Vertex L) (k : Fin 3) :
    neighbor (neighbor v k) k=v := by
  cases v <;> fin_cases k <;> simp [neighbor]

@[simp] theorem reverseGerm_reverseGerm {L : ℕ} (g : Germ L) :
    reverseGerm (reverseGerm g)=g := by
  rcases g with ⟨v,k⟩; simp [reverseGerm]

def upEnd {L : ℕ} (e : Edge L) : Vertex L := .up e.1.1 e.1.2
def downEnd {L : ℕ} (e : Edge L) : Vertex L := neighbor (upEnd e) e.2

def dartSign {L : ℕ} : Germ L → ℤ
  | (.up _ _,_) => 1
  | (.down _ _,_) => -1

noncomputable def dartFlow {L : ℕ} (g : Germ L) : Edge L →₀ ℤ :=
  Finsupp.single (edgeOf g) (dartSign g)
noncomputable def wordFlow {L : ℕ} : Germ L → List Bool → Edge L →₀ ℤ
  | _,[] => 0
  | g,b::w => dartFlow (g.1,outgoingSlot g b)+wordFlow (advance g b) w

noncomputable def edgeBoundary {L : ℕ} : (Edge L →₀ ℤ) →+ (Vertex L →₀ ℤ) :=
  Finsupp.liftAddHom fun e => Finsupp.singleAddHom (upEnd e)-Finsupp.singleAddHom (downEnd e)

@[simp] theorem edgeBoundary_single {L : ℕ} (e : Edge L) (a : ℤ) :
    edgeBoundary (Finsupp.single e a)=Finsupp.single (upEnd e) a-Finsupp.single (downEnd e) a := by
  simp [edgeBoundary]

@[simp] theorem edgeBoundary_dartFlow {L : ℕ} (g : Germ L) :
    edgeBoundary (dartFlow g)=Finsupp.single g.1 1-Finsupp.single (neighbor g.1 g.2) 1 := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> simp [dartFlow,edgeOf,dartSign,upEnd,downEnd,neighbor,Finsupp.single_neg]

@[simp] theorem boundary_wordFlow {L : ℕ} (g : Germ L) (w : List Bool) :
    edgeBoundary (wordFlow g w)=Finsupp.single g.1 1-Finsupp.single (terminalGerm g w).1 1 := by
  induction w generalizing g with
  | nil => simp [wordFlow,terminalGerm]
  | cons b w ih =>
    simp only [wordFlow,map_add,edgeBoundary_dartFlow,ih,terminalGerm]
    simp only [advance]
    abel

theorem boundary_up {L : ℕ} (q : Edge L →₀ ℤ) (i : ZMod L) (j : ℤ) :
    edgeBoundary q (.up i j)=q ((i,j),0)+q ((i,j),1)+q ((i,j),2) := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
    rcases e with ⟨⟨x,y⟩,k⟩
    fin_cases k <;> simp [upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm]

theorem boundary_down {L : ℕ} (q : Edge L →₀ ℤ) (i : ZMod L) (j : ℤ) :
    edgeBoundary q (.down i j)=-(q ((i,j+1),0)+q ((i,j),1)+q ((i+1,j),2)) := by
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
    rcases e with ⟨⟨x,y⟩,k⟩
    have hy : j=y-1 ↔ y=j+1 := by omega
    have hx : i=x-1 ↔ x=i+1 := by constructor <;> intro h <;> rw [h] <;> ring
    fin_cases k <;> simp [upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm,hy,hx]

structure Conserved {L : ℕ} (q : Edge L →₀ ℤ) : Prop where
  up : ∀ i j, q ((i,j),0)+q ((i,j),1)+q ((i,j),2)=0
  down : ∀ i j, q ((i,j+1),0)+q ((i,j),1)+q ((i+1,j),2)=0

theorem closed_word_conserved {L : ℕ} (g : Germ L) (w : List Bool)
    (hc : terminalGerm g w=g) : Conserved (wordFlow g w) := by
  constructor
  · intro i j; rw [← boundary_up,boundary_wordFlow,hc,sub_self]; rfl
  · intro i j
    have h := boundary_down (wordFlow g w) i j
    rw [boundary_wordFlow,hc,sub_self] at h
    simp only [Finsupp.zero_apply] at h
    omega

 
noncomputable def finitePrefix (j : ℤ) : (ℤ →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom fun k => if k<j then AddMonoidHom.id ℤ else 0

@[simp] theorem prefix_single (j k a : ℤ) : finitePrefix j (Finsupp.single k a)=if k<j then a else 0 := by
  simp [finitePrefix]; split_ifs <;> rfl

noncomputable def shiftDown (f : ℤ →₀ ℤ) : ℤ →₀ ℤ := f.mapDomain (fun k => k-1)

@[simp] theorem shiftDown_zero : shiftDown 0=0 := by simp [shiftDown]
@[simp] theorem shiftDown_add (f r : ℤ →₀ ℤ) : shiftDown (f+r)=shiftDown f+shiftDown r := by
  simp [shiftDown,Finsupp.mapDomain_add]
@[simp] theorem shiftDown_single (k a : ℤ) : shiftDown (Finsupp.single k a)=Finsupp.single (k-1) a := by
  simp [shiftDown]

@[simp] theorem shiftDown_apply (f : ℤ →₀ ℤ) (k : ℤ) : shiftDown f k=f (k+1) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f r hf hr => simp only [shiftDown_add,Finsupp.add_apply,hf,hr]
  | single j a =>
    simp only [shiftDown_single,Finsupp.single_apply]
    split_ifs <;> omega

theorem prefix_derivative (f : ℤ →₀ ℤ) (j : ℤ) : finitePrefix j (shiftDown f-f)=f j := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f r hf hr =>
    rw [shiftDown_add,show shiftDown f+shiftDown r-(f+r)=(shiftDown f-f)+(shiftDown r-r) by abel,map_add,hf,hr]
    rfl
  | single k a =>
    simp only [map_sub,shiftDown_single,prefix_single,Finsupp.single_apply]
    split_ifs <;> omega

theorem prefix_step (f : ℤ →₀ ℤ) (j : ℤ) : finitePrefix (j+1) f-finitePrefix j f=f j := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f r hf hr => simp only [map_add,Finsupp.add_apply]; omega
  | single k a => simp only [prefix_single,Finsupp.single_apply]; split_ifs <;> omega

noncomputable def column {L : ℕ} (q : Edge L →₀ ℤ) (i : ZMod L) (k : Fin 3) : ℤ →₀ ℤ :=
  Finsupp.comapDomain (fun j => ((i,j),k)) q (by intro a _ b _ h; exact (Prod.mk.inj (Prod.mk.inj h).1).2)
@[simp] theorem column_apply {L : ℕ} (q : Edge L →₀ ℤ) (i : ZMod L) (k : Fin 3) (j : ℤ) :
    column q i k j=q ((i,j),k) := rfl

theorem column_derivative {L : ℕ} (q : Edge L →₀ ℤ) (hq : Conserved q) (i : ZMod L) :
    shiftDown (column q i 0)-column q i 0=column q i 2-column q (i+1) 2 := by
  ext j
  simp only [Finsupp.sub_apply,shiftDown_apply,column_apply]
  have hu:=hq.up i j
  have hd:=hq.down i j
  omega

noncomputable def potential {L : ℕ} (q : Edge L →₀ ℤ) (a : Face L) : ℤ :=
  -finitePrefix a.2 (column q (a.1+1) 2)

theorem potential_gradient {L : ℕ} (q : Edge L →₀ ℤ) (hq : Conserved q) (i : ZMod L) (j : ℤ) :
    q ((i,j),0)=potential q (i,j)-potential q (i-1,j) ∧
    q ((i,j),1)=potential q (i-1,j+1)-potential q (i,j) ∧
    q ((i,j),2)=potential q (i-1,j)-potential q (i-1,j+1) := by
  have h0 := prefix_derivative (column q i 0) j
  rw [column_derivative q hq i,map_sub] at h0
  have h2 := prefix_step (column q i 2) j
  have hu := hq.up i j
  simp only [column_apply] at h0 h2
  simp only [potential,sub_add_cancel]
  omega

end PolynomialVacuumCylinder

end OAI
