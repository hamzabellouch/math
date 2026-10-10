import OAI.Combinatorics.PolynomialVacuum.Cylinder.Flow

namespace OAI

namespace PolynomialVacuumCylinder
variable {M : ℕ}
@[simp] theorem traced_append (g : Germ M) (u w : List Bool) :
    traced g (u++w)=traced g u++traced (terminalGerm g u) w := by
  induction u generalizing g with
  | nil => rfl
  | cons b u ih => simp [traced,terminalGerm,ih]
@[simp] theorem terminalGerm_append (g : Germ M) (u w : List Bool) :
    terminalGerm g (u++w)=terminalGerm (terminalGerm g u) w := by
  induction u generalizing g with
  | nil => rfl
  | cons b u ih => simp [terminalGerm,ih]

 
noncomputable def orientedFlow : (Edge M →₀ ℤ) →+ (Germ M →₀ ℤ) :=
  Finsupp.liftAddHom fun e =>
    Finsupp.singleAddHom (upEnd e,e.2) - Finsupp.singleAddHom (downEnd e,e.2)

@[simp] theorem orientedFlow_single (e : Edge M) (a : ℤ) :
    orientedFlow (Finsupp.single e a) =
      Finsupp.single (upEnd e,e.2) a - Finsupp.single (downEnd e,e.2) a := by
  simp [orientedFlow]

@[simp] theorem orientedFlow_dartFlow (g : Germ M) :
    orientedFlow (dartFlow g) = Finsupp.single g 1 - Finsupp.single (reverseGerm g) 1 := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [dartFlow,edgeOf,dartSign,upEnd,downEnd,neighbor,reverseGerm]

 
noncomputable def turnVisit : Germ M → List Bool → (Germ M →₀ ℤ)
  | _, [] => 0
  | g, b :: w =>
      Finsupp.single (g.1,outgoingSlot g b) 1 - Finsupp.single g 1 +
        turnVisit (advance g b) w

 
theorem orientedFlow_wordFlow (g : Germ M) (w : List Bool) :
    orientedFlow (wordFlow g w) =
      turnVisit g w + Finsupp.single g 1 - Finsupp.single (terminalGerm g w) 1 := by
  induction w generalizing g with
  | nil => simp [wordFlow,turnVisit,terminalGerm]
  | cons b w ih =>
      simp only [wordFlow,map_add,orientedFlow_dartFlow,turnVisit,terminalGerm,ih]
      have h : reverseGerm (g.1,outgoingSlot g b) = advance g b := rfl
      rw [h]
      abel

theorem turnVisit_eq_zero_of_not_mem (g : Germ M) (w : List Bool) (v : Vertex M)
    (k : Fin 3) (hv : v ∉ traced g w) : turnVisit g w (v,k) = 0 := by
  classical
  induction w generalizing g with
  | nil => simp [turnVisit]
  | cons b w ih =>
      simp only [traced,List.mem_cons,not_or] at hv
      have hne : (v,k) ≠ g := by intro h; exact hv.1 (congrArg Prod.fst h)
      have hne' : (g.1,outgoingSlot g b) ≠ (v,k) := by
        intro h; exact hv.1 (congrArg Prod.fst h).symm
      simp [turnVisit,ih _ hv.2,hne,hne']

 

theorem simple_closed_word_local (g : Germ M) (b : Bool) (w : List Bool)
    (hN : (traced g (b :: w)).Nodup) (hc : terminalGerm g (b :: w) = g)
    (k : Fin 3) :
    orientedFlow (wordFlow g (b :: w)) (g.1,k) =
      (if k = outgoingSlot g b then 1 else 0) - (if k = g.2 then 1 else 0) := by
  classical
  rw [orientedFlow_wordFlow,hc,add_sub_cancel_right]
  simp only [traced,List.nodup_cons] at hN
  have ht := turnVisit_eq_zero_of_not_mem (advance g b) w g.1 k hN.1
  rcases g with ⟨v,j⟩
  simp [turnVisit,ht,Finsupp.single_apply,eq_comm]

 
theorem orientedFlow_up (q : Edge M →₀ ℤ) (i : ZMod M) (j : ℤ) (k : Fin 3) :
    orientedFlow q (.up i j,k) = q ((i,j),k) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]
  | single e a =>
      rcases e with ⟨⟨x,y⟩,l⟩
      fin_cases l <;> fin_cases k <;>
        simp [orientedFlow_single,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm]

theorem orientedFlow_down (q : Edge M →₀ ℤ) (i : ZMod M) (j : ℤ) (k : Fin 3) :
    orientedFlow q (.down i j,k) = -q (edgeOf (.down i j,k)) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
      rcases e with ⟨⟨x,y⟩,l⟩
      have hy : j = y - 1 ↔ y = j + 1 := by omega
      have hx : i = x - 1 ↔ x = i + 1 := by constructor <;> intro h <;> rw [h] <;> ring
      fin_cases l <;> fin_cases k <;>
        simp [orientedFlow_single,edgeOf,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm,hy,hx]

 

def RepresentsFlow (p : Face M → ℤ) (q : Edge M →₀ ℤ) : Prop :=
  ∀ g : Germ M, orientedFlow q g = p (leftFace g) - p (rightFace g)

theorem closed_word_has_potential (g : Germ M) (w : List Bool)
    (hc : terminalGerm g w = g) :
    RepresentsFlow (potential (wordFlow g w)) (wordFlow g w) := by
  intro d
  have hp := potential_gradient (wordFlow g w) (closed_word_conserved g w hc)
  rcases d with ⟨v,k⟩
  cases v with
  | up i j =>
      have h := hp i j
      fin_cases k <;>
        simp [orientedFlow_up,leftFace,rightFace,reverseGerm,neighbor] <;> omega
  | down i j =>
      have h0 := (hp i (j+1)).1
      have h1 := (hp i j).2.1
      have h2 := (hp (i+1) j).2.2
      fin_cases k <;>
        simp [orientedFlow_down,edgeOf,leftFace,rightFace,reverseGerm,neighbor] at * <;> omega

@[simp] theorem wordFlow_append (g : Germ M) (u w : List Bool) :
    wordFlow g (u ++ w) = wordFlow g u + wordFlow (terminalGerm g u) w := by
  induction u generalizing g with
  | nil => simp [wordFlow,terminalGerm]
  | cons b u ih => simp [wordFlow,terminalGerm,ih,add_assoc]

 

theorem closed_word_rotate (g : Germ M) (u w : List Bool)
    (hN : (traced g (u ++ w)).Nodup) (hc : terminalGerm g (u ++ w) = g) :
    let g' := terminalGerm g u
    (traced g' (w ++ u)).Nodup ∧
    terminalGerm g' (w ++ u) = g' ∧ wordFlow g' (w ++ u) = wordFlow g (u ++ w) := by
  dsimp only
  have ht : terminalGerm (terminalGerm g u) w = g := by simpa using hc
  rw [traced_append] at hN
  simp only [traced_append,terminalGerm_append,wordFlow_append,ht]
  exact ⟨List.nodup_append_comm.mp hN,trivial,add_comm _ _⟩

def LocalContour (q : Edge M →₀ ℤ) (g : Germ M) (b : Bool) : Prop :=
  ∀ k : Fin 3, orientedFlow q (g.1,k) =
    (if k = outgoingSlot g b then 1 else 0) - (if k = g.2 then 1 else 0)

def WordContour (q : Edge M →₀ ℤ) : Germ M → List Bool → Prop
  | _, [] => True
  | g, b :: w => LocalContour q g b ∧ WordContour q (advance g b) w

theorem wordContour_of_splits (q : Edge M →₀ ℤ) (g : Germ M) (w : List Bool)
    (hs : ∀ u b v, w = u ++ b :: v → LocalContour q (terminalGerm g u) b) :
    WordContour q g w := by
  induction w generalizing g with
  | nil => trivial
  | cons b w ih =>
      refine ⟨by simpa only [terminalGerm] using hs [] b w rfl, ih (advance g b) ?_⟩
      intro u c v hv
      simpa only [terminalGerm] using hs (b :: u) c v (by simp [hv])

 
theorem simple_closed_word_contour (g : Germ M) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g) :
    WordContour (wordFlow g w) g w := by
  apply wordContour_of_splits
  intro u b v h
  subst w
  obtain ⟨hN',hc',hq⟩ := closed_word_rotate g u (b :: v) hN hc
  rw [← hq]
  intro k
  exact simple_closed_word_local (terminalGerm g u) b (v ++ u) hN' hc' k

 

theorem localContour_sides (p : Face M → ℤ) (q : Edge M →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ M) (b : Bool) (hl : LocalContour q g b) :
    p (rightFace (advance g b)) = p (rightFace g) ∧
    p (leftFace (advance g b)) = p (leftFace g) ∧
    p (rightFace g) - p (leftFace g) = 1 := by
  have h0 := (hp (g.1,0)).symm.trans (hl 0)
  have h1 := (hp (g.1,1)).symm.trans (hl 1)
  have h2 := (hp (g.1,2)).symm.trans (hl 2)
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;> cases b <;>
    simp [advance,outgoingSlot,leftFace,rightFace,reverseGerm,neighbor] at * <;> omega

 
theorem wordContour_sides (p : Face M → ℤ) (q : Edge M →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ M) (w : List Bool) (hw : WordContour q g w) :
    p (rightFace (terminalGerm g w)) = p (rightFace g) ∧
      p (leftFace (terminalGerm g w)) = p (leftFace g) := by
  induction w generalizing g with
  | nil => exact ⟨rfl,rfl⟩
  | cons b w ih =>
      obtain ⟨hr,hl,_⟩ := localContour_sides p q hp g b hw.1
      obtain ⟨hr',hl'⟩ := ih (advance g b) hw.2
      exact ⟨hr'.trans hr,hl'.trans hl⟩

@[simp] theorem rightFace_reverse (g : Germ M) :
    rightFace (reverseGerm g) = leftFace g := by simp [rightFace]

@[simp] theorem reverseGerm_advance (g : Germ M) (b : Bool) :
    reverseGerm (advance g b) = (g.1,outgoingSlot g b) := by
  simp [reverseGerm,advance]

def canonicalDart (e : Edge M) : Germ M := (upEnd e,e.2)

theorem canonicalDart_edgeOf (g : Germ M) :
    canonicalDart (edgeOf g) = g ∨ canonicalDart (edgeOf g) = reverseGerm g := by
  rcases g with ⟨v,k⟩
  cases v <;> fin_cases k <;>
    simp [canonicalDart,edgeOf,upEnd,reverseGerm,neighbor]

def SideValues (p : Face M → ℤ) (L R : ℤ) (g : Germ M) : Prop :=
  (p (leftFace g) = L ∨ p (leftFace g) = R) ∧
    (p (rightFace g) = L ∨ p (rightFace g) = R)

theorem SideValues.reverse {p : Face M → ℤ} {L R : ℤ} {g : Germ M}
    (h : SideValues p L R g) : SideValues p L R (reverseGerm g) := by
  exact ⟨h.2,by simpa only [rightFace_reverse] using h.1⟩

theorem SideValues.canonical {p : Face M → ℤ} {L R : ℤ} {g : Germ M}
    (h : SideValues p L R g) : SideValues p L R (canonicalDart (edgeOf g)) := by
  rcases canonicalDart_edgeOf g with he | he
  · exact he ▸ h
  · exact he ▸ h.reverse

 
theorem wordFlow_edge_sides (p : Face M → ℤ) (q : Edge M →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ M) (w : List Bool) (hw : WordContour q g w)
    (e : Edge M) (he : wordFlow g w e ≠ 0) :
    SideValues p (p (rightFace g)) (p (leftFace g)) (canonicalDart e) := by
  classical
  induction w generalizing g with
  | nil => simp [wordFlow] at he
  | cons b w ih =>
      obtain ⟨hr,hl,_⟩ := localContour_sides p q hp g b hw.1
      by_cases hz : dartFlow (g.1,outgoingSlot g b) e = 0
      · have ht : wordFlow (advance g b) w e ≠ 0 := by
          simpa only [wordFlow,Finsupp.add_apply,hz,zero_add] using he
        have hs := ih (advance g b) hw.2 ht
        rw [hr,hl] at hs
        exact hs
      · have heq : edgeOf (g.1,outgoingSlot g b) = e := by
          by_contra h
          exact hz (by simp [dartFlow,h])
        have hs : SideValues p (p (rightFace g)) (p (leftFace g)) (advance g b) :=
          ⟨Or.inr hl,Or.inl hr⟩
        have hs' := hs.reverse.canonical
        simpa only [reverseGerm_advance,heq] using hs'

end PolynomialVacuumCylinder

end OAI
