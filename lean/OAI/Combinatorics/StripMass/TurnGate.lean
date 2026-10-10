import Mathlib
import OAI.Combinatorics.StripMass.CollisionLeaf

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip.Diagram
noncomputable section
open scoped Classical

namespace Pairing

 

def gateTurn (ga gb ha hb : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![0, gb-ga+3, ha-ga, hb-ga],
    ![ga-gb-3, 0, ha-gb, hb-gb],
    ![ga-ha, gb-ha, 0, hb-ha-3],
    ![ga-hb, gb-hb, ha-hb+3, 0]]

lemma gateTurn_reverse (ga gb ha hb : ℤ) (i j : Fin 4) :
    gateTurn ga gb ha hb j i= -gateTurn ga gb ha hb i j := by
  fin_cases i <;> fin_cases j <;> simp [gateTurn] <;> ring

lemma cap_arcTurn_general {n : ℕ} {p : Pairing n} {a b x y : Fin n}
    (g : Fin n → ℤ) (hab : a.val+1=b.val)
    (hx : p.Adj a x) (hy : p.Adj b y) (hn : ¬p.Adj a b) :
    arcTurn g x a+(g b-g a+3)+arcTurn g b y=arcTurn g x y := by
  have hc:=cap_turn_order hab hx hy hn
  simp only [arcTurn]
  omega

lemma arcTurn_congr {n : ℕ} {g h : Fin n → ℤ} {i j : Fin n}
    (hi : g i=h i) (hj : g j=h j) : arcTurn g i j=arcTurn h i j := by
  simp only [arcTurn,hi,hj]

lemma turnOrder_embedding {n m : ℕ} (f : Fin n → Fin m) {i j : Fin n}
    (hij : f i < f j ↔ i < j) (hji : f j < f i ↔ j < i) :
    turnOrder (f i) (f j)=turnOrder i j := by simp only [turnOrder,hij,hji]

 
structure GatePotentials {n : ℕ} (p q : Pairing n) (a b : Fin n) (t : Tile)
    (g h : Fin n → ℤ) (B : Fin n → ℤ) (T : Fin 4 → ℤ) : Prop where
  old_arc : ∀ i j,p.Adj i j → B j-B i=arcTurn g i j
  tile_arc : ∀ i j,t.Adj i j →
    T j-T i=gateTurn (g a) (g b) (h a) (h b) i j
  input_left : B a=T 0
  input_right : B b=T 1
  output_left : T 2=q.turnPotential h a
  output_right : T 3=q.turnPotential h b
  outside : ∀ i,i≠a → i≠b → B i=q.turnPotential h i

 
def gateBoundary {n : ℕ} (a b : Fin n) (F : Fin n → ℤ) (x y : ℤ) : Fin n → ℤ :=
  fun i=>if i=a then x else if i=b then y else F i

@[simp] lemma gateBoundary_left {n : ℕ} (a b : Fin n) (F : Fin n → ℤ) (x y : ℤ) :
    gateBoundary a b F x y a=x := by simp [gateBoundary]
@[simp] lemma gateBoundary_right {n : ℕ} (a b : Fin n) (hab : a≠b)
    (F : Fin n → ℤ) (x y : ℤ) : gateBoundary a b F x y b=y := by
  simp [gateBoundary,hab.symm]
lemma gateBoundary_other {n : ℕ} (a b : Fin n) (F : Fin n → ℤ) (x y : ℤ)
    (i : Fin n) (ha : i≠a) (hb : i≠b) : gateBoundary a b F x y i=F i := by
  simp [gateBoundary,ha,hb]

lemma gatePotentials_vacant {n : ℕ} (p : Pairing n) (a b : Fin n)
    (_hab : a.val+1=b.val) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i)
    (ha : ¬p.Occupied a) (hb : ¬p.Occupied b) :
    ∃ B T,GatePotentials p p a b .vacant g h B T := by
  refine ⟨p.turnPotential h,![p.turnPotential h a,p.turnPotential h b,
    p.turnPotential h a,p.turnPotential h b],?_,?_,?_,?_,?_,?_,?_⟩
  · intro i j hij
    rw [turnPotential_of_adj h hij]
    apply arcTurn_congr
    · exact hg i (fun he=>ha (he ▸ ⟨j,hij⟩)) (fun he=>hb (he ▸ ⟨j,hij⟩))
    · exact hg j (fun he=>ha (he ▸ ⟨i,hij.symm⟩)) (fun he=>hb (he ▸ ⟨i,hij.symm⟩))
  · intro i j hij
    exact (Tile.vacant_not_occupied i ⟨j,hij⟩).elim
  all_goals simp

lemma gatePotentials_through {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i) (t : Tile)
    (ht : t=.vertical₀ ∨ t=.vertical₁ ∨ t=.verticalPair)
    (hc : (t.Occupied 0 ↔ p.Occupied a) ∧ (t.Occupied 1 ↔ p.Occupied b)) :
    ∃ B T,GatePotentials p p a b t g h B T := by
  let F := p.turnPotential h
  let x := F a-(h a-g a)
  let y := F b-(h b-g b)
  let B := gateBoundary a b F x y
  have hab' : a≠b := by omega
  have he (i : Fin n) : B i=p.turnPotential g i := by
    by_cases hia : i=a
    · subst i; simp only [B,gateBoundary_left,x,F,turnPotential]; omega
    · by_cases hib : i=b
      · subst i; simp only [B,gateBoundary_right _ _ hab',y,F,turnPotential]; omega
      · simp only [B,gateBoundary_other _ _ _ _ _ _ hia hib,F,turnPotential,hg i hia hib]
  refine ⟨B,![x,y,F a,F b],⟨?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i j hij
    rw [he i,he j]
    exact turnPotential_of_adj g hij
  · intro i j hij
    rcases ht with rfl|rfl|rfl <;> fin_cases i <;> fin_cases j <;>
      simp_all [Tile.Adj,Tile.edges,gateTurn,x,y]
  · simp [B]
  · simp [B,gateBoundary,hab'.symm]
  · rfl
  · rfl
  · exact fun i hi hj=>gateBoundary_other a b F x y i hi hj

lemma gatePotentials_cup {n : ℕ} (p : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i)
    (ha : ¬p.Occupied a) (hb : ¬p.Occupied b) :
    ∃ B T,GatePotentials p (p.insertCup a b hab ha hb) a b .cup g h B T := by
  let q := p.insertCup a b hab ha hb
  let F := q.turnPotential h
  have hab' : a<b := by omega
  have hq : q.Adj a b := by simp [q,Adj,insertCup]
  have hF : F b-F a=h b-h a-3 := by
    have he := turnPotential_of_adj h hq
    simpa only [F,arcTurn,turnOrder,hab',ite_true,mul_one] using he
  refine ⟨F,![F a,F b,F a,F b],⟨?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i j hij
    have hqij : q.Adj i j := by
      rcases hij with hij | hij
      · exact Or.inl (Finset.mem_insert_of_mem hij)
      · exact Or.inr (Finset.mem_insert_of_mem hij)
    rw [show F j-F i=arcTurn h i j from turnPotential_of_adj h hqij]
    apply arcTurn_congr
    · exact hg i (fun he=>ha (he ▸ ⟨j,hij⟩)) (fun he=>hb (he ▸ ⟨j,hij⟩))
    · exact hg j (fun he=>ha (he ▸ ⟨i,hij.symm⟩)) (fun he=>hb (he ▸ ⟨i,hij.symm⟩))
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Tile.Adj,Tile.edges,gateTurn]
    omega
  all_goals simp [F,q]

lemma gatePotentials_swap {n : ℕ} (p : Pairing n) (a b : Fin n)
    (_hab : a.val+1=b.val) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i) (t : Tile)
    (ht : t=.diagonal₀ ∨ t=.diagonal₁)
    (hf : ∀ i j,p.Occupied i → p.Occupied j →
      (Equiv.swap a b i < Equiv.swap a b j ↔ i<j)) :
    ∃ B T,GatePotentials p (p.mapOccupied (Equiv.swap a b).toEmbedding hf) a b t g h B T := by
  let q := p.mapOccupied (Equiv.swap a b).toEmbedding hf
  let F := q.turnPotential h
  let f := Equiv.swap a b
  let B : Fin n → ℤ := fun i=>F (f i)+g i-h (f i)
  have hBa : B a=F b+g a-h b := by simp [B,f]
  have hBb : B b=F a+g b-h a := by simp [B,f]
  refine ⟨B,![B a,B b,F a,F b],⟨?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i j hij
    have hi : p.Occupied i := ⟨j,hij⟩
    have hj : p.Occupied j := ⟨i,hij.symm⟩
    have hq : q.Adj (f i) (f j) :=
      (mapOccupied_adj p (Equiv.swap a b).toEmbedding hf i j).mpr hij
    have hF : F (f j)-F (f i)=arcTurn h (f i) (f j) := turnPotential_of_adj h hq
    have ho : turnOrder (f i) (f j)=turnOrder i j :=
      turnOrder_embedding f (hf i j hi hj) (hf j i hj hi)
    dsimp only [B]
    simp only [arcTurn,ho] at hF ⊢
    omega
  · intro i j hij
    rcases ht with rfl|rfl <;> fin_cases i <;> fin_cases j <;>
      simp_all [Tile.Adj,Tile.edges,gateTurn] <;> omega
  · rfl
  · rfl
  · rfl
  · rfl
  · intro i hi hj
    simp [B,f,Equiv.swap_apply_of_ne_of_ne hi hj,hg i hi hj,F,q]

lemma gatePotentials_cap_general {n : ℕ} (p q : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i) (x y : Fin n)
    (hx : p.Adj a x) (hy : p.Adj b y) (hn : ¬p.Adj a b)
    (hqxy : q.Adj x y)
    (hout : ∀ i j,(p.omitTwo a b).Adj i j → q.Adj i j)
    (t : Tile) (ht : t=.cap ∨ t=.capCup)
    (hcup : t=.capCup → q.Adj a b) :
    ∃ B T,GatePotentials p q a b t g h B T := by
  let F := q.turnPotential h
  let u := F x+arcTurn g x a
  let v := u+(g b-g a+3)
  let B := gateBoundary a b F u v
  have hab' : a≠b := by omega
  obtain ⟨hxa,hxb,hya,hyb,hxy⟩ := adjacent_partners hab hx hy hn
  have hFxy : F y-F x=arcTurn g x y :=
    (turnPotential_of_adj h hqxy).trans (arcTurn_congr (hg x hxa hxb) (hg y hya hyb))
  have hcap := cap_arcTurn_general g hab hx hy hn
  have hBa : B a=u := gateBoundary_left _ _ _ _ _
  have hBb : B b=v := gateBoundary_right _ _ hab' _ _ _
  have hBx : B x=F x := gateBoundary_other _ _ _ _ _ _ hxa hxb
  have hBy : B y=F y := gateBoundary_other _ _ _ _ _ _ hya hyb
  have hax : F x-u=arcTurn g a x := by rw [arcTurn_reverse g x a]; dsimp [u]; omega
  have hby : F y-v=arcTurn g b y := by dsimp [v,u]; omega
  refine ⟨B,![u,v,F a,F b],⟨?_,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i j hij
    by_cases hia : i=a
    · subst i
      have hj : j=x := adj_unique hij hx
      subst j
      rw [hBa,hBx]
      exact hax
    · by_cases hja : j=a
      · subst j
        have hi : i=x := adj_unique hij.symm hx
        subst i
        rw [hBa,hBx,arcTurn_reverse g a x]
        omega
      · by_cases hib : i=b
        · subst i
          have hj : j=y := adj_unique hij hy
          subst j
          rw [hBb,hBy]
          exact hby
        · by_cases hjb : j=b
          · subst j
            have hi : i=y := adj_unique hij.symm hy
            subst i
            rw [hBb,hBy,arcTurn_reverse g b y]
            omega
          · rw [show B i=F i from gateBoundary_other _ _ _ _ _ _ hia hib,
              show B j=F j from gateBoundary_other _ _ _ _ _ _ hja hjb]
            exact (turnPotential_of_adj h (hout i j ((omitTwo_adj _ _ _ _ _).mpr
              ⟨hij,hia,hib,hja,hjb⟩))).trans
              (arcTurn_congr (hg i hia hib) (hg j hja hjb))
  · intro i j hij
    have hablt : a<b := by omega
    have hFab : t=.capCup → F b-F a=h b-h a-3 := by
      intro ht'
      have he:=turnPotential_of_adj h (hcup ht')
      simpa only [F,arcTurn,turnOrder,hablt,ite_true,mul_one] using he
    rcases ht with rfl|rfl <;> fin_cases i <;> fin_cases j <;>
      simp_all [Tile.Adj,Tile.edges,gateTurn,v] <;> omega
  · exact hBa
  · exact hBb
  · rfl
  · rfl
  · exact fun i hi hj=>gateBoundary_other _ _ _ _ _ _ hi hj

 

theorem gatePotentials_of_step {n : ℕ} (p q : Pairing n) (a b : Fin n)
    (hab : a.val+1=b.val) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i) (t : Tile)
    (hq : p.tileStep a b hab t=some q) :
    ∃ B T,GatePotentials p q a b t g h B T := by
  cases t with
  | vacant =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_vacant p a b hab g h hg hc.1 hc.2
  | vertical₀ =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_through p a b hab g h hg .vertical₀ (Or.inl rfl)
        (by simp [hc.1,hc.2,Tile.Occupied,Tile.Adj,Tile.edges])
  | vertical₁ =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_through p a b hab g h hg .vertical₁ (Or.inr (Or.inl rfl))
        (by simp [hc.1,hc.2,Tile.Occupied,Tile.Adj,Tile.edges])
  | verticalPair =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_through p a b hab g h hg .verticalPair (Or.inr (Or.inr rfl))
        (by simp [hc.1,hc.2,Tile.Occupied,Tile.Adj,Tile.edges])
  | diagonal₀ =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_swap p a b hab g h hg .diagonal₀ (Or.inl rfl)
        (fun _ _ hi hj=>swap_adjacent_order hab (fun he=>hc.2 (he ▸ hi))
          (fun he=>hc.2 (he ▸ hj)))
  | diagonal₁ =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_swap p a b hab g h hg .diagonal₁ (Or.inr rfl)
        (fun _ _ hi hj=>swap_adjacent_order_lower hab (fun he=>hc.1 (he ▸ hi))
          (fun he=>hc.1 (he ▸ hj)))
  | cup =>
    simp only [tileStep] at hq
    split_ifs at hq with hc
    · cases hq
      exact gatePotentials_cup p a b hab g h hg hc.1 hc.2
  | cap =>
    simp only [tileStep] at hq
    split_ifs at hq with ha hb hn; try cases hq
    apply gatePotentials_cap_general p _ a b hab g h hg (p.partner a ha) (p.partner b hb)
      (p.partner_adj a ha) (p.partner_adj b hb) hn
    · simp [capRemove]
    · intro i j hij
      simp only [capRemove,capSplice_adj]
      exact Or.inr (Or.inr hij)
    · exact Or.inl rfl
    · intro h; cases h
  | capCup =>
    simp only [tileStep] at hq
    split_ifs at hq with ha hb hn; try cases hq
    apply gatePotentials_cap_general p _ a b hab g h hg (p.partner a ha) (p.partner b hb)
      (p.partner_adj a ha) (p.partner_adj b hb) hn
    · simp [capRemove]
    · intro i j hij
      simp only [insertCup_adj,capRemove,capSplice_adj]
      exact Or.inr (Or.inr (Or.inr (Or.inr hij)))
    · exact Or.inr rfl
    · intro _
      simp

end Pairing

 

 


namespace CompactGate
variable {V : Type*} {n : ℕ} {r : V → V → Prop} [Std.Symm r]
  {old : Fin n → V} {p q : Pairing n}

 

theorem transport_potential (hp : GraphRealizes r old p) (a b : Fin n)
    (hab : a.val+1=b.val) (t : Tile) (g h : Fin n → ℤ)
    (hg : ∀ i,i≠a → i≠b → h i=g i)
    (hq : p.tileStep a b hab t=some q) (P : V → ℤ)
    (hP : ∀ i j,p.Adj i j → P (old j)-P (old i)=Pairing.arcTurn g i j) :
    ∃ Q : Sum V (Fin 4) → ℤ,
      (∀ i,Q (boundary old a b i)=q.turnPotential h i) ∧
      (∀ v w,r v w → Q (.inl w)-Q (.inl v)=P w-P v) ∧
      (∀ i j,t.Adj i j → Q (.inr j)-Q (.inr i)=
        Pairing.gateTurn (g a) (g b) (h a) (h b) i j) ∧
      Q (.inl (old a))=Q (.inr 0) ∧ Q (.inl (old b))=Q (.inr 1) := by
  obtain ⟨B,T,hB⟩ := Pairing.gatePotentials_of_step p q a b hab g h hg t hq
  obtain ⟨P',hP',hE⟩ := Graph.renormalize_potential hp P B
    (fun i j hij=>(hB.old_arc i j hij).trans (hP i j hij).symm)
  refine ⟨Sum.elim P' T,?_,hE,hB.tile_arc,?_,?_⟩
  · intro i
    by_cases hia : i=a
    · subst i
      simpa only [boundary_left,Sum.elim_inr] using hB.output_left
    · by_cases hib : i=b
      · subst i
        simpa only [boundary,ite_eq_right hia,ite_true,Sum.elim_inr] using hB.output_right
      · simpa only [boundary,ite_eq_right hia,ite_eq_right hib,Sum.elim_inl,hP'] using hB.outside i hia hib
  · simpa only [Sum.elim_inl,Sum.elim_inr,hP'] using hB.input_left
  · simpa only [Sum.elim_inl,Sum.elim_inr,hP'] using hB.input_right

end CompactGate

namespace Circuit
variable {n : ℕ}

 
inductive TurnGauges : Circuit n → Type
  | nil (g : Fin n → ℤ) : TurnGauges .nil
  | snoc {c : Circuit n} (gc : TurnGauges c) (a : Gate n)
      (h : Fin n → ℤ) : TurnGauges (.snoc c a)

namespace TurnGauges

def final : {c : Circuit n} → TurnGauges c → Fin n → ℤ
  | .nil,.nil g => g
  | .snoc _ _,.snoc _ _ h => h

def Compatible : {c : Circuit n} → TurnGauges c → Prop
  | .nil,.nil _ => True
  | .snoc _ a,.snoc gc _ h => gc.Compatible ∧
      ∀ i,i≠a.left → i≠a.right → h i=gc.final i

 
def edgeTurn (p : Pairing n) : {c : Circuit n} → TurnGauges c →
    c.CompactVertex → c.CompactVertex → ℤ
  | .nil,.nil g,i,j => Pairing.arcTurn g i j
  | .snoc _ _a,.snoc gc _ _h,.inl v,.inl w => gc.edgeTurn p v w
  | .snoc _ a,.snoc gc _ h,.inr i,.inr j =>
      Pairing.gateTurn (gc.final a.left) (gc.final a.right) (h a.left) (h a.right) i j
  | .snoc _ _,.snoc _ _ _,.inl _,.inr _ => 0
  | .snoc _ _,.snoc _ _ _,.inr _,.inl _ => 0

 
theorem potential (p : Pairing n) {c : Circuit n} (gc : TurnGauges c)
    (hc : gc.Compatible) (q : Pairing n) (hq : eval p c=some q) :
    ∃ P : c.CompactVertex → ℤ,
      (∀ i,P (c.compactBoundary i)=q.turnPotential gc.final i) ∧
      ∀ v w,compactWiring p c v w → P w-P v=gc.edgeTurn p v w := by
  induction gc generalizing q with
  | nil g =>
    have hpq : p=q := Option.some.inj hq
    subst q
    refine ⟨p.turnPotential g,fun _=>rfl,?_⟩
    exact fun _ _ h=>Pairing.turnPotential_of_adj g h
  | @snoc c gc a h ih =>
    have ⟨hc,hg⟩ := hc
    cases hr : eval p c with
    | none => simp [eval,hr] at hq
    | some r =>
      have hs : r.tileStep a.left a.right a.adjacent a.tile=some q := by
        simpa only [eval,hr,Option.bind_some] using hq
      obtain ⟨P,hP,hE⟩ := ih hc r hr
      have hPr : ∀ i j,r.Adj i j →
          P (c.compactBoundary j)-P (c.compactBoundary i)=Pairing.arcTurn gc.final i j := by
        intro i j hij
        rw [hP,hP]
        exact Pairing.turnPotential_of_adj _ hij
      obtain ⟨Q,hQ,hOld,hTile,ha,hb⟩ := CompactGate.transport_potential
        (compact_eval_sound p c r hr) a.left a.right a.adjacent a.tile gc.final h hg hs P hPr
      refine ⟨Q,hQ,?_⟩
      intro v w hvw
      cases v with
      | inl v =>
        cases w with
        | inl w => exact (hOld v w hvw).trans (hE v w hvw)
        | inr j =>
          rcases hvw with ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩
          · change Q (.inr 0)-Q (.inl (c.compactBoundary a.left))=0
            omega
          · change Q (.inr 1)-Q (.inl (c.compactBoundary a.right))=0
            omega
      | inr i =>
        cases w with
        | inl w =>
          rcases hvw with ⟨rfl,rfl,_⟩ | ⟨rfl,rfl,_⟩
          · change Q (.inl (c.compactBoundary a.left))-Q (.inr 0)=0
            omega
          · change Q (.inl (c.compactBoundary a.right))-Q (.inr 1)=0
            omega
        | inr j => exact hTile i j hvw

end TurnGauges
end Circuit

 

 


namespace BoundaryInsert
variable {n m : ℕ}

 
def old (k : ℕ) (_hk : k≤n) : Fin n ↪o Fin (n+m) where
  toFun i := ⟨if i.val<k then i.val else i.val+m,by split_ifs <;> omega⟩
  inj' := by intro i j hij; apply Fin.ext; have := congrArg Fin.val hij; dsimp at this; split_ifs at this <;> omega
  map_rel_iff' := by intro i j; change (if i.val<k then i.val else i.val+m) ≤
    (if j.val<k then j.val else j.val+m) ↔ i.val≤j.val; split_ifs <;> omega

def fresh (k : ℕ) (hk : k≤n) : Fin m ↪o Fin (n+m) where
  toFun j := ⟨k+j.val,by omega⟩
  inj' := by intro i j hij; apply Fin.ext; have := congrArg Fin.val hij; dsimp at this; omega
  map_rel_iff' := by intro i j; change k+i.val≤k+j.val ↔ i.val≤j.val; omega

lemma disjoint (k : ℕ) (hk : k≤n) (i : Fin n) (j : Fin m) : old k hk i≠fresh k hk j := by
  intro he
  have := congrArg Fin.val he
  change (if i.val<k then i.val else i.val+m)=k+j.val at this
  split_ifs at this <;> omega

lemma cover (k : ℕ) (hk : k≤n) (i : Fin (n+m)) :
    (∃ j,old k hk j=i) ∨ (∃ j,fresh k hk j=i) := by
  by_cases hi : i.val<k
  · left
    refine ⟨⟨i.val,by omega⟩,?_⟩
    apply Fin.ext
    change (if i.val<k then i.val else i.val+m)=i.val
    simp [hi]
  · by_cases hj : i.val<k+m
    · right
      refine ⟨⟨i.val-k,by omega⟩,?_⟩
      apply Fin.ext
      change k+(i.val-k)=i.val
      omega
    · left
      refine ⟨⟨i.val-m,by omega⟩,?_⟩
      apply Fin.ext
      change (if i.val-m<k then i.val-m else i.val-m+m)=i.val
      rw [ite_eq_right (by omega)]
      omega

 

lemma not_cross (k : ℕ) (hk : k≤n) (a b : Fin n) (i j : Fin m) :
    ¬Pairing.Cross (old k hk a) (old k hk b) (fresh k hk i) (fresh k hk j) := by
  change ¬Pairing.Cross
    (⟨if a.val<k then a.val else a.val+m, _⟩ : Fin (n+m))
    ⟨if b.val<k then b.val else b.val+m, _⟩ ⟨k+i.val, _⟩ ⟨k+j.val, _⟩
  simp only [Pairing.Cross,Fin.lt_def]
  split_ifs <;> omega

 
def pairing (k : ℕ) (hk : k≤n) (p : Pairing n) (t : Pairing m) : Pairing (n+m) where
  val := (p.map (old k hk)).val ∪ (t.map (fresh k hk)).val
  property := by
    have hp := (p.map (old (m:=m) k hk)).property
    have ht := (t.map (fresh (n:=n) k hk)).property
    refine ⟨?_,?_,?_⟩
    · intro a h
      rcases Finset.mem_union.mp h with h|h
      · exact hp.1 a h
      · exact ht.1 a h
    · intro a ha b hb
      rcases Finset.mem_union.mp ha with ha|ha <;>
        rcases Finset.mem_union.mp hb with hb|hb
      · exact hp.2.1 a ha b hb
      · obtain ⟨⟨i,j⟩,hij,he⟩ := Finset.mem_map.mp ha
        obtain ⟨⟨x,y⟩,hxy,hf⟩ := Finset.mem_map.mp hb
        subst a; subst b
        exact Or.inr ⟨disjoint k hk i x,disjoint k hk i y,
          disjoint k hk j x,disjoint k hk j y⟩
      · obtain ⟨⟨i,j⟩,hij,he⟩ := Finset.mem_map.mp ha
        obtain ⟨⟨x,y⟩,hxy,hf⟩ := Finset.mem_map.mp hb
        subst a; subst b
        exact Or.inr ⟨(disjoint k hk x i).symm,(disjoint k hk y i).symm,
          (disjoint k hk x j).symm,(disjoint k hk y j).symm⟩
      · exact ht.2.1 a ha b hb
    · intro a ha b hb
      rcases Finset.mem_union.mp ha with ha|ha <;>
        rcases Finset.mem_union.mp hb with hb|hb
      · exact hp.2.2 a ha b hb
      · obtain ⟨⟨i,j⟩,hij,he⟩ := Finset.mem_map.mp ha
        obtain ⟨⟨x,y⟩,hxy,hf⟩ := Finset.mem_map.mp hb
        subst a; subst b
        intro hh
        exact not_cross k hk i j x y (Or.inl hh)
      · obtain ⟨⟨i,j⟩,hij,he⟩ := Finset.mem_map.mp ha
        obtain ⟨⟨x,y⟩,hxy,hf⟩ := Finset.mem_map.mp hb
        subst a; subst b
        intro hh
        exact not_cross k hk x y i j (Or.inr (Or.inl hh))
      · exact ht.2.2 a ha b hb

end BoundaryInsert
end
end CriticalStrip.Diagram

end OAI
