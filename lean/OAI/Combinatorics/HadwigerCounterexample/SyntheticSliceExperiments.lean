import OAI.Combinatorics.HadwigerCounterexample.CommonPredictions

namespace OAI

/-! # Synthetic Slice Experiments -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module Function Finset
open scoped BigOperators
variable {p : Shape} {n : ℕ}

abbrev Punch (p : Shape) := ProbeIdx p.g × Fin p.r
abbrev Gauge (p : Shape) := Punch p × Bool
def gaugeAddr (p : Shape) (i : Gauge p) := if i.2 then 2*i.1.2.val else 2*i.1.2.val+1
def usesPunch (p : Shape) (l : Tag p.g) (f : Flavor p.g) (i : Punch p) := f.keeps l
  (asBlock i.1)
instance (p : Shape) (l f i) : Decidable (usesPunch p l f i) := Classical.propDecidable _

abbrev Tickets (p : Shape) := Vec (Gauge p)
def punchField (p : Shape) (x : Knobs p.g n) : Tickets p :=
  fun i => zget (x (asBlock i.1.1)) (gaugeAddr p i)
def issued (p : Shape) (w : Tickets p) (x : Knobs p.g n) := punchField p x=w

def rung (p : Shape) (n : ℕ) (w : Tickets p) : Wgt (Knobs p.g n) :=
  onW (spins p n) (issued p w)
def ticketsFee (p : Shape) := (1/2:ℝ)^Fintype.card (Gauge p)
theorem ticketsFee_pos (p : Shape) : 0<ticketsFee p := by unfold ticketsFee; positivity
set_option maxHeartbeats 800000 in
theorem rungPrice (n : ℕ) (w : Tickets p) (h : 2*p.r≤n) :
    pr (spins p n) (issued p w)=ticketsFee p := by
  classical
  have he i : gaugeAddr p i<n := by
    rcases i with ⟨⟨i,j⟩,b⟩
    have := j.isLt
    cases b <;> simp only [gaugeAddr]
    all_goals
      simp
      omega
  let g : Gauge p → BaseIdx p.g n := fun i => (asBlock i.1.1,⟨gaugeAddr p i,he i⟩)
  have hi : Injective g := by
    rintro ⟨⟨i,j⟩,c⟩ ⟨⟨k,l⟩,d⟩ hh
    obtain rfl : i=k := asBlock_inj (congrArg Prod.fst hh)
    have hh := congrArg (fun x : BaseIdx p.g n=>x.2.val) hh
    cases c <;> cases d
    all_goals
      simp only [g,gaugeAddr,Bool.false_eq_true, ↓reduceIte] at hh
      first
      | solve | omega
      | solve | simp [Fin.ext (show j.val=l.val from by omega)]
  let e : Base p.g n≃Knobs p.g n := ⟨curry,uncurry,fun _=>rfl,fun _=>rfl⟩
  have hh (x : Base p.g n) : issued p w (e x)↔ ∀ i,x (g i)=w i := by
    unfold issued
    rw [funext_iff]
    simp only [punchField,zget,dite_eq_left (he _)]
    rfl
  rw [spins,←draws_unif,← unif_equiv e,mapW_pr]
  simp_rw [hh]; rw [draws_unif]
  change pr (prodW (fun (_ : BaseIdx p.g n)=>unif)) _= _
  rw [prodW_pr_inj hi (fun _=>unif_law) (fun i y=>y=w i)]
  simp only [pr_point',unif_apply,F,ZMod.card,ticketsFee]
  simp

theorem ticketLaw (n : ℕ) (w : Tickets p) (h : 2*p.r≤n) : IsLaw (rung p n w) :=
  on_law (spins_law p n).nz ((ticketsFee_pos p).trans_eq (rungPrice n w h).symm)
theorem ticketFlow (n : ℕ) (w : Tickets p) (h : 2*p.r≤n) :
    mapW (rung p n w) (freePart p)=unif := by
  refine fresh_Z p n (issued p w) (fun x y=>?_) (ticketLaw n w h)
  have hi : punchField p (x+Pi.single Block.Z y)=punchField p x := by
    classical
    funext i
    have hh : asBlock i.1.1≠Block.Z := by
      rcases i with ⟨⟨⟨i,j⟩|⟨⟩,b⟩,c⟩ <;> simp [asBlock,Block.O,Block.S,Block.Z]
    unfold punchField; simp only [Pi.add_apply,Pi.single_eq_of_ne hh,add_zero]
  unfold issued; rw [hi]
theorem ticketCap (n : ℕ) (w : Tickets p) (h : 2*p.r≤n) :
    ∀ x,rung p n w x≤(ticketsFee p)⁻¹ * spins p n x :=
  on_mon (spins_law p n).nz (ticketsFee_pos p) (le_of_eq (Eq.symm (rungPrice n w h)))

def tabGram (p : Shape) (l : Tag p.g) (f : Flavor p.g) (x y : Tickets p) :=
    ∑ i:Punch p, if usesPunch p l f i then x (i,true)*y (i,false) else 0

theorem tabGram_sound (p : Shape) (n : ℕ) (l : Tag p.g) (s : Label p.b) (f : Flavor p.g)
    (x y : Knobs p.g n) (m : Mixer p n) (hj : 1 ≤ p.j) :
    let E:=selfM p n m.mixM
    evmat E (spring p l s f x) (spring p l s f y)=tabGram p l f (punchField p x)
      (punchField p y) := by
  classical
  intro E
  let z (x : Knobs p.g n) := lit f l x
  let A (B : Block p.g) := test p n B (z x) (z y)
  let h i := usesPunch p l f i
  have hX (i : ProbeIdx p.g) :
      A (asBlock i) = ∑ j : Fin p.r, (fun t:Punch p => if usesPunch p l f t then
        punchField p x (t,true)*punchField p y (t,false) else 0) (i,j) := by
    unfold A test z; refine Finset.sum_congr rfl fun j _=>?_
    let B := asBlock i
    have he (u : Knobs p.g n) (k) :
        readBit (lit f l u) B k=if f.keeps l B then zget (u B) k else 0 := by
      by_cases hh : k<n <;> simp [lit,zget,readBit,hh]
    by_cases ht : f.keeps l B
    · rw [he,he,ite_eq_left ht,ite_eq_left ht]
      exact Eq.symm (ite_eq_left (show usesPunch p l f (i,j) from ht))
    rw [he,he,ite_eq_right ht,ite_eq_right ht,zero_mul]
    exact Eq.symm (ite_eq_right (show ¬usesPunch p l f (i,j) from ht))
  rw [←mpair_outer]; unfold E spring selfM; simp_rw [mpair_add,mpair_sum]
  rw [sharpM_point _ hj]; simp only [char_two,zero_mul,sum_const_zero,add_zero]
  unfold tabGram
  rw [Fintype.sum_prod_type,Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]

  congr 1
  · refine Finset.sum_congr rfl fun i _=>Finset.sum_congr rfl fun j _=> ?_
    exact (etab_point p (Block.O i j) ..).trans (hX (.inl (i,j)))
  exact (etab_point p Block.S ..).trans (hX (.inr ()))
end HadwigerCounterexample

end

end OAI
