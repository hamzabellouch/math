import OAI.Combinatorics.HadwigerCounterexample.PairedTemplateConcentration

namespace OAI

/-! # Template Typicality -/

noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset Matrix Function
open scoped BigOperators
variable {p : Shape} {M n N : ℕ}
variable {I J G : Type} [Fintype I] [DecidableEq I]

theorem fork_law {a : I → Type} [∀ i,Fintype (a i)]
    (p : I→Prop) [DecidablePred p] (w : ∀ i,Wgt (a i)) :
    let E := Equiv.piEquivPiSubtypeProd p a
    mapW (prodW w) E=pairW (prodW (fun i:{i // p i} => w i.val))
      (prodW (fun i:{i // ¬p i} => w i.val)) := by
  intro E
  funext x
  obtain ⟨y,rfl⟩ := E.surjective x
  rw [mapW_equiv_val,Equiv.symm_apply_apply]
  exact (Fintype.prod_subtype_mul_prod_subtype p (fun i => w i (y i))).symm

namespace Template
variable (v : Template p I)

def collect (p : Shape) (v : Template p I) (f : J→I) : Template p J :=
  ⟨v.aim ∘ f, v.t ∘ f, v.s ∘ f,v.f ∘ f⟩

abbrev PosA (v : Template p I) := {i:I//v.aim i}
abbrev PosB (v : Template p I) := {i:I//¬v.aim i}
def atA := collect p v (Subtype.val : v.PosA→I)
def atB := collect p v (Subtype.val : v.PosB→I)

def forkI (n : ℕ) : Inputs p n I ≃ Inputs p n v.PosA × Inputs p n v.PosB :=
  Equiv.piEquivPiSubtypeProd (fun i:I => v.aim i) (fun _ => _)
def forkK (N : ℕ) : Keys (p:=p) v.t N ≃ Keys (p:=p) v.atA.t N × Keys (p:=p) v.atB.t N :=
  Equiv.piEquivPiSubtypeProd (fun i:I => v.aim i) (fun i => AtomKey (p:=p) (v.t i) N)

def sampleAll (u : I→Wgt (Knobs p.g n))
    (T : Inputs p n I → Keys (p:=p) v.t N → ℝ)
    (x : UnitType p n N) :=
  avg (prodW u) (fun i => T i ((v.draw i).keys v.t x))

def connectT (T : Inputs p n I → Keys (p:=p) v.t N → ℝ)
    (x : v.atA.Datum n N × v.atB.Datum n N) :=
  T ((v.forkI n).symm (x.1.1,x.2.1))
    ((v.forkK N).symm ((scatter v.atA.t N).symm x.1.2,(scatter v.atB.t N).symm x.2.2))

set_option maxHeartbeats 800000 in
theorem connect_avg (u : I→Wgt (Knobs p.g n))
    (T : Inputs p n I → Keys (p:=p) v.t N → ℝ)
    (x : UnitType p n N) :
    let a := fun i : v.PosA => u i.val
    let b := fun i : v.PosB => u i.val
    v.sampleAll u T x = avg
      (pairW ((v.atA.singleP n).makeData (prodW a) x.1)
        ((v.atB.singleP n).makeData (prodW b) x.2)) (v.connectT T) := by
  classical
  intro a b
  let s (i : Inputs p n v.PosA) : v.atA.Datum n N :=
    (i,(v.atA.singleP n).showKey i x.1)
  let t (i : Inputs p n v.PosB) : v.atB.Datum n N :=
    (i,(v.atB.singleP n).showKey i x.2)
  have hi (i : Inputs p n I) :
      T i ((v.draw i).keys v.t x) =
      v.connectT T (s ((v.forkI n i).1), t ((v.forkI n i).2)) := by
    let y := (v.draw i).keys v.t x
    let Y := v.forkK N y
    have hA :
        (scatter v.atA.t N).symm ((v.atA.singleP n).showKey ((v.forkI n i).1) x.1)=Y.1 := by
      rw [single_show,Equiv.symm_apply_apply]; funext j

      change keyOne p (v.t j.val) _ _ x.1=keyOne p _ _ _ (onSide x (v.aim j.val))
      rw [j.property]; rfl
    have hB :
        (scatter v.atB.t N).symm ((v.atB.singleP n).showKey ((v.forkI n i).2) x.2)=Y.2 := by
      rw [single_show,Equiv.symm_apply_apply]; funext j
      change keyOne p (v.t j.val) _ _ x.2=keyOne p _ _ _ (onSide x (v.aim j.val))
      rw [Bool.eq_false_iff.mpr j.property]; rfl
    unfold connectT s t
    rw [hA,hB]
    simp [Y,Equiv.symm_apply_apply,y]
  let Q (j : Inputs p n v.PosA × Inputs p n v.PosB) := v.connectT T (s j.1, t j.2)
  calc _ = avg (mapW (prodW u) (v.forkI n)) Q := by
             rw [mapW_avg,sampleAll]; simp_rw [hi]; rfl
       _ = avg (pairW (prodW a) (prodW b)) Q := congrArg (fun w => avg w Q)
          (fork_law (fun i => v.aim i) u)
       _ = _ := by
         rw [pairW_avg,pairW_avg,Program.makeData,Program.makeData,mapW_avg]
         simp_rw [mapW_avg]; rfl

theorem typical_calendar (v : Template p I) (M : ℕ) (hM : 1≤M)
    (C ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n)
      (w : Wgt (UnitType p n N)), IsLaw w →
      let μ := raw m N; let ρ := pairW μ μ
      let H := bp ((1/32:ℝ)*n)
      (∀ x,mapW w Prod.fst x ≤ H*μ x) → (∀ x,mapW w Prod.snd x ≤ H*μ x) →
      (∀ x,w x ≤ bp (C*N) *ρ x) → 2*num (Full p n)<N →
      ∀ (u : I→ Wgt (Knobs p.g n)), (∀ i, IsLaw (u i)) →
        (∀ i,mapW (u i) (freePart p)=unif) →
        ∀ T : Inputs p n I → Keys (p:=p) v.t N → ℝ, (∀ x y,|T x y|≤1) →
        let f := v.sampleAll u T
        pr w (fun x => ε≤ |f x-avg ρ f|) ≤ bp (-(1/16:ℝ)*n) := by
  classical
  filter_upwards [twinned v.atA v.atB M hM C ε hε]
    with n hn N m w hw μ ρ H hA hB hw' hN u hu hz T hT f
  let a := u ∘ (Subtype.val : v.PosA→I)
  let b := u ∘ (Subtype.val : v.PosB→I)
  have h := hn m w hw hA hB hw' hN a b
    (fun i => hu _) (fun i => hz _) (fun i => hu _) (fun i => hz _)
    (connectT v T) (fun x => hT _ _)
  have he : f = fun x : UnitType p n N => avg
      (pairW ((v.atA.singleP n).makeData (prodW a) x.1)
        ((v.atB.singleP n).makeData (prodW b) x.2)) (v.connectT T) :=
    funext fun x => connect_avg v u T x
  rw [he]; exact h

end Template
end HadwigerCounterexample

end

end OAI
