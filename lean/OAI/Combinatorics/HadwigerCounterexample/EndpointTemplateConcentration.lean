import OAI.Combinatorics.HadwigerCounterexample.ConcentrationScales

namespace OAI

/-! # Endpoint Template Concentration -/

noncomputable section
namespace HadwigerCounterexample
open Filter Real Finset Matrix Function
open scoped BigOperators
variable {p : Shape} {M n N : ℕ}
variable {I J K G : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype G]
variable [DecidableEq I] [DecidableEq J] [DecidableEq K] [DecidableEq G]

namespace Template

variable (v : Template p I)

def callP (n : ℕ) (g : Route (KeySlots p v.t) G) : Program p n g (Inputs p n I) :=
  ⟨fun x => queryLaw v x,fun x => queryLaw v x⟩
def singleP (n : ℕ) := callP v n (ownPort (p:=p) v.t)
def doubleP (n : ℕ) := callP v n (globPort p v.t v.aim)

omit [Fintype I] [DecidableEq I] in
theorem own_inj (i : Comp p.g) :
    Injective (fun i : Port (ownPort (p:=p) v.t) i => i.val.1) := by
  rintro ⟨⟨a,c⟩,ha⟩ ⟨⟨b,d⟩,hb⟩ he
  change a=b at he; subst b
  have h : c=d := Subtype.ext (ha.trans hb.symm)
  subst d; rfl

omit [Fintype I] [DecidableEq I] in
theorem glob_inj (i : Ports p) :
    Injective (fun i : Port (globPort p v.t v.aim) i => i.val.1) := by
  rintro ⟨⟨a,c⟩,ha⟩ ⟨⟨b,d⟩,hb⟩ he
  change a=b at he; subst b
  have h : c=d := Subtype.ext (congrArg Prod.snd (ha.trans hb.symm))
  subst d; rfl

omit [Fintype G] in
theorem free_price (n : ℕ) (w : I→ Wgt (Knobs p.g n)) (hw : ∀ i,IsLaw (w i))
    (hz : ∀ i,mapW (w i) (freePart p)=unif)
    (g : Route (KeySlots p v.t) G)
    (he : ∀ i : G,Injective (fun j : Port g i => j.val.1)) :
    pr (draws K (prodW w)) (fun x => ¬ (v.callP n g).free x)≤ bp (num K * num I-n) := by
  refine le_trans ?_ (buds p n _ hz)
  exact pr_mono (draws_law (prodW_law hw)).nz fun i h hh => h
    ⟨queries_bloom v i g hh he, queries_bloom v i g hh he⟩

def callOne (i) (x : Knobs p.g n) (o : Orient p n N) :=
  keyOne p (v.t i) (v.s i) (lit (v.f i) (v.t i) x) o

omit [Fintype I] [DecidableEq I] in
theorem single_show (z : Inputs p n I) (x : Orient p n N) :
    (v.singleP n).showKey z x=scatter v.t N (fun i => callOne v i (z i) x) := by
  apply Prod.ext <;> rfl

omit [Fintype I] [DecidableEq I] in
theorem double_show (z : Inputs p n I) (x : UnitType p n N) :
    (v.doubleP n).showKey z (mergeR p x)=scatter v.t N ((v.draw z).keys v.t x) :=
  peek_keys v.t (v.draw z) x

theorem raw_variance (v : Template p I) (M : ℕ) (hM : 1≤M) :
    ∀ᶠ n : ℕ in atTop, let N := M*n; ∀ (m : Mixer p n) (w : I→Wgt (Knobs p.g n)),
      (∀ i, IsLaw (w i)) → (∀ i,mapW (w i) (freePart p)=unif) → 2*num (Full p n)<N →
      ∀ T : Inputs p n I → Keys (p:=p) v.t N → ℝ, (∀ x y,|T x y|≤1) →
      let u:= raw m N
      let f:= fun o => avg (prodW w) (fun z => T z (fun i => callOne v i (z i) o))
      avg u (fun x => (f x-avg u f)^2) ≤ bp (-(1/4:ℝ)*n) := by
  let g := ownPort (p:=p) v.t
  filter_upwards [Program.variance_calendar p M g (num Bool*num I) 1 zero_lt_one hM]
    with n hn N m w hw hz hN T hT r f
  let s := v.singleP n
  let t (x : Inputs p n I) (y : Rack (KeySlots p v.t) N) := T x ((scatter v.t N).symm y)
  have hf : f = s.oexpect (prodW w) t := by
    unfold s f Program.oexpect t
    simp_rw [single_show,Equiv.symm_apply_apply]
  have h := hn m _ s t (prodW w) (prodW_law hw) (fun x y => hT _ _) hN
    (free_price v n w hw hz g (own_inj v))
  rw [one_mul] at h
  rw [hf]; exact h

end Template
end HadwigerCounterexample

end

end OAI
