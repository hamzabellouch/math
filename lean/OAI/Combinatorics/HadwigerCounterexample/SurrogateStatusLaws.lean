import OAI.Combinatorics.HadwigerCounterexample.AnalyticParameters

namespace OAI

/-! # Surrogate Status Laws -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology

variable {A B C H : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype H]
variable {p : Shape} {n N K M r : ℕ}
abbrev Silhouette (p : Shape) (N r : ℕ) :=
  ∀ t : Tag p.g,F→AtomKey (p:=p) t N→Fin r

namespace StatusAnalysis
structure Appearance (p : Shape) where
  l : Tag p.g
  s : Label p.b
  f : Flavor p.g
  q : F

instance : Fintype (Appearance p) := by
  classical
  let A := Tag p.g × Label p.b × Flavor p.g × F
  let E : A ≃ Appearance p := {
    toFun x:=⟨x.1,x.2.1,x.2.2.1,x.2.2.2⟩
    invFun x:=(x.l,x.s,x.f,x.q)
    left_inv _:=rfl
    right_inv _:=rfl }
  exact Fintype.ofEquiv _ E

namespace Appearance
variable (x : Appearance p)
def apt := canDial p x.l x.f x.q
def trot := Template.solo p x.l x.s x.f
def wit (x : Appearance p) (n : ℕ) := scopedBit p n x.l x.f x.q
def face (o : Orient p n N) (w : Knobs p.g n) : AtomKey (p:=p) x.l N :=
  x.trot.desc w o
def profile {d : ℕ} (i : Nodes) (o : UnitType p n N) (m : Mixer p n) (v : Ax p n d)
    (z : Knobs p.g n) : Magazine p d :=
  specify p i v m o x.l x.s x.f z
theorem witLaw {x : Appearance p} (h : x.apt) (hq : 1≤p.r) (hn : 2*p.r≤n) :
    IsLaw (x.wit n) := dial_law _ _ _ _ _ hq hn h

variable (Y : Silhouette p N r)
def showTag (o : Orient p n N) := fun w=>Y x.l x.q (x.face o w)

def reference := mapW (lawOmega p N x.l x.q) (Y x.l x.q)
def empirical (o : Orient p n N) := mapW (x.wit n) (x.showTag Y o)

variable {d : ℕ}
def reflected (i : Nodes) (o : UnitType p n N) (m : Mixer p n) (v : Ax p n d) (a : Fin r) :=
  mapW (stained (x.wit n) (x.showTag Y (onSide o i)) a) (x.profile i o m v)

theorem reflectedLaw (h : IsLaw (x.wit n)) (i : Nodes)
    (o : UnitType p n N) (m : Mixer p n) (v : Ax p n d)
    (a : Fin r) : IsLaw (x.reflected Y i o m v a) :=
  mapW_law (stained_law _ h _) _

def close (o : Orient p n N) (ε : ℝ) :=
  varOne (x.reference Y) (x.empirical Y o) ≤ ε
end Appearance

omit [Fintype B] in
private theorem stained_except (w : Wgt A) (f : A→B) (x : B)
    (hx : mapW w f x ≠0) :
    carried (stained w f x) (fun i=> f i=x) := by
  unfold stained; rw [ite_eq_left hx]
  exact normW_carried (subW_carried w _)

theorem inside_color (w : Wgt A) (hw : IsLaw w) (f : A→B) (r : A→C)
    (u : B→C→ℝ) :
    avg w (fun i=> u (f i) (r i)) = avg (mapW w f) (fun i=>avg (mapW (stained w f i) r) (u i)) := by
  classical
  let d i:= u (f i) (r i)
  calc avg w d = avg (mixW (mapW w f) (stained w f)) d := congrArg (fun w=>avg w d)
         (stain_inputs f hw)
       _ = _ := by
        rw [mixW_avg]
        refine avg_congr fun i hi=> ?_
        rw [mapW_avg]
        refine avg_congr fun j hj=> ?_
        have he : f j=i := not_not.mp (fun h=>hj (stained_except w f i hi j h))
        unfold d; rw [he]

theorem varError (w v : Wgt A) (f : A→ℝ) (h : ∀ i, |f i|≤1) :
    |avg w f-avg v f| ≤ varOne w v := by
  unfold avg varOne
  rw [←sum_sub_distrib]
  refine (abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun i _=> ?_)
  rw [← sub_mul,abs_mul]; exact (mul_le_mul_of_nonneg_left (h _) (abs_nonneg _)).trans_eq (mul_one _)

namespace Appearance
variable (x : Appearance p) (Y : Silhouette p N r)
variable {d : ℕ}

theorem close_expect (i : Nodes) (o : UnitType p n N) (m : Mixer p n) (v : Ax p n d)
    (hw : IsLaw (x.wit n)) (u : Fin r → Magazine p d→ ℝ) (hu : ∀ i j, |u i j| ≤ 1)
    {ε : ℝ} (h : x.close Y (onSide o i) ε) :
    |avg (x.reference Y) (fun a=> avg (x.reflected Y i o m v a) (u a))-
     avg (x.wit n) (fun a=>u (x.showTag Y (onSide o i) a) (x.profile i o m v a))|≤ ε := by
  rw [inside_color _ hw]
  refine le_trans (varError (x.reference Y) (x.empirical Y (onSide o i)) _ (fun j=>?_)) h
  let w := x.reflected Y i o m v j
  have he : IsLaw w:= x.reflectedLaw Y hw i o m v j
  exact (abs_avg_le he.nz).trans ((avg_mono he.nz (hu j)).trans_eq (he.avg_const _))

theorem show_pr (i : Nodes) (o : UnitType p n N) (m : Mixer p n) (v : Ax p n d)
    (hw : IsLaw (x.wit n)) (j : Fin r) (U : Magazine p d→Prop) :
    pr (x.wit n) (fun y => x.showTag Y (onSide o i) y=j∧ U (x.profile i o m v y))=
      x.empirical Y (onSide o i) j * pr (x.reflected Y i o m v j) U := by
  classical
  rw [pr_of_on hw.nz]
  unfold reflected empirical
  rw [mapW_pr]
  let f:=x.showTag Y (onSide o i)
  let w:= x.wit n
  by_cases h : mapW w f j ≠0
  · unfold stained; rw [ite_eq_left h]; rfl
  have hh : pr w (fun y=> f y=j)=0 := not_not.mp h
  change pr w _*_=pr w _ * _
  rw [hh,zero_mul,zero_mul]

theorem reflection_exact (i : Nodes) (o : UnitType p n N) (m : Mixer p n) (v : Ax p n d)
    (j : Fin r) (P : Magazine p d→Prop)
    (hw : carried (x.wit n) (P ∘ x.profile i o m v)) :
    carried (x.reflected Y i o m v j) P := by
  unfold reflected
  let f := P∘x.profile i o m v
  refine mapW_carried (p:=f) ?_ (fun _ hh=>hh)
  unfold stained; split
  next h =>
    refine normW_carried ?_; intro a ha
    unfold subW; rw [hw a ha,zero_mul]
  next => exact hw
end Appearance
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
