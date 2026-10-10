import OAI.Combinatorics.HadwigerCounterexample.ConditionalSignaturePositivity
import OAI.Combinatorics.HadwigerCounterexample.WeakProductComparison
import OAI.Combinatorics.HadwigerCounterexample.BinaryMixingBounds

namespace OAI

/-! # Surrogate Query Scores -/

noncomputable section
namespace HadwigerCounterexample
open Filter Finset Matrix Function
open scoped BigOperators Topology
open Template
variable {p : Shape} {n N K M r : ℕ}
namespace StatusAnalysis
variable {q:Format} {d : Rates} {b:Bool}
namespace Quill

variable (w : Quill p q d b) (t : Tagging p (Messenger q)) (z : Messenger q → F)

def allure (i : Messenger q) : Appearance p := ⟨t i,w.sel i,w.flav i,z i⟩
theorem allure_apt (h : w.moral t z) (i : Messenger q) :
    (w.allure t z i).apt := canDraw t z h i

def policies (n:ℕ) := fun i => (w.allure t z i).wit n
variable (o : UnitType p n N)
def stencil (s : Charts p n d) (m : Mixer p n) (i : Messenger q) (v : Knobs p.g n) :=
  let j:=parcel b i
  ind ((w.allure t z i).profile j o m (s j) v=w.amp i)

theorem stencil_floor (s : Charts p n d) (m : Mixer p n) (i v) :
    |w.stencil t z o s m i v|≤1 := by
  unfold stencil; dsimp only; rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _

variable (m : Mixer p n)
def seraph (s : Charts p n d) (Y:Silhouette p N r) (i:Messenger q) : Wgt (AtomKey (p:=p) (t i) N) :=
  let j:=parcel b i
  fun h=> (w.allure t z i).reflected Y j o m (s j) (Y (t i) (z i) h) (w.amp i)
def mirror (s : Charts p n d) (Y:Silhouette p N r) := fun x:Keys (p:=p) t N=>
    (w.pen t).kappa*prodW (w.seraph t z o m s Y) x

theorem seraphFloor (s : Charts p n d) (Y:Silhouette p N r) (i:Messenger q)
    (hw : IsLaw (w.policies t z n i)) (x) :
    0≤ seraph w t z o m s Y i x ∧ seraph w t z o m s Y i x≤1 :=
  let h:= Appearance.reflectedLaw (w.allure t z i) Y hw (parcel b i) o m _ (Y _ (z i) x)

  ⟨h.nz _,(weight_le_tot h.nz _).trans h.total.le⟩

theorem kappaTop : (w.pen t).kappa ≤1 := by
  unfold kappa wavelength
  classical
  have hh : IsLaw (prism (w.pen t).Abbey) := prodW_law (fun _ => unif_law)
  exact (weight_le_tot hh.nz _).trans hh.total.le

theorem mirror_floor (s : Charts p n d) (Y:Silhouette p N r)
    (hw : ∀ i,IsLaw (w.policies t z n i))
    (x:Keys (p:=p) t N) :
    0≤ w.mirror t z o m s Y x ∧ w.mirror t z o m s Y x≤1 := by
  let f:= w.seraph t z o m s Y
  let v:= w.pen t
  have hh i:= seraphFloor w t z o m s Y i (hw i) (x i)
  have h0 : 0 ≤ prodW f x:= prodW_nonneg (fun i y=> (seraphFloor w t z o m s Y i (hw i) y).1) _
  have h1 : prodW f x≤1 := (Finset.prod_le_prod₀ (s:=Finset.univ)
    (g:=fun i: Messenger q=> (1:ℝ)) (fun i _=> (hh i).1) (fun i _=> (hh i).2)).trans_eq
    (by simp)
  exact ⟨mul_nonneg v.kappa_pos.le h0,(mul_le_mul (kappaTop w t) h1 h0 zero_le_one).trans_eq
    (one_mul _)⟩

def sheen (s : Charts p n d) (Y:Silhouette p N r) (W:Wgt (Keys (p:=p) t N)) :=
  avg (lawNu p N t z) (fun x=>w.mirror t z o m s Y x*W x)

theorem painted (s : Charts p n d)
    (x:Inputs p n (Messenger q)) :
    prodW (w.stencil t z o s m) x=
    ind (printed b s t w.sel w.flav m o x=w.amp) := by
  classical
  rw [funext_iff,ind_all]; rfl

theorem prowl_astonish (s : Charts p n d) (W : Wgt (Keys (p:=p) t N)) :
    w.prowl s t z m o W=astonish (w.pen t) z W w.script m (w.policies t z n)
      (w.stencil t z o s m) o := by
  classical

  let v:=w.pen t
  have ht : astonish v z W w.script m (w.policies t z n) (w.stencil t z o s m) o=
    avg (v.state z n) (fun x=> ind (earns v w.script m z o x)*W (v.resultKey o x)*prodW
      (w.stencil t z o s m) x) := astonish_val v z _ _ m _ _ _
  rw [ht]; unfold prowl; apply avg_congr
  intro i _
  rw [painted]
  simp_rw [deposit, earns,ind_and]
  let a:=ind (printed b s t w.sel w.flav m o i=w.amp); let b0:=ind ((v.draw i).reads w.script m)
  let x:= v.resultKey o i; let c:= ind (ownPart v.t z x)
  change a*(b0*c)*W x= (b0*c)*W x*a
  ring

theorem sheen_sun (s : Charts p n d) (Y:Silhouette p N r) (W:Wgt (Keys (p:=p) t N)) :
    w.sheen t z o m s Y W=
      (w.pen t).kappa * avg (lawNu p N t z) (fun x=>W x*prodW (w.seraph t z o m s Y) x) := by
  unfold sheen mirror; rw [←avg_mul']
  apply avg_congr; intro i _; ring

end Quill
end StatusAnalysis
end HadwigerCounterexample

end

end OAI
