import OAI.Combinatorics.HadwigerCounterexample.PredictionClasses
import OAI.Combinatorics.HadwigerCounterexample.PolynomialCompatibility

namespace OAI

/-! # Phase Class Compatibility -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Finset LinearMap
open scoped BigOperators
variable {p : Shape} {n N : ℕ}
namespace PredictionClass
def compatible (α : Party) (x : F) : PredictionClass→Quad→Prop
| dusk,v=> v=repeatQ x
| dawn i,v=> v.1 i+v.2 i=firstBit α i
| twinned,v=> dotProduct allSide v.1 +dotProduct allSide v.2=0
| noon,_=> True

def matchUp (Δ : UnitType p n N→Ambient p N) (α : Party) (x : F)
    (c : PredictionClass) (v : UnitType p n N × UnitType p n N) :=
  c.compatible α x (quench p Δ v)

theorem dusk_lit (α : Party) (h : dusk.lit α) : ∀ i,α i = 1 := fun i=>by
  have hh : 1+α i=0 := h.1 i not_false
  exact add_left_cancel (hh.trans (char_two 1).symm)
theorem meet (c : PredictionClass) (α : Party) (x : F) : ∃ v,c.compatible α x v := by
  cases c
  · exact ⟨_,rfl⟩
  · rename_i i; exact ⟨(0,fun _=>firstBit α i),zero_add _⟩
  · exact ⟨0, by simp [compatible]⟩
  exact ⟨0,trivial⟩
end PredictionClass

open PredictionClass

def glint (p : Shape) {n} (x : Bool → Profile p n) := ∑ i, role p n (x i)
def exactInk (p : Shape) (m : Mixer p n) (z : BMark p n N) (x) :=
  ∀ i:Bool,silent (yoke p m x i (z x i) 1)

theorem lone (p : Shape) {n N} (x : UnitType p n N) (i : Bool) (v : Ambient p N) :
    tone p x (unary i) v= ufun (onSide x i) v := by
  classical
  unfold tone joinPhase unary; rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same,one_smul]
    rw [show onSide (listens p x) i=hcube p (onSide x i) from by cases i<;>rfl, phase_actual]
  · intro j _ h; simp [h]
  simp

theorem zero_delta (z : BMark p n N) (x : UnitType p n N) (h : delta z x=0) :
    Uembed x.1 (z x true)=Uembed x.2 (z x false) := by
  exact add_right_cancel (h.trans (char_two _).symm)

theorem exactInner (m : Mixer p n) (z : BMark p n N) (x : UnitType p n N)
    (h : exactInk p m z x) :
    ∀ i, ∀ v∈Xspace p n,innerP p x i v = grad m (z x i) v := by
  intro i v hv
  have he := h i v hv
  change innerP p x i v+(Tsym m (z x i) v +1*role p n v)=0 at he
  rw [one_mul,add_comm (Tsym m (z x i) v),← grad_val] at he
  exact add_right_cancel (he.trans (char_two _).symm)

theorem delta_dusk (m : Mixer p n) (z : BMark p n N) (x : UnitType p n N)
    (hx : ∀ i,z x i∈Xspace p n)
    (h : exactInk p m z x) (hz : delta z x=0)
    (he : (rawHoles m).unit x) (hi : ∀ i,frameLaw m (onSide x i)) :
    glint p (z x)=0 := by
  apply (bit_cases _).resolve_right
  intro hh
  have heq := exactInner m z x h
  unfold glint at hh; rw [Fintype.sum_bool] at hh
  apply he
  exact ⟨hi true,hi false,z x true,z x false,hx _,hx _,zero_delta z x hz,heq true,heq false,hh⟩

theorem diag_dusk (m : Mixer p n) (z : BMark p n N) (x : UnitType p n N)
    (hx : ∀ i,z x i∈Xspace p n)
    (h : exactInk p m z x) (hi : ∀ i,frameLaw m (onSide x i)) :
    tone p x allSide (delta z x)=0 := by
  have he (i) : innerP p x i (z x i)=0 := by
    rw [exactInner m z x h _ _ (hx i),grad_val,T_diag,char_two]
  have he1 : ufun x.1 (mrAmbient z x false)=0 := he false
  have he2 : ufun x.2 (mrAmbient z x true)=0 := he true
  rw [tone_vec]
  unfold dotProduct; simp_rw [Fintype.sum_bool,allSide,one_mul,lone,delta,map_add]
  have h1 : ufun x.1 (mrAmbient z x true)=0 := ufun_self (hi true) _
  have h2 : ufun x.2 (mrAmbient z x false)=0 := ufun_self (hi false) _
  simp [onSide,h1,h2,he1,he2]

theorem fade (c : PredictionClass) (α : Party) (r : F)
    (h : c.lit α) (hα : α true=α false) (hd : c=dusk → r=0)
    (Δ : UnitType p n N→Ambient p N) (x : UnitType p n N × UnitType p n N)
    (hx : Δ x.1=0) (hy : Δ x.2=0) :
    c.matchUp Δ α r x := by
  classical
  have ht : quench p Δ x=0 := by
    unfold quench tone; rw [hx,hy]
    simp only [map_zero]; rfl
  unfold matchUp; rw [ht]
  cases c
  · rw [hd rfl]; rfl
  · rename_i i
    cases i
    · have hh : firstBit α true=0 := h.1 true (show false≠true from Bool.false_ne_true)
      unfold firstBit at hh; rw [hα] at hh
      exact (zero_add _).trans hh.symm
    have hh : firstBit α false=0 := h.1 false (show true≠false from Ne.symm Bool.false_ne_true)
    unfold firstBit at hh; rw [←hα] at hh
    exact (zero_add _).trans hh.symm
  · simp [compatible]
  trivial

theorem tiny_morn (p : Shape) {n N : ℕ} (Δ : UnitType p n N→Ambient p N)
    (w : Wgt (UnitType p n N)) (hw : IsLaw w) (d : ℕ) (h : tonalTiny p Δ w d)
    (hN : bp (-0.24*N) < 0.1) (α r i) :
    0.4 ≤ pr (pairW w w) (matchUp Δ α r (dawn i)) := by
  classical
  obtain ⟨_,_,_,hx⟩:= h
  have hi : |pitch p Δ w (unary i) (unary i)| ≤0.1 := (hx i _).trans hN.le
  let P := matchUp Δ α r (dawn i)
  let v := firstBit α i
  let x (x : UnitType p n N×UnitType p n N) :=
    tone p x.1 (unary i) (Δ x.2)+tone p x.2 (unary i) (Δ x.1)
  let C:=pairW w w
  have he (j) : P j ↔ x j = v := by
    unfold P matchUp compatible quench x v; simp only [add_comm]
  have hU : pr C P=(1/2)*(avg C (fun _=>1)+wsign v * avg C (fun i=> wsign (x i))) := by
    unfold pr
    rw [←avg_mul',←avg_add,←avg_mul']
    apply avg_congr
    intro i _
    rcases bit_cases v with h|h<;> rcases bit_cases (x i) with hx|hx <;> norm_num [he,h,hx,ind]
  have hz := abs_le.mp hi
  change |avg C (fun i=> wsign (x i))| ≤_ at hi
  change _≤pr C P
  rw [hU,(pairW_law hw hw).avg_const]
  rcases bit_cases v with h|h <;> rw [h] <;> simp only [wsign_zero, wsign_one,one_mul,neg_mul] <;>
    linarith only [(abs_le.mp hi).1,(abs_le.mp hi).2]
end HadwigerCounterexample

end

end OAI
