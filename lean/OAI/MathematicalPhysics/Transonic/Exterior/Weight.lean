import OAI.MathematicalPhysics.Transonic.Exterior.Parameters
import OAI.MathematicalPhysics.Transonic.Exterior.Step

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorJet
open FixedInterval

lemma holds_grow' {Q r : ℤ} {b : Box} {x : ℝ} (hx : Holds Q b x) (hr : 0≤r) :
    Holds Q (grow b r) x := by
  unfold Holds grow at *;push_cast
  have hr' : (0:ℝ)≤r := by exact_mod_cast hr
  linarith

def rationalWide (Q a b : ℤ) : Box := grow (ofRat Q a b) 1
lemma holds_rationalWide {Q a b : ℤ} (hQ : 0<Q) (hb : 0<b) :
    Holds Q (rationalWide Q a b) ((a:ℝ)/b) :=
  holds_grow' (holds_ofRat hQ hb) (by norm_num)

def sourceWeights (Q : ℤ) (sig kap : Box) : Weights where
  p0 := sub (oneBox Q) sig
  p1 := scale 1 256 (sub (scale 3 1 sig) (oneBox Q))
  p2 := scale (-3) (256^2) sig
  p3 := scale 1 (256^3) sig
  a11 := scale 1 (256^2) (add (scale 4 5 kap) (rationalWide Q 18 5))
  a20 := scale 1 256 (sub (scale (-2) 1 kap) (rationalWide Q 18 5))
  a21 := scale 1 (256^2) (sub (scale 2 1 kap) (rationalWide Q 9 5))
  a30 := scale 1 256 (add (scale 12 5 kap) (rationalWide Q 9 5))
  a31 := scale (-12) (5*256^2) kap
  a40 := scale (-3) (5*256) kap
  a41 := scale 3 (5*256^2) kap

lemma sourceWeights_hold {Q : ℤ} (hQ : 0<Q) {sig kap : Box} {sigma kappa : ℝ}
    (hs : Holds Q sig sigma) (hk : Holds Q kap kappa) :
    WeightsHold Q (sourceWeights Q sig kap) (1/256) sigma kappa (3/5) := by
  have h18 := holds_rationalWide (a:=18) (b:=5) hQ (by norm_num)
  have h9 := holds_rationalWide (a:=9) (b:=5) hQ (by norm_num)
  constructor
  · exact holds_sub (holds_oneBox Q) hs
  · convert holds_scale (a:=1) (b:=256) (by norm_num)
      (holds_sub (holds_scale (a:=3) (b:=1) (by norm_num) hs) (holds_oneBox Q)) using 1 <;>
      norm_num [sourceWeights,p1]
  · convert holds_scale (a:= -3) (b:=256^2) (by norm_num) hs using 1 <;>
      norm_num [sourceWeights,p2] ; ring
  · convert holds_scale (a:=1) (b:=256^3) (by norm_num) hs using 1 <;>
      norm_num [sourceWeights,p3]
  · convert holds_scale (a:=1) (b:=256^2) (by norm_num)
      (holds_add (holds_scale (a:=4) (b:=5) (by norm_num) hk) h18) using 1 <;>
      norm_num [sourceWeights,i11]
  · convert holds_scale (a:=1) (b:=256) (by norm_num)
      (holds_sub (holds_scale (a:= -2) (b:=1) (by norm_num) hk) h18) using 1 <;>
      norm_num [sourceWeights,i20] ; ring
  · convert holds_scale (a:=1) (b:=256^2) (by norm_num)
      (holds_sub (holds_scale (a:=2) (b:=1) (by norm_num) hk) h9) using 1 <;>
      norm_num [sourceWeights,i21] ; ring
  · convert holds_scale (a:=1) (b:=256) (by norm_num)
      (holds_add (holds_scale (a:=12) (b:=5) (by norm_num) hk) h9) using 1 <;>
      norm_num [sourceWeights,i30]
  · convert holds_scale (a:= -12) (b:=5*256^2) (by norm_num) hk using 1 <;>
      norm_num [sourceWeights,i31] ; ring
  · convert holds_scale (a:= -3) (b:=5*256) (by norm_num) hk using 1 <;>
      norm_num [sourceWeights,i40] ; ring
  · convert holds_scale (a:=3) (b:=5*256^2) (by norm_num) hk using 1 <;>
      norm_num [sourceWeights,i41] ; ring

def sourceL0 (Q : ℤ) (sig st : Box) : Box := scale 2 1 (mul Q (sub (oneBox Q) sig) st)
def natBox (Q : ℤ) (n : ℕ) : Box := ⟨Q*n,0⟩
lemma holds_natBox (Q : ℤ) (n : ℕ) : Holds Q (natBox Q n) n := by simp [Holds,natBox]
def sourceDen (Q : ℤ) (l0 rho : Box) (n : ℕ) : Box := mul Q l0 (sub rho (natBox Q n))

lemma sourceL0_hold {Q : ℤ} (hQ : 0<Q) {sig st : Box} {sigma s : ℝ}
    (hs : Holds Q sig sigma) (hst : Holds Q st s) :
    Holds Q (sourceL0 Q sig st) (2*(1-sigma)*s) := by
  convert holds_scale (a:=2) (b:=1) (by norm_num) (holds_mul hQ (holds_sub (holds_oneBox Q) hs) hst) using 1 <;>
    norm_num [sourceL0] ; ring
lemma sourceDen_hold {Q : ℤ} (hQ : 0<Q) {l0 rh : Box} {v rho : ℝ} (n : ℕ)
    (hl : Holds Q l0 v) (hr : Holds Q rh rho) :
    Holds Q (sourceDen Q l0 rh n) (v*(rho-n)) :=
  holds_mul hQ hl (holds_sub hr (holds_natBox Q n))

lemma holds_between {Q : ℤ} (hQ : 0<Q) {b : Box} {l x r : ℝ}
    (hl : Holds Q b l) (hr : Holds Q b r) (hx : l≤x ∧ x≤r) : Holds Q b x := by
  have hQ' : (0:ℝ)≤Q := by exact_mod_cast hQ.le
  have h1 := mul_le_mul_of_nonneg_left hx.1 hQ'
  have h2 := mul_le_mul_of_nonneg_left hx.2 hQ'
  rw [Holds,abs_le] at *
  constructor <;> linarith [hl.1,hr.2]

end SepticProfile.ExteriorJet

end
end

end OAI
