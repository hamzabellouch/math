import OAI.Combinatorics.HadwigerCounterexample.SyntheticTolerances

namespace OAI

/-! # Synthetic Parity -/

noncomputable section
namespace HadwigerCounterexample
open Matrix Module LinearMap Submodule Function Finset
open scoped BigOperators
variable {p : Shape} {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
variable {d e n N : ℕ}

abbrev Hue (d : ℕ) := Option (Bool × Fin d)
def beamMap (d : ℕ) : Mat (Hue d) (Hue d) :=
  Matrix.of (fun i j =>
    i.elim 0 (fun x=> j.elim 0 (fun y=> if x.1=true∧y.1=false∧x.2=y.2 then 1 else 0)))
def jet (i : I) := (Pi.single i 1 : Vec I)
abbrev incarn {d : ℕ} (x : Fin d) (b : Bool) : Hue d := some (b,x)
def plumeDiff (d : ℕ) (b : Bool) : Mat (Hue d) (Fin d) :=
  Matrix.of (fun i j => jet none i + jet (incarn j b) i)

def arches (F : Vec (Hue d) → F) : Mat (Fin d) (Fin d) :=
  Matrix.of (fun i j =>
    let x:=jet (incarn i true)
    let y:=jet (incarn j false)
    let z:=jet (none : Hue d)
    F (z+x+y)+F x+(F y+F z))

omit [DecidableEq I] in
theorem quad_cross_gen (Q : Mat I I) (x y z : Vec I) :
    evmat Q (z+x+y) (z+x+y)+evmat Q x x+(evmat Q y y+evmat Q z z)=
      evmat (Q+Qᵀ) (z+x) (z+y) := by
  rw [evmat_addM,evmat_transpose]
  unfold evmat; simp only [mulVec_add,add_dotProduct,dotProduct_add]
  ring_nf
  simp only [mul_two,char_two,zero_add,add_zero]

theorem arches_from (F : Vec (Hue d) → F) (Q : Mat (Hue d) (Hue d))
    (h : ∀ x,weightsAff x → F x=evmat Q x x) :
    arches F = pullM (plumeDiff d true) (plumeDiff d false) (Q+Qᵀ) := by
  classical
  ext i j
  let x:=jet (incarn i true); let y:=jet (incarn j false)
  let z:=jet (none : Hue d)
  have hj (x : Hue d) : weightsAff (jet x) := by simp [weightsAff,jet]
  have hz : weightsAff (z+x+y) := by
    unfold weightsAff
    simp only [Finset.sum_add_distrib,Pi.add_apply]
    rw [show ∑ i,z i=1 from hj _,show ∑ i,x i=1 from hj _,show ∑ i,y i=1 from hj _,char_two,zero_add]
  change F (z+x+y)+F x+(F y+F z)=_
  rw [h _ hz,h _ (hj _),h _ (hj _),h _ (hj _),quad_cross_gen]
  rw [pullM_def,Matrix.mul_assoc]
  rfl

theorem arches_rank (F : Vec (Hue d) → F) (Q : Mat (Hue d) (Hue d))
    (h : ∀ x,weightsAff x → F x=evmat Q x x) :
    (arches F).rank≤2*Q.rank := by
  rw [arches_from F Q h]
  refine le_trans (rank_lift_le ..) ?_
  rw [two_mul]
  exact (mrk_add_le ..).trans (by rw [Matrix.rank_transpose])

theorem arches_beam (d : ℕ) :
    arches (fun x => evmat (beamMap d) x x)= (1:Mat (Fin d) (Fin d)) := by
  classical
  ext i j
  have he (a b : Hue d) :
      evmat (beamMap d) (jet a) (jet b)=beamMap d a b := by simp [evmat,jet]

  let x:=jet (incarn i true); let y:=jet (incarn j false); let z:=jet (none:Hue d)
  change evmat _ (z+x+y) (z+x+y)+_+_=_
  rw [quad_cross_gen,evmat_addM,evmat_transpose]
  have h1 (a b c e : Hue d) : evmat (beamMap d) (jet a+jet b) (jet c+jet e)=
      beamMap d a c+beamMap d b c+(beamMap d a e+beamMap d b e) := by
    simp_rw [← he]; unfold evmat; rw [Matrix.mulVec_add,dotProduct_add,add_dotProduct,add_dotProduct]
  rw [h1,h1]
  simp [beamMap,Matrix.one_apply]

def libColor (p : Shape) (l : Tag p.g) (u : Vec I) (x : Display p I N) :
    AtomKey (p:=p) l N :=
  fun i b=> if b then (x i.val).1 *ᵥ u else (x i.val).2 *ᵥ u
def libPredict (p : Shape) (l : Tag p.g) (s : Augur p N) (G : Mat I I) (x : Display p I N)
    (u : Vec I) := s l (evmat G u u) (libColor p l u x)
def libAug (p : Shape) (l : Tag p.g) (s : Augur p N) (G : Mat I I) (x : Display p I N) (u : Vec I) :=
  libPredict p l s G x u+evmat G u u

omit [DecidableEq I] in
theorem lib_see (p : Shape) (l s f) (x : I →Knobs p.g n)
    (u : Vec I) (h : weightsAff u) (o : Orient p n N) :
    let A := incision p l s f x
    let y := compound p x u
    libColor p l u (drill p A o) = keyOne p l s (lit f l y) o := by
  intro A y; funext i b
  cases b
  · change (primary _* A) *ᵥ u=primary _*ᵥ spring _ _ _ _ _
    rw [←Matrix.mulVec_mulVec,inc_compound p l s f x u h]; rfl
  change (primary _ * A)*ᵥ u=primary _*ᵥ spring _ _ _ _ _
  rw [← Matrix.mulVec_mulVec,inc_compound p l s f x u h]; rfl
end HadwigerCounterexample

end

end OAI
