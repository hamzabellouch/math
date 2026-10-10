import OAI.Combinatorics.HadwigerCounterexample.RandomLinearTransforms

namespace OAI

/-! # Free Block Fourier -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module LinearMap Filter Function
open scoped BigOperators
variable {p : Shape} {n : ℕ} {I A : Type} [Fintype I] [DecidableEq I]
variable [Fintype A]

theorem zavg (p : Shape) (w : Wgt (Knobs p.g n)) (h : flowZ p w)
    (f : Wgt (Knobs p.g n)) :
    avg w f=avg w (fun x => avg unif (fun y => f (update x Block.Z y))) := by
  classical
  let A := Knobs p.g n
  let v : Wgt A := unif
  let k (f : Wgt A) (x : A) := f x * density v w x
  have he (f : Wgt A) : avg w f=avg v (k f) := by
    unfold avg; refine Finset.sum_congr rfl fun i _ => ?_
    have hv : v i ≠ 0 := by unfold v; rw [unif_apply]; positivity
    unfold k density
    field_simp
  let b : Block p.g→ Wgt (Vec (Fin n)) := fun _ => unif
  have hv : prodW b=v := draws_unif.symm
  rw [he f,he (fun _ => avg _ _), ← hv,update_avg b Block.Z (k f) unif_law]
  refine avg_congr fun i _ => ?_
  unfold k
  have ht (x) : density v w (update i Block.Z x)=density v w i := by
    unfold density; rw [h]; rfl
  simp_rw [ht,avg_mul]
  rfl

def zhat (p : Shape) (f : Wgt (Knobs p.g n)) (x : Knobs p.g n) (i : Vec (Fin n)) :=
  avg unif (fun y => vectorPhase i y * f (update x Block.Z y))
def zchar (p : Shape) (f : Wgt (Knobs p.g n)) (i : Vec (Fin n)) (x : Knobs p.g n) :=
  zhat p f x i * vectorPhase i (x Block.Z)
def zim (p : Shape) (f : Wgt (Knobs p.g n)) (s : Finset (Vec (Fin n))) (x) :=
  ∑ i∈s,zchar p f i x

omit [DecidableEq I] in
private theorem vpsym (x y : Vec I) : vectorPhase x y=vectorPhase y x :=
  congrArg wsign (dotProduct_comm ..)
theorem hat_eqn (f : Wgt (Vec I)) (x : Vec I) :
    ∑ i:Vec I,(avg unif (fun y => vectorPhase i y*f y))*vectorPhase i x=f x := by
  classical
  unfold avg; simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hi y :
      ∑ i:Vec I,unif y*(vectorPhase i y*f y)*vectorPhase i x=
        ind (y=x)*f y := by
    rw [vector_expand]
    simp only [avg,Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by rw [unif_apply,unif_apply]; ring
  simp_rw [hi]; simp [ind]

theorem z_atlas (p : Shape) (f : Wgt (Knobs p.g n)) (x) :
    zim p f univ x=f x := by
  unfold zim zchar zhat
  rw [hat_eqn (fun y => f (update x Block.Z y))]
  simp

theorem zhat_replay (p : Shape) (f : Wgt (Knobs p.g n)) (x) (y) (i) :
    zhat p f (update x Block.Z y) i= zhat p f x i := by simp [zhat]

theorem zchar_orth (p : Shape) (f g w : Wgt (Knobs p.g n)) (h : flowZ p w)
    (i j : Vec (Fin n)) (he : i≠j) :
    avg w (fun x => zchar p f i x * zchar p g j x)=0 := by
  rw [zavg p w h]
  have hh (x : Knobs p.g n) :
      avg unif (fun y => zchar p f i (update x Block.Z y)*zchar p g j (update x Block.Z y))=0 := by
    unfold zchar
    simp_rw [zhat_replay,update_self]
    have hi (x) : vectorPhase i x*vectorPhase j x = vectorPhase x i*vectorPhase x j := by
      rw [vpsym i,vpsym j]
    have ht (y : Vec (Fin n)) :
        zhat p f x i * vectorPhase i y * (zhat p g x j * vectorPhase j y) =
        zhat p f x i * zhat p g x j * (vectorPhase y i * vectorPhase y j) := by
      rw [←hi]; ring
    simp_rw [ht,avg_mul',←vector_expand,ind_zero he,mul_zero]
  simp_rw [hh,avg_zero]

theorem zsplit_orth (p : Shape) (f g w : Wgt (Knobs p.g n)) (h : flowZ p w)
    (s t : Finset (Vec (Fin n))) (hh : Disjoint s t) :
    avg w (fun x => zim p f s x*zim p g t x)=0 := by
  unfold zim; simp_rw [Finset.sum_mul,Finset.mul_sum,avg_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
    zchar_orth p f g w h i j (fun e => Finset.disjoint_left.mp hh hi (e ▸ hj))

theorem zsplit_cost (p : Shape) (f w : Wgt (Knobs p.g n)) (h : flowZ p w)
    (hw : ∀ i, 0 ≤ w i) (s : Finset (Vec (Fin n))) :
    avg w (fun x => (zim p f s x)^2)≤avg w (fun x => f x^2) := by
  classical
  let t := univ\s
  let A := zim p f s; let B := zim p f t
  have hh x : f x^2 = A x^2+B x^2+2*(A x*B x) := by
    have he : A x+B x=f x := by
      unfold A B zim t
      rw [add_comm, Finset.sum_sdiff (subset_univ s)]; exact z_atlas p f x
    rw [← he]; ring
  have h0 := zsplit_orth p f f w h s t (Finset.disjoint_left.mpr (fun j hj hk =>
    (mem_sdiff.mp hk).2 hj))
  simp_rw [hh,avg_add,avg_mul',show avg w (fun x => A x*B x)=0 from h0,mul_zero,add_zero]
  exact le_add_of_nonneg_right (avg_nonneg hw (fun _ => sq_nonneg _))
end HadwigerCounterexample

end

end OAI
