import OAI.Combinatorics.HadwigerCounterexample.ProductCharacterTests

namespace OAI

/-! # Pair Indexed Tests -/

noncomputable section
namespace HadwigerCounterexample
open Finset Matrix Module Function
open scoped BigOperators
variable {I J A : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype A]
variable {s : Stage I J} {B : J→ Type}
variable [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)]

def listen (s : Stage I J) (f : ∀ i,A→A→Vec (B i)) (x : I→ A) := fun i =>
  f i (x (s.first i)) (x (s.nextP i))

def prism (B : J →Type) [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)] :
    Wgt (∀ i,Vec (B i)) := prodW (fun _ : J => unif)
def wavelength (B : J →Type) [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)] :=
  prism B 0

omit [DecidableEq J] in
theorem wavelength_pos (B : J →Type) [∀ i,Fintype (B i)] [∀ i,DecidableEq (B i)] :
    0<wavelength B := prod_pos (fun i _ => by simp only [unif_apply]; positivity)

omit [Fintype I] [DecidableEq I] [Fintype A] in
theorem prism_expand (s : Stage I J) (F : ∀ i,A→A→Vec (B i)) (v : ∀ i,Vec (B i)) (x : I→A) :
    ind (listen s F x=v)=avg (prism B) (fun u => ∏ i:J,
      (vectorPhase (u i) (F i (x (s.first i)) (x (s.nextP i)))*vectorPhase (u i) (v i))) := by
  classical
  rw [funext_iff, ind_all]; simp_rw [listen,vector_expand]
  exact (prodW_avg (fun i => unif) (fun i u =>
    vectorPhase u (F i (x (s.first i)) (x (s.nextP i)))*vectorPhase u (v i))).symm

set_option maxHeartbeats 800000 in
theorem hear_band (s : Stage I J) (F : ∀ i,A→A→Vec (B i)) (v : ∀ i,Vec (B i))
    (w : I → Wgt A) (hw : ∀ i,IsLaw (w i))
    (η : ℝ) (hη : 0≤η)
    (h : ∀ i:J,∀ u:Vec (B i),u≠0 → ∀ p q : Wgt A,(∀ i,|p i|≤1) → (∀ i,|q i|≤1) →
      |avg (pairW (w (s.first i)) (w (s.nextP i))) (fun x =>
        vectorPhase u (F i x.1 x.2)*(p x.1*q x.2))|≤η) :
    ∀ p : I→ Wgt A,(∀ i x,|p i x|≤1) →
    |avg (prodW w) (fun x => ind (listen s F x=v)*prodW p x)-
      wavelength B*∏ i:I,avg (w i) (p i)|≤η := by
  classical
  intro p hp
  let P (u : ∀ i, Vec (B i)) (i:J) (x y : A) := vectorPhase (u i) (F i x y)
  let Q (u : ∀ i,Vec (B i)) := ∏ i:J,vectorPhase (u i) (v i)
  let U (u:∀ i,Vec (B i)) := avg (prodW w) (fun x =>
    (∏ i:J,P u i (x (s.first i)) (x (s.nextP i)))*prodW p x)
  have he :
      avg (prodW w) (fun x => ind (listen s F x=v)*prodW p x)=
        avg (prism B) (fun u => Q u*U u) := by
    simp_rw [prism_expand,←avg_mul]
    rw [avg_avg]; unfold Q U P; simp_rw [←avg_mul',Finset.prod_mul_distrib]
    apply avg_congr; intro x _; refine avg_congr fun i _ => ?_
    ring
  have hU : U 0=∏ i:I,avg (w i) (p i) := by
    unfold U P
    simp only [vectorPhase,Pi.zero_apply,zero_dotProduct,wsign_zero,prod_const_one,one_mul]
    exact prodW_avg ..
  have hQ : Q 0=1 := by simp [Q,vectorPhase]
  have hq u : |Q u|=1 := by simp [Q,abs_prod,vectorPhase]
  let V := ∏ i:I,avg (w i) (p i)
  let L (u : ∀ i,Vec (B i)) := ind (u=0)*V
  have hi : avg (prism B) L=wavelength B*V := by
    unfold L; rw [avg_mul,show avg (prism B) (fun i => ind (i=0))= _ from pr_point' (prism B) 0]; rfl
  have hh u : |Q u*U u-L u| ≤ η := by
    by_cases hg : u=0
    · subst u; unfold L V; rw [ind_one (show (0:∀ i,Vec (B i))=0 from rfl),hU,hQ,sub_self,abs_zero]
      exact hη
    obtain ⟨i,ha⟩ := Function.ne_iff.mp hg
    unfold L; rw [ind_zero hg,zero_mul,sub_zero,abs_mul,hq,one_mul]
    exact band_res s w hw p hp (P u) (by intro k x y; simp [P,vectorPhase]) i η (h i (u i) ha)
  have h0 : IsLaw (prism B) := prodW_law (fun _ => unif_law)
  rw [he]; change |_ - wavelength B * V|≤_
  rw [←hi,←avg_sub]
  exact (abs_avg_le h0.nz).trans (h0.avg_le hh)

end HadwigerCounterexample

end

end OAI
