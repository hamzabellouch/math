import Mathlib
import OAI.Combinatorics.SharpRamsey.Entropy.TestActualSecondMoment
import OAI.Combinatorics.SharpRamsey.Geometry.TestProjectiveTail

namespace OAI

section
namespace SharpLogRamsey.PreparedProjectiveGeometry
open Finset MeasureTheory SharpRamseyFive.PoissonScore SharpLogRamsey.PointScore
open scoped Classical BigOperators NNReal
noncomputable section
variable {K V I : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]
local instance flat_JoinedTestPointMoments_1 : Finite (Module.Dual K V) := Module.finite_of_finite K
local instance flat_JoinedTestPointMoments_2 : Fintype (Projectivization K (Module.Dual K V)) := Fintype.ofFinite _

theorem actual_point_high_tail
    (j : ℕ) (hj : 2 ≤ j) (hj3 : j ≤ 3) (hdim : Module.finrank K V ≤ j+1)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule ≤ LinearMap.ker H.rep)
    (f B : ℝ) (hf : f ≤ 1/25) {p : ℕ} (hp : 0<p) (hpe : Even p) (R : ℕ)
    (hL : 10000 ≤ (L:ℝ))
    (hlow : ∀ H∈A,3/4 ≤ (c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card)
    (hupp : ∀ H∈A,(c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card ≤ 2)
    (hdelta : ∀ H∈A,|(c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f)| ≤ 13/100)
    (hB : Real.exp (3*((L:ℝ)*R)) ≤ B)
    (hcard : ((∑ i∈range j,Nat.card K^i):ℝ) ≤ 4*B^2)
    (hdir : ((∑ i∈range (j-1),Nat.card K^i):ℝ) ≤ 4*B)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i∈T,0 ≤ a i)
    (hcover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap (S\(O∪{x})) x c H J →
      ∃ i∈T,a i ≤ overlap (S\(O∪{x})) x c H J ∧ overlap (S\(O∪{x})) x c H J ≤ 2*a i)
    (hcount : ∀ i∈T,((largePairs (S\(O∪{x})) x c (a i) A).card:ℝ)*a i^200 ≤ B^2*Real.exp (((L:ℝ)*R)/50))
    (hrow : ∀ H∈A,∀ i∈T,((largeNeighbors (S\(O∪{x})) x c (a i) A H).card:ℝ)*a i^200 ≤ B*Real.exp (((L:ℝ)*R)/50))
    (hstrong : ∀ H∈A,((largeNeighbors (S\(O∪{x})) x c (1/(100*(p:ℝ))) A H).card:ℝ) ≤ B*Real.exp (-3*((L:ℝ)*R)))
    (hsq : (∑ H∈A,((c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2) ≤ B*Real.exp (((L:ℝ)*R)/100))
    (hpoly : SharpLogRamsey.MomentBudgetBridge.certificateOverhead p T.card ((L:ℝ)*R) ≤ Real.exp (2*((L:ℝ)*R)/25))
    (hshift : SharpLogRamsey.MomentBudgetBridge.shiftOverhead p T.card ≤ Real.exp (2*((L:ℝ)*R)/25))
    (hp2 : (p:ℝ)^2 ≤ Real.exp (((L:ℝ)*R)/10))
    (hps : 2*(p:ℝ)+3 ≤ Real.exp (((L:ℝ)*R)/10))
    (h : ℕ) (hh : 0<h) (hR : 400 ≤ R) (hsize : h ≤ (R/2)/400)
    (herr : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2)
    (t : ℝ) (ht : 0<t) :
    (batchMeasure (fun _ : Fin R × S => L*c)).real
      {ω | (∀ r (y : S),y.1=x → ω (r,y)=0) ∧
        t ≤ |pointScore (fun y : S => y.1∈O)
          (fun (H : A) (y : S) => y.1.submodule ≤ LinearMap.ker H.1.rep)
          (Real.exp (-(L:ℝ)*(1-f))) ω|}
      ≤ (B^p*Real.exp (-(1/10:ℝ)*(p*((L:ℝ)*R))))/t^p := by
  have hB0 : 0≤B := (Real.exp_pos _).le.trans hB
  apply projective_point_tail S O x c L A hA R _ p hpe t _ ht (by positivity)
  intro bits
  exact actual_projective_high_moment j hj hj3 hdim (S\(O∪{x})) x c L A hA f B hf hp R bits
    hL hlow hupp hdelta hB hcard hdir T a ha hcover hcount hrow hstrong hsq
    hpoly hshift hp2 hps h hh hR hsize herr

theorem actual_point_second_tail
    (j : ℕ) (hdim : Module.finrank K V ≤ j+1)
    (S O : Finset (Projectivization K V)) (x : Projectivization K V) (c L : ℝ≥0)
    (A : Finset (Projectivization K (Module.Dual K V)))
    (hA : ∀ H∈A,x.submodule ≤ LinearMap.ker H.rep)
    (f B C : ℝ) (hf : f ≤ 1/4) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (R : ℕ) (hL : 1 ≤ (L:ℝ)) (hR : 200 ≤ R)
    (hlow : ∀ H∈A,3/4 ≤ (c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card)
    (hupp : ∀ H∈A,(c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card ≤ 2)
    (hdelta : ∀ H∈A,|(c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f)| ≤ 1)
    (hsq : (∑ H∈A,((c:ℝ)*((S\(O∪{x})).filter (fun y => y≠x ∧ y.submodule ≤ LinearMap.ker H.rep)).card-(1-f))^2) ≤ C*B*Real.exp ((L:ℝ)/100))
    (hcard : ((∑ i∈range j,Nat.card K^i):ℝ) ≤ C*B^2)
    (T : Finset I) (a : I → ℝ) (ha : ∀ i∈T,0<a i)
    (hcover : ∀ H∈A,∀ J∈A,H≠J → 0<overlap (S\(O∪{x})) x c H J →
      ∃ i∈T,a i ≤ overlap (S\(O∪{x})) x c H J ∧ overlap (S\(O∪{x})) x c H J ≤ 2*a i)
    (hcount : ∀ i∈T,((largePairs (S\(O∪{x})) x c (a i) A).card:ℝ)*a i^200 ≤ B^2*Real.exp (((L:ℝ)*R)/50))
    (hd : C*2^R ≤ Real.exp ((L:ℝ)*R/20))
    (hp : (2*(L:ℝ)^2)^R ≤ Real.exp ((L:ℝ)*R/25))
    (hb : C^2*Real.exp ((L:ℝ)/50)+(T.card:ℝ)*2^R*Real.exp ((L:ℝ)*R/50) ≤ Real.exp ((L:ℝ)*R/20))
    (h2 : 2 ≤ Real.exp ((L:ℝ)*R/20))
    (t : ℝ) (ht : 0<t) :
    (batchMeasure (fun _ : Fin R × S => L*c)).real
      {ω | (∀ r (y : S),y.1=x → ω (r,y)=0) ∧
        t ≤ |pointScore (fun y : S => y.1∈O)
          (fun (H : A) (y : S) => y.1.submodule ≤ LinearMap.ker H.1.rep)
          (Real.exp (-(L:ℝ)*(1-f))) ω|}
      ≤ (B^2*Real.exp (-(3/5:ℝ)*((L:ℝ)*R)))/t^2 := by
  apply projective_point_tail S O x c L A hA R _ 2 (by decide) t _ ht (by positivity)
  intro bits
  exact actual_projective_second_moment j hdim (S\(O∪{x})) x c L A hA f B C hf hB hC R bits
    hL hR hlow hupp hdelta hsq hcard T a ha hcover hcount hd hp hb h2

end
end SharpLogRamsey.PreparedProjectiveGeometry

end

end OAI
