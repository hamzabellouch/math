import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.PrimitiveRootClosure
import OAI.Combinatorics.Chromatic.Shuffle.InputProduct

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic QuantumTorus WeightedTorusSeries WallUnits PowerSeries
noncomputable section
variable {I J M : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (Ω : M→+M→+ℤ) (hΩ : ∀p,Ω p p=0)
variable (p : I→M) (κ : I→ℤ) (ε : I→Bool)
variable (w : I→ℕ) [Fact (∀i,0<w i)]
variable (c η : I→ℝ) (hc : ∀i,0<c i) (t : ℝ)
variable (hp : ∀i j,(Ω (p i) (p j):ℝ)=t*(η i*c j-c i*η j))
variable (l : List I) (hn : l.Nodup) (hall : l.toFinset=Finset.univ)
variable (hl : l.Pairwise (fun i j=>0≤Ω (p i) (p j)))
variable (C : (J→ℤ)→+M) (hroot : ∀d,HasRootDegree C (weight w d) (rootSum p d))
variable (h : M→+ℝ) (θ : ℝ) (hh : ∀d,h (rootSum p d)=slopeValue c η θ d)
variable (V : M→Prop) (hv : ∀d∈slopeDimensions c η hc θ,V (rootSum p d))

include hΩ hc hp hn hall hl hroot hh hv in
theorem geometric_zero_rootClosure :
    InPrecisionClosure LaurentRay.vUnit Ω (literalRootProducts Ω C V)
      (PowerSeriesSplit.zeroFactor (positiveProject LaurentRay.vUnit Ω h)
        (zeroProject LaurentRay.vUnit Ω h)
        ((l.map (literalAxis κ ε Ω (rootSum p) w)).prod)) := by
  let a:=geometricQuiver Ω p ε
  let : Fact (∀θ,SlopeEulerSymmetric a c η θ) :=
    ⟨geometricQuiver_symmetric Ω p ε hΩ c η hc t hp⟩
  have H:=literalInput_ordered a κ ε Ω (rootSum p) w
    (geometricQuiver_euler Ω p ε hΩ) l hn hall
    (geometricQuiver_pairwise Ω p ε hΩ l hn hl)
  rw [←H]
  exact finiteInput_zero_rootClosure a κ c η hc w Ω (rootSum p) C
    (geometricQuiver_euler Ω p ε hΩ) hroot θ V hv h hh ε
    (geometricQuiver_diag Ω p ε)
end
end ElementaryPositivity.RawShuffle

end
section
namespace ElementaryPositivity.RawShuffle
open SlopeArithmetic QuantumTorus WeightedTorusSeries WallUnits
noncomputable section
variable {I J M : Type*} [Fintype I] [DecidableEq I] [Fintype J] [AddCommGroup M]
variable (p : I→M) (w : I→ℕ) (C : (J→ℤ)→+M)

lemma rootDegree_finset_sum {A : Type*} (s : Finset A) (n : A→ℕ) (m : A→M)
    (h : ∀i∈s,HasRootDegree C (n i) (m i)) :
    HasRootDegree C (∑i∈s,n i) (∑i∈s,m i) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using rootDegree_zero C
  | @insert a s ha ih=>
    simp only [Finset.sum_insert ha]
    exact rootDegree_add C (h a (by simp)) (ih (fun i hi=>h i (by simp [hi])))

omit [DecidableEq I] in
lemma rootSum_rootDegree (hp : ∀i,HasRootDegree C (w i) (p i)) (d : I→ℕ) :
    HasRootDegree C (weight w d) (rootSum p d) := by
  exact rootDegree_finset_sum C Finset.univ (fun i=>d i*w i) (fun i=>d i • p i)
    (fun i _=>rootDegree_nsmul C (hp i) (d i))

omit [DecidableEq I] in
lemma rootSum_mem (V : AddSubmonoid M) (hp : ∀i,p i∈V) (d : I→ℕ) : rootSum p d∈V := by
  exact V.sum_mem (fun i _=>V.nsmul_mem (hp i) (d i))

omit [DecidableEq I] in
lemma rootSum_slope_zero (h : M→+ℝ) (c : I→ℝ) (d : I→ℕ) :
    h (rootSum p d)=slopeValue c (fun i=>h (p i)) 0 d := by
  simp only [rootSum,AddMonoidHom.coe_mk,ZeroHom.coe_mk,map_sum,map_nsmul,
    slopeValue,zero_mul,sub_zero,mass,nsmul_eq_mul]
end
end ElementaryPositivity.RawShuffle

end

end OAI
