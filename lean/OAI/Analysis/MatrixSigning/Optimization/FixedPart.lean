import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Potential
import OAI.Analysis.MatrixSigning.Optimization.RootTolerance
import OAI.Analysis.MatrixSigning.Optimization.Lookup

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Variational
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

variable {d N n : ℕ}

def fixedPart (e : Fin n → Fin N) (base : Coordinates N) (A : Fin N → H d) : H d :=
  ∑ i,(lookup e i).elim (base i • A i) (fun _ => 0)

lemma S_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d) (y : Coordinates n) :
    S A (extend e base y)=fixedPart e base A+S (fun j => A (e j)) y := by
  exact sum_extend e he (fun (i : Fin N) (t : ℝ) => (t • A i : H d)) base y

lemma penalty_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (hb : ∀ i,lookup e i=none → |base i|=1) (y : Coordinates n) :
    (∑ i,psi (extend e base y i))=∑ j,psi (y j) := by
  rw [sum_extend e he (fun _ t => psi t) base y]
  have hz : (∑ i,(lookup e i).elim (psi (base i)) (fun _ => 0))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    cases hi : lookup e i with
    | none => exact psi_endpoint (hb i hi)
    | some j => rfl
  rw [hz,zero_add]

lemma eta_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hb : ∀ i,lookup e i=none → |base i|=1) (y : Coordinates n) (c : ℝ) :
    eta c A (extend e base y)=eta c (fun j => A (e j)) y := by
  apply ContinuousLinearMap.ext
  intro Z
  rw [eta_apply,eta_apply]
  have hsum := sum_extend e he (fun (i : Fin N) (t : ℝ) => ((c*psi t) • sandwich (A i) Z : H d)) base y
  rw [hsum]
  have hz : (∑ i,(lookup e i).elim ((c*psi (base i)) • sandwich (A i) Z) (fun _ => 0))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    cases hi : lookup e i with
    | none => simp only [Option.elim_none,psi_endpoint (hb i hi),mul_zero,zero_smul]
    | some j => rfl
  rw [hz,zero_add]

lemma potential_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hb : ∀ i,lookup e i=none → |base i|=1) (y : Coordinates n) (ε lam : ℝ) :
    value ε (S A (extend e base y)) (eta 384 A (extend e base y))+
      lam*∑ i,psi (extend e base y i)=
    value ε (fixedPart e base A+S (fun j => A (e j)) y) (eta 384 (fun j => A (e j)) y)+
      lam*∑ j,psi (y j) := by
  rw [S_extend e he,eta_extend e he base A hb,penalty_extend e he base hb]

end CurrentKS.RationalFace

namespace CurrentKS.RationalSDP
open CurrentKS.RationalFace

variable {d N n : ℕ}

def faceQuery (coords : Fin N → Fin d × Fin d → ℚ) (base : Fin N → ℚ)
    (y : Fin (activeIndices base).length → ℚ) (ν lam error : ℚ) : ℚ :=
  potentialQuery coords (extend (activeIndex base) base y) ν lam error

open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational CurrentKS.State CurrentKS.Scalar
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

lemma faceQuery_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) (y : Fin (activeIndices base).length → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam error : ℚ} (hν : 0<ν) (hν1 : ν≤1) (hlam : 0≤lam)
    (he : 0<error) (he1 : error≤1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i|≤1) (hy : ∀ j,|y j|≤1) :
    |(faceQuery coords base y ν lam error:ℝ)-
      (value ((ν:ℝ)/d)
        (fixedPart (activeIndex base) (fun i => (base i:ℝ)) (rationalAtoms coords)+
          S (fun j => rationalAtoms coords (activeIndex base j)) (fun j => (y j:ℝ)))
        (eta 384 (fun j => rationalAtoms coords (activeIndex base j)) (fun j => (y j:ℝ)))+
        (lam:ℝ)*∑ j,psi (y j:ℝ))|≤(error:ℝ) := by
  have hcube : Cube (fun i => ((extend (activeIndex base) base y i : ℚ):ℝ)) := by
    intro i
    change |((extend (activeIndex base) base y i : ℚ):ℝ)| ≤ 1
    exact_mod_cast extend_cube (e := activeIndex base) base y hb hy i
  have hq := potentialQuery_correct coords (extend (activeIndex base) base y)
    hA htr hν hν1 hlam he he1 hvar hcube
  have heq := potential_extend (activeIndex base) (activeIndex_injective base)
    (fun i => (base i:ℝ)) (rationalAtoms coords) (real_active_outside_endpoint base hb)
    (fun j => (y j:ℝ)) ((ν:ℝ)/d) (lam:ℝ)
  have hext := map_extend (fun q : ℚ => (q:ℝ)) (activeIndex base) base y
  have hext' : ∀ i, ((extend (activeIndex base) base y i : ℚ):ℝ) =
      extend (activeIndex base) (fun i => (base i:ℝ)) (fun j => (y j:ℝ)) i :=
    fun i => congrFun hext i
  simp_rw [hext'] at hq
  rw [heq] at hq
  exact hq

end CurrentKS.RationalSDP

end

end OAI
