import OAI.NumberTheory.DirichletL.PrimeRows.CentralProduct

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def centralBranch (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : Fin 3→ℂ :=
  ![-star (idealRowHom u.val P.val),centralRegularError η u P hs x w z,
    centralRepeatedTerm η u P hs x w z]

theorem central_branch_sum (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    centralNormalizedSlot η u P hs x w z=∑b:Fin 3,centralBranch η u P hs x w z b := by
  simpa [centralBranch,Fin.sum_univ_three] using centralNormalizedSlot_split η u P hs x w z

theorem central_slots_branch_expansion {K : ℕ}
    (η : Character) (u : FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    (∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralNormalizedSlot η u P.val (hT i P.val P.property) x w z)=
    ∑b:Fin K→Fin 3,∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralBranch η u P.val (hT i P.val P.property) x w z (b i) := by
  simp_rw [central_branch_sum,Finset.mul_sum]
  have hs (i : Fin K) :
      (∑P:T i,∑b:Fin 3,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralBranch η u P.val (hT i P.val P.property) x w z b)=
      ∑b:Fin 3,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralBranch η u P.val (hT i P.val P.property) x w z b := Finset.sum_comm
  simp_rw [hs]
  exact Fintype.prod_sum _

theorem calibrated_central_branch_expansion {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (T : Fin K→Finset PrimeIdeal)
    (hPS : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (a e : ℝ) (x w z : ℂ)
    (htail : FirstTail (4*e) S) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hx : x.re=a+16*e)
    (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hQ : ∀i P,P∈T i→(480:ℝ)≤P.val.absNorm)
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hsmall : ∀i P,P∈T i→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) :
    (∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hPS i (P i).val (P i).property) W Y x w z)=
      centralRowScalar S hS hmax η u x w z*
      ∑b:Fin K→Fin 3,∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralBranch η u P.val
          (outside_prime_supported S hS.bad P.val (hPS i P.val P.property)) x w z (b i) := by
  rw [calibrated_prime_slots_separate S hS hmax η u T hPS hdis W Y a e x w z
    htail ha ha1 he he1 hx hw hz hQ hη hsmall]
  congr 1
  exact central_slots_branch_expansion η u T
    (fun i P hP=>outside_prime_supported S hS.bad P (hPS i P hP)) W Y x w z
end SevenEighths.ProbeHighRowFamily
end

end OAI
