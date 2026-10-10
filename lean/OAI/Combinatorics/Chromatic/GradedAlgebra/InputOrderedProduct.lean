import Mathlib
import OAI.Combinatorics.Chromatic.Walls.WeightedRay
import OAI.Combinatorics.Chromatic.GradedAlgebra.HNSeries
import OAI.Combinatorics.Chromatic.Shuffle.InputOrderedEnergy

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open ElementaryPositivity.RawShuffle QuantumTorus PowerSeries
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (a : I → I → ℕ) (u : I → ℕ → R)
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
variable (hΩ : ∀d e,Ω (P d) (P e)=eulerForm a d e-eulerForm a e d)

def partialCoefficient (S : Finset I) : (I → ℕ) → R :=
  supportedCoefficient S (fun d=>(∏i∈S,u i (d i))*↑(v^(crossInteraction a d)))

include hΩ in
lemma partialCoefficient_union (S T : Finset I) (hST : Disjoint S T)
    (ha : ∀i∈S,∀j∈T,a i j=0) :
    partialCoefficient a u v (S∪T)=convolution v Ω P
      (partialCoefficient a u v S) (partialCoefficient a u v T) := by
  funext d
  rw [partialCoefficient,partialCoefficient,partialCoefficient,supported_convolution v Ω P S T hST]
  unfold supportedCoefficient
  by_cases hd : Supported (S∪T) d
  · rw [ite_eq_left hd,ite_eq_left hd]
    dsimp only
    rw [Finset.prod_union hST,crossInteraction_restrict_union a S T hST ha d hd,←hΩ]
    have hS : (∏i∈S,u i (restrictDim S d i))=∏i∈S,u i (d i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [restrictDim,ite_eq_left hi]
    have hT : (∏i∈T,u i (restrictDim T d i))=∏i∈T,u i (d i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [restrictDim,ite_eq_left hi]
    rw [hS,hT,zpow_add,zpow_add,Units.val_mul,Units.val_mul]
    ring
  · rw [ite_eq_right hd,ite_eq_right hd]

variable (w : I → ℕ) [Fact (∀i,0<w i)]
local instance partialCoefficientAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid

omit [DecidableEq I] in
lemma partialCoefficient_empty (d : I → ℕ) :
    partialCoefficient a u v ∅ d=if d=0 then 1 else 0 := by
  have H : Supported ∅ d ↔ d=0 := by simp [Supported,funext_iff]
  simp only [partialCoefficient,supportedCoefficient,H,Finset.prod_empty,one_mul]
  split_ifs with hd
  · subst d
    simp [crossInteraction]
  · rfl

omit [DecidableEq I] in
lemma push_partial_empty : push w v Ω P (partialCoefficient a u v ∅)=1 := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero=>
    rw [coeff_zero_eq_constantCoeff]
    rw [push_constant w v Ω P _ (by simp [partialCoefficient_empty])]
    simp
  | succ n=>
    simp only [push,coeff_mk,pushCoeff,coeff_one,show n+1≠0 from Nat.succ_ne_zero n,ite_false]
    apply Finset.sum_eq_zero
    intro d hd
    have H : d.val≠0 := by
      intro hzero
      have HH:=d.property
      rw [hzero,map_zero] at HH
      omega
    rw [partialCoefficient_empty,ite_eq_right H,Torus.monomial_zero]

include hΩ in
lemma push_partial_union (S T : Finset I) (hST : Disjoint S T)
    (ha : ∀i∈S,∀j∈T,a i j=0) :
    push w v Ω P (partialCoefficient a u v (S∪T))=
      push w v Ω P (partialCoefficient a u v S)*push w v Ω P (partialCoefficient a u v T) := by
  rw [partialCoefficient_union a u v Ω P hΩ S T hST ha,push_convolution]

include hΩ in

theorem push_partial_list (l : List I) (hl : l.Nodup) (ho : l.Pairwise fun i j=>a i j=0) :
    push w v Ω P (partialCoefficient a u v l.toFinset)=
      (l.map (fun i=>push w v Ω P (partialCoefficient a u v {i}))).prod := by
  induction l with
  | nil=> simpa using push_partial_empty a u v Ω P w
  | cons i l ih=>
    have hnil:=List.nodup_cons.mp hl
    have hord:=List.pairwise_cons.mp ho
    rw [List.toFinset_cons,←Finset.singleton_union]
    rw [push_partial_union a u v Ω P hΩ w {i} l.toFinset]
    · simp only [ih hnil.2 hord.2,List.map_cons,List.prod_cons]
    · simpa using hnil.1
    · intro j hj k hk
      have hji : j=i := by simpa using hj
      subst j
      exact hord.1 k (List.mem_toFinset.mp hk)

end
end ElementaryPositivity.WeightedTorusSeries

end
section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus PowerSeries
noncomputable section
attribute [local instance] Classical.propDecidable
variable {I R M : Type*} [Fintype I] [DecidableEq I] [CommRing R] [AddCommGroup M]
variable (w : I → ℕ) [hw : Fact (∀i,0<w i)]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I → ℕ) →+ M)
local instance pushAxisAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid

omit hw in
lemma weight_single (i : I) (k : ℕ) : weight w (Pi.single i k)=k*w i := by
  simp [weight,Pi.single_apply,ite_mul]

omit [Fintype I] in
lemma supported_single_eq (i : I) (d : I → ℕ) (hd : Supported {i} d) : d=Pi.single i (d i) := by
  funext j
  by_cases hj : j=i
  · subst j; simp
  · simp [hj,hd j (by simpa)]

omit [Fintype I] in
lemma single_nsmul (i : I) (k : ℕ) : Pi.single i k=k • (Pi.single i 1 : I → ℕ) := by
  funext j
  by_cases hj : j=i
  · subst j; simp
  · simp [hj]

lemma push_axis (i : I) (f : PowerSeries R) :
    push w v Ω P (supportedCoefficient {i} (fun d=>coeff (d i) f))=
      weightedRay v Ω (w i) (P (Pi.single i 1)) f := by
  apply PowerSeries.ext
  intro n
  rw [push,coeff_mk,pushCoeff,coeff_weightedRay]
  by_cases hn : w i∣n
  · rw [ite_eq_left hn]
    let d₀ : Slice w n:=⟨Pi.single i (n/w i),by
      rw [weight_single,Nat.div_mul_cancel hn]⟩
    rw [Finset.sum_eq_single d₀]
    · have HS : Supported {i} d₀.val := by
        intro j hj
        have H : j≠i := by simpa using hj
        simp [d₀,H]
      rw [supportedCoefficient,ite_eq_left HS]
      dsimp only [d₀]
      rw [Pi.single_eq_same,single_nsmul,map_nsmul]
    · intro d hd hne
      have HS : ¬Supported {i} d.val := by
        intro HS
        apply hne
        apply Subtype.ext
        have HE:=d.property
        rw [supported_single_eq i d.val HS,weight_single] at HE
        have HV : d.val i=n/w i := by
          calc
            d.val i=(d.val i*w i)/(w i) := (Nat.mul_div_left _ (hw.out i)).symm
            _=n/(w i) := congrArg (fun x=>x/(w i)) HE
        rw [supported_single_eq i d.val HS,HV]
      rw [supportedCoefficient,ite_eq_right HS,Torus.monomial_zero]
    · simp
  · rw [ite_eq_right hn]
    apply Finset.sum_eq_zero
    intro d hd
    have HS : ¬Supported {i} d.val := by
      intro HS
      apply hn
      have HE:=d.property
      rw [supported_single_eq i d.val HS,weight_single] at HE
      exact ⟨d.val i,by rw [Nat.mul_comm,HE]⟩
    rw [supportedCoefficient,ite_eq_right HS,Torus.monomial_zero]

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
