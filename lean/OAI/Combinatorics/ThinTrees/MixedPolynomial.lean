import OAI.Combinatorics.ThinTrees.DeterminantCalculus

namespace OAI

universe uI uD uR

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

def diffProduct (dirs : List I) : MvPolynomial I R →ₗ[R] MvPolynomial I R :=
  dirs.foldr (fun j f => f.comp (LinearMap.id-(MvPolynomial.pderiv j).toLinearMap)) LinearMap.id

omit [Fintype I] [Fintype D] [DecidableEq D] in
omit [DecidableEq I] in
@[simp] lemma diffProduct_nil (p : MvPolynomial I R) : diffProduct [] p=p := rfl

omit [Fintype I] [Fintype D] [DecidableEq D] in
omit [DecidableEq I] in
@[simp] lemma diffProduct_cons (j : I) (dirs : List I) (p : MvPolynomial I R) :
    diffProduct (j::dirs) p=diffProduct dirs (p-MvPolynomial.pderiv j p) := rfl

omit [Fintype I] [Fintype D] [DecidableEq D] in
omit [DecidableEq I] in
lemma diffProduct_foldl (dirs : List I) (p : MvPolynomial I R) :
    diffProduct dirs p=dirs.foldl (fun q j => q-MvPolynomial.pderiv j q) p := by
  induction dirs generalizing p with
  | nil => rfl
  | cons j dirs ih => exact ih _

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma diffProduct_perm {s t : List I} (h : s.Perm t) (p : MvPolynomial I R) :
    diffProduct s p=diffProduct t p := by
  induction h generalizing p with
  | nil => rfl
  | cons j h ih => simpa only [diffProduct_cons] using ih _
  | swap i j s =>
    simp only [diffProduct_cons]
    apply congrArg (diffProduct s)
    simp only [map_sub]
    rw [pderiv_commute p i j]
    abel
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ p).trans (ih₂ p)

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma eval_zero_zeroSub (j : I) (p : MvPolynomial I R) :
    MvPolynomial.eval (fun _ => 0) (zeroSub j p)=MvPolynomial.eval (fun _ => 0) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p i hp =>
    by_cases hi : i=j
    · subst i; simp
    · simp [hi]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma zeroSub_pderiv {j i : I} (h : i ≠ j) (p : MvPolynomial I R) :
    zeroSub j (MvPolynomial.pderiv i p)=MvPolynomial.pderiv i (zeroSub j p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p k hp =>
    by_cases hk : k=j
    · subst k; simp [Ne.symm h]
    · by_cases hki : k=i
      · subst k; simp [h,hp]
      · simp [hk,hki,hp]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma diffProduct_zeroSub (j : I) (dirs : List I) (h : j ∉ dirs) (p : MvPolynomial I R) :
    diffProduct dirs (zeroSub j p)=zeroSub j (diffProduct dirs p) := by
  induction dirs generalizing p with
  | nil => rfl
  | cons i dirs ih =>
    have hi : i ≠ j := fun he => h (by simp [he])
    have hj : j ∉ dirs := fun hj => h (List.mem_cons_of_mem _ hj)
    simp only [diffProduct_cons]
    rw [←zeroSub_pderiv hi,←map_sub,ih hj]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma eval_zero_diffProduct_cons (j : I) (dirs : List I) (h : j ∉ dirs) (p : MvPolynomial I R) :
    MvPolynomial.eval (fun _ => 0) (diffProduct (j::dirs) p)=
      MvPolynomial.eval (fun _ => 0) (diffProduct dirs (zeroDiff j p)) := by
  rw [diffProduct_cons,zeroDiff,diffProduct_zeroSub j dirs h,eval_zero_zeroSub]

def mixedEval (dirs : List I) (M : Matrix D D R) (A : I → Matrix D D R) : R :=
  MvPolynomial.eval (fun _ => 0) (diffProduct dirs (basePencil M A))

end StrongThinTree.MSS

end
end

end OAI
