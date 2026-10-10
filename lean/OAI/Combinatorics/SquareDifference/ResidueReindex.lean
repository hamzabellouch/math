import OAI.Combinatorics.SquareDifference.SelectedPair

namespace OAI

section

open Finset

open scoped BigOperators ComplexConjugate

namespace SquareDifference

open LiftTheory.SquareDifference

section Reindex

variable {J K : Type*} [instFintypeJ : Fintype J] [instDecidableEqJ : DecidableEq J] [instFintypeK : Fintype K] [instDecidableEqK : DecidableEq K]
  (p : J → ℕ) (m : K → ℕ) [instNeZeropj : ∀j,NeZero (p j)] [∀k,NeZero (m k)]
  (e : K ≃ J) (hm : m=fun k => p (e k))

noncomputable def residueReindex : ResidueSpace p ≃ ResidueSpace m := by
  subst m
  exact (Equiv.piCongrLeft (fun j => ZMod (p j)) e).symm

lemma residueReindex_neg {J : Type*}
    {K : Type*}
    [Fintype J]
    [DecidableEq J]
    [Fintype K]
    [DecidableEq K]
    (p : J → ℕ)
    (m : K → ℕ)
    [∀ (j : J), NeZero (p j)]
    [∀ (k : K), NeZero (m k)]
    (e : K ≃ J)
    (hm : m = fun k => p (e k)) (a : ResidueSpace p) :
    residueReindex p m e hm (-a)= -residueReindex p m e hm a := by
  subst m
  rfl

lemma residueReindex_natCast {J : Type*}
    {K : Type*}
    [Fintype J]
    [DecidableEq J]
    [Fintype K]
    [DecidableEq K]
    (p : J → ℕ)
    (m : K → ℕ)
    [∀ (j : J), NeZero (p j)]
    [∀ (k : K), NeZero (m k)]
    (e : K ≃ J)
    (hm : m = fun k => p (e k)) (n : ℕ) :
    residueReindex p m e hm (fun j => (n:ZMod (p j)))=(fun k => (n:ZMod (m k))) := by
  subst m
  rfl

lemma prodChar_reindex {J : Type*}
    {K : Type*}
    [Fintype J]
    [DecidableEq J]
    [Fintype K]
    [DecidableEq K]
    (p : J → ℕ)
    (m : K → ℕ)
    [∀ (j : J), NeZero (p j)]
    [∀ (k : K), NeZero (m k)]
    (e : K ≃ J)
    (hm : m = fun k => p (e k)) (a x : ResidueSpace p) :
    prodChar m (residueReindex p m e hm a) (residueReindex p m e hm x)=prodChar p a x := by
  subst m
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

lemma supportDenominator_reindex {J : Type*}
    {K : Type*}
    [Fintype J]
    [DecidableEq J]
    [Fintype K]
    [DecidableEq K]
    (p : J → ℕ)
    (m : K → ℕ)
    [∀ (j : J), NeZero (p j)]
    [∀ (k : K), NeZero (m k)]
    (e : K ≃ J)
    (hm : m = fun k => p (e k)) (a : ResidueSpace p) :
    supportDenominator m (residueReindex p m e hm a)=supportDenominator p a := by
  subst m
  simp only [supportDenominator,primeSupport,prod_filter]
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

lemma residueFourier_reindex (F : ResidueSpace p → ℂ) (a : ResidueSpace p) :
    residueFourier m (fun x => F ((residueReindex p m e hm).symm x)) (residueReindex p m e hm a)=
      residueFourier p F a := by
  symm
  apply Fintype.expect_equiv (residueReindex p m e hm)
  intro x
  simp only [Equiv.symm_apply_apply,prodChar_reindex]

lemma squareMultiplier_reindex (a : ResidueSpace p) :
    squareMultiplier m (residueReindex p m e hm a)=squareMultiplier p a := by
  subst m
  unfold squareMultiplier
  let u := (Equiv.piCongrLeft (fun j => (ZMod (p j))ˣ) e).symm
  have hu : (𝔼 x : ∀j,(ZMod (p j))ˣ,
      prodChar (fun k => p (e k)) (residueReindex p (fun k => p (e k)) e rfl a)
        (fun k => (x (e k):ZMod (p (e k)))^2))=
      𝔼 y : ∀k,(ZMod (p (e k)))ˣ,
        prodChar (fun k => p (e k)) (residueReindex p (fun k => p (e k)) e rfl a)
          (fun k => (y k:ZMod (p (e k)))^2) :=
    Fintype.expect_equiv u _ _ (fun _ => rfl)
  rw [←hu]
  apply expect_congr rfl
  intro x _
  unfold prodChar
  exact Fintype.prod_equiv e _ _ (fun _ => rfl)

lemma sequenceResidueFourier_reindex {Ω : Type*} [Fintype Ω]
    (N : ℕ) (F : Ω → ℂ) (n : Ω → ℕ) (a : ResidueSpace p) :
    sequenceResidueFourier m N F n (residueReindex p m e hm a)=sequenceResidueFourier p N F n a := by
  unfold sequenceResidueFourier
  congr 1
  apply sum_congr rfl
  intro x _
  rw [←residueReindex_natCast p m e hm,prodChar_reindex]

lemma low_pair_reindex (F G : ResidueSpace p → ℂ) (H : ℝ) :
    (∑a∈univ.filter (fun a => (supportDenominator m a:ℝ)≤H),
      residueFourier m (fun x => F ((residueReindex p m e hm).symm x)) (-a)*
      residueFourier m (fun x => G ((residueReindex p m e hm).symm x)) a*squareMultiplier m a)=
    ∑a∈univ.filter (fun a => (supportDenominator p a:ℝ)≤H),
      residueFourier p F (-a)*residueFourier p G a*squareMultiplier p a := by
  simp only [sum_filter]
  symm
  apply Fintype.sum_equiv (residueReindex p m e hm)
  intro a
  rw [supportDenominator_reindex,←residueReindex_neg,residueFourier_reindex,
    residueFourier_reindex,squareMultiplier_reindex]

end Reindex

end SquareDifference

end

end OAI
