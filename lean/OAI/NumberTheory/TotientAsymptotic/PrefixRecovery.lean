import OAI.NumberTheory.TotientAsymptotic.PrefixProjection

namespace OAI

/-! The head, common inner prefix and suffix determine a tuple exactly. -/

noncomputable section
open scoped BigOperators

namespace TotientAsymptotic

lemma tuple_recovered_from_parts {n i : ℕ} {τ σ : TotientTuple n}
    (hi : 1 ≤ i) (hin : i ≤ n+1) (hh : τ.head=σ.head)
    (hp : tupleInnerPrefix τ (i-1)=tupleInnerPrefix σ (i-1))
    (hs : tupleSuffix τ i=tupleSuffix σ i) : τ=σ := by
  have hd : τ.tail.d=σ.tail.d := congrArg (fun z : PrefixDatum (n+1-i) => z.d) hs
  have he : τ.tail.primes=σ.tail.primes := by
    funext j
    by_cases hj : j.val < i-1
    · have h := congrFun hp ⟨j.val,hj⟩
      simpa only [tupleInnerPrefix,dite_eq_left j.isLt] using h
    · let k : Fin (n+1-i) := ⟨j.val+1-i,by have := j.isLt; omega⟩
      have h := congrFun (congrArg PrefixDatum.primes hs) k
      change tuplePrimes τ ⟨i+k.val,by have := k.isLt; omega⟩=
        tuplePrimes σ ⟨i+k.val,by have := k.isLt; omega⟩ at h
      have hk : i+k.val=j.val+1 := by dsimp [k]; omega
      simp only [hk] at h
      exact h
  cases τ with
  | mk th tt =>
    cases σ with
    | mk sh st =>
      cases tt
      cases st
      simp_all

lemma tupleValue_split_inner_suffix {n i : ℕ} (τ : TotientTuple n)
    (hi : 1 ≤ i) (hin : i ≤ n) :
    tupleValue τ=(τ.head-1)*(∏ j, (tupleInnerPrefix τ (i-1) j-1))*
      prefixDenominator (tupleSuffix τ i) := by
  classical
  let c : Fin (n+1) := ⟨i,by omega⟩
  let z : Fin (n+1) := 0
  have hpart : Finset.Iio c ∪ Finset.Ici c=Finset.univ := by
    ext j
    simp only [Finset.mem_union,Finset.mem_Iio,Finset.mem_Ici,Finset.mem_univ]
    exact iff_true_intro (lt_or_ge j c)
  have hdis : Disjoint (Finset.Iio c) (Finset.Ici c) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    exact (not_lt_of_ge (Finset.mem_Ici.mp hk)) (Finset.mem_Iio.mp hj)
  have hpref : Finset.Iio c=insert z (Finset.Icc (⟨1,by omega⟩ : Fin (n+1)) ⟨i-1,by omega⟩) := by
    ext j
    simp only [Finset.mem_Iio,Finset.mem_insert,Finset.mem_Icc,Fin.lt_def,Fin.le_def]
    change (j.val < i) ↔ j=z ∨ 1 ≤ j.val ∧ j.val ≤ i-1
    constructor
    · intro hj
      by_cases hz : j.val=0
      · exact Or.inl (Fin.ext hz)
      · exact Or.inr ⟨by omega,by omega⟩
    · rintro (rfl | hj)
      · change 0 < i
        omega
      · omega
  have hprod : (∏ j ∈ Finset.Icc (⟨1,by omega⟩ : Fin (n+1)) ⟨i-1,by omega⟩, (tuplePrimes τ j-1)) =
      ∏ j, (tupleInnerPrefix τ (i-1) j-1) := by
    symm
    apply Finset.prod_bij (fun j _ => (⟨j.val+1,by have := j.isLt; omega⟩ : Fin (n+1)))
    · intro j _
      apply Finset.mem_Icc.mpr
      constructor
      · change 1 ≤ j.val+1
        omega
      · change j.val+1 ≤ i-1
        have := j.isLt
        omega
    · intro j _ k _ he
      apply Fin.ext
      have he' := congrArg (fun z : Fin (n+1) => z.val) he
      dsimp only at he'
      omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      have hjlo : 1 ≤ j.val := by
        have hh := hj'.1
        change ((⟨1,by omega⟩ : Fin (n+1)).val) ≤ j.val at hh
        exact hh
      have hjhi : j.val ≤ i-1 := hj'.2
      refine ⟨⟨j.val-1,by omega⟩,Finset.mem_univ _,?_⟩
      apply Fin.ext
      dsimp only
      omega
    · intro j _
      have hj : j.val < n := by have := j.isLt; omega
      simp only [tupleInnerPrefix,dite_eq_left hj]
      rfl
  rw [tupleValue,← hpart,Finset.prod_union hdis,hpref,
    Finset.prod_insert (by simp [z]),hprod,tupleSuffix_denominator_product τ hin]
  dsimp only [z,c]
  simp only [tuplePrimes,Fin.cons_zero]
  ring

end TotientAsymptotic

end

end OAI
