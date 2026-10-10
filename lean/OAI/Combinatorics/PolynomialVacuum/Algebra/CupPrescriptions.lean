import OAI.Combinatorics.PolynomialVacuum.Algebra.Table

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial
open Classical

noncomputable def polyExchangeNumerator {ι : Type*} (x y : MvPolynomial ι ℂ)
    (a b : Pair) : MvPolynomial ι ℂ :=
  (C (t^2)*y-x)*(C T*x-y)*C (Pzero a b) +
  (C T*y-x)*(C (t^2)*x-y)*C (Pone a b) +
  (C (t^2)*y-x)*(C T*y-x)*C (Ptwo a b)

@[simp] theorem eval_polyExchangeNumerator {ι : Type*} (X : ι → ℂ)
    (x y : MvPolynomial ι ℂ) (a b : Pair) :
    eval X (polyExchangeNumerator x y a b) =
      exchangeNumerator (eval X x) (eval X y) a b := by
  simp [polyExchangeNumerator,exchangeNumerator,Matrix.add_apply,Matrix.smul_apply]

theorem polyExchangeNumerator_homogeneous {ι : Type*} {x y : MvPolynomial ι ℂ}
    (hx : x.IsHomogeneous 1) (hy : y.IsHomogeneous 1) (a b : Pair) :
    (polyExchangeNumerator x y a b).IsHomogeneous 2 := by
  have h (u v : ℂ) : ((C u*y-x)*(C v*x-y)).IsHomogeneous 2 :=
    (hy.C_mul u |>.sub hx).mul (hx.C_mul v |>.sub hy)
  have h' (u v : ℂ) : ((C u*y-x)*(C v*y-x)).IsHomogeneous 2 :=
    (hy.C_mul u |>.sub hx).mul (hy.C_mul v |>.sub hx)
  unfold polyExchangeNumerator
  apply IsHomogeneous.add
  · apply IsHomogeneous.add
    · simpa only [mul_comm] using (h (t^2) T).C_mul (Pzero a b)
    · simpa only [mul_comm] using (h T (t^2)).C_mul (Pone a b)
  · simpa only [mul_comm] using (h' (t^2) T).C_mul (Ptwo a b)

abbrev PolynomialTensor (N : ℕ) (ι : Type*) := (Fin N → Spin) → MvPolynomial ι ℂ

noncomputable def tensorExchange {N : ℕ} {ι : Type*} (i j : Fin N)
    (x y : MvPolynomial ι ℂ) (W : PolynomialTensor N ι) : PolynomialTensor N ι :=
  fun s => ∑ ab : Pair, polyExchangeNumerator x y (s i,s j) ab *
    W (Function.update (Function.update s i ab.1) j ab.2)

theorem tensorExchange_mul {N : ℕ} {ι : Type*} (i j : Fin N)
    (x y c : MvPolynomial ι ℂ) (W : PolynomialTensor N ι) :
    tensorExchange i j x y (fun s => c*W s) = fun s => c*tensorExchange i j x y W s := by
  funext s
  simp only [tensorExchange,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab _
  ring

theorem tensorExchange_homogeneous {N d : ℕ} {ι : Type*} (i j : Fin N)
    {x y : MvPolynomial ι ℂ} (hx : x.IsHomogeneous 1) (hy : y.IsHomogeneous 1)
    {W : PolynomialTensor N ι} (hW : ∀ s, (W s).IsHomogeneous d) (s : Fin N → Spin) :
    (tensorExchange i j x y W s).IsHomogeneous (d+2) := by
  apply IsHomogeneous.sum
  intro ab _
  simpa only [Nat.add_comm] using (polyExchangeNumerator_homogeneous hx hy (s i,s j) ab).mul (hW _)

 
noncomputable def transportCup {n : ℕ} (i : Fin (n+1))
    (ks : List (Fin (n+1))) (W : PolynomialTensor (n+2) (Fin (n+1))) :
    PolynomialTensor (n+2) (Fin (n+1)) :=
  ks.foldl (fun A k => tensorExchange (pairLeft k) (pairRight k) (C T*X i) (X k) A) W

noncomputable def rightSpectators {n : ℕ} (i : Fin (n+1)) : List (Fin (n+1)) :=
  (List.finRange (n+1)).filter (fun k => i<k)

noncomputable def initialCup {n : ℕ} (ψ : State n) (i : Fin (n+1)) :
    PolynomialTensor (n+2) (Fin (n+1)) := fun s =>
  C (cup (s (pairLeft i),s (pairRight i))) *
    rename i.succAbove (ψ (s ∘ omitPair i))

 

noncomputable def leftFusionFactors {n : ℕ} (i : Fin (n+1)) : MvPolynomial (Fin (n+1)) ℂ :=
  ∏ k ∈ Finset.univ.filter (fun k => k < i), (X k-C (t^5)*X i)*(X k-C (t^6)*X i)

noncomputable def cupPrescription {n : ℕ} (ψ : State n) (i : Fin (n+1)) :
    PolynomialTensor (n+2) (Fin (n+1)) := fun s =>
  C (1+T)*X i*leftFusionFactors i * transportCup i (rightSpectators i) (initialCup ψ i) s

 

theorem marked_variable_dvd_cupPrescription {n : ℕ} (ψ : State n) (i : Fin (n+1))
    (s : Fin (n+2) → Spin) : X i ∣ cupPrescription ψ i s := by
  refine ⟨C (1+T)*leftFusionFactors i*transportCup i (rightSpectators i) (initialCup ψ i) s,?_⟩
  unfold cupPrescription
  ring

theorem transportCup_homogeneous {n d : ℕ} (i : Fin (n+1)) (ks : List (Fin (n+1)))
    (W : PolynomialTensor (n+2) (Fin (n+1))) (hW : ∀ s, (W s).IsHomogeneous d)
    (s : Fin (n+2) → Spin) :
    (transportCup i ks W s).IsHomogeneous (d+2*ks.length) := by
  induction ks generalizing W d with
  | nil => simpa [transportCup] using hW s
  | cons k ks ih =>
    have hj := ih (tensorExchange (pairLeft k) (pairRight k) (C T*X i) (X k) W)
      (fun v => tensorExchange_homogeneous _ _ (isHomogeneous_C_mul_X T i)
        (isHomogeneous_X _ _) hW v)
    simpa [transportCup,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hj

theorem cupPrescription_homogeneous {n d : ℕ} (ψ : State n)
    (hψ : ∀ s, (ψ s).IsHomogeneous d) (i : Fin (n+1)) (s : Fin (n+2) → Spin) :
    (cupPrescription ψ i s).IsHomogeneous
      (1+2*(Finset.univ.filter (fun k : Fin (n+1) => k < i)).card + d+2*(rightSpectators i).length) := by
  have hinit (v) : (initialCup ψ i v).IsHomogeneous d := by
    exact ((hψ _).rename_isHomogeneous).C_mul _
  have hleft : (leftFusionFactors i).IsHomogeneous
      (2*(Finset.univ.filter (fun k : Fin (n+1) => k < i)).card) := by
    unfold leftFusionFactors
    rw [show 2*(Finset.univ.filter (fun k : Fin (n+1) => k < i)).card =
      ∑ k ∈ Finset.univ.filter (fun k : Fin (n+1) => k < i), (2 : ℕ) by
        simp [Nat.mul_comm]]
    apply IsHomogeneous.prod
    intro k hk
    exact ((isHomogeneous_X _ k).sub (isHomogeneous_C_mul_X _ i)).mul
      ((isHomogeneous_X _ k).sub (isHomogeneous_C_mul_X _ i))
  have h := ((isHomogeneous_C_mul_X (1+T) i).mul hleft).mul
    (transportCup_homogeneous i (rightSpectators i) (initialCup ψ i) hinit s)
  simpa only [cupPrescription,Nat.add_assoc] using h

end PolynomialVacuumAlgebra

end OAI
