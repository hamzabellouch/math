import OAI.NumberTheory.Ostmann.QuadraticCenter.WalshMoments

namespace OAI

namespace Ostmann.QuadraticCenter
open scoped BigOperators

def flipSign {ι : Type*} [DecidableEq ι] (i : ι) (ε : ι → Bool) : ι → Bool :=
  Function.update ε i (!(ε i))

theorem flipSign_involutive {ι : Type*} [DecidableEq ι] (i : ι) :
    Function.Involutive (flipSign i) := by
  intro ε
  funext j
  by_cases hj : j = i
  · subst j
    simp [flipSign]
  · simp [flipSign, hj]

def flipSignEquiv {ι : Type*} [DecidableEq ι] (i : ι) : (ι → Bool) ≃ (ι → Bool) :=
  ⟨flipSign i, flipSign i, flipSign_involutive i, flipSign_involutive i⟩

theorem signMean_flip {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (f : (ι → Bool) → ℝ) :
    signMean (fun ε => f (flipSign i ε)) = signMean f := by
  rw [signMean, signMean]
  congr 1
  exact (flipSignEquiv i).sum_comp f

@[simp] theorem sign_flipSign {ι : Type*} [DecidableEq ι] (i : ι) (ε : ι → Bool) :
    sign (flipSign i ε i) = -sign (ε i) := by
  cases he : ε i <;> simp [flipSign, he]

@[simp] theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by cases b <;> norm_num [sign]

theorem walshCharacter_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (ε : ι → Bool) :
    walshCharacter s ε = ∏ i ∈ s, sign (ε i) := by
  simp [walshCharacter, signMonomial, Finset.prod_ite_mem]

@[simp] theorem walshCharacter_empty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → Bool) : walshCharacter ∅ ε = 1 := by
  simp [walshCharacter_eq_prod]

theorem walshCharacter_insert {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i : ι} {s : Finset ι} (hi : i ∉ s) (ε : ι → Bool) :
    walshCharacter (insert i s) ε = sign (ε i) * walshCharacter s ε := by
  simp only [walshCharacter_eq_prod, Finset.prod_insert hi]

theorem walshCharacter_flip_of_notMem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i : ι} {s : Finset ι} (hi : i ∉ s) (ε : ι → Bool) :
    walshCharacter s (flipSign i ε) = walshCharacter s ε := by
  simp only [walshCharacter_eq_prod]
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by intro he; subst j; exact hi hj
  simp [flipSign, hji]

noncomputable def restrictedWalshPolynomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (c : Finset ι → ℝ) (ε : ι → Bool) : ℝ :=
  ∑ s ∈ I.powerset, c s * walshCharacter s ε

noncomputable def restrictedWalshEnergy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (c : Finset ι → ℝ) (w : ℝ) : ℝ :=
  ∑ s ∈ I.powerset, w ^ s.card * c s ^ 2

theorem restrictedWalshPolynomial_flip {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i : ι} {I : Finset ι} (hi : i ∉ I) (c : Finset ι → ℝ) (ε : ι → Bool) :
    restrictedWalshPolynomial I c (flipSign i ε) = restrictedWalshPolynomial I c ε := by
  apply Finset.sum_congr rfl
  intro s hs
  rw [walshCharacter_flip_of_notMem (Finset.notMem_of_mem_powerset_of_notMem hs hi)]

theorem restrictedWalshPolynomial_insert {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i : ι} {I : Finset ι} (hi : i ∉ I) (c : Finset ι → ℝ) (ε : ι → Bool) :
    restrictedWalshPolynomial (insert i I) c ε =
      restrictedWalshPolynomial I c ε + sign (ε i) *
        restrictedWalshPolynomial I (fun s => c (insert i s)) ε := by
  unfold restrictedWalshPolynomial
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [walshCharacter_insert (Finset.notMem_of_mem_powerset_of_notMem hs hi)]
  ring

theorem restrictedWalshEnergy_insert {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i : ι} {I : Finset ι} (hi : i ∉ I) (c : Finset ι → ℝ) (w : ℝ) :
    restrictedWalshEnergy (insert i I) c w =
      restrictedWalshEnergy I c w + w * restrictedWalshEnergy I (fun s => c (insert i s)) w := by
  unfold restrictedWalshEnergy
  rw [Finset.sum_powerset_insert hi, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.card_insert_of_notMem (Finset.notMem_of_mem_powerset_of_notMem hs hi), pow_succ]
  ring

theorem restrictedWalshEnergy_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (I : Finset ι) (c : Finset ι → ℝ) {w : ℝ} (hw : 0 ≤ w) :
    0 ≤ restrictedWalshEnergy I c w :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (pow_nonneg hw _) (sq_nonneg _))

end Ostmann.QuadraticCenter

end OAI
