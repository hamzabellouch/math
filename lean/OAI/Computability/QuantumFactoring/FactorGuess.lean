import Mathlib
import OAI.Computability.QuantumFactoring.FactorVerifierBounds

namespace OAI

section
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open BitArithmetic BooleanNetwork Exactness

/-- The specified sorted, zero-padded n²-bit root encoding. -/
def guessWords (n : ℕ) (x : Basis (n*n)) : List ℕ :=
  List.ofFn (fun i : Fin n => (bitsValue (block x i)).toNat)

lemma guessWords_injective (n : ℕ) : Function.Injective (guessWords n) := by
  intro x y h
  have he : (fun i : Fin n => (bitsValue (block x i)).toNat)=
      (fun i : Fin n => (bitsValue (block y i)).toNat) := List.ofFn_injective h
  funext a
  obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective a
  have hi := congrFun he i
  have hb : bitsValue (block x i) = bitsValue (block y i) := BitVec.eq_of_toNat_eq hi
  have hj := congrArg (fun z : BitVec n => z.getLsbD j.val) hb
  simpa only [bitsValue_bit,block] using hj

lemma guessWords_surjective_bounded {n : ℕ} (xs : List ℕ) (hl : xs.length=n)
    (hb : ∀ a∈xs, a<2^n) : ∃ x : Basis (n*n), guessWords n x=xs := by
  let f : Fin n→ℕ := fun i => xs[i.val]'(by omega)
  let x : Basis (n*n) := fun a =>
    (BitVec.ofNat n (f (finProdFinEquiv.symm a).1)).getLsbD (finProdFinEquiv.symm a).2.val
  refine ⟨x,?_⟩
  have he : ∀ i : Fin n, (bitsValue (block x i)).toNat=f i := by
    intro i
    have hf : f i<2^n := hb _ (List.getElem_mem (by omega))
    have hg : block x i=fun j => (BitVec.ofNat n (f i)).getLsbD j.val := by
      funext j
      simp only [block,x,Equiv.symm_apply_apply]
    rw [hg,bitsValue_bits,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hf]
  simp only [guessWords,he]
  have h := List.ofFn_get xs
  subst n
  exact h

/-- Existence/uniqueness is a mathematical fact about the required output,
not a factoring oracle used in the circuit. -/
theorem unique_good_guess {N n : ℕ} (hN : 2≤N) (hb : N<2^n) :
    ∃! x : Basis (n*n), CorrectEncoding N n (guessWords n x) := by
  obtain ⟨xs,hx,hl,hb'⟩ := correctEncoding_exists hN hb
  obtain ⟨x,rfl⟩ := guessWords_surjective_bounded xs hl hb'
  refine ⟨x,hx,?_⟩
  intro y hy
  apply guessWords_injective n
  exact correctEncoding_unique hy hx

noncomputable def fairState (b : ℕ) : State b := fun _ => (Real.sqrt 2:ℂ)⁻¹^b

lemma fairState_mass (b : ℕ) (x : Basis b) :
    Complex.normSq (fairState b x)=(2:ℝ)⁻¹^b := by
  simp only [fairState,map_pow,Complex.normSq_inv,Complex.normSq_ofReal,
    Real.mul_self_sqrt (by norm_num : (0:ℝ)≤2)]

lemma fairState_normalized (b : ℕ) : ∑ x, Complex.normSq (fairState b x)=1 := by
  simp only [fairState_mass,Finset.sum_const,Finset.card_univ,Fintype.card_fun,
    Fintype.card_bool,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

/-- The actual fair-bit guess contributes exactly 2^(-n²), not an
input-dependent success probability. -/
theorem fair_guess_mass {N n : ℕ} (hN : 2≤N) (hb : N<2^n) :
    outcomeMass (fun x => CorrectEncoding N n (guessWords n x)) (fairState (n*n))=
      (2:ℝ)⁻¹^(n*n) := by
  classical
  obtain ⟨x,hx,hu⟩ := unique_good_guess hN hb
  have he : ∀ y : Basis (n*n), CorrectEncoding N n (guessWords n y) ↔ y=x := by
    intro y
    exact ⟨fun hy => hu y hy,fun h => h ▸ hx⟩
  simp only [outcomeMass,he,Finset.sum_ite_eq',Finset.mem_univ,ite_true,fairState_mass]

/-- Concrete Boolean root-verification circuit with no run-time primality or
factorization oracle. The integer input is retained separately from the guess. -/
def guessVerifier (n : ℕ) : BooleanNetwork (n+n*n) 1 :=
  factorVerifierOn (select (Fin.castAdd (n*n)))
    (fun i => select (fun j => Fin.natAdd n (finProdFinEquiv (i,j))))

lemma guessVerifier_correct {n : ℕ} (hn : 128≤n) (a : Basis n) (x : Basis (n*n)) :
    (guessVerifier n).eval (Fin.append a x) 0=true ↔
      CorrectEncoding (bitsValue a).toNat n (guessWords n x) := by
  rw [guessVerifier,factorVerifierOn_correct hn]
  have hN : (select (Fin.castAdd (n*n))).eval (Fin.append a x)=a := by
    funext i
    exact Fin.append_left a x i
  rw [hN]
  apply iff_of_eq
  congr 1
  apply congrArg List.ofFn
  funext i
  congr 2
  funext j
  exact Fin.append_right a x (finProdFinEquiv (i,j))

lemma guessVerifier_count (n : ℕ) :
    (guessVerifier n).net.count≤factorVerifierBound n 0 := by
  apply factorVerifierOn_count <;> simp

end ExactQuantumFactoring


end

end OAI
