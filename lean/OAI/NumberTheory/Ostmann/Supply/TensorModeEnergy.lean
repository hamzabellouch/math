import OAI.NumberTheory.Ostmann.Supply.TensorModes

namespace OAI

noncomputable section
namespace Ostmann.Supply.TensorModes
open TensorOperators
open Finset
open scoped TensorProduct BigOperators ComplexConjugate

private theorem norm_sq_complex {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : H) : ((‖x‖^2 : ℝ) : ℂ) = inner ℂ x x := by
  apply Complex.ext
  · exact norm_sq_eq_re_inner (𝕜 := ℂ) x
  · exact (inner_self_im (𝕜 := ℂ) x).symm

theorem exactMode_inner_eq_zero (E : ℕ → FiniteHilbertSpace) (n : ℕ)
    {s t : Finset ℕ} (hs : s ⊆ range n) (ht : t ⊆ range n) (hst : s ≠ t)
    (x y : tensorSpace (fun i => augmentedSpace (E i)) n) :
    inner ℂ (exactMode E n s x) (exactMode E n t y) = 0 := by
  have hh := (exactMode_star E n s).isSelfAdjoint.isSymmetric x (exactMode E n t y)
  change inner ℂ (exactMode E n s x) (exactMode E n t y) =
    inner ℂ x (exactMode E n s (exactMode E n t y)) at hh
  rw [hh]
  change inner ℂ x ((exactMode E n s * exactMode E n t) y) = 0
  rw [exactMode_mul_eq_zero E n hs ht hst]
  simp

theorem norm_lowModes_sq (E : ℕ → FiniteHilbertSpace) (n K : ℕ)
    (x : tensorSpace (fun i => augmentedSpace (E i)) n) :
    ‖lowModes E n K x‖^2 = ∑ s ∈ retainedModes n K, ‖exactMode E n s x‖^2 := by
  have hinner : inner ℂ (lowModes E n K x) (lowModes E n K x) =
      ∑ s ∈ retainedModes n K, inner ℂ (exactMode E n s x) (exactMode E n s x) := by
    simp only [lowModes, _root_.sum_apply, sum_inner, inner_sum]
    apply sum_congr rfl
    intro s hs
    apply sum_eq_single s
    · intro t ht hts
      exact exactMode_inner_eq_zero E n (mem_powerset.mp (mem_filter.mp ht).1)
        (mem_powerset.mp (mem_filter.mp hs).1) hts x x
    · intro hnot
      exact False.elim (hnot hs)
  apply Complex.ofReal_injective
  rw [norm_sq_complex, Complex.ofReal_sum]
  simp_rw [norm_sq_complex]
  exact hinner

def augmentedPoint (E : FiniteHilbertSpace) (v : E) : augmentedSpace E :=
  WithLp.toLp 2 ((1 : ℂ), v)

def empiricalTensor {α : Type*} (A : Finset α) {E : ℕ → FiniteHilbertSpace}
    (v : α → ∀ i, E i) (n : ℕ) : tensorSpace (fun i => augmentedSpace (E i)) n :=
  (A.card : ℂ)⁻¹ • ∑ a ∈ A, pureTensor (fun i => augmentedPoint (E i) (v a i)) n

theorem exactMode_pureTensor_inner {E : ℕ → FiniteHilbertSpace} (n : ℕ)
    (s : Finset ℕ) (hs : s ⊆ range n) (v w : ∀ i, E i) :
    inner ℂ
      (exactMode E n s (pureTensor (fun i => augmentedPoint (E i) (v i)) n))
      (exactMode E n s (pureTensor (fun i => augmentedPoint (E i) (w i)) n)) =
      ∏ i ∈ s, inner ℂ (v i) (w i) := by
  simp only [exactMode, tensorOp_pureTensor, pureTensor_inner]
  have hlocal (i : ℕ) :
      inner ℂ
        ((if i ∈ s then centeredPart (E i) else scalarPart (E i)) (augmentedPoint (E i) (v i)))
        ((if i ∈ s then centeredPart (E i) else scalarPart (E i)) (augmentedPoint (E i) (w i))) =
        if i ∈ s then inner ℂ (v i) (w i) else 1 := by
    by_cases hi : i ∈ s
    · simp only [ite_eq_left hi]
      rw [centeredPart_apply, centeredPart_apply]
      change inner ℂ (0 : ℂ) 0 + inner ℂ (v i) (w i) = inner ℂ (v i) (w i)
      simp
    · simp only [ite_eq_right hi]
      rw [scalarPart_apply, scalarPart_apply]
      change inner ℂ (1 : ℂ) 1 + inner ℂ (0 : E i) 0 = 1
      simp
  simp_rw [hlocal]
  calc
    _ = ∏ i ∈ s, (if i ∈ s then inner ℂ (v i) (w i) else 1) :=
      (prod_subset hs (fun i hi hnot => ite_eq_right hnot)).symm
    _ = _ := prod_congr rfl (fun i hi => ite_eq_left hi)

theorem norm_exactMode_empirical_eq_gram {α : Type*} (A : Finset α)
    {E : ℕ → FiniteHilbertSpace} (v : α → ∀ i, E i) (n : ℕ)
    (s : Finset ℕ) (hs : s ⊆ range n) :
    ((‖exactMode E n s (empiricalTensor A v n)‖^2 : ℝ) : ℂ) =
      (A.card : ℂ)⁻¹^2 * ∑ a ∈ A, ∑ b ∈ A, ∏ i ∈ s, inner ℂ (v a i) (v b i) := by
  rw [norm_sq_complex]
  simp only [empiricalTensor, map_smul, map_sum, inner_smul_left, inner_smul_right,
    map_inv₀, map_natCast, sum_inner, inner_sum]
  simp_rw [exactMode_pureTensor_inner n s hs]
  rw [← mul_sum, sum_comm (s := A) (t := A)]
  ring

def residueCenteredFamily (p : ℕ → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ p : ℕ, Finset (ZMod p)) (i : ℕ) : FiniteHilbertSpace :=
  FiniteHilbertSpace.of (centeredSpace (S (p i)))

def residueCenteredVector (p : ℕ → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ p : ℕ, Finset (ZMod p)) (a i : ℕ) : residueCenteredFamily p S i :=
  (centeredSpace (S (p i))).orthogonalProjectionOnto (EuclideanSpace.single (a : ZMod (p i)) 1)

theorem norm_residue_exactMode_sq (A : Finset ℕ) (p : ℕ → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ p : ℕ, Finset (ZMod p)) (n : ℕ) (s : Finset ℕ) (hs : s ⊆ range n)
    (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p (s : Set ℕ)) :
    ‖exactMode (residueCenteredFamily p S) n s
      (empiricalTensor A (residueCenteredVector p S) n)‖^2 =
      centeredEnergy A S (∏ i ∈ s, p i) := by
  have hpf : (∏ i ∈ s, p i).primeFactors = s.image p := by
    have hprod : (∏ q ∈ s.image p, q) = ∏ i ∈ s, p i :=
      prod_image (f := fun q : ℕ => q) (fun i hi j hj hij => hinj hi hj hij)
    rw [← hprod]
    exact Nat.primeFactors_prod (fun q hq => by obtain ⟨i, hi, rfl⟩ := mem_image.mp hq; exact hp i hi)
  apply Complex.ofReal_injective
  rw [norm_exactMode_empirical_eq_gram A (residueCenteredVector p S) n s hs,
    centeredEnergy_eq_gram, hpf]
  congr 1
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  rw [prod_image (fun i hi j hj hij => hinj hi hj hij)]
  apply prod_congr rfl
  intro i hi
  rw [centeredInner_eq]
  rfl

theorem norm_residue_lowModes_sq (A : Finset ℕ) (p : ℕ → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ p : ℕ, Finset (ZMod p)) (n K : ℕ)
    (hp : ∀ i < n, (p i).Prime) (hinj : Set.InjOn p (range n : Set ℕ)) :
    ‖lowModes (residueCenteredFamily p S) n K
      (empiricalTensor A (residueCenteredVector p S) n)‖^2 =
      ∑ s ∈ retainedModes n K, centeredEnergy A S (∏ i ∈ s, p i) := by
  rw [norm_lowModes_sq]
  apply sum_congr rfl
  intro s hs
  have hsub := mem_powerset.mp (mem_filter.mp hs).1
  exact norm_residue_exactMode_sq A p S n s hsub
    (fun i hi => hp i (mem_range.mp (hsub hi))) (hinj.mono hsub)

end Ostmann.Supply.TensorModes

end

end OAI
