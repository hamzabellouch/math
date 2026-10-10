import OAI.NumberTheory.Ostmann.Supply.TensorModeBudget

namespace OAI

noncomputable section
namespace Ostmann.Supply.TensorModes
open TensorOperators
open Finset
open scoped BigOperators

def reflectedSupport (S : ∀ p : ℕ, Finset (ZMod p)) (p : ℕ) : Finset (ZMod p) :=
  (S p).image Neg.neg

@[simp] theorem mem_reflectedSupport (S : ∀ p : ℕ, Finset (ZMod p))
    (p : ℕ) (x : ZMod p) : x ∈ reflectedSupport S p ↔ -x ∈ S p := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
    simpa only [neg_neg] using hy
  · intro hx
    exact mem_image.mpr ⟨-x, hx, neg_neg x⟩

@[simp] theorem card_reflectedSupport (S : ∀ p : ℕ, Finset (ZMod p)) (p : ℕ) :
    (reflectedSupport S p).card = (S p).card := card_image_of_injective _ neg_injective

@[simp] theorem supportRatio_reflectedSupport (S : ∀ p : ℕ, Finset (ZMod p)) (p : ℕ) :
    supportRatio (reflectedSupport S) p = supportRatio S p := by
  simp only [supportRatio, card_reflectedSupport]

theorem centeredProjection_reflection_gram (S : ∀ p : ℕ, Finset (ZMod p))
    (p : ℕ) [NeZero p] (x y : ZMod p) (hx : -x ∈ S p) (hy : -y ∈ S p) :
    inner ℂ (centeredProjection (S p) (EuclideanSpace.single (-x) (1 : ℂ)))
      (centeredProjection (S p) (EuclideanSpace.single (-y) (1 : ℂ))) =
    inner ℂ (centeredProjection (reflectedSupport S p) (EuclideanSpace.single x (1 : ℂ)))
      (centeredProjection (reflectedSupport S p) (EuclideanSpace.single y (1 : ℂ))) := by
  rw [centeredProjection_gram (S p) _ _ hx hy,
    centeredProjection_gram (reflectedSupport S p) _ _
      ((mem_reflectedSupport S p x).mpr hx) ((mem_reflectedSupport S p y).mpr hy)]
  simp only [neg_inj, card_reflectedSupport]

def negResidueCenteredVector (p : ℕ → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ p : ℕ, Finset (ZMod p)) (a i : ℕ) : residueCenteredFamily p S i :=
  (centeredSpace (S (p i))).orthogonalProjectionOnto
    (EuclideanSpace.single (-(a : ZMod (p i))) 1)

theorem norm_negResidue_exactMode_sq (A : Finset ℕ) (p : ℕ → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ p : ℕ, Finset (ZMod p)) (n : ℕ) (s : Finset ℕ) (hs : s ⊆ range n)
    (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p (s : Set ℕ))
    (hS : ∀ a ∈ A, ∀ i ∈ s, -(a : ZMod (p i)) ∈ S (p i)) :
    ‖exactMode (residueCenteredFamily p S) n s
      (empiricalTensor A (negResidueCenteredVector p S) n)‖^2 =
      centeredEnergy A (reflectedSupport S) (∏ i ∈ s, p i) := by
  have hpf : (∏ i ∈ s, p i).primeFactors = s.image p := by
    have hprod : (∏ q ∈ s.image p, q) = ∏ i ∈ s, p i :=
      prod_image (f := fun q : ℕ => q) (fun i hi j hj hij => hinj hi hj hij)
    rw [← hprod]
    exact Nat.primeFactors_prod (fun q hq => by obtain ⟨i, hi, rfl⟩ := mem_image.mp hq; exact hp i hi)
  apply Complex.ofReal_injective
  rw [norm_exactMode_empirical_eq_gram A (negResidueCenteredVector p S) n s hs,
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
  change inner ℂ
      (centeredProjection (S (p i)) (EuclideanSpace.single (-(a : ZMod (p i))) 1))
      (centeredProjection (S (p i)) (EuclideanSpace.single (-(b : ZMod (p i))) 1)) = _
  exact centeredProjection_reflection_gram S (p i) _ _ (hS a ha i hi) (hS b hb i hi)

theorem norm_negResidue_lowModes_sq (A : Finset ℕ) (p : ℕ → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ p : ℕ, Finset (ZMod p)) (n K : ℕ)
    (hp : ∀ i < n, (p i).Prime) (hinj : Set.InjOn p (range n : Set ℕ))
    (hS : ∀ a ∈ A, ∀ i < n, -(a : ZMod (p i)) ∈ S (p i)) :
    ‖lowModes (residueCenteredFamily p S) n K
      (empiricalTensor A (negResidueCenteredVector p S) n)‖^2 =
      ∑ t ∈ retainedProducts p n K, centeredEnergy A (reflectedSupport S) t := by
  rw [norm_lowModes_sq]
  have he : (∑ s ∈ retainedModes n K,
      ‖exactMode (residueCenteredFamily p S) n s
        (empiricalTensor A (negResidueCenteredVector p S) n)‖^2) =
      ∑ s ∈ retainedModes n K, centeredEnergy A (reflectedSupport S) (∏ i ∈ s, p i) := by
    apply sum_congr rfl
    intro s hs
    have hsub := mem_powerset.mp (mem_filter.mp hs).1
    exact norm_negResidue_exactMode_sq A p S n s hsub
      (fun i hi => hp i (mem_range.mp (hsub hi))) (hinj.mono hsub)
      (fun a ha i hi => hS a ha i (mem_range.mp (hsub hi)))
  rw [he]
  symm
  exact sum_image (fun s hs t ht h => indexPrimeProduct_injOn p n hp hinj
    (mem_filter.mp hs).1 (mem_filter.mp ht).1 h)

theorem norm_negResidue_lowModes_sq_le_sum (A : Finset ℕ) (p : ℕ → ℕ) [∀ i, NeZero (p i)]
    (S : ∀ p : ℕ, Finset (ZMod p)) (n K : ℕ)
    (hp : ∀ i < n, (p i).Prime) (hinj : Set.InjOn p (range n : Set ℕ))
    (hS : ∀ a ∈ A, ∀ i < n, -(a : ZMod (p i)) ∈ S (p i))
    (T : Finset ℕ) (hT : retainedProducts p n K ⊆ T) :
    ‖lowModes (residueCenteredFamily p S) n K
      (empiricalTensor A (negResidueCenteredVector p S) n)‖^2 ≤
      ∑ t ∈ T, centeredEnergy A (reflectedSupport S) t := by
  rw [norm_negResidue_lowModes_sq A p S n K hp hinj hS]
  exact sum_le_sum_of_subset_of_nonneg hT (fun t ht hnot => centeredEnergy_nonneg A _ t)

end Ostmann.Supply.TensorModes

end

end OAI
