import OAI.Algebra.AuslanderReiten.HomComplex.FullHomSourceDuality
import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProductLinear

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.FullTate
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R] [CharP k 2]
open CompleteComparison TateKoszul
variable (τ : FrobeniusTrace k R) (hs : ∀ a b : R, τ.trace (a*b)=τ.trace (b*a))
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)
variable (hK : TotallyAcyclicComplex (chainOfCochain K))
local notation "H" => CohomologyClass K K

structure PositiveModel (p q : H 3) where
  positive : ∀ n : ℕ, H (3*(n:ℤ)) ≃ₗ[k] BinaryKoszul.Piece k n
  outside : ∀ a : ℤ, 0 ≤ a → (∀ n : ℕ, a ≠ 3*(n:ℤ)) → Subsingleton (H a)
  right_x : ∀ (a : ℤ) (n : ℕ) (ha : a=3*(n:ℤ)) (v : H a),
    positive (n+1) (degreeEquiv (k := k) H (show a+3=3*((n+1:ℕ):ℤ) by omega)
      (fullHomProduct v p)) = BinaryKoszul.mulX k n (positive n (degreeEquiv (k := k) H ha v))
  right_y : ∀ (a : ℤ) (n : ℕ) (ha : a=3*(n:ℤ)) (v : H a),
    positive (n+1) (degreeEquiv (k := k) H (show a+3=3*((n+1:ℕ):ℤ) by omega)
      (fullHomProduct v q)) = BinaryKoszul.mulY k n (positive n (degreeEquiv (k := k) H ha v))
  left_x : ∀ (a : ℤ) (n : ℕ) (ha : a=3*(n:ℤ)) (v : H a),
    positive (n+1) (degreeEquiv (k := k) H (show 3+a=3*((n+1:ℕ):ℤ) by omega)
      (fullHomProduct p v)) = BinaryKoszul.mulX k n (positive n (degreeEquiv (k := k) H ha v))
  left_y : ∀ (a : ℤ) (n : ℕ) (ha : a=3*(n:ℤ)) (v : H a),
    positive (n+1) (degreeEquiv (k := k) H (show 3+a=3*((n+1:ℕ):ℤ) by omega)
      (fullHomProduct q v)) = BinaryKoszul.mulY k n (positive n (degreeEquiv (k := k) H ha v))

variable {K}

def negativeChart (positive : ∀ n : ℕ, H (3*(n:ℤ)) ≃ₗ[k] BinaryKoszul.Piece k n)
    (n : ℕ) : H (-1-3*(n:ℤ)) ≃ₗ[k] BinaryKoszul.DualPiece k n :=
  (τ.fullHomSourceDualityAt hs K hK (3*(n:ℤ)) (-1-3*(n:ℤ)) (by omega)).symm.trans
    (positive n).symm.dualMap

omit [CharP k 2] in
theorem negativeChart_transport_apply
    (positive : ∀ n : ℕ, H (3*(n:ℤ)) ≃ₗ[k] BinaryKoszul.Piece k n)
    (a : ℤ) (n : ℕ) (ha : a=-1-3*(n:ℤ)) (v : H a) (w : BinaryKoszul.Piece k n) :
    negativeChart τ hs hK positive n (degreeEquiv (k := k) H ha v) w =
      ((τ.fullHomSourceDualityAt hs K hK (3*(n:ℤ)) a (by omega)).symm v)
        ((positive n).symm w) := by
  subst a
  rfl

omit [CharP k 2] in
theorem duality_source_transport {a a' b : ℤ} (h : a=a')
    (hb : b=-a-1) (hb' : b=-a'-1) (v : H b) (u : H a) :
    ((τ.fullHomSourceDualityAt hs K hK a b hb).symm v) u =
      ((τ.fullHomSourceDualityAt hs K hK a' b hb').symm v) (degreeEquiv (k := k) H h u) := by
  subst a'
  rfl

theorem negativeChart_action
    (positive : ∀ n : ℕ, H (3*(n:ℤ)) ≃ₗ[k] BinaryKoszul.Piece k n)
    (p : H 3) (op : ∀ n, BinaryKoszul.Piece k n →ₗ[k] BinaryKoszul.Piece k (n+1))
    (hp : ∀ (a : ℤ) (n : ℕ) (ha : a=3*(n:ℤ)) (v : H a),
      positive (n+1) (degreeEquiv (k := k) H (show 3+a=3*((n+1:ℕ):ℤ) by omega)
        (fullHomProduct p v)) = op n (positive n (degreeEquiv (k := k) H ha v)))
    (a : ℤ) (n : ℕ) (ha : a=-1-3*((n+1:ℕ):ℤ)) (v : H a) :
    negativeChart τ hs hK positive n
      (degreeEquiv (k := k) H (show a+3=-1-3*(n:ℤ) by omega) (fullHomProduct v p)) =
      (op n).dualMap (negativeChart τ hs hK positive (n+1) (degreeEquiv (k := k) H ha v)) := by
  apply LinearMap.ext
  intro w
  rw [negativeChart_transport_apply]
  rw [τ.fullHomSourceDualityAt_product hs K hK (3*(n:ℤ)) 3 a (by omega)]
  rw [duality_source_transport τ hs hK (show 3+3*(n:ℤ)=3*((n+1:ℕ):ℤ) by omega)
    (by omega) (by omega)]
  change _ = negativeChart τ hs hK positive (n+1) (degreeEquiv (k := k) H ha v) (op n w)
  rw [negativeChart_transport_apply]
  congr 1
  apply (positive (n+1)).injective
  rw [hp _ n rfl]
  simp [degreeEquiv]

def model {p q : CohomologyClass K K 3} (P : PositiveModel (k := k) K p q) :
    TateKoszul.Model (fun a => fullHomRightMultiply (k := k) (K := K) (L := K) (M := K) (n := a) p)
      (fun a => fullHomRightMultiply (k := k) (K := K) (L := K) (M := K) (n := a) q) where
  positive := P.positive
  negative := negativeChart τ hs hK P.positive
  outside a hp hn := by
    by_cases ha : 0 ≤ a
    · exact P.outside a ha hp
    · have hb : 0 ≤ -a-1 := by omega
      have hnb : ∀ n : ℕ, -a-1 ≠ 3*(n:ℤ) := by
        intro n h
        exact hn n (by omega)
      let := P.outside (-a-1) hb hnb
      let e := τ.fullHomSourceDualityAt hs K hK (-a-1) a (by omega)
      exact ⟨fun x y => e.symm.injective (Subsingleton.elim _ _)⟩
  positive_x := P.right_x
  positive_y := P.right_y
  negative_x := negativeChart_action τ hs hK P.positive p (BinaryKoszul.mulX k) P.left_x
  negative_y := negativeChart_action τ hs hK P.positive q (BinaryKoszul.mulY k) P.left_y

end ArExplicit.FullTate

end

end OAI
