import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.Filters

namespace OAI

/-! Two-factor optimization and Hermitian reflection rotations. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.OptimizerGauge
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
variable {L q : ℕ}

def prefixReplacement (A : ℕ → Operator L q) (k n : ℕ) (hk : k < n) :
    Operator L q →ₗ[ℂ] Operator L q where
  toFun B := orderedPrefix (Function.update A k B) n
  map_add' := prefix_update_add A k n hk
  map_smul' := prefix_update_smul A k n hk

def prefixTwoReplacement (A : ℕ → Operator L q) (k l n : ℕ)
    (hk : k < n) (hl : l < n) (hkl : k ≠ l) :
    Operator L q →ₗ[ℂ] Operator L q →ₗ[ℂ] Operator L q where
  toFun B := prefixReplacement (Function.update A k B) l n hl
  map_add' B C := by
    apply LinearMap.ext
    intro D
    change orderedPrefix (Function.update (Function.update A k (B+C)) l D) n =
      orderedPrefix (Function.update (Function.update A k B) l D) n +
        orderedPrefix (Function.update (Function.update A k C) l D) n
    simp only [Function.update_comm hkl]
    exact prefix_update_add _ k n hk B C
  map_smul' c B := by
    apply LinearMap.ext
    intro D
    change orderedPrefix (Function.update (Function.update A k (c • B)) l D) n =
      c • orderedPrefix (Function.update (Function.update A k B) l D) n
    simp only [Function.update_comm hkl]
    exact prefix_update_smul _ k n hk c B

theorem two_affine_prefix (A : ℕ → Operator L q) (k l n : ℕ)
    (hk : k<n) (hl : l<n) (hkl : k ≠ l) (B C : Operator L q) (s t c d : ℂ) :
    orderedPrefix (Function.update (Function.update A k (c • (A k + s • B)))
      l (d • (A l + t • C))) n =
      (c*d) • (orderedPrefix A n +
        s • orderedPrefix (Function.update A k B) n +
        t • orderedPrefix (Function.update A l C) n +
        (s*t) • orderedPrefix (Function.update (Function.update A k B) l C) n) := by
  let T := prefixTwoReplacement A k l n hk hl hkl
  change T (c • (A k + s • B)) (d • (A l + t • C)) = _
  have h00 : T (A k) (A l) = orderedPrefix A n := by
    simp only [T,prefixTwoReplacement,prefixReplacement,LinearMap.coe_mk,AddHom.coe_mk,
      Function.update_eq_self]
  have h01 : T (A k) C = orderedPrefix (Function.update A l C) n := by
    simp only [T,prefixTwoReplacement,prefixReplacement,LinearMap.coe_mk,AddHom.coe_mk,
      Function.update_eq_self]
  have h10 : T B (A l) = orderedPrefix (Function.update A k B) n := by
    change orderedPrefix (Function.update (Function.update A k B) l (A l)) n = _
    rw [Function.update_comm hkl,Function.update_eq_self]
  have h11 : T B C = orderedPrefix (Function.update (Function.update A k B) l C) n := rfl
  simp only [map_smul,map_add,LinearMap.smul_apply,LinearMap.add_apply,
    h00,h01,h10,h11,smul_add,smul_smul]
  module

end PolynomialPEPS.Subvolume.OptimizerGauge

namespace PolynomialPEPS.Subvolume.OptimizerGauge
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
variable {L q : ℕ}

theorem two_replacement_bound (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k l : ℕ) (_hk : k < n) (_hl : l < n) (hkl : k ≠ l)
    (V : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ))
    (W : unitary (Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ))
    (G : LocalPositiveFilter q (X k)) (hG : filterTracePower G (2/a k) = 1)
    (H : LocalPositiveFilter q (X l)) (hH : filterTracePower H (2/a l) = 1) :
    ‖asMap (L := L) (q := q) (orderedPrefix
      (Function.update (Function.update (fun j => liftLocal (X j) (F j).matrix)
        k (liftLocal (X k) ((V : Matrix _ _ ℂ)*G.matrix)))
        l (liftLocal (X l) ((W : Matrix _ _ ℂ)*H.matrix))) n) ψ‖ ≤
      ‖filteredVector (fun j : Fin n => F j.val) ψ‖ := by
  let U : (j : ℕ) → unitary (Matrix (RegionConfiguration q (X j))
      (RegionConfiguration q (X j)) ℂ) := Function.update (Function.update (fun _ => 1) k V) l W
  let P : (j : ℕ) → LocalPositiveFilter q (X j) := Function.update (Function.update F k G) l H
  have hp : ∀ j < n, filterTracePower (P j) (2/a j) = 1 := by
    intro j hj
    by_cases hjl : j=l
    · subst j
      simpa [P] using hH
    · by_cases hjk : j=k
      · subst j
        simpa [P,Function.update_of_ne hkl] using hG
      · simpa [P,Function.update_of_ne hjk,Function.update_of_ne hjl] using hF.1 ⟨j,hj⟩
  have heq : (fun j => liftLocal (X j) ((U j : Matrix _ _ ℂ)*(P j).matrix)) =
      Function.update (Function.update (fun j => liftLocal (X j) (F j).matrix) k
        (liftLocal (X k) ((V : Matrix _ _ ℂ)*G.matrix))) l
        (liftLocal (X l) ((W : Matrix _ _ ℂ)*H.matrix)) := by
    funext j
    by_cases hjl : j=l
    · subst j
      simp [U,P]
    · by_cases hjk : j=k
      · subst j
        simp [U,P,Function.update_of_ne hkl]
      · simp [U,P,Function.update_of_ne hjk,Function.update_of_ne hjl]
  simpa only [heq] using unitary_positive_family_bound hq X hX a ψ n
    (fun j : Fin n => F j.val) hF U P hp

def rightPositive {X : Finset (Vertex L)} (F : LocalPositiveFilter q X)
    (R : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)) :
    LocalPositiveFilter q X :=
  ⟨star (R : Matrix _ _ ℂ)*F.matrix*(R : Matrix _ _ ℂ),
    posSemidef_unitary_conj F.matrix F.positive R⟩

theorem rightPositive_capacity {X : Finset (Vertex L)} (F : LocalPositiveFilter q X)
    (R : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)) (p : ℝ) :
    filterTracePower (rightPositive F R) p = filterTracePower F p := by
  unfold filterTracePower NestedFilter.tracePower rightPositive
  rw [eigenvalues_unitary_conj _ F.positive]

theorem rightPositive_factorization {X : Finset (Vertex L)} (F : LocalPositiveFilter q X)
    (R : unitary (Matrix (RegionConfiguration q X) (RegionConfiguration q X) ℂ)) :
    (R : Matrix _ _ ℂ)*(rightPositive F R).matrix = F.matrix*(R : Matrix _ _ ℂ) := by
  change (R : Matrix _ _ ℂ)*(star (R : Matrix _ _ ℂ)*F.matrix*(R : Matrix _ _ ℂ)) = _
  simp only [← mul_assoc,R.property.2,one_mul]

end PolynomialPEPS.Subvolume.OptimizerGauge

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
namespace PolynomialPEPS.Subvolume.ReflectionRotation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def numerator (W : Matrix ι ι ℂ) (t : ℝ) : Matrix ι ι ℂ :=
  1 + ((t : ℂ)*Complex.I) • W

def scale (t : ℝ) : ℝ := (Real.sqrt (1+t^2))⁻¹

theorem scale_pos (t : ℝ) : 0 < scale t := by
  unfold scale
  positivity

theorem scale_sq (t : ℝ) : (scale t)^2*(1+t^2)=1 := by
  have hp : 0 < 1+t^2 := by positivity
  rw [scale, inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ (ne_of_gt hp)]

theorem numerator_star_mul (W : unitary (Matrix ι ι ℂ))
    (hW : star (W : Matrix ι ι ℂ) = (W : Matrix ι ι ℂ)) (t : ℝ) :
    star (numerator (W : Matrix ι ι ℂ) t) * numerator (W : Matrix ι ι ℂ) t =
      ((1+t^2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
  have hWW : (W : Matrix ι ι ℂ)*(W : Matrix ι ι ℂ)=1 := by
    simpa only [hW] using W.property.2
  unfold numerator
  simp only [star_add, star_one, star_smul, star_mul, RCLike.star_def,
    Complex.conj_ofReal, Complex.conj_I, hW, add_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, smul_smul, hWW, smul_add]
  have hc : ((t : ℂ)*Complex.I) * (-Complex.I * (t : ℂ)) = ((t^2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_pow]
    ring_nf
    simp [Complex.I_sq]
  rw [hc, Complex.ofReal_add, Complex.ofReal_one, add_smul, one_smul]
  module

theorem numerator_mul_star (W : unitary (Matrix ι ι ℂ))
    (hW : star (W : Matrix ι ι ℂ) = (W : Matrix ι ι ℂ)) (t : ℝ) :
    numerator (W : Matrix ι ι ℂ) t * star (numerator (W : Matrix ι ι ℂ) t) =
      ((1+t^2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) := by
  have hn : star (numerator (W : Matrix ι ι ℂ) (-t)) = numerator (W : Matrix ι ι ℂ) t := by
    simp [numerator, hW, mul_comm]
  have hn' : numerator (W : Matrix ι ι ℂ) (-t) = star (numerator (W : Matrix ι ι ℂ) t) := by
    rw [← hn, star_star]
  simpa only [hn, hn', neg_sq, star_star] using numerator_star_mul W hW (-t)

def rotation (W : unitary (Matrix ι ι ℂ))
    (hW : star (W : Matrix ι ι ℂ) = (W : Matrix ι ι ℂ)) (t : ℝ) :
    unitary (Matrix ι ι ℂ) :=
  ⟨(scale t : ℂ) • numerator (W : Matrix ι ι ℂ) t, by
    have hc : (scale t : ℂ)*(scale t : ℂ)*((1+t^2 : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← sq, scale_sq, Complex.ofReal_one]
    constructor
    · simp only [star_smul, RCLike.star_def, Complex.conj_ofReal,
        smul_mul_assoc, mul_smul_comm, smul_smul, numerator_star_mul W hW,
        ← mul_assoc, hc, one_smul]
    · simp only [star_smul, RCLike.star_def, Complex.conj_ofReal,
        smul_mul_assoc, mul_smul_comm, smul_smul, numerator_mul_star W hW,
        ← mul_assoc, hc, one_smul]⟩

end PolynomialPEPS.Subvolume.ReflectionRotation

end

end OAI
