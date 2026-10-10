import OAI.Algebra.AuslanderReiten.Modules.CoinducedBimodule
import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorProjective
import Mathlib.Algebra.Module.Opposite

namespace OAI

noncomputable section
namespace ArExplicit
namespace DualTensor

variable {k R V W : Type*} [CommRing k] [Ring R] [Algebra k R]
  [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]
  [AddCommGroup W] [Module k W] [Module R W] [IsScalarTower k R W]

def formula : Coinduced k R →ₗ[k] V →ₗ[k] Module.Dual k (V →ₗ[R] R) where
  toFun ℓ :=
    { toFun v :=
        { toFun f := ℓ.functional (f v)
          map_add' f g := by simp
          map_smul' a f := by simp }
      map_add' v w := by ext f; simp
      map_smul' a v := by ext f; simp [LinearMap.map_smul_of_tower] }
  map_add' ℓ μ := by ext v f; rfl
  map_smul' a ℓ := by ext v f; rfl

def evaluation : BalancedTensor k R (Coinduced k R) V →ₗ[k] Module.Dual k (V →ₗ[R] R) :=
  BalancedTensor.lift formula (by
    intro ℓ r v
    ext f
    change ℓ.functional (r * f v) = ℓ.functional (f (r • v))
    rw [f.map_smul, smul_eq_mul])

@[simp] theorem evaluation_tmul (ℓ : Coinduced k R) (v : V) (f : V →ₗ[R] R) :
    evaluation (BalancedTensor.tmul ℓ v) f = ℓ.functional (f v) := rfl

variable {n : ℕ}

def coefficientRight (s : V →ₗ[R] (Fin n → R)) (i : Fin n) : R →ₗ[k] (V →ₗ[R] R) where
  toFun r :=
    { toFun v := s v i * r
      map_add' v w := by simp [add_mul]
      map_smul' a v := by simp [mul_assoc] }
  map_add' r t := by ext v; simp [mul_add]
  map_smul' a r := by ext v; simp

omit [Module k V] [IsScalarTower k R V] in
@[simp] theorem coefficientRight_apply (s : V →ₗ[R] (Fin n → R)) (i : Fin n) (r : R) (v : V) :
    coefficientRight (k := k) s i r v = s v i * r := rfl

def inverseUsing (s : V →ₗ[R] (Fin n → R)) (p : (Fin n → R) →ₗ[R] V)
    (φ : Module.Dual k (V →ₗ[R] R)) : BalancedTensor k R (Coinduced k R) V :=
  ∑ i, BalancedTensor.tmul (Coinduced.mk (φ.comp (coefficientRight s i))) (p (Pi.single i 1))

theorem sum_coefficients (s : V →ₗ[R] (Fin n → R)) (p : (Fin n → R) →ₗ[R] V)
    (h : p.comp s = LinearMap.id) (v : V) :
    (∑ i, s v i • p (Pi.single i 1)) = v := by
  calc
    _ = ∑ i, p (Pi.single i (s v i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← p.map_smul]
      congr 1
      ext j
      by_cases hij : j = i
      · subst j; simp
      · simp [hij]
    _ = p (s v) := by rw [← map_sum, Finset.univ_sum_single]
    _ = v := LinearMap.congr_fun h v

omit [Module k V] [IsScalarTower k R V] in
theorem sum_coefficientRight (s : V →ₗ[R] (Fin n → R)) (p : (Fin n → R) →ₗ[R] V)
    (h : p.comp s = LinearMap.id) (f : V →ₗ[R] R) :
    (∑ i, coefficientRight (k := k) s i (f (p (Pi.single i 1)))) = f := by
  apply LinearMap.ext
  intro v
  simp only [LinearMap.sum_apply, coefficientRight_apply]
  simpa only [map_sum, map_smul, smul_eq_mul] using congrArg f (sum_coefficients s p h v)

theorem evaluation_inverseUsing (s : V →ₗ[R] (Fin n → R)) (p : (Fin n → R) →ₗ[R] V)
    (h : p.comp s = LinearMap.id) (φ : Module.Dual k (V →ₗ[R] R)) :
    evaluation (inverseUsing s p φ) = φ := by
  ext f
  change evaluation (∑ i, BalancedTensor.tmul
    (Coinduced.mk (φ.comp (coefficientRight s i))) (p (Pi.single i 1))) f = φ f
  simp only [map_sum, LinearMap.sum_apply, evaluation_tmul, LinearMap.comp_apply]
  rw [← map_sum, sum_coefficientRight s p h]

theorem inverseUsing_evaluation (s : V →ₗ[R] (Fin n → R)) (p : (Fin n → R) →ₗ[R] V)
    (h : p.comp s = LinearMap.id) (z : BalancedTensor k R (Coinduced k R) V) :
    inverseUsing s p (evaluation z) = z := by
  induction z using BalancedTensor.induction_on with
  | zero =>
    simp only [inverseUsing, map_zero, LinearMap.zero_comp]
    apply Finset.sum_eq_zero
    intro i hi
    exact BalancedTensor.zero_tmul _
  | add x y hx hy =>
    change (∑ i, BalancedTensor.tmul
      (Coinduced.mk ((evaluation (x + y)).comp (coefficientRight s i))) (p (Pi.single i 1))) = x + y
    have hadd (i : Fin n) : Coinduced.mk ((evaluation (x + y)).comp (coefficientRight s i)) =
        Coinduced.mk ((evaluation x).comp (coefficientRight s i)) +
        Coinduced.mk ((evaluation y).comp (coefficientRight s i)) := by
      ext r
      simp
    simp_rw [hadd, BalancedTensor.add_tmul, Finset.sum_add_distrib]
    exact congrArg₂ (· + ·) hx hy
  | tmul ℓ v =>
    change (∑ i, BalancedTensor.tmul
      (Coinduced.mk ((evaluation (BalancedTensor.tmul ℓ v)).comp (coefficientRight s i)))
        (p (Pi.single i 1))) = BalancedTensor.tmul ℓ v
    have hc (i : Fin n) :
        Coinduced.mk ((evaluation (BalancedTensor.tmul ℓ v)).comp (coefficientRight s i)) =
          MulOpposite.op (s v i) • ℓ := by
      ext r
      rfl
    simp_rw [hc, BalancedTensor.balance]
    change (∑ i, (BalancedTensor.mk (k := k) (R := R) ℓ) (s v i • p (Pi.single i 1))) =
      (BalancedTensor.mk (k := k) (R := R) ℓ) v
    rw [← map_sum, sum_coefficients s p h]

theorem evaluation_bijective [Module.Finite R V] [Module.Projective R V] :
    Function.Bijective (evaluation (k := k) (R := R) (V := V)) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R V
  obtain ⟨s, hs⟩ := Module.projective_lifting_property p (LinearMap.id : V →ₗ[R] V) hp
  exact ⟨Function.LeftInverse.injective (inverseUsing_evaluation s p hs),
    Function.RightInverse.surjective (evaluation_inverseUsing s p hs)⟩

def evaluationEquiv [Module.Finite R V] [Module.Projective R V] :
    BalancedTensor k R (Coinduced k R) V ≃ₗ[k] Module.Dual k (V →ₗ[R] R) :=
  LinearEquiv.ofBijective evaluation evaluation_bijective

theorem evaluation_natural (a : V →ₗ[R] W)
    (z : BalancedTensor k R (Coinduced k R) V) (f : W →ₗ[R] R) :
    evaluation (BalancedTensor.mapRight (S := k) a z) f = evaluation z (f.comp a) := by
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | tmul ℓ v => rfl
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

theorem evaluation_left (r : R)
    (z : BalancedTensor k R (Coinduced k R) V) (f : V →ₗ[R] R) :
    evaluation (r • z) f = evaluation z (MulOpposite.op r • f) := by
  induction z using BalancedTensor.induction_on with
  | zero => simp
  | tmul ℓ v => rfl
  | add x y hx hy => simp only [smul_add, map_add, LinearMap.add_apply, hx, hy]

end DualTensor
end ArExplicit

end

end OAI
