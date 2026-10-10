import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.Transition

namespace OAI

/-! Singular-safe local crossing and modular substitution identities. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open scoped BigOperators Matrix.Norms.L2Operator
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.CrossingIdentity
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.OptimizerGauge PolynomialPEPS.Subvolume.ActualTransition
open PolynomialPEPS.Subvolume.TraceStripping PolynomialPEPS.Subvolume.SpectralCurve
open PolynomialPEPS.Subvolume.KernelPerturbation
variable {L q : ℕ}

def inverseOnSupport {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (e : ι → ℝ) : Matrix ι ι ℂ :=
  spectralHom U (fun i => ((e i)⁻¹:ℂ))

theorem inverse_mul_add_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : unitary (Matrix ι ι ℂ)) (e : ι → ℝ) :
    inverseOnSupport U e * spectralHom U (fun i => (e i:ℂ)) + kernel U e = 1 := by
  unfold inverseOnSupport kernel
  rw [← map_mul,← map_add,← map_one (spectralHom U)]
  apply congrArg (spectralHom U)
  ext i
  by_cases hi : e i = 0
  · simp [hi]
  · simp [hi,Complex.ofReal_ne_zero.mpr hi]

theorem commute_prefix (A : ℕ → Operator L q) (H : Operator L q) (k : ℕ)
    (hc : ∀ j, j<k → Commute H (A j)) : Commute H (orderedPrefix A k) := by
  induction k with
  | zero => simpa only [orderedPrefix_zero] using Commute.one_right H
  | succ k ih =>
    rw [orderedPrefix_succ]
    exact (hc k (by omega)).mul_right (ih (fun j hj => hc j (by omega)))

def residual (A : ℕ → Operator L q) (H Q : Operator L q) (k n : ℕ) : Operator L q :=
  orderedPrefix (fun j => A (k+1+j)) (n-(k+1)) * A k * H * Q * orderedPrefix A k

theorem inserted_add_residual (A : ℕ → Operator L q) (H D Q : Operator L q)
    (k n : ℕ) (hk : k<n) (hDQ : D*A k + Q = 1)
    (hc : Commute H (orderedPrefix A k)) :
    insertedProduct A (A k*H*D) (k+1) n + residual A H Q k n =
      orderedPrefix A n * H := by
  have hsplit : orderedPrefix A n =
      orderedPrefix (fun j => A (k+1+j)) (n-(k+1)) * A k * orderedPrefix A k := by
    simpa only [Function.update_eq_self] using orderedPrefix_replace_split A k n hk (A k)
  unfold insertedProduct residual
  rw [orderedPrefix_succ]
  calc
    _ = orderedPrefix (fun j => A (k+1+j)) (n-(k+1)) * A k * H *
        (D*A k+Q) * orderedPrefix A k := by noncomm_ring
    _ = orderedPrefix A n * H := by
      rw [hDQ,mul_one,hsplit]
      simpa only [mul_assoc] using congrArg
        (fun M => orderedPrefix (fun j => A (k+1+j)) (n-(k+1)) * A k * M) hc.eq

theorem adjacent_replacement (A : ℕ → Operator L q) (H Q : Operator L q)
    (k n : ℕ) (hk : k+1<n) :
    orderedPrefix (Function.update (Function.update A k Q) (k+1) (A (k+1)*(A k*H))) n =
      residual A H Q k n := by
  rw [orderedPrefix_replace_split _ (k+1) n hk,orderedPrefix_succ,
    Function.update_self,prefix_update_outside A k k Q le_rfl]
  have hout : (fun j => Function.update A k Q (k+1+1+j)) = fun j => A (k+1+1+j) := by
    funext j
    rw [Function.update_of_ne (by omega)]
  rw [hout]
  unfold residual
  rw [show n-(k+1) = (n-(k+1+1))+1 by omega,orderedPrefix_shift_head]
  simp only [mul_assoc]

end PolynomialPEPS.Subvolume.CrossingIdentity

namespace PolynomialPEPS.Subvolume.CrossingIdentity
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.OptimizerGauge PolynomialPEPS.Subvolume.ActualTransition
open PolynomialPEPS.Subvolume.TraceStripping PolynomialPEPS.Subvolume.SpectralCurve
open PolynomialPEPS.Subvolume.KernelPerturbation
variable {L q : ℕ}

theorem optimizer_residual_zero (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k : ℕ) (hk : k < n) (hp : 2 < 2/a k)
    (U : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ))
    (e : RegionConfiguration q (X k) → ℝ) (he : ∀ i, 0 ≤ e i)
    (hrep : (F k).matrix = spectralHom U (fun i => (e i : ℂ)))
    (hs : ∑ i, (e i)^(2/a k) = 1)
    (H : Operator L q) (hH : ∀ j, k<j → j<n → SupportedOn H (X j)) :
    let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
    let Q : Operator L q := liftLocal (X k) (kernel U e)
    let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
    inner ℂ v (asMap (L := L) (q := q) (residual A H Q k n) ψ) = 0 := by
  dsimp only
  let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
  let Q : Operator L q := liftLocal (X k) (kernel U e)
  let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
  rcases lt_or_eq_of_le (show k+1≤n by omega) with hkn|hkn
  · obtain ⟨K,hK⟩ := hH (k+1) (by omega) hkn
    let C := liftBetween (hX (show k≤k+1 by omega)) (F k).matrix * K
    have hC : liftLocal (X (k+1)) C = A k*H := by
      rw [liftLocal_mul,liftLocal_liftBetween,← hK]
    have hm := mixed_kernel_moment_zero hq X hX a ψ n F hF k (k+1) hk hkn
      (by omega) hp U e he hrep hs C
    dsimp only at hm
    change inner ℂ v (asMap (L := L) (q := q)
      (orderedPrefix (Function.update (Function.update A k Q) (k+1)
        (liftLocal (X (k+1)) ((F (k+1)).matrix*C))) n) ψ) = 0 at hm
    rw [liftLocal_mul,hC,adjacent_replacement A H Q k n hkn] at hm
    exact hm
  · subst n
    have hz := ActualKernel.kernel_output_zero hq X hX a ψ (k+1) F hF k hk hp U e he hrep hs
    rw [orderedPrefix_succ,Function.update_self,prefix_update_outside _ k k _ le_rfl] at hz
    change asMap (L := L) (q := q) (Q*orderedPrefix A k) ψ = 0 at hz
    have hr : residual A H Q k (k+1) = (A k*H)*(Q*orderedPrefix A k) := by
      simp only [residual,Nat.sub_self,orderedPrefix_zero,one_mul,mul_assoc]
    change inner ℂ v (asMap (L := L) (q := q) (residual A H Q k (k+1)) ψ) = 0
    rw [hr]
    change inner ℂ v (Matrix.toEuclideanCLM (𝕜 := ℂ)
      ((A k*H)*(Q*orderedPrefix A k)) ψ) = 0
    rw [map_mul]
    change inner ℂ v (asMap (L := L) (q := q) (A k*H)
      (asMap (L := L) (q := q) (Q*orderedPrefix A k) ψ)) = 0
    rw [hz,map_zero,inner_zero_right]

theorem optimizer_modular_substitution (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k : ℕ) (hk : k < n) (hp : 2 < 2/a k)
    (U : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ))
    (e : RegionConfiguration q (X k) → ℝ) (he : ∀ i, 0 ≤ e i)
    (hrep : (F k).matrix = spectralHom U (fun i => (e i : ℂ)))
    (hs : ∑ i, (e i)^(2/a k) = 1)
    (H : Operator L q)
    (hH : ∀ j, k<j → j<n → SupportedOn H (X j))
    (hc : ∀ j, j<k → Commute H (liftLocal (X j) (F j).matrix)) :
    let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
    let D : Operator L q := liftLocal (X k) (inverseOnSupport U e)
    let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
    inner ℂ v (asMap (L := L) (q := q) (orderedPrefix A n*H) ψ) =
      inner ℂ v (asMap (L := L) (q := q) (A k*H*D) v) := by
  dsimp only
  let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
  let D : Operator L q := liftLocal (X k) (inverseOnSupport U e)
  let Q : Operator L q := liftLocal (X k) (kernel U e)
  let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
  have hDQ : D*A k+Q=1 := by
    change liftLocal (X k) (inverseOnSupport U e) * liftLocal (X k) (F k).matrix +
      liftLocal (X k) (kernel U e) = 1
    rw [← liftLocal_mul,← liftLocal_add,hrep,inverse_mul_add_kernel,liftLocal_one]
  have hr := optimizer_residual_zero hq X hX a ψ n F hF k hk hp U e he hrep hs H hH
  have hm : ∀ j, k+1≤j → j<n → SupportedOn (A k*H*D) (X j) := by
    intro j hkj hjn
    have hf : SupportedOn (A k) (X j) := SupportedOn.mono (hX (by omega)) ⟨(F k).matrix,rfl⟩
    have hd : SupportedOn D (X j) := SupportedOn.mono (hX (by omega)) ⟨inverseOnSupport U e,rfl⟩
    exact (hf.mul (hH j (by omega) hjn)).mul hd
  have ht := optimizer_strip_outer hq X hX a ψ n F hF (k+1) (by omega) (A k*H*D) hm
  have halg := inserted_add_residual A H D Q k n hk hDQ (commute_prefix A H k hc)
  have hvec : asMap (L := L) (q := q) (orderedPrefix A n*H) ψ =
      asMap (L := L) (q := q) (insertedProduct A (A k*H*D) (k+1) n) ψ +
        asMap (L := L) (q := q) (residual A H Q k n) ψ := by
    rw [← halg]
    change Matrix.toEuclideanCLM (𝕜 := ℂ) (_+_) ψ = _
    rw [map_add]
    rfl
  change inner ℂ v (asMap (L := L) (q := q) (orderedPrefix A n*H) ψ) = _
  rw [hvec,inner_add_right,hr,add_zero]
  exact ht.symm

end PolynomialPEPS.Subvolume.CrossingIdentity

end

end OAI
