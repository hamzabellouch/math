import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.MixedKernel
import OAI.MathematicalPhysics.PEPSSubvolume.UnitaryVariation
import OAI.MathematicalPhysics.PEPSSubvolume.TraceFunctionals

namespace OAI

/-! Local transition functionals and descending trace stripping. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open scoped Topology
open Filter
open scoped MatrixOrder
open PolynomialPEPS.PinnedEntropy

namespace PolynomialPEPS.Subvolume.ActualTransition
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.OptimizerGauge PolynomialPEPS.Subvolume.ActualKernel
open PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.KernelPerturbation
variable {L q : ℕ}

def replacementOutput (A : ℕ → Operator L q) (S : Finset (Vertex L))
    (ψ : State L q) (k n : ℕ) (hk : k<n) :
    Matrix (RegionConfiguration q S) (RegionConfiguration q S) ℂ →ₗ[ℂ] State L q where
  toFun H := asMap (L := L) (q := q)
    (orderedPrefix (Function.update A k (liftLocal S H)) n) ψ
  map_add' H K := by
    rw [liftLocal_add,prefix_update_add A k n hk]
    change Matrix.toEuclideanCLM (𝕜 := ℂ) (_+_) ψ = _
    simp only [map_add,add_apply]
    rfl
  map_smul' c H := by
    rw [liftLocal_smul,prefix_update_smul A k n hk]
    change Matrix.toEuclideanCLM (𝕜 := ℂ) (c • _) ψ = _
    simp only [map_smul,smul_apply]
    rfl

theorem optimizer_moment_commute (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k : ℕ) (hk : k < n)
    (H : Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ) :
    let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
    let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
    inner ℂ v (replacementOutput A (X k) ψ k n hk (H*(F k).matrix)) =
      inner ℂ v (replacementOutput A (X k) ψ k n hk ((F k).matrix*H)) := by
  dsimp only
  let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
  let T := replacementOutput A (X k) ψ k n hk
  let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
  have ht : T (F k).matrix = v := by
    change asMap (L := L) (q := q) (orderedPrefix (Function.update A k (A k)) n) ψ = v
    rw [Function.update_eq_self]
  have hfv : filteredVector (fun j : Fin n => F j.val) ψ = v := by
    unfold filteredVector
    rw [PhysicalCurve.orderedFilterProduct_eq_prefix]
  have hleft (V : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ)) :
      ‖T ((V : Matrix _ _ ℂ)*(F k).matrix)‖ ≤ ‖T (F k).matrix‖ := by
    rw [ht,← hfv]
    exact one_replacement_bound hq X hX a ψ n F hF k hk V (F k) (hF.1 ⟨k,hk⟩)
  have hright (V : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ)) :
      ‖T ((F k).matrix*(V : Matrix _ _ ℂ))‖ ≤ ‖T (F k).matrix‖ := by
    have hv := one_replacement_bound hq X hX a ψ n F hF k hk V (rightPositive (F k) V)
      (by rw [rightPositive_capacity]; exact hF.1 ⟨k,hk⟩)
    rw [rightPositive_factorization] at hv
    rw [ht,← hfv]
    exact hv
  let l : Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ →ₗ[ℂ] ℂ :=
    (innerSL ℂ (T (F k).matrix)).toLinearMap.comp T
  have hm := HermitianFunctional.moment_commute l (F k).matrix (F k).positive
    (fun K hK => UnitaryStationarity.left_moment_real T (F k).matrix hleft K hK)
    (fun K hK => UnitaryStationarity.right_moment_real T (F k).matrix hright K hK) H
  change inner ℂ (T (F k).matrix) (T (H*(F k).matrix)) =
    inner ℂ (T (F k).matrix) (T ((F k).matrix*H)) at hm
  simpa only [ht] using hm

theorem mixed_kernel_moment_zero (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k l : ℕ) (hk : k < n) (hl : l < n) (hkl : k ≠ l) (hp : 2 < 2/a k)
    (U : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ))
    (e : RegionConfiguration q (X k) → ℝ) (he : ∀ i, 0 ≤ e i)
    (hrep : (F k).matrix = spectralHom U (fun i => (e i : ℂ)))
    (hs : ∑ i, (e i)^(2/a k) = 1)
    (H : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ) :
    let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
    let B : Operator L q := liftLocal (X k) (kernel U e)
    inner ℂ (asMap (L := L) (q := q) (orderedPrefix A n) ψ)
      (replacementOutput (Function.update A k B) (X l) ψ l n hl ((F l).matrix*H)) = 0 := by
  dsimp only
  let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
  let B : Operator L q := liftLocal (X k) (kernel U e)
  let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
  let T := replacementOutput (Function.update A k B) (X l) ψ l n hl
  let f : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ →ₗ[ℂ] ℂ :=
    ((innerSL ℂ v).toLinearMap.comp T).comp (LinearMap.mulLeft ℂ (F l).matrix)
  have hf (W : unitary (Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ))
      (hW : star (W : Matrix (RegionConfiguration q (X l)) (RegionConfiguration q (X l)) ℂ)=W) :
      f W = 0 :=
    mixed_transition_zero hq X hX a ψ n F hF k l hk hl hkl hp U e he hrep hs W hW
  exact ReflectionSpan.zero_of_reflection_tests f hf H

end PolynomialPEPS.Subvolume.ActualTransition

namespace PolynomialPEPS.Subvolume.TraceStripping
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.OptimizerGauge PolynomialPEPS.Subvolume.ActualTransition
variable {L q : ℕ}

theorem orderedPrefix_split (A : ℕ → Operator L q) (k t : ℕ) :
    orderedPrefix A (k+t) =
      orderedPrefix (fun j => A (k+j)) t * orderedPrefix A k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ,orderedPrefix_succ,orderedPrefix_succ,ih,mul_assoc]

theorem orderedPrefix_shift_head (A : ℕ → Operator L q) (k t : ℕ) :
    orderedPrefix (fun j => A (k+j)) (t+1) =
      orderedPrefix (fun j => A (k+1+j)) t * A k := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [orderedPrefix_succ,ih,orderedPrefix_succ]
    simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
      (mul_assoc (A (k+(t+1)))
        (orderedPrefix (fun j => A (k+1+j)) t) (A k)).symm

theorem orderedPrefix_replace_split (A : ℕ → Operator L q) (k n : ℕ)
    (hk : k<n) (B : Operator L q) :
    orderedPrefix (Function.update A k B) n =
      orderedPrefix (fun j => A (k+1+j)) (n-(k+1)) * B * orderedPrefix A k := by
  have hn : n = k+1+(n-(k+1)) := by omega
  have hf : (fun j => Function.update A k B (k+1+j)) = (fun j => A (k+1+j)) := by
    funext j
    rw [Function.update_of_ne (by omega)]
  have hb : orderedPrefix (Function.update A k B) (k+1) = B*orderedPrefix A k := by
    rw [orderedPrefix_succ,Function.update_self,prefix_update_outside A k k B le_rfl]
  calc
    orderedPrefix (Function.update A k B) n =
        orderedPrefix (Function.update A k B) (k+1+(n-(k+1))) := by rw [← hn]
    _ = orderedPrefix (fun j => A (k+1+j)) (n-(k+1)) * B * orderedPrefix A k := by
      rw [orderedPrefix_split,hf,hb,mul_assoc]

def insertedProduct (A : ℕ → Operator L q) (H : Operator L q) (k n : ℕ) : Operator L q :=
  orderedPrefix (fun j => A (k+j)) (n-k) * H * orderedPrefix A k

theorem insertedProduct_at_end (A : ℕ → Operator L q) (H : Operator L q) (n : ℕ) :
    insertedProduct A H n n = H*orderedPrefix A n := by simp [insertedProduct]

theorem insertedProduct_right (A : ℕ → Operator L q) (H : Operator L q)
    (k n : ℕ) (hk : k<n) :
    insertedProduct A H k n = orderedPrefix (Function.update A k (A k*H)) n := by
  rw [orderedPrefix_replace_split A k n hk]
  unfold insertedProduct
  rw [show n-k = (n-(k+1))+1 by omega,orderedPrefix_shift_head]
  simp only [mul_assoc]

theorem insertedProduct_left (A : ℕ → Operator L q) (H : Operator L q)
    (k n : ℕ) (hk : k<n) :
    insertedProduct A H (k+1) n = orderedPrefix (Function.update A k (H*A k)) n := by
  rw [orderedPrefix_replace_split A k n hk]
  unfold insertedProduct
  rw [orderedPrefix_succ]
  simp only [mul_assoc]

theorem strip_outer (A : ℕ → Operator L q) (H : Operator L q)
    (f : Operator L q → ℂ) (r n : ℕ) (hr : r≤n)
    (hc : ∀ k, r≤k → k<n →
      f (orderedPrefix (Function.update A k (H*A k)) n) =
        f (orderedPrefix (Function.update A k (A k*H)) n)) :
    f (H*orderedPrefix A n) = f (insertedProduct A H r n) := by
  have heq (k : ℕ) (hrk : r≤k) (hkn : k≤n) :
      f (insertedProduct A H k n) = f (insertedProduct A H r n) := by
    induction k,hrk using Nat.le_induction with
    | base => rfl
    | succ k hrk ih =>
      have hk : k<n := by omega
      rw [insertedProduct_left A H k n hk,hc k hrk hk,
        ← insertedProduct_right A H k n hk]
      exact ih (by omega)
  simpa only [insertedProduct_at_end] using heq n hr le_rfl

theorem optimizer_strip_outer (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (r : ℕ) (hr : r≤n) (H : Operator L q)
    (hH : ∀ k, r≤k → k<n → SupportedOn H (X k)) :
    let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
    let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
    inner ℂ v (asMap (L := L) (q := q) H v) =
      inner ℂ v (asMap (L := L) (q := q) (insertedProduct A H r n) ψ) := by
  dsimp only
  let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
  let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
  have hc (k : ℕ) (hrk : r≤k) (hkn : k<n) :
      inner ℂ v (asMap (L := L) (q := q) (orderedPrefix (Function.update A k (H*A k)) n) ψ) =
        inner ℂ v (asMap (L := L) (q := q) (orderedPrefix (Function.update A k (A k*H)) n) ψ) := by
    obtain ⟨K,hK⟩ := hH k hrk hkn
    have hc := optimizer_moment_commute hq X hX a ψ n F hF k hkn K
    simpa only [replacementOutput,LinearMap.coe_mk,AddHom.coe_mk,liftLocal_mul,← hK] using hc
  have h := strip_outer A H
    (fun M => inner ℂ v (asMap (L := L) (q := q) M ψ)) r n hr hc
  have heq : asMap (L := L) (q := q) (H*orderedPrefix A n) ψ = asMap H v := by
    change Matrix.toEuclideanCLM (𝕜 := ℂ) (H*orderedPrefix A n) ψ = _
    rw [map_mul]
    rfl
  rw [heq] at h
  exact h

end PolynomialPEPS.Subvolume.TraceStripping

end

end OAI
