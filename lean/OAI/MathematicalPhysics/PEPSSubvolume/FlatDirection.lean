import Mathlib
import OAI.MathematicalPhysics.PEPSFilters.LocalOperators
import OAI.MathematicalPhysics.PEPSSubvolume.Filters
import OAI.MathematicalPhysics.PEPSSubvolume.KernelPerturbation

namespace OAI

/-! Flat second variations and vanishing optimizing kernel directions. -/

noncomputable section
open scoped BigOperators ComplexOrder
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open scoped BigOperators
open PolynomialPEPS.PinnedEntropy

open scoped Topology
open Filter
namespace PolynomialPEPS.Subvolume.OptimizerFlatDirection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem second_variation (v u w : E) (C K p : ℝ) (hp : 2 < p)
    (h : ∀ t : ℝ, ‖v + t • u + t^2 • w‖^2 ≤
      (‖v‖^2 + C*t^2) * (1 + K*|t|^p)) :
    2 * inner ℝ v w + ‖u‖^2 ≤ C := by
  have hb (t : ℝ) (ht : 0 < t) :
      2 * inner ℝ v w + ‖u‖^2 ≤
        C + K*‖v‖^2*t^(p-2) + K*C*t^p := by
    have hp' := h t
    have hm' := h (-t)
    have hsum : ‖(v+t^2 • w) + t • u‖^2 + ‖(v+t^2 • w) - t • u‖^2 ≤
        2 * ((‖v‖^2+C*t^2)*(1+K*t^p)) := by
      simpa only [neg_smul, neg_sq, abs_neg, abs_of_pos ht, sub_eq_add_neg,
        add_assoc, add_left_comm, add_comm, two_mul] using add_le_add hp' hm'
    rw [parallelogram_law_with_norm ℝ, norm_add_sq_real] at hsum
    simp only [inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg t), abs_of_pos ht, mul_pow] at hsum
    have hr : t^p = t^2 * t^(p-2) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht]
      congr 1
      norm_num
    have ht2 : 0 < t^2 := sq_pos_of_pos ht
    apply (mul_le_mul_iff_right₀ ht2).mp
    have hw : 0 ≤ (t^2)^2 * ‖w‖^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [hr] at hsum ⊢
    nlinarith only [hsum,hw]
  have hpow : Tendsto (fun t : ℝ => t^(p-2)) (𝓝[>] 0) (𝓝 0) := by
    have ht := (Real.continuousAt_rpow_const 0 (p-2)
      (Or.inr (by linarith))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa [Real.zero_rpow (show p-2 ≠ 0 by linarith)] using ht
  have hpow' : Tendsto (fun t : ℝ => t^p) (𝓝[>] 0) (𝓝 0) := by
    have ht := (Real.continuousAt_rpow_const 0 p
      (Or.inr (by linarith))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
    simpa [Real.zero_rpow (ne_of_gt (show 0 < p by linarith))] using ht
  have hl : Tendsto (fun t : ℝ => C+K*‖v‖^2*t^(p-2)+K*C*t^p)
      (𝓝[>] 0) (𝓝 C) := by
    convert (tendsto_const_nhds.add (tendsto_const_nhds.mul hpow)).add
      (tendsto_const_nhds.mul hpow') using 1
    simp
  apply ge_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hb t ht

theorem first_direction_vanishes (v w : E) (K p : ℝ) (hp : 2 < p)
    (h : ∀ t : ℝ, ‖v + t • w‖^2 ≤ ‖v‖^2 * (1+K*|t|^p)) :
    w = 0 := by
  have hb := second_variation v w 0 0 K p hp (by simpa using h)
  simp only [inner_zero_right, mul_zero, zero_add] at hb
  simpa using norm_eq_zero.mp (le_antisymm (by nlinarith [norm_nonneg w]) (norm_nonneg w))

theorem mixed_direction_vanishes (v u w : E) (K p : ℝ) (hp : 2 < p)
    (h : ∀ c t : ℝ, ‖v + t • u + (c*t^2) • w‖^2 ≤
      (‖v‖^2+‖v‖^2*t^2)*(1+K*|c*t|^p)) :
    inner ℝ v w = 0 := by
  have hc (c : ℝ) : 2*c*inner ℝ v w + ‖u‖^2 ≤ ‖v‖^2 := by
    have hb := second_variation v u (c • w) (‖v‖^2) (K*|c|^p) p hp (fun t => by
      simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc, abs_mul,
        Real.mul_rpow (abs_nonneg c) (abs_nonneg t)] using h c t)
    simpa [inner_smul_right, mul_assoc, mul_left_comm, mul_comm] using hb
  by_contra hn
  have hne : 2 * inner ℝ v w ≠ 0 := mul_ne_zero (by norm_num) hn
  have H := hc ((‖v‖^2+‖u‖^2+1)/(2*inner ℝ v w))
  have heq : 2*((‖v‖^2+‖u‖^2+1)/(2*inner ℝ v w))*inner ℝ v w =
      ‖v‖^2+‖u‖^2+1 := by field_simp
  rw [heq] at H
  nlinarith [sq_nonneg ‖u‖]

end PolynomialPEPS.Subvolume.OptimizerFlatDirection

namespace PolynomialPEPS.Subvolume.ActualKernel
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open PolynomialPEPS.Subvolume.SpectralCurve PolynomialPEPS.Subvolume.KernelPerturbation
open PolynomialPEPS.Subvolume.KernelNormalization PolynomialPEPS.Subvolume.OptimizerGauge
variable {L q : ℕ}

theorem affine_output (A : ℕ → Operator L q) (k n : ℕ) (hk : k<n)
    (B : Operator L q) (c d : ℂ) (ψ : State L q) :
    asMap (L := L) (q := q) (orderedPrefix (Function.update A k (c • (A k + d • B))) n) ψ =
      c • (asMap (L := L) (q := q) (orderedPrefix A n) ψ +
        d • asMap (L := L) (q := q) (orderedPrefix (Function.update A k B) n) ψ) := by
  rw [prefix_update_smul A k n hk, prefix_update_add A k n hk,
    Function.update_eq_self, prefix_update_smul A k n hk]
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (_ • (_ + _ • _)) ψ = _
  simp only [map_smul, map_add, smul_apply, add_apply]
  rfl

theorem perturbation_envelope (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k : ℕ) (hk : k < n) (hp : 2 < 2/a k)
    (U : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ))
    (e : RegionConfiguration q (X k) → ℝ) (he : ∀ i, 0 ≤ e i)
    (hrep : (F k).matrix = spectralHom U (fun i => (e i : ℂ)))
    (hs : ∑ i, (e i)^(2/a k) = 1)
    (ζ : unitary ℂ) (t : ℝ) :
    let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
    let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
    let w : State L q := asMap (L := L) (q := q) (orderedPrefix (Function.update A k (liftLocal (X k) (kernel U e))) n) ψ
    ‖v + ((t : ℂ)*(ζ : ℂ)) • w‖^2 ≤ ‖v‖^2 * cost e (2/a k) t := by
  dsimp only
  let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
  let c := scale (cost e (2/a k) t) (2/a k)
  let G : LocalPositiveFilter q (X k) :=
    ⟨normalized U e (2/a k) t, normalized_posSemidef U e he (2/a k) t⟩
  have hG : filterTracePower G (2/a k) = 1 :=
    normalized_capacity U e he (2/a k) (by linarith) hs t
  have hb := one_replacement_bound hq X hX a ψ n F hF k hk
    (perturbUnitary U e ζ t) G hG
  have hmat : liftLocal (X k)
      ((perturbUnitary U e ζ t : Matrix _ _ ℂ)*G.matrix) =
      (c : ℂ) • (A k + ((t : ℂ)*(ζ : ℂ)) • liftLocal (X k) (kernel U e)) := by
    rw [show G.matrix = normalized U e (2/a k) t from rfl,
      normalized_factorization, ← hrep, liftLocal_smul, liftLocal_add, liftLocal_smul]
  have houtput : asMap (L := L) (q := q) (orderedPrefix (Function.update A k
      (liftLocal (X k) ((perturbUnitary U e ζ t : Matrix _ _ ℂ)*G.matrix))) n) ψ =
      (c : ℂ) • (asMap (L := L) (q := q) (orderedPrefix A n) ψ +
        ((t : ℂ)*(ζ : ℂ)) •
          asMap (L := L) (q := q) (orderedPrefix (Function.update A k (liftLocal (X k) (kernel U e))) n) ψ) := by
    rw [hmat]
    exact affine_output A k n hk _ _ _ ψ
  have hfv : filteredVector (fun j : Fin n => F j.val) ψ = asMap (L := L) (q := q) (orderedPrefix A n) ψ := by
    unfold filteredVector
    rw [PhysicalCurve.orderedFilterProduct_eq_prefix]
  have hc : 0 < c := scale_pos _ _
    (lt_of_lt_of_le zero_lt_one (one_le_cost e (2/a k) t))
  have hb' := hb
  rw [houtput, hfv, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at hb'
  exact norm_sq_bound _ _ _ _ (norm_nonneg _) (norm_nonneg _)
    (one_le_cost e (2/a k) t) hp hb'

theorem kernel_output_zero (hq : 0 < q)
    (X : ℕ → Finset (Vertex L)) (hX : Monotone X)
    (a : ℕ → ℝ) (ψ : State L q) (n : ℕ)
    (F : (j : ℕ) → LocalPositiveFilter q (X j))
    (hF : IsFilterOptimizer ψ (fun j : Fin n => a j.val) (fun j : Fin n => F j.val))
    (k : ℕ) (hk : k < n) (hp : 2 < 2/a k)
    (U : unitary (Matrix (RegionConfiguration q (X k)) (RegionConfiguration q (X k)) ℂ))
    (e : RegionConfiguration q (X k) → ℝ) (he : ∀ i, 0 ≤ e i)
    (hrep : (F k).matrix = spectralHom U (fun i => (e i : ℂ)))
    (hs : ∑ i, (e i)^(2/a k) = 1) :
    asMap (L := L) (q := q) (orderedPrefix (Function.update (fun j => liftLocal (X j) (F j).matrix)
      k (liftLocal (X k) (kernel U e))) n) ψ = 0 := by
  let A : ℕ → Operator L q := fun j => liftLocal (X j) (F j).matrix
  let v : State L q := asMap (L := L) (q := q) (orderedPrefix A n) ψ
  let w : State L q := asMap (L := L) (q := q) (orderedPrefix (Function.update A k (liftLocal (X k) (kernel U e))) n) ψ
  let K : ℝ := ∑ i, if e i = 0 then (1:ℝ) else 0
  have hb (t : ℝ) : ‖v + t • w‖^2 ≤ ‖v‖^2*(1+K*|t|^(2/a k)) := by
    have H := perturbation_envelope hq X hX a ψ n F hF k hk hp U e he hrep hs 1 t
    change ‖v + ((t : ℂ)*(1 : unitary ℂ)) • w‖^2 ≤ ‖v‖^2*(1+K*|t|^(2/a k)) at H
    have htw : (t : ℂ) • w = t • w := by
      ext i
      simp [Complex.real_smul]
    simpa only [OneMemClass.coe_one, mul_one, htw] using H
  exact OptimizerFlatDirection.first_direction_vanishes v w K (2/a k) hp hb

end PolynomialPEPS.Subvolume.ActualKernel

end

end OAI
