import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Tactic.Linarith
import OAI.NumberTheory.SiegelZeros.Differentials.DerivativeBound
import OAI.NumberTheory.SiegelZeros.Selection.EventuallyPivots
import OAI.NumberTheory.SiegelZeros.Selection.PivotReindexing
import OAI.NumberTheory.SiegelZeros.Structure.FiniteLower

namespace OAI

namespace SiegelZeros


noncomputable section

namespace SiegelZerosAwei.W36

open scoped BigOperators

variable {K : Type*} [Field K] [NumberField K]

theorem abs_norm_eq_prod_embeddings (x : K) :
    |(Algebra.norm ℚ x : ℝ)| = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ x‖ := by
  simpa only [eq_ratCast, Complex.norm_ratCast, norm_prod] using
    congrArg (fun z : ℂ => ‖z‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ x)

theorem log_abs_norm_eq_sum_embeddings {x : K} (hx : x ≠ 0) :
    Real.log |(Algebra.norm ℚ x : ℝ)| =
      ∑ σ : K →ₐ[ℚ] ℂ, Real.log ‖σ x‖ := by
  rw [abs_norm_eq_prod_embeddings]
  exact Real.log_prod (fun σ _ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))

theorem log_abs_norm_le_finrank_mul {x : K} (hx : x ≠ 0) (B : ℝ)
    (hB : ∀ σ : K →ₐ[ℚ] ℂ, Real.log ‖σ x‖ ≤ B) :
    Real.log |(Algebra.norm ℚ x : ℝ)| ≤ (Module.finrank ℚ K : ℝ) * B := by
  rw [log_abs_norm_eq_sum_embeddings hx]
  calc
    _ ≤ ∑ _σ : K →ₐ[ℚ] ℂ, B := Finset.sum_le_sum (fun σ _ => hB σ)
    _ = _ := by simp [AlgHom.card]

theorem quarter_log_abs_norm_le {x : K} (hx : x ≠ 0)
    (hdegree : Module.finrank ℚ K = 4) (B : ℝ)
    (hB : ∀ σ : K →ₐ[ℚ] ℂ, Real.log ‖σ x‖ ≤ B) :
    (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ x : ℝ)| ≤ B := by
  have h := log_abs_norm_le_finrank_mul hx B hB
  rw [hdegree] at h
  norm_num at h ⊢
  linarith

theorem quarter_log_abs_norm_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (hA : A.det ≠ 0)
    (hdegree : Module.finrank ℚ K = 4) (B : ℝ)
    (hB : ∀ σ : K →ₐ[ℚ] ℂ, Real.log ‖(σ.mapMatrix A).det‖ ≤ B) :
    (1 / 4 : ℝ) * Real.log |(Algebra.norm ℚ A.det : ℝ)| ≤ B := by
  apply quarter_log_abs_norm_le hA hdegree B
  intro σ
  rw [σ.map_det]
  exact hB σ

end SiegelZerosAwei.W36

end


noncomputable section

namespace SiegelZerosAwei.W36

open scoped BigOperators

variable {K : Type*} [Field K] [NumberField K]

def thetaRowMatrix {m : ℕ} (g : Fin 3 → K →+* K) (a b : K)
    (orders : Fin m → Fin 3 → ℕ) (n : Fin m → Fin 4 → ℕ) :
    Matrix (Fin m) (Fin m) K := fun i j =>
  g 0 (WeightedTorusJets.W34.theta a b (n j)) ^ orders i 0 *
    g 1 (WeightedTorusJets.W34.theta a b (n j)) ^ orders i 1 *
    g 2 (WeightedTorusJets.W34.theta a b (n j)) ^ orders i 2

theorem map_thetaRowMatrix {m : ℕ} (g : Fin 3 → K →+* K) (a b : K)
    (orders : Fin m → Fin 3 → ℕ) (n : Fin m → Fin 4 → ℕ)
    (σ : K →ₐ[ℚ] ℂ) :
    σ.mapMatrix (thetaRowMatrix g a b orders n) =
      WeightedTorusJets.W35.eigenvalueMatrix
        (fun k j => (σ.toRingHom.comp (g k))
          (WeightedTorusJets.W34.theta a b (n j))) orders := by
  ext i j
  simp [thetaRowMatrix, WeightedTorusJets.W35.eigenvalueMatrix, map_mul, map_pow]

theorem archimedean_norm_bound {m : ℕ} (hm : 0 < m)
    (g : Fin 3 → K →+* K) (a b : K) (d : ℤ) (q N : ℕ)
    (orders : Fin m → Fin 3 → ℕ) (n : Fin m → Fin 4 → ℕ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hq : 1 ≤ q) (hN : 0 < N) (hd : |(d : ℝ)| ≤ (q : ℝ))
    (hn : ∀ j i, n j i ≤ N) (hdegree : Module.finrank ℚ K = 4)
    (hne : (thetaRowMatrix g a b orders n).det ≠ 0) :
    (1 / 4 : ℝ) *
        Real.log |(Algebra.norm ℚ (thetaRowMatrix g a b orders n).det : ℝ)| ≤
      (m : ℝ) / 2 * Real.log m +
      (∑ i, ((orders i 0 + orders i 1 + orders i 2 : ℕ) : ℝ)) *
        (Real.log N + (1 / 2 : ℝ) * Real.log q + Real.log 8) := by
  apply quarter_log_abs_norm_det_le _ hne hdegree
  intro σ
  have hmapped : (σ.mapMatrix (thetaRowMatrix g a b orders n)).det ≠ 0 := by
    rw [← σ.map_det]
    exact (map_ne_zero σ).mpr hne
  rw [map_thetaRowMatrix] at hmapped ⊢
  exact WeightedTorusJets.W35.embedding_log_det_bound hm
    (fun k => σ.toRingHom.comp (g k)) a b d q N orders n
    ha hb hq hN hd hn hmapped

end SiegelZerosAwei.W36

end


open scoped BigOperators NumberField

namespace SiegelZerosAwei.W46

open SiegelZerosAwei.W31

theorem cutoff_first_sum_pos (P : Finset MultiIndex) (H N : ℕ)
    (hH : 1 ≤ H) (hHN : H ≤ N) (hN : 18818 ≤ N)
    (hcard : P.card = N ^ 4)
    (hcut : ∀ a ∈ P, weight (H : ℝ) a ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    0 < ∑ a ∈ P, (a 0 : ℝ) := by
  have hHr : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  exact lt_of_lt_of_le (by positivity)
    (Result.Workers.W33.cutoff_pivot_lower P H N hH hHN hN hcard hcut)

theorem cutoff_normalization_pos (P : Finset MultiIndex) (H N q : ℕ)
    (hH : 1 ≤ H) (hHN : H ≤ N) (hN : 18818 ≤ N) (hq : 3 ≤ q)
    (hcard : P.card = N ^ 4)
    (hcut : ∀ a ∈ P, weight (H : ℝ) a ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ)) :
    0 < (∑ a ∈ P, (a 0 : ℝ)) * Real.log ((N : ℝ) ^ (4 / 3 : ℝ)) ∧
      0 < Real.log (q : ℝ) := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hqr : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  exact ⟨mul_pos (cutoff_first_sum_pos P H N hH hHN hN hcard hcut)
    (Real.log_pos (Real.one_lt_rpow hNr (by norm_num))), Real.log_pos hqr⟩

variable {K : Type*} [Field K] [NumberField K]

theorem integral_field_log_norm (Δ : 𝓞 K) :
    Real.log |(Algebra.norm ℤ Δ : ℝ)| =
      Real.log |(Algebra.norm ℚ (Δ : K) : ℝ)| := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Algebra.coe_norm_int Δ)
  simpa only [Rat.cast_intCast] using congrArg (fun x : ℝ => Real.log |x|) h

theorem master_actual_determinant
    (P : Finset MultiIndex) (H N q : ℕ)
    (hH : 1 ≤ H) (hHN : H ≤ N) (hN : 18818 ≤ N) (hq : 3 ≤ q)
    (hcard : P.card = N ^ 4)
    (hcut : ∀ a ∈ P, weight (H : ℝ) a ≤
      96 * (H : ℝ) ^ (2 / 3 : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ))
    (e : Fin (N ^ 4) ≃ P)
    (g : Fin 3 → K →+* K) (a b : K) (d : ℤ)
    (n : Fin (N ^ 4) → Fin 4 → ℕ)
    (ha : a ^ 2 = (d : K)) (hb : b ^ 2 = 2)
    (hheight : |(d : ℝ)| ≤ (q : ℝ)) (hn : ∀ j i, n j i ≤ N)
    (hdegree : Module.finrank ℚ K = 4)
    (Δ : 𝓞 K) (hΔ : Δ ≠ 0)
    (hdet : (Δ : K) = (W36.thetaRowMatrix g a b (fun i => e i) n).det)
    (C CH delta : ℝ) (hC : Real.log 4 ≤ C)
    (good : Finset ℕ)
    (hsub : good ⊆ SiegelZeros.W08.primesUpTo ((N : ℝ) ^ (4 / 3 : ℝ)))
    (hmass : Real.log ((N : ℝ) ^ (4 / 3 : ℝ)) - C * Real.log q -
      C * delta * ((Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) ^ 2) / Real.log q - CH ≤
        ∑ p ∈ good, Real.log (p : ℝ) / p)
    (hdiv : ∀ p ∈ good,
      (p : 𝓞 K) ^ SiegelZeros.W44.exponent P (fun α => α 0) p ∣ Δ) :
    1 ≤ masterRHS (∑ α ∈ P, (α 0 : ℝ))
      (∑ α ∈ P, ((α 1 : ℝ) + (α 2 : ℝ))) P.card
      ((N : ℝ) ^ (4 / 3 : ℝ)) C CH (Real.log q) delta
      (Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) (Real.log P.card) (Real.log 8) := by
  classical
  have hNpos : 0 < N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hqr : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hU : 0 ≤ (N : ℝ) ^ (4 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hΔK : (Δ : K) ≠ 0 := by
    intro h
    apply hΔ
    exact Subtype.ext h
  have hdet0 : (W36.thetaRowMatrix g a b (fun i => e i) n).det ≠ 0 := by
    rw [← hdet]
    exact hΔK
  have horders :
      (∑ i : Fin (N ^ 4), (((e i : MultiIndex) 0 + (e i : MultiIndex) 1 +
        (e i : MultiIndex) 2 : ℕ) : ℝ)) =
      (∑ α ∈ P, (α 0 : ℝ)) + ∑ α ∈ P, ((α 1 : ℝ) + (α 2 : ℝ)) := by
    rw [sum_equiv_finset P e (fun α => ((α 0 + α 1 + α 2 : ℕ) : ℝ))]
    simp only [Nat.cast_add, Finset.sum_add_distrib, add_assoc]
  have harch := W36.archimedean_norm_bound (pow_pos hNpos 4) g a b d q N
    (fun i => (e i : MultiIndex)) n ha hb (by omega) hNpos hheight hn hdegree hdet0
  rw [horders, ← hdet, ← integral_field_log_norm, ← hcard] at harch
  have hlower := SiegelZeros.W08.quartic_norm_source_finitelower
    P (fun α => α 0) hU good hsub hmass hdegree Δ hΔ hdiv
  have herror : Real.log 4 * (P.card : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) ≤
      C * (P.card : ℝ) * (N : ℝ) ^ (4 / 3 : ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)) hU
  have hfinite : (∑ α ∈ P, (α 0 : ℝ)) *
      (Real.log ((N : ℝ) ^ (4 / 3 : ℝ)) - C * Real.log q -
        C * (delta * ((Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) ^ 2) / Real.log q) - CH) -
      C * P.card * (N : ℝ) ^ (4 / 3 : ℝ) ≤
      (1 / 4 : ℝ) * Real.log |(Algebra.norm ℤ Δ : ℝ)| := by
    have heq : C * (delta * ((Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) ^ 2) / Real.log q) =
        C * delta * ((Real.log ((N : ℝ) ^ (4 / 3 : ℝ))) ^ 2) / Real.log q := by ring
    rw [heq]
    exact (sub_le_sub_left herror _).trans hlower
  exact master_from_power_scale _ _ _ _ _ C CH delta _
    (cutoff_first_sum_pos P H N hH hHN hN hcard hcut) hNr hqr harch hfinite

end SiegelZerosAwei.W46




end SiegelZeros

end OAI
