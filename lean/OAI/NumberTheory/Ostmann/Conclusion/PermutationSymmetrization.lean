import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Conclusion

def permuteTuple {ι Ω : Type*} (σ : Equiv.Perm ι) (x : ι → Ω) : ι → Ω :=
  fun i => x (σ i)

def tuplePermutation {ι Ω : Type*} (σ : Equiv.Perm ι) : (ι → Ω) ≃ (ι → Ω) where
  toFun := permuteTuple σ
  invFun := permuteTuple σ.symm
  left_inv x := by funext i; simp [permuteTuple]
  right_inv x := by funext i; simp [permuteTuple]

def jointWeight {ι Ω : Type*} [Fintype ι] (w : Ω → ℝ) (x : ι → Ω) : ℝ :=
  ∏ i, w (x i)

theorem jointWeight_permute {ι Ω : Type*} [Fintype ι]
    (w : Ω → ℝ) (σ : Equiv.Perm ι) (x : ι → Ω) :
    jointWeight w (permuteTuple σ x) = jointWeight w x :=
  Equiv.prod_comp σ (fun i => w (x i))

def finiteCorrelation {ι Ω S : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Fintype S] (w : Ω → ℝ) (G A : (ι → Ω) → S → ℂ) : ℂ :=
  ∑ x, (jointWeight w x : ℂ) * ∑ s, G x s * A x s

def symmetrizedAmplitude {ι Ω S : Type*} [Fintype ι] [DecidableEq ι]
    (A : (ι → Ω) → S → ℂ) (x : ι → Ω) (s : S) : ℂ :=
  (Fintype.card (Equiv.Perm ι) : ℂ)⁻¹ * ∑ σ : Equiv.Perm ι, A (permuteTuple σ x) s

theorem finiteCorrelation_permute {ι Ω S : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Fintype S] (w : Ω → ℝ) (G A : (ι → Ω) → S → ℂ)
    (σ : Equiv.Perm ι) (hG : ∀ x s, G (permuteTuple σ x) s = G x s) :
    finiteCorrelation w G (fun x s => A (permuteTuple σ x) s) = finiteCorrelation w G A := by
  have h := (tuplePermutation (Ω := Ω) σ).sum_comp
    (fun x => (jointWeight w x : ℂ) * ∑ s, G x s * A x s)
  simpa only [finiteCorrelation, tuplePermutation, Equiv.coe_fn_mk, jointWeight_permute, hG] using h

theorem finiteCorrelation_sum {ι Ω S J : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Fintype S] [Fintype J]
    (w : Ω → ℝ) (G : (ι → Ω) → S → ℂ) (A : J → (ι → Ω) → S → ℂ) :
    finiteCorrelation w G (fun x s => ∑ j, A j x s) =
      ∑ j, finiteCorrelation w G (A j) := by
  unfold finiteCorrelation
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ x, ∑ j, ∑ s, (jointWeight w x : ℂ)*(G x s*A j x s) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_comm

theorem finiteCorrelation_symmetrize {ι Ω S : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Fintype S] (w : Ω → ℝ) (G A : (ι → Ω) → S → ℂ)
    (hG : ∀ σ x s, G (permuteTuple σ x) s = G x s) :
    finiteCorrelation w G (symmetrizedAmplitude A) = finiteCorrelation w G A := by
  have hlin : ∀ (c : ℂ) (B : (ι → Ω) → S → ℂ),
      finiteCorrelation w G (fun x s => c*B x s) = c*finiteCorrelation w G B := by
    intro c B
    unfold finiteCorrelation
    simp_rw [show ∀ x s, G x s*(c*B x s) = c*(G x s*B x s) from fun _ _ => by ring]
    simp_rw [← Finset.mul_sum]
    calc
      _ = ∑ x, c*((jointWeight w x : ℂ)*∑ s, G x s*B x s) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      _ = _ := (Finset.mul_sum _ _ _).symm
  unfold symmetrizedAmplitude
  rw [hlin, finiteCorrelation_sum]
  simp_rw [finiteCorrelation_permute w G A _ (hG _)]
  have hcard : (Fintype.card (Equiv.Perm ι) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [hcard]

theorem norm_sum_sq_eq_pair_sum {J : Type*} [Fintype J] (z : J → ℂ) :
    ‖∑ j, z j‖^2 = ∑ i, ∑ j, (z i * conj (z j)).re := by
  calc
    ‖∑ j, z j‖^2 = ((∑ j, z j)*conj (∑ j, z j)).re := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rfl
    _ = _ := by
      simp only [map_sum, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
      exact Finset.sum_comm

theorem weighted_cauchy_schwarz {J : Type*} [Fintype J]
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) (G A : J → ℂ) :
    ‖∑ j, (w j : ℂ)*G j*A j‖^2 ≤
      (∑ j, w j*‖G j‖^2)*(∑ j, w j*‖A j‖^2) := by
  have htriangle : ‖∑ j, (w j : ℂ)*G j*A j‖ ≤
      ∑ j, w j*‖G j‖*‖A j‖ := by
    refine (norm_sum_le _ _).trans_eq ?_
    apply Finset.sum_congr rfl
    intro j hj
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j)]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  let f := fun j => Real.sqrt (w j)*‖G j‖
  let g := fun j => Real.sqrt (w j)*‖A j‖
  have hfg : ∀ j, f j*g j = w j*‖G j‖*‖A j‖ := by
    intro j
    dsimp [f,g]
    calc
      Real.sqrt (w j)*‖G j‖*(Real.sqrt (w j)*‖A j‖)
          = (Real.sqrt (w j))^2*(‖G j‖*‖A j‖) := by ring
      _ = w j*‖G j‖*‖A j‖ := by rw [Real.sq_sqrt (hw j)]; ring
  have hff : ∀ j, (f j)^2 = w j*‖G j‖^2 := by
    intro j
    simp only [f,mul_pow,Real.sq_sqrt (hw j)]
  have hgg : ∀ j, (g j)^2 = w j*‖A j‖^2 := by
    intro j
    simp only [g,mul_pow,Real.sq_sqrt (hw j)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  simp_rw [hfg,hff,hgg] at hcs
  exact hsq.trans hcs

theorem finiteCorrelation_cauchy_schwarz {ι Ω S : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [Fintype S] (w : Ω → ℝ) (hw : ∀ a, 0 ≤ w a)
    (G A : (ι → Ω) → S → ℂ) :
    ‖finiteCorrelation w G A‖^2 ≤
      (∑ x, jointWeight w x*∑ s, ‖G x s‖^2)*
      (∑ x, jointWeight w x*∑ s, ‖A x s‖^2) := by
  have h := weighted_cauchy_schwarz
    (fun z : (ι → Ω) × S => jointWeight w z.1)
    (fun z => Finset.prod_nonneg fun i _ => hw (z.1 i))
    (fun z => G z.1 z.2) (fun z => A z.1 z.2)
  simpa only [finiteCorrelation,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc] using h

end Ostmann.Conclusion

end

end OAI
