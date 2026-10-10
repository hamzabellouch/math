import OAI.InformationTheory.AmplitudeDamping.SequentialProjections

namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

@[simp] theorem kraus_zero (γ ν : ℝ) : kraus γ ν 0 = !![(Real.sqrt (1 - ν) : ℂ), 0; 0, (Real.sqrt (1 - ν) * Real.sqrt (1 - γ) : ℂ)] := by
  norm_num [kraus]

@[simp] theorem kraus_one (γ ν : ℝ) : kraus γ ν 1 = !![0, (Real.sqrt (γ * (1 - ν)) : ℂ); 0, 0] := by
  norm_num [kraus]

@[simp] theorem kraus_two (γ ν : ℝ) : kraus γ ν 2 = !![(Real.sqrt ν * Real.sqrt (1 - γ) : ℂ), 0; 0, (Real.sqrt ν : ℂ)] := by
  simp only [kraus, show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide, ite_false, ite_true]

@[simp] theorem kraus_three (γ ν : ℝ) : kraus γ ν 3 = !![0, 0; (Real.sqrt (γ * ν) : ℂ), 0] := by
  simp only [kraus, show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide, ite_false]

theorem sum_fin_cons {α : Type u_1} {M : Type u_2} [Fintype α] [AddCommMonoid M] {n : ℕ}
    (f : (Fin (n+1) → α) → M) :
    ∑ r, f r = ∑ a, ∑ r : Fin n → α, f (Fin.cons a r) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) ↦ α)).sum_comp f]
  rw [Fintype.sum_prod_type]
  rfl

def pure {ι : Type u_3} (ψ : ι → ℂ) : Matrix ι ι ℂ := fun i j ↦ ψ i * star (ψ j)

def applyKraus {ι : Type u_4} {κ : Type u_5} {ρ : Type u_6} [Fintype κ] [Fintype ρ]
    (L : ρ → Matrix ι κ ℂ) (P : Matrix κ κ ℂ) : Matrix ι ι ℂ :=
  ∑ r, L r * P * (L r).conjTranspose

theorem local_channel (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    applyKraus (kraus γ ν) P =
      !![((1-γ*ν:ℝ):ℂ)*P 0 0+((γ*(1-ν):ℝ):ℂ)*P 1 1,
         (Real.sqrt (1-γ):ℂ)*P 0 1;
         (Real.sqrt (1-γ):ℂ)*P 1 0,
         ((γ*ν:ℝ):ℂ)*P 0 0+((1-γ*(1-ν):ℝ):ℂ)*P 1 1] := by
  have hγ0 : 0 ≤ 1-γ := sub_nonneg.mpr hγ.2
  have hν0 : 0 ≤ 1-ν := sub_nonneg.mpr hν.2
  have hs (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ)^2 = (x:ℂ) := by
    norm_cast; exact Real.sq_sqrt hx
  have hsν := hs ν hν.1
  have hsγν := hs (ν*γ) (mul_nonneg hν.1 hγ.1)
  have hsγν' := hs (-(ν*γ)+γ) (by nlinarith only [mul_nonneg hγ.1 hν0])
  simp only [applyKraus, Fin.sum_univ_four, kraus_zero, kraus_one, kraus_two, kraus_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    simp only [hsν, hsγν, hsγν', hs (1-ν) hν0, hs (1-γ) hγ0] <;>
    push_cast <;> ring

theorem kraus_complete (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) :
    ∑ r, (kraus γ ν r).conjTranspose * kraus γ ν r = 1 := by
  have hγ0 : 0 ≤ 1-γ := sub_nonneg.mpr hγ.2
  have hν0 : 0 ≤ 1-ν := sub_nonneg.mpr hν.2
  have hs (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ)^2 = (x:ℂ) := by
    norm_cast; exact Real.sq_sqrt hx
  have hsν := hs ν hν.1
  have hsγν := hs (ν*γ) (mul_nonneg hν.1 hγ.1)
  have hsγν' := hs (-(ν*γ)+γ) (by nlinarith only [mul_nonneg hγ.1 hν0])
  simp only [Fin.sum_univ_four, kraus_zero, kraus_one, kraus_two, kraus_three]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two] <;>
    ring_nf <;>
    simp only [hsν, hsγν, hsγν', hs (1-ν) hν0, hs (1-γ) hγ0] <;>
    push_cast <;> ring

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem tensorKraus_complete (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) :
    ∑ r, (tensorKraus γ ν n r).conjTranspose * tensorKraus γ ν n r = 1 := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, tensorKraus,
    star_prod]
  simp only [← Finset.prod_mul_distrib]
  have hinner (r : Fin n → Fin 4) :
      (∑ b : Basis n, ∏ k, star (kraus γ ν (r k) (b k) (i k)) * kraus γ ν (r k) (b k) (j k)) =
      ∏ k, ∑ b : Fin 2, star (kraus γ ν (r k) b (i k)) * kraus γ ν (r k) b (j k) :=
    (Fintype.prod_sum (fun k b ↦ star (kraus γ ν (r k) b (i k)) * kraus γ ν (r k) b (j k))).symm
  simp only [hinner]
  rw [← Fintype.prod_sum (fun k r ↦ ∑ b : Fin 2,
    star (kraus γ ν r b (i k)) * kraus γ ν r b (j k))]
  have hc (k : Fin n) :
      (∑ r : Fin 4, ∑ b : Fin 2, star (kraus γ ν r b (i k)) * kraus γ ν r b (j k)) =
      if i k = j k then 1 else 0 := by
    have h := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ ↦ A (i k) (j k))
      (kraus_complete γ ν hγ hν)
    simpa only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply] using h
  simp_rw [hc]
  simp [Fintype.prod_ite_zero, funext_iff, Matrix.one_apply]

theorem applyKraus_posSemidef {ι : Type u_7} {κ : Type u_8} {ρ : Type u_9} [Fintype ι] [Fintype κ] [Fintype ρ]
    [DecidableEq ι] [DecidableEq κ] (L : ρ → Matrix ι κ ℂ)
    {P : Matrix κ κ ℂ} (hP : P.PosSemidef) : (applyKraus L P).PosSemidef := by
  rw [← Matrix.nonneg_iff_posSemidef]
  exact Finset.sum_nonneg (fun r _ ↦ Matrix.nonneg_iff_posSemidef.mpr
    (hP.mul_mul_conjTranspose_same (L r)))

theorem applyKraus_trace {ι : Type u_10} {κ : Type u_11} {ρ : Type u_12} [Fintype ι] [Fintype κ] [Fintype ρ]
    [DecidableEq κ] (L : ρ → Matrix ι κ ℂ)
    (hL : ∑ r, (L r).conjTranspose * L r = 1) (P : Matrix κ κ ℂ) :
    (applyKraus L P).trace = P.trace := by
  simp only [applyKraus, Matrix.trace_sum]
  calc
    _ = ∑ r, ((L r).conjTranspose * L r * P).trace := by
      apply Finset.sum_congr rfl
      intro r _
      exact Matrix.trace_mul_cycle _ _ _
    _ = _ := by
      rw [← Matrix.trace_sum, ← Matrix.sum_mul, hL, Matrix.one_mul]

theorem channel_trace (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) (P : QMatrix n) :
    (channel γ ν n P).trace = P.trace :=
  applyKraus_trace _ (tensorKraus_complete γ ν hγ hν n) P

theorem channel_posSemidef (γ ν : ℝ) (n : ℕ) {P : QMatrix n} (hP : P.PosSemidef) :
    (channel γ ν n P).PosSemidef := applyKraus_posSemidef _ hP

theorem mul_pure_mul_conjTranspose {ι : Type u_13} {κ : Type u_14} [Fintype κ]
    (L : Matrix ι κ ℂ) (ψ : κ → ℂ) : L * pure ψ * L.conjTranspose = pure (L *ᵥ ψ) := by
  change L * Matrix.vecMulVec ψ (star ψ) * L.conjTranspose =
    Matrix.vecMulVec (L *ᵥ ψ) (star (L *ᵥ ψ))
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]

def columns {ι : Type u_15} {κ : Type u_16} {ρ : Type u_17} [Fintype κ] (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) :
    Matrix ι ρ ℂ := fun i r ↦ (L r *ᵥ ψ) i

theorem columns_mul_conjTranspose {ι : Type u_18} {κ : Type u_19} {ρ : Type u_20} [Fintype κ] [Fintype ρ]
    (L : ρ → Matrix ι κ ℂ) (ψ φ : κ → ℂ) :
    columns L ψ * (columns L φ).conjTranspose =
      ∑ r, L r * Matrix.vecMulVec ψ (star φ) * (L r).conjTranspose := by
  simp_rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
  ext i j
  simp [columns, Matrix.mul_apply, Matrix.vecMulVec, Matrix.conjTranspose_apply, Matrix.sum_apply]

theorem columns_pure {ι : Type u_21} {κ : Type u_22} {ρ : Type u_23} [Fintype κ] [Fintype ρ]
    (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) :
    columns L ψ * (columns L ψ).conjTranspose = applyKraus L (pure ψ) :=
  columns_mul_conjTranspose L ψ ψ

end GAD

end

end OAI
