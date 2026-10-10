import OAI.Probability.BenjaminiSchramm.LayerMomentCauchy
import OAI.Probability.BenjaminiSchramm.PrefixMaximumBootstrap

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace Percolation.BenjaminiSchramm

lemma ennreal_iSup_square_le {ι : Sort*} (f : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (h : ∀ i, (f i)^2 ≤ C) : (⨆ i, f i)^2 ≤ C := by
  have hsqrt (z : ℝ≥0∞) : (z^((1 : ℝ)/2))^2=z := by
    rw [←ENNReal.rpow_two,←ENNReal.rpow_mul]
    norm_num
  have hroot (i : ι) : f i ≤ C^((1 : ℝ)/2) := by
    have hh := ENNReal.rpow_le_rpow (h i) (by norm_num : 0 ≤ (1 : ℝ)/2)
    rw [←ENNReal.rpow_two,←ENNReal.rpow_mul] at hh
    norm_num at hh
    exact hh
  exact (pow_le_pow_left' (iSup_le hroot) 2).trans_eq (hsqrt C)

end Percolation.BenjaminiSchramm

namespace CriticalPercolation.BondGraph
open Percolation.BenjaminiSchramm
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem adjusted_layer_prefactor_bootstrap
    (a : V → ℝ) (R : ℝ) (hR : 0 < R) (p : unitInterval) (β A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hne : ∀ n, G.supAdjustedUpLayerMoment a R p n ≠ ⊤)
    (hprob : ∀ (n : ℕ) (x : V),
      G.law p (restrictedHit G.ends Set.univ x
        {y | R*((n : ℝ)-1) ≤ G.orbitAdjustedHeight a x y}) ≤ ENNReal.ofReal (B*Real.exp (-β*n)))
    (hsecond : ∀ (n : ℕ) (x : V) (u : ℝ),
      (∫⁻ ω, (restrictedLayerCount G.ends
        (Percolation.internalEdges G.ends {y | G.adjustedLayerIndex a R u x y ≤ (n : ℤ)})
        {y | G.adjustedLayerIndex a R u x y=(n : ℤ)} ω x)^2 ∂G.law p) ≤
          ENNReal.ofReal (A*Real.exp (-β*n)*prefixMaximum
            (fun j => Real.exp (β*j)*(G.supAdjustedUpLayerMoment a R p j).toReal) n)) :
    ∀ n : ℕ, G.supAdjustedUpLayerMoment a R p n ≤ ENNReal.ofReal (A*B*Real.exp (-β*n)) := by
  let S := G.supAdjustedUpLayerMoment a R p
  let H : ℕ → ℝ := fun j => Real.exp (β*j)*(S j).toReal
  have hH (j : ℕ) : 0 ≤ H j := mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  have hM (n : ℕ) : 0 ≤ prefixMaximum H n := (hH 0).trans (le_prefixMaximum H (Nat.zero_le n))
  have hsq (n : ℕ) : (S n)^2 ≤ ENNReal.ofReal (A*B*(Real.exp (-β*n))^2*prefixMaximum H n) := by
    apply ennreal_iSup_square_le
    intro x
    apply ennreal_iSup_square_le
    intro u
    have hh := (G.adjustedUpLayerMoment_cauchy a R hR p n x u).trans
      (mul_le_mul' (hprob n x) (hsecond n x u))
    rw [←ENNReal.ofReal_mul (mul_nonneg hB (Real.exp_nonneg _))] at hh
    convert hh using 1
    congr 1
    dsimp only [H,S]
    ring
  have hrec (n : ℕ) : (H n)^2 ≤ A*B*prefixMaximum H n := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hsq n)
    have hnneg : 0 ≤ A*B*(Real.exp (-β*n))^2*prefixMaximum H n :=
      mul_nonneg (mul_nonneg (mul_nonneg hA hB) (sq_nonneg _)) (hM n)
    rw [ENNReal.toReal_pow,ENNReal.toReal_ofReal hnneg] at hh
    have hc : (Real.exp (β*n))^2*(Real.exp (-β*n))^2=1 := by
      rw [←mul_pow,←Real.exp_add,show β*(n : ℝ)+ -β*n=0 by ring,Real.exp_zero,one_pow]
    calc
      _ = (Real.exp (β*n))^2*((S n).toReal)^2 := mul_pow _ _ _
      _ ≤ (Real.exp (β*n))^2*(A*B*(Real.exp (-β*n))^2*prefixMaximum H n) :=
        mul_le_mul_of_nonneg_left hh (sq_nonneg _)
      _ = A*B*((Real.exp (β*n))^2*(Real.exp (-β*n))^2)*prefixMaximum H n := by ring
      _ = _ := by rw [hc,mul_one]
  intro n
  have hb := prefix_square_bootstrap H (A*B) (mul_nonneg hA hB) hrec n
  have hreal : (S n).toReal ≤ A*B*Real.exp (-β*n) := by
    have hc : Real.exp (-β*n)*Real.exp (β*n)=1 := by
      rw [←Real.exp_add,show -β*(n : ℝ)+β*n=0 by ring,Real.exp_zero]
    calc
      _ = Real.exp (-β*n)*H n := by dsimp only [H]; rw [←mul_assoc,hc,one_mul]
      _ ≤ Real.exp (-β*n)*(A*B) := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)
      _ = _ := by ring
  have he := ENNReal.ofReal_le_ofReal hreal
  rwa [ENNReal.ofReal_toReal (hne n)] at he

end CriticalPercolation.BondGraph

end

end OAI
