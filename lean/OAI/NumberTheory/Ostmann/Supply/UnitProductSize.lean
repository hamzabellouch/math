import OAI.NumberTheory.Ostmann.Supply.KernelProducts
import OAI.NumberTheory.Ostmann.Supply.UnitKernelGenerating

namespace OAI

noncomputable section
namespace Ostmann.Supply
open scoped BigOperators

theorem exp_neg_two_mul_le_one_sub {a : ℝ} (ha : 0≤a) (ha' : a≤1/2) :
    Real.exp (-2*a)≤1-a := by
  have hp : 0<1-a := by linarith
  apply (Real.le_log_iff_exp_le hp).mp
  apply le_trans _ (Real.one_sub_inv_le_log_of_pos hp)
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [mul_sub,mul_inv_cancel₀ hp.ne']
  nlinarith

theorem sparse_unitKernelMean_exp_lower {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hp : 2≤p) (hlo : (1/3:ℝ)≤density S) (hhi : density S≤2/3)
    (hg : gamma S ≤ supplyEpsilon^2) :
    Real.exp (-8*supplyEpsilon/(p:ℝ))≤unitKernelMean S sparseKernelScale := by
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr (by omega)
  have hp2 : (2:ℝ)≤p := by exact_mod_cast hp
  have ha0 : 0≤4*supplyEpsilon/(p:ℝ) := by have := supplyEpsilon_pos; positivity
  have ha : 4*supplyEpsilon/(p:ℝ)≤1/2 := by
    apply (div_le_iff₀ hp0).mpr
    norm_num only [supplyEpsilon] at ⊢
    linarith
  have h := exp_neg_two_mul_le_one_sub ha0 ha
  have hl := sparse_unitKernelMean_lower S hp sparseKernelScale_nonneg sparseKernelScale_le_one
    (by linarith) (by linarith) hg
  convert h.trans hl using 1
  congr 1
  ring

theorem sparse_unitKernelMean_exp_upper {p : ℕ} [NeZero p] (S : Finset (ZMod p))
    (hp : 2≤p) (hlo : (1/3:ℝ)≤density S) (hhi : density S≤2/3)
    (hg : gamma S ≤ supplyEpsilon^2) :
    unitKernelMean S sparseKernelScale≤Real.exp (8*supplyEpsilon/(p:ℝ)) := by
  have h := sparse_unitKernelGenerating_norm S 1 1 hp hlo hhi hg (by norm_num) (by norm_num)
  rw [unitKernelGenerating_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (sparse_unitKernelMean_pos S hp sparseKernelScale_nonneg sparseKernelScale_le_one
      (by linarith) (by linarith) hg)] at h
  exact h.trans (by simpa [add_comm] using Real.add_one_le_exp (8*supplyEpsilon/(p:ℝ)))

theorem kernelUnitProduct_exp_bounds {ι : Type*} (P : Finset ι)
    (p : ι→ℕ) [∀i,NeZero (p i)] (S : ∀i,Finset (ZMod (p i)))
    (hp : ∀i∈P,2≤p i) (hlo : ∀i∈P,(1/3:ℝ)≤density (S i))
    (hhi : ∀i∈P,density (S i)≤2/3) (hg : ∀i∈P,gamma (S i) ≤ supplyEpsilon^2) :
    Real.exp (-8*supplyEpsilon*reciprocalMass P p)≤kernelUnitProduct P p S ∧
      kernelUnitProduct P p S≤Real.exp (8*supplyEpsilon*reciprocalMass P p) := by
  have he (c : ℝ) : (∏i∈P,Real.exp (c/(p i:ℝ)))=Real.exp (c*reciprocalMass P p) := by
    rw [←Real.exp_sum]
    congr 1
    unfold reciprocalMass
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  constructor
  · rw [←he (-8*supplyEpsilon)]
    exact Finset.prod_le_prod₀ (fun i hi => (Real.exp_pos _).le)
      (fun i hi => sparse_unitKernelMean_exp_lower (S i) (hp i hi) (hlo i hi) (hhi i hi) (hg i hi))
  · rw [←he (8*supplyEpsilon)]
    exact Finset.prod_le_prod₀
      (fun i hi => (sparse_unitKernelMean_pos (S i) (hp i hi)
        sparseKernelScale_nonneg sparseKernelScale_le_one
        (by linarith [hlo i hi]) (by linarith [hhi i hi]) (hg i hi)).le)
      (fun i hi => sparse_unitKernelMean_exp_upper (S i) (hp i hi) (hlo i hi) (hhi i hi) (hg i hi))

end Ostmann.Supply

end

end OAI
