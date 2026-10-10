import Mathlib
import OAI.Probability.LogConcave.OraclePrograms.Expression

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory
open OracleCompiler OracleCompiler.Expression

namespace SeedCompiler

variable {k d : ℕ}

lemma slotTransform_add_shift (c : ℝ) (a v : Fin k → ℝ) (g : Fin k → Point d) (Δ : Point d) :
    slotTransform c a (shiftSlots v Δ g)=
      shiftSlots (slotTransform c a v) Δ (slotTransform c a g) := by
  have hs : slotSum a (shiftSlots v Δ g)=slotSum a g+(slotSum a v) • Δ := by
    simp only [slotSum,shiftSlots,smul_add,Finset.sum_add_distrib,smul_smul,smul_eq_mul]
    rw [Finset.sum_smul]
  ext i
  simp only [slotTransform,shiftSlots,hs,smul_add,sub_smul,smul_smul,smul_eq_mul]
  abel_nf

lemma slotTransform_scalar_mul (c s : ℝ) (a v : Fin k → ℝ) :
    slotTransform c a (fun i => s*v i)=fun i => s*slotTransform c a v i := by
  ext i
  simp only [slotTransform,slotSum,smul_eq_mul]
  have he : (∑i,a i*(s*v i))=s*∑i,a i*v i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

lemma inverse_shift_identity (a v : Fin k → ℝ) (ha : (∑i,a i^2)<1)
    (s : ℝ) (g : Fin k → Point d) (Δ : Point d) :
    slotTransform (sqrtCoefficient a) a
      (shiftSlots (fun i => s*slotTransform (inverseCoefficient a) a v i) Δ g)=
      shiftSlots v (s • Δ) (slotTransform (sqrtCoefficient a) a g) := by
  rw [slotTransform_add_shift,slotTransform_scalar_mul,slotTransform_inverse a ha]
  funext i
  simp only [shiftSlots,smul_smul]
  rw [mul_comm s (v i)]

lemma inverse_shift_energy (a v : Fin k → ℝ) (ha : (∑i,a i^2)≤1/4) (s : ℝ) :
    (∑i,(s*slotTransform (inverseCoefficient a) a v i)^2) ≤
      4*s^2*(∑i,v i^2) := by
  have h := inverse_slot_energy (E:=ℝ) a ha v
  simp only [Real.norm_eq_abs,sq_abs] at h
  simp_rw [mul_pow]
  rw [←Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg s)]

lemma measurable_slotTransform (c : ℝ) (a : Fin k → ℝ) :
    Measurable (slotTransform (E:=Point d) c a) := by
  unfold slotTransform slotSum
  fun_prop

theorem transformed_mean_equivariant {queryCount : ℕ}
    (M : Program (Point d × (Fin k → Point d)) d queryCount (Point d))
    {r : ℝ} (hr : r≠0) (v a : Fin k → ℝ) (ha : (∑i,a i^2)<1)
    (hM : ∀Δ,M.Equivariant (moveSeed (fun x => x+r • Δ) v Δ) id)
    (c : ℝ) (Δ : Point d) :
    (M.seedMap (fun z => (z.1,slotTransform (sqrtCoefficient a) a z.2))
      (measurable_fst.prodMk ((measurable_slotTransform _ _).comp measurable_snd))).Equivariant
      (moveSeed (fun x => x+c • Δ)
        (fun i => (c/r)*slotTransform (inverseCoefficient a) a v i) Δ) id := by
  apply (hM ((c/r) • Δ)).seedMap
  intro z
  apply Prod.ext
  · dsimp [moveSeed]
    rw [smul_smul]
    congr 2
    field_simp
  · dsimp [moveSeed]
    exact inverse_shift_identity a v ha (c/r) z.2 Δ

end SeedCompiler
end LogConcaveSampling

end

end

end

end OAI
