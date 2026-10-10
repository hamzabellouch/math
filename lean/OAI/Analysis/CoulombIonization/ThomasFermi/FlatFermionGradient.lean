import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.FlatFermionAverage

namespace OAI

noncomputable section

namespace CoulombNeumann

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_FlatFermionGradient_scope

open MeasureTheory Filter
open scoped BigOperators Topology

open CoulombAtom
variable {N : ℕ}

lemma flatSignedPermutation_gradient
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (π : Equiv.Perm (Fin N))
    (s : Fin N → Fin 2) (x : (Fin N × Fin 3) → ℝ) (q : Fin N × Fin 3) :
    fderiv ℝ (flatSignedPermutation π f s) x (Pi.single q 1) =
      (((Equiv.Perm.sign π:ℤ):ℂ)) *
        fderiv ℝ (f (s ∘ π)) (flatPermutation π x) (Pi.single ((particlePermute π).symm q) 1) := by
  change fderiv ℝ (fun y => (((Equiv.Perm.sign π:ℤ):ℂ)) * f (s ∘ π) (flatPermutation π y)) x (Pi.single q 1) = _
  have h := (((hf (s ∘ π)).differentiable (by simp) (flatPermutation π x)).hasFDerivAt.comp x
    (flatPermutation π).hasFDerivAt).const_mul (((Equiv.Perm.sign π:ℤ):ℂ))
  simpa [flatSignedPermutation,ContinuousLinearMap.comp_apply,flatPermutation_single]
    using congrArg (fun L : ((Fin N × Fin 3) → ℝ) →L[ℝ] ℂ => L (Pi.single q 1)) h.fderiv

lemma flatFermionAverage_gradient
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (s : Fin N → Fin 2) (x : (Fin N × Fin 3) → ℝ) (q : Fin N × Fin 3) :
    fderiv ℝ (flatFermionAverage f s) x (Pi.single q 1) =
      finiteMean (fun π : Equiv.Perm (Fin N) =>
        fderiv ℝ (flatSignedPermutation π f s) x (Pi.single q 1)) := by
  change fderiv ℝ (fun y => (Fintype.card (Equiv.Perm (Fin N)):ℝ)⁻¹ •
    ∑ π : Equiv.Perm (Fin N), flatSignedPermutation π f s y) x (Pi.single q 1) = _
  have h := (HasFDerivAt.fun_sum (u := Finset.univ) (fun π _ =>
    ((flatSignedPermutation_contDiff hf π s).differentiable (by simp) x).hasFDerivAt)).const_smul
      (Fintype.card (Equiv.Perm (Fin N)):ℝ)⁻¹
  simpa [flatFermionAverage,finiteMean,Pi.smul_def] using congrArg
    (fun L : ((Fin N × Fin 3) → ℝ) →L[ℝ] ℂ => L (Pi.single q 1)) h.fderiv

lemma flatSignedPermutation_gradient_memLp
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (hg : ∀ s q, MemLp (fun x => fderiv ℝ (f s) x (Pi.single q 1)) 2)
    (π : Equiv.Perm (Fin N)) (s : Fin N → Fin 2) (q : Fin N × Fin 3) :
    MemLp (fun x => fderiv ℝ (flatSignedPermutation π f s) x (Pi.single q 1)) 2 := by
  simp_rw [flatSignedPermutation_gradient hf]
  exact ((hg (s ∘ π) ((particlePermute π).symm q)).comp_measurePreserving
    (flatPermutation_preserving π)).const_smul (((Equiv.Perm.sign π:ℤ):ℂ))

lemma flatFermionAverage_gradient_memLp
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (hg : ∀ s q, MemLp (fun x => fderiv ℝ (f s) x (Pi.single q 1)) 2)
    (s : Fin N → Fin 2) (q : Fin N × Fin 3) :
    MemLp (fun x => fderiv ℝ (flatFermionAverage f s) x (Pi.single q 1)) 2 := by
  simp_rw [flatFermionAverage_gradient hf]
  exact finiteMean_memLp (fun π => flatSignedPermutation_gradient_memLp hf hg π s q)

lemma flatSignedPermutation_kinetic
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s)) (π : Equiv.Perm (Fin N)) :
    (∑ s, ∑ q, ∫ x, ‖fderiv ℝ (flatSignedPermutation π f s) x (Pi.single q 1)‖^2) =
      ∑ s, ∑ q, ∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2 := by
  simp_rw [flatSignedPermutation_gradient hf,norm_mul,flat_complex_sign_norm,one_mul]
  calc
    _ = ∑ s, ∑ q, ∫ x, ‖fderiv ℝ (f (s ∘ π)) x
        (Pi.single ((particlePermute π).symm q) 1)‖^2 := by
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro q _
      exact (flatPermutation_preserving π).integral_comp
        (flatPermutation π).toHomeomorph.measurableEmbedding
        (fun x : (Fin N × Fin 3) → ℝ => ‖fderiv ℝ (f (s ∘ π)) x
          (Pi.single ((particlePermute π).symm q) 1)‖^2)
    _ = _ := by
      calc
        _ = ∑ s, ∑ q, ∫ x, ‖fderiv ℝ (f (s ∘ π)) x (Pi.single q 1)‖^2 := by
          apply Finset.sum_congr rfl
          intro s _
          exact (particlePermute π).symm.sum_comp
            (fun q => ∫ x, ‖fderiv ℝ (f (s ∘ π)) x (Pi.single q 1)‖^2)
        _ = _ := flat_sum_spins_permutation π (fun s => ∑ q, ∫ x,
          ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2)

lemma flatFermionAverage_kinetic_le
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, ContDiff ℝ 1 (f s))
    (hg : ∀ s q, MemLp (fun x => fderiv ℝ (f s) x (Pi.single q 1)) 2) :
    (∑ s, ∑ q, ∫ x, ‖fderiv ℝ (flatFermionAverage f s) x (Pi.single q 1)‖^2) ≤
      ∑ s, ∑ q, ∫ x, ‖fderiv ℝ (f s) x (Pi.single q 1)‖^2 := by
  simp_rw [flatFermionAverage_gradient hf]
  calc
    _ ≤ ∑ s, ∑ q, finiteMean (fun π => ∫ x,
        ‖fderiv ℝ (flatSignedPermutation π f s) x (Pi.single q 1)‖^2) := by
      apply Finset.sum_le_sum
      intro s _
      exact Finset.sum_le_sum (fun q _ => finiteMean_integral_norm_sq_le
        (fun π => flatSignedPermutation_gradient_memLp hf hg π s q))
    _ = finiteMean (fun π => ∑ s, ∑ q, ∫ x,
        ‖fderiv ℝ (flatSignedPermutation π f s) x (Pi.single q 1)‖^2) := by
      simp_rw [sum_finiteMean]
    _ = _ := by simp_rw [flatSignedPermutation_kinetic hf]; exact finiteMean_const _

end Work_FlatFermionGradient_scope

open MeasureTheory Filter
open scoped BigOperators Topology

open CoulombAtom
variable {N : ℕ}

def FlatAEAntisymmetric (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ) : Prop :=
  ∀ (π : Equiv.Perm (Fin N)) (s : Fin N → Fin 2),
    ∀ᵐ x, f (s ∘ π) (flatPermutation π x) = (((Equiv.Perm.sign π:ℤ):ℂ)) * f s x

lemma flatSignedPermutation_ae_fixed
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : FlatAEAntisymmetric f) (π : Equiv.Perm (Fin N)) (s : Fin N → Fin 2) :
    flatSignedPermutation π f s =ᵐ[volume] f s := by
  filter_upwards [hf π s] with x hx
  unfold flatSignedPermutation
  rw [hx,←mul_assoc]
  have hs : ((((Equiv.Perm.sign π:ℤ):ℂ)) * (((Equiv.Perm.sign π:ℤ):ℂ))) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]
  rw [hs,one_mul]

lemma flatFermionAverage_ae_fixed
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : FlatAEAntisymmetric f) (s : Fin N → Fin 2) :
    flatFermionAverage f s =ᵐ[volume] f s := by
  have ha : ∀ᵐ x, ∀ π : Equiv.Perm (Fin N), flatSignedPermutation π f s x = f s x :=
    ae_all_iff.mpr (fun π => flatSignedPermutation_ae_fixed hf π s)
  filter_upwards [ha] with x hx
  unfold flatFermionAverage
  simp_rw [hx]
  exact finiteMean_const _

lemma flatFermionAverage_ae_tendsto
    {u : ℕ → (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : FlatAEAntisymmetric f)
    (ht : ∀ s, ∀ᵐ x, Tendsto (fun n => u n s x) atTop (𝓝 (f s x)))
    (s : Fin N → Fin 2) :
    ∀ᵐ x, Tendsto (fun n => flatFermionAverage (u n) s x) atTop (𝓝 (f s x)) := by
  have hp (π : Equiv.Perm (Fin N)) : ∀ᵐ x,
      Tendsto (fun n => flatSignedPermutation π (u n) s x) atTop
        (𝓝 (flatSignedPermutation π f s x)) := by
    filter_upwards [(flatPermutation_preserving π).quasiMeasurePreserving.ae (ht (s ∘ π))] with x hx
    exact hx.const_mul _
  filter_upwards [ae_all_iff.mpr hp,flatFermionAverage_ae_fixed hf s] with x hx he
  rw [←he]
  exact finiteMean_tendsto hx

end CoulombNeumann

end

end OAI
