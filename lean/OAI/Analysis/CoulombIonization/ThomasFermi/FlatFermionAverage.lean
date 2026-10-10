import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.RetainedMeasurable
import OAI.Analysis.CoulombIonization.FieldAnalysis.FiniteMean

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter
open scoped BigOperators Topology

namespace CoulombNeumann
open CoulombAtom
variable {N : ℕ}

lemma flat_complex_sign_norm (π : Equiv.Perm (Fin N)) :
    ‖(((Equiv.Perm.sign π : ℤ) : ℂ))‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hs | hs <;> simp [hs]

lemma flat_sum_spins_permutation (π : Equiv.Perm (Fin N)) (f : (Fin N → Fin 2) → ℝ) :
    (∑ s : Fin N → Fin 2, f (s ∘ π)) = ∑ s, f s := by
  let e : (Fin N → Fin 2) ≃ (Fin N → Fin 2) :=
    { toFun := fun s => s ∘ π
      invFun := fun s => s ∘ π.symm
      left_inv := fun s => by funext i; simp
      right_inv := fun s => by funext i; simp }
  exact Equiv.sum_comp e f

def flatPermutation (π : Equiv.Perm (Fin N)) :
    ((Fin N × Fin 3) → ℝ) ≃L[ℝ] ((Fin N × Fin 3) → ℝ) :=
  realReindex (particlePermute π).symm

lemma flatPermutation_apply (π : Equiv.Perm (Fin N)) (x : (Fin N × Fin 3) → ℝ) :
    flatPermutation π x = x ∘ particlePermute π := by
  simp only [flatPermutation,realReindex_apply,Equiv.symm_symm]

lemma flatPermutation_preserving (π : Equiv.Perm (Fin N)) :
    MeasurePreserving (flatPermutation π) :=
  volume_measurePreserving_piCongrLeft (fun _ : Fin N × Fin 3 => ℝ) (particlePermute π).symm

lemma flatPermutation_mul (π σ : Equiv.Perm (Fin N)) (x : (Fin N × Fin 3) → ℝ) :
    flatPermutation σ (flatPermutation π x) = flatPermutation (π*σ) x := by
  funext q
  rcases q with ⟨i,a⟩
  simp [flatPermutation_apply,particlePermute,Function.comp_def]

lemma flatPermutation_single (π : Equiv.Perm (Fin N)) (q : Fin N × Fin 3) :
    flatPermutation π (Pi.single q 1) = Pi.single ((particlePermute π).symm q) 1 := by
  classical
  exact realReindex_single _ _

def flatSignedPermutation (π : Equiv.Perm (Fin N))
    (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ)
    (s : Fin N → Fin 2) (x : (Fin N × Fin 3) → ℝ) : ℂ :=
  (((Equiv.Perm.sign π:ℤ):ℂ)) * f (s ∘ π) (flatPermutation π x)

def flatFermionAverage (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ)
    (s : Fin N → Fin 2) (x : (Fin N × Fin 3) → ℝ) : ℂ :=
  finiteMean (fun π : Equiv.Perm (Fin N) => flatSignedPermutation π f s x)

lemma flatSignedPermutation_mul (π σ : Equiv.Perm (Fin N))
    (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ) :
    flatSignedPermutation π (flatSignedPermutation σ f) = flatSignedPermutation (π*σ) f := by
  funext s x
  simp only [flatSignedPermutation,flatPermutation_mul,Equiv.Perm.sign_mul,
    Units.val_mul,Int.cast_mul,Function.comp_def,Equiv.Perm.coe_mul]
  ring

lemma flatFermionAverage_fixed (π : Equiv.Perm (Fin N))
    (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ) :
    flatSignedPermutation π (flatFermionAverage f) = flatFermionAverage f := by
  funext s x
  change (((Equiv.Perm.sign π:ℤ):ℂ)) *
    ((Fintype.card (Equiv.Perm (Fin N)):ℝ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin N), flatSignedPermutation σ f (s ∘ π) (flatPermutation π x)) = _
  rw [mul_smul_comm,Finset.mul_sum]
  change (Fintype.card (Equiv.Perm (Fin N)):ℝ)⁻¹ •
    (∑ σ : Equiv.Perm (Fin N), flatSignedPermutation π (flatSignedPermutation σ f) s x) = _
  simp_rw [flatSignedPermutation_mul]
  unfold flatFermionAverage finiteMean
  congr 1
  exact Fintype.sum_equiv (Equiv.mulLeft π) _ _ (fun σ => rfl)

lemma flatFermionAverage_anti
    (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ) :
    FlatAntisymmetric (flatFermionAverage f) := by
  intro i j hij s x
  have hh := congrFun (congrFun (flatFermionAverage_fixed (Equiv.swap i j) f) s) x
  simp only [flatSignedPermutation,Equiv.Perm.sign_swap hij,Units.val_neg,
    Units.val_one,Int.cast_neg,Int.cast_one,neg_one_mul,flatPermutation_apply] at hh
  exact neg_eq_iff_eq_neg.mp hh

lemma flatSignedPermutation_contDiff
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    {n : WithTop ℕ∞} (hf : ∀ s, ContDiff ℝ n (f s)) (π : Equiv.Perm (Fin N)) (s : Fin N → Fin 2) :
    ContDiff ℝ n (flatSignedPermutation π f s) := by
  exact contDiff_const.mul ((hf (s ∘ π)).comp (flatPermutation π).contDiff)

lemma flatFermionAverage_contDiff
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    {n : WithTop ℕ∞} (hf : ∀ s, ContDiff ℝ n (f s)) (s : Fin N → Fin 2) :
    ContDiff ℝ n (flatFermionAverage f s) := by
  exact contDiff_const.smul (ContDiff.sum (fun π _ => flatSignedPermutation_contDiff hf π s))

lemma flatSignedPermutation_memLp
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, MemLp (f s) 2) (π : Equiv.Perm (Fin N)) (s : Fin N → Fin 2) :
    MemLp (flatSignedPermutation π f s) 2 := by
  exact ((hf (s ∘ π)).comp_measurePreserving (flatPermutation_preserving π)).const_smul
    (((Equiv.Perm.sign π:ℤ):ℂ))

lemma flatFermionAverage_memLp
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, MemLp (f s) 2) (s : Fin N → Fin 2) : MemLp (flatFermionAverage f s) 2 :=
  finiteMean_memLp (fun π => flatSignedPermutation_memLp hf π s)

lemma flatSignedPermutation_mass
    (f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ) (π : Equiv.Perm (Fin N)) :
    (∑ s, ∫ x, ‖flatSignedPermutation π f s x‖^2) = ∑ s, ∫ x, ‖f s x‖^2 := by
  simp only [flatSignedPermutation,norm_mul,flat_complex_sign_norm,one_mul]
  calc
    _ = ∑ s, ∫ x, ‖f (s ∘ π) x‖^2 := by
      apply Finset.sum_congr rfl
      intro s _
      exact (flatPermutation_preserving π).integral_comp
        (flatPermutation π).toHomeomorph.measurableEmbedding
        (fun x : (Fin N × Fin 3) → ℝ => ‖f (s ∘ π) x‖^2)
    _ = _ := flat_sum_spins_permutation π (fun s => ∫ x, ‖f s x‖^2)

lemma flatFermionAverage_mass_le
    {f : (Fin N → Fin 2) → ((Fin N × Fin 3) → ℝ) → ℂ}
    (hf : ∀ s, MemLp (f s) 2) :
    (∑ s, ∫ x, ‖flatFermionAverage f s x‖^2) ≤ ∑ s, ∫ x, ‖f s x‖^2 := by
  calc
    _ ≤ ∑ s, finiteMean (fun π => ∫ x, ‖flatSignedPermutation π f s x‖^2) := by
      exact Finset.sum_le_sum (fun s _ => finiteMean_integral_norm_sq_le
        (fun π => flatSignedPermutation_memLp hf π s))
    _ = finiteMean (fun π => ∑ s, ∫ x, ‖flatSignedPermutation π f s x‖^2) := by
      simp only [finiteMean,←Finset.smul_sum]
      rw [Finset.sum_comm]
    _ = _ := by simp_rw [flatSignedPermutation_mass]; exact finiteMean_const _

end CoulombNeumann

end

end OAI
