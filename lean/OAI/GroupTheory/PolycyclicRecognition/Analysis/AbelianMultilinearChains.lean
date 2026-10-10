import OAI.GroupTheory.PolycyclicRecognition.Geometry.MultilinearBarBoundary
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.AbelianSecondHomologyPairing

namespace OAI

/-! # Multilinear evaluations of abelian bar chains in every degree -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {A V : Type} [CommGroup A] [AddCommGroup V]

def abelianMultilinearChains {n : ℕ}
    (F : MultilinearMap ℤ (fun _ : Fin n => Additive A) V) :
    ((Fin n → A) →₀ ℤ) →ₗ[ℤ] V :=
  Finsupp.linearCombination ℤ (fun v => F (Additive.ofMul ∘ v))

@[simp] theorem abelianMultilinearChains_single {n : ℕ}
    (F : MultilinearMap ℤ (fun _ : Fin n => Additive A) V) (v : Fin n → A) (c : ℤ) :
    abelianMultilinearChains F (Finsupp.single v c) = c • F (Additive.ofMul ∘ v) := by
  simp [abelianMultilinearChains]

theorem abelianMultilinearChains_boundary {n : ℕ}
    (F : MultilinearMap ℤ (fun _ : Fin n => Additive A) V) :
    (abelianMultilinearChains F).comp
      (groupHomology.inhomogeneousChains.d (integralTrivialCoefficient A) n).hom = 0 := by
  apply Finsupp.lhom_ext'
  intro v
  apply LinearMap.ext
  intro c
  change abelianMultilinearChains F
    (groupHomology.inhomogeneousChains.d (integralTrivialCoefficient A) n
      (Finsupp.single v c)) = 0
  rw [groupHomology.inhomogeneousChains.d_single]
  change abelianMultilinearChains F
    (Finsupp.single (fun i => v i.succ) c +
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j.val + 1) •
        Finsupp.single (Fin.contractNth j (· * ·) v) c) = 0
  simp only [map_add, map_sum, map_smul, abelianMultilinearChains_single]
  have h := multilinear_abelian_bar_boundary F (Additive.ofMul ∘ v)
  have he (j : Fin (n + 1)) :
      Additive.ofMul ∘ Fin.contractNth j (· * ·) v =
        Fin.contractNth j (· + ·) (Additive.ofMul ∘ v) :=
    Fin.comp_contractNth (· * ·) (· + ·) (fun _ _ => rfl) j v
  simp_rw [← he] at h
  have hc := congrArg (fun x : V => c • x) h
  rw [smul_add, Finset.smul_sum, smul_zero] at hc
  simpa only [Function.comp_def, smul_comm c] using hc

end PolycyclicRecognition

end

end OAI
