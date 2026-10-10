import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.GlobalDensityBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter Complex TopologicalSpace
open scoped Topology InnerProductSpace ENNReal
open MeasureTheory Filter Complex
open scoped Topology BigOperators ComplexConjugate FourierTransform SchwartzMap ENNReal
namespace CoulombPauli

section
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B}

def pull (f : A → B) (hf : MeasurePreserving f μ ν) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ f hf).toContinuousLinearMap

lemma pull_ae (f : A → B) (hf : MeasurePreserving f μ ν) (ψ : Lp ℂ 2 ν) :
    pull f hf ψ =ᵐ[μ] (fun x => ψ (f x)) := Lp.coeFn_compMeasurePreserving ψ hf

lemma pull_norm (f : A → B) (hf : MeasurePreserving f μ ν) (ψ : Lp ℂ 2 ν) :
    ‖pull f hf ψ‖ = ‖ψ‖ := Lp.norm_compMeasurePreserving ψ hf

lemma pull_inner (f : A → B) (hf : MeasurePreserving f μ ν) (ψ φ : Lp ℂ 2 ν) :
    ⟪pull f hf ψ, pull f hf φ⟫_ℂ = ⟪ψ,φ⟫_ℂ :=
  (Lp.compMeasurePreservingₗᵢ ℂ f hf).inner_map_map ψ φ

lemma pull_involution (f : A → A) (hf : MeasurePreserving f μ μ)
    (hinv : Function.Involutive f) (ψ : Lp ℂ 2 μ) : pull f hf (pull f hf ψ) = ψ := by
  apply Lp.ext
  filter_upwards [pull_ae f hf (pull f hf ψ), hf.quasiMeasurePreserving.ae (pull_ae f hf ψ)] with x h1 h2
  rw [h1,h2,hinv]

end

section EquivPull
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
  {μ : Measure A} {ν : Measure B}
lemma pull_symm (e : A ≃ᵐ B) (he : MeasurePreserving e μ ν) (ψ : Lp ℂ 2 μ) :
    pull e he (pull e.symm he.symm ψ) = ψ := by
  apply Lp.ext
  filter_upwards [pull_ae e he (pull e.symm he.symm ψ),
    he.quasiMeasurePreserving.ae (pull_ae e.symm he.symm ψ)] with x hx hx'
  rw [hx,hx',e.symm_apply_apply]

lemma pull_injective (f : A → B) (hf : MeasurePreserving f μ ν) :
    Function.Injective (pull f hf) := by
  change Function.Injective (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ f hf)
  exact (Lp.compMeasurePreservingₗᵢ (E := ℂ) (p := 2) ℂ f hf).injective
end EquivPull
section

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

abbrev configMeasure (N : ℕ) (μ : Measure A) := Measure.pi (fun _ : Fin N => μ)
abbrev sectorL2 (N : ℕ) (μ : Measure A) := Lp ℂ 2 (configMeasure N μ)

lemma memLp_pure {N : ℕ} (u : Fin N → Lp ℂ 2 μ) :
    MemLp (fun x : Fin N → A => ∏ i, u i (x i)) 2 (configMeasure N μ) := by
  have hm : AEStronglyMeasurable (fun x : Fin N → A => ∏ i, u i (x i)) (configMeasure N μ) :=
    Finset.aestronglyMeasurable_fun_prod _ fun i _ =>
      (Lp.aestronglyMeasurable (u i)).comp_quasiMeasurePreserving
        (Measure.quasiMeasurePreserving_eval (fun _ : Fin N => μ) i)
  apply (memLp_two_iff_integrable_sq_norm hm).2
  simpa only [norm_prod, ← Finset.prod_pow] using
    Integrable.fintype_prod (fun i =>
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (u i))).1 (Lp.memLp (u i)))

def pureTensor {N : ℕ} (u : Fin N → Lp ℂ 2 μ) : sectorL2 N μ :=
  (memLp_pure u).toLp _

lemma pureTensor_ae {N : ℕ} (u : Fin N → Lp ℂ 2 μ) :
    pureTensor u =ᵐ[configMeasure N μ] (fun x => ∏ i, u i (x i)) := MemLp.coeFn_toLp _

def splitAt {N : ℕ} (i : Fin (N+1)) : (Fin (N+1) → A) ≃ᵐ A × (Fin N → A) :=
  MeasurableEquiv.piFinSuccAbove (fun _ => A) i

lemma splitAt_preserving {N : ℕ} (i : Fin (N+1)) :
    MeasurePreserving (splitAt (A := A) i) (configMeasure (N+1) μ) (μ.prod (configMeasure N μ)) :=
  measurePreserving_piFinSuccAbove (fun _ => μ) i

lemma pureTensor_split {N : ℕ} (u : Fin (N+1) → Lp ℂ 2 μ) (i : Fin (N+1)) :
    pull (splitAt i) (splitAt_preserving i)
      (tensor (u i) (pureTensor (fun j => u (i.succAbove j)))) = pureTensor u := by
  apply Lp.ext
  filter_upwards [pull_ae (splitAt i) (splitAt_preserving i)
      (tensor (u i) (pureTensor (fun j => u (i.succAbove j)))),
    (splitAt_preserving i).quasiMeasurePreserving.ae
      (tensor_ae (u i) (pureTensor (fun j => u (i.succAbove j)))),
    (splitAt_preserving i).quasiMeasurePreserving.ae
      (Measure.quasiMeasurePreserving_snd.ae (pureTensor_ae (fun j => u (i.succAbove j)))),
    pureTensor_ae u] with x h1 h2 h3 h4
  rw [h1,h2,h4]
  dsimp only [splitAt, MeasurableEquiv.piFinSuccAbove_apply] at h3 ⊢
  rw [h3]
  exact (Fin.prod_univ_succAbove (fun j => u j (x j)) i).symm

lemma pureTensor_zero_inner (ψ : sectorL2 0 μ)
    (hψ : ∀ u : Fin 0 → Lp ℂ 2 μ, ⟪pureTensor u,ψ⟫_ℂ = 0) : ψ = 0 := by
  let u : Fin 0 → Lp ℂ 2 μ := Fin.elim0
  have he : ⟪pureTensor u, ψ⟫_ℂ = ψ default := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, ψ x ∂configMeasure 0 μ := by
        apply integral_congr_ae
        filter_upwards [pureTensor_ae u] with x hx
        simp only [hx, Finset.univ_eq_empty, Finset.prod_empty, inner, star_one, mul_one]
      _ = ψ default := by simp [integral_unique, Measure.real, configMeasure]
  apply Lp.ext
  have hv := he.symm.trans (hψ u)
  filter_upwards [Lp.coeFn_zero ℂ 2 (configMeasure 0 μ)] with x hx
  rw [hx]
  simpa only [Subsingleton.elim x default, Pi.zero_apply] using hv

lemma eq_zero_of_pureTensor_orthogonal (N : ℕ) (ψ : sectorL2 N μ)
    (hψ : ∀ u : Fin N → Lp ℂ 2 μ, ⟪pureTensor u,ψ⟫_ℂ = 0) : ψ = 0 := by
  induction N with
  | zero => exact pureTensor_zero_inner ψ hψ
  | succ N ih =>
    let Φ := pull (splitAt (A := A) (0 : Fin (N+1))).symm (splitAt_preserving (μ := μ) 0).symm ψ
    have hΦ : Φ = 0 := by
      apply eq_zero_of_tensor_orthogonal
      intro u v
      have hv : (tensorLeft u).adjoint Φ = 0 := by
        apply ih
        intro w
        rw [ContinuousLinearMap.adjoint_inner_right, tensorLeft_apply]
        have he := pull_inner (splitAt (A := A) (0 : Fin (N+1)))
          (splitAt_preserving (μ := μ) 0) (tensor u (pureTensor w)) Φ
        have ht : pull (splitAt (A := A) (0 : Fin (N+1))) (splitAt_preserving (μ := μ) 0)
            (tensor u (pureTensor w)) = pureTensor (Fin.cons u w) := by
          simpa using pureTensor_split (Fin.cons u w) 0
        rw [ht, show pull (splitAt (A := A) (0 : Fin (N+1))) (splitAt_preserving (μ := μ) 0) Φ = ψ from
          pull_symm _ _ ψ, hψ] at he
        exact he.symm
      rw [← tensorLeft_apply, ← ContinuousLinearMap.adjoint_inner_right, hv, inner_zero_right]
    have he := congrArg (pull (splitAt (A := A) (0 : Fin (N+1))) (splitAt_preserving (μ := μ) 0)) hΦ
    rw [show pull (splitAt (A := A) (0 : Fin (N+1))) (splitAt_preserving (μ := μ) 0) Φ = ψ from
      pull_symm _ _ ψ, map_zero] at he
    exact he

end

variable {A : Type*} [MeasurableSpace A] {μ : Measure A} [SigmaFinite μ]

lemma continuousLinearMap_ext_pure {N : ℕ}
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (F G : sectorL2 N μ →L[ℂ] H)
    (h : ∀ u : Fin N → Lp ℂ 2 μ, F (pureTensor u) = G (pureTensor u)) : F = G := by
  have hz (w : H) : (F-G).adjoint w = 0 := by
    apply eq_zero_of_pureTensor_orthogonal
    intro u
    rw [ContinuousLinearMap.adjoint_inner_right]
    simp only [sub_apply, h u, sub_self, inner_zero_left]
  ext x
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  change ⟪(F-G) x, (F-G) x⟫_ℂ = 0
  rw [← ContinuousLinearMap.adjoint_inner_right, hz, inner_zero_right]

omit [SigmaFinite μ] in
lemma pull_adjoint_pull {B : Type*} [MeasurableSpace B] {ν : Measure B}
    (f : A → B) (hf : MeasurePreserving f μ ν) (ψ : Lp ℂ 2 ν) :
    (pull f hf).adjoint (pull f hf ψ) = ψ := by
  apply ext_inner_left ℂ
  intro φ
  rw [ContinuousLinearMap.adjoint_inner_right, pull_inner]

def insertOrbital {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ) :
    sectorL2 N μ →L[ℂ] sectorL2 (N+1) μ :=
  (pull (splitAt i) (splitAt_preserving i)).comp (tensorLeft u)

def projectOrbital {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ) :
    sectorL2 (N+1) μ →L[ℂ] sectorL2 (N+1) μ :=
  (insertOrbital i u).comp (insertOrbital i u).adjoint

lemma insertOrbital_adjoint_pure {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ)
    (f : Fin (N+1) → Lp ℂ 2 μ) :
    (insertOrbital i u).adjoint (pureTensor f) = ⟪u,f i⟫_ℂ • pureTensor (fun j => f (i.succAbove j)) := by
  rw [← pureTensor_split f i]
  dsimp only [insertOrbital]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply,
    pull_adjoint_pull, tensorLeft_adjoint_tensor]

lemma insertOrbital_pure {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ)
    (f : Fin (N+1) → Lp ℂ 2 μ) :
    insertOrbital i u (pureTensor (fun j => f (i.succAbove j))) = pureTensor (Function.update f i u) := by
  simpa only [insertOrbital, ContinuousLinearMap.comp_apply, tensorLeft_apply, Function.update_self, Function.update_of_ne (Fin.succAbove_ne i _)] using
    pureTensor_split (Function.update f i u) i

lemma projectOrbital_pure {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ)
    (f : Fin (N+1) → Lp ℂ 2 μ) :
    projectOrbital i u (pureTensor f) = ⟪u,f i⟫_ℂ • pureTensor (Function.update f i u) := by
  dsimp only [projectOrbital, ContinuousLinearMap.comp_apply]
  rw [insertOrbital_adjoint_pure, map_smul, insertOrbital_pure]

def permCoords {N : ℕ} (π : Equiv.Perm (Fin N)) : (Fin N → A) ≃ᵐ (Fin N → A) :=
  MeasurableEquiv.piCongrLeft (fun _ => A) π.symm

lemma permCoords_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (x : Fin N → A) :
    permCoords π x = x ∘ π := by
  ext j
  simp [permCoords, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

lemma permCoords_preserving {N : ℕ} (π : Equiv.Perm (Fin N)) :
    MeasurePreserving (permCoords (A := A) π) (configMeasure N μ) (configMeasure N μ) :=
  measurePreserving_piCongrLeft (fun _ : Fin N => μ) π.symm

def permute {N : ℕ} (π : Equiv.Perm (Fin N)) : sectorL2 N μ →L[ℂ] sectorL2 N μ :=
  pull (permCoords π) (permCoords_preserving π)

lemma permute_norm {N : ℕ} (π : Equiv.Perm (Fin N)) (ψ : sectorL2 N μ) :
    ‖permute π ψ‖ = ‖ψ‖ := pull_norm _ _ _

lemma permute_pure {N : ℕ} (π : Equiv.Perm (Fin N)) (f : Fin N → Lp ℂ 2 μ) :
    permute π (pureTensor f) = pureTensor (f ∘ π.symm) := by
  apply Lp.ext
  filter_upwards [pull_ae (permCoords π) (permCoords_preserving π) (pureTensor f),
    (permCoords_preserving π).quasiMeasurePreserving.ae (pureTensor_ae f),
    pureTensor_ae (f ∘ π.symm)] with x h1 h2 h3
  change pull (permCoords π) (permCoords_preserving π) (pureTensor f) x = _
  rw [h1,h2,h3,permCoords_apply]
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
    Equiv.prod_comp π (fun j => f (π.symm j) (x j))

lemma projectOrbital_covariance {N : ℕ} (i : Fin (N+1)) (u : Lp ℂ 2 μ)
    (π : Equiv.Perm (Fin (N+1))) :
    (permute π).comp (projectOrbital i u) = (projectOrbital (π i) u).comp (permute π) := by
  classical
  apply continuousLinearMap_ext_pure
  intro f
  simp only [ContinuousLinearMap.comp_apply, projectOrbital_pure, map_smul, permute_pure,
    Function.comp_apply, Equiv.symm_apply_apply]
  congr 2
  exact Function.update_comp_equiv f π.symm i u

end CoulombPauli

end

end OAI
