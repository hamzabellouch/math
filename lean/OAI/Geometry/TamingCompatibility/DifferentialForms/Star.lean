import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ContDiffApply
import OAI.Geometry.TamingCompatibility.DifferentialForms.FormPairing
import OAI.Geometry.TamingCompatibility.DifferentialForms.InnerJLeft

namespace OAI

noncomputable section
open scoped Manifold ContDiff
open scoped Manifold ContDiff Topology
open Filter Set
attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid
open scoped Manifold ContDiff Topology
open Bundle Filter Set
open Set
open Bundle Set Filter
open scoped Topology
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology
open scoped BigOperators
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open ContinuousAlternatingMap
namespace TamingCompatibility.HodgeThree
open RealInnerProductSpace FormMetric ExteriorForms ContinuousAlternatingMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def star (F : Form (E := E) 2) (α : Form (E := E) 3) : Form (E := E) 1 :=
  ofSubsingletonLIE (0 : Fin 1)
    (-(pairingCLM (E := E) (k := 3) α ∘L (volumeSquare F).curryLeft))

lemma star_apply (F : Form (E := E) 2) (α : Form (E := E) 3) (u : E) :
    star F α ![u] = -pairing α ((volumeSquare F).curryLeft u) := by
  rfl

section Frame
variable (b : OrthonormalBasis (Fin 4) ℝ E) (J : E →L[ℝ] E)
  (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
  (h2 : J (b 2) = b 3) (h3 : J (b 3) = -b 2)
  (F : Form (E := E) 2) (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫)

include h0 h1 h2 h3 hF in
omit [FiniteDimensional ℝ E] in
lemma volume_on_frame (i j : Fin 4) :
    (volumeSquare F).curryLeft (b i) (fun l => b (tripleIndices j l)) =
      if i = j then (-1 : ℝ) ^ (i : ℕ) else 0 := by
  have hb := orthonormal_iff_ite.mp b.orthonormal
  have ht : (volumeSquare F).curryLeft (b i) (fun l => b (tripleIndices j l)) =
      (volumeSquare F) ![b i, b (tripleIndices j 0), b (tripleIndices j 1),
        b (tripleIndices j 2)] := by
    change (volumeSquare F) (Matrix.vecCons (b i) (fun l => b (tripleIndices j l))) = _
    congr 1
    ext l
    fin_cases l <;> rfl
  rw [ht, volumeSquare_apply]
  fin_cases i <;> fin_cases j <;>
    simp [tripleIndices, hF, h0, h1, h2, h3, hb]
  norm_num

include h0 h1 h2 h3 hF in
lemma star_on_frame (α : Form (E := E) 3) (i : Fin 4) :
    star F α ![b i] = -((-1 : ℝ) ^ (i : ℕ) * α (fun l => b (tripleIndices i l))) := by
  rw [star_apply, pairing_three b]
  simp_rw [volume_on_frame b J h0 h1 h2 h3 F hF]
  simp [mul_comm]

include h0 h1 h2 h3 hF in
lemma star_injective_frame : Function.Injective (star F) := by
  intro α β h
  apply sharp_injective
  apply (tripleBasis b).repr.injective
  ext i
  have hi := congrArg (fun a : Form (E := E) 1 => a ![b i]) h
  rw [star_on_frame b J h0 h1 h2 h3 F hF,
    star_on_frame b J h0 h1 h2 h3 F hF] at hi
  have he := mul_left_cancel₀ (pow_ne_zero (i : ℕ) (by norm_num : (-1 : ℝ) ≠ 0)) (neg_injective hi)
  simpa only [tripleBasis_repr] using he
end Frame

lemma star_injective (J : E →ₗᵢ[ℝ] E) (hJ : ∀ u, J (J u) = -u)
    (hdim : Module.finrank ℝ E = 4) (F : Form (E := E) 2)
    (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫) : Function.Injective (star F) := by
  obtain ⟨b,h0,h1,h2,h3⟩ := UnitaryBasis.exists_unitary_basis J hJ hdim
  exact star_injective_frame b J.toContinuousLinearMap h0 h1 h2 h3 F hF

lemma star_zero (F : Form (E := E) 2) : star F 0 = 0 := by
  ext v
  have hv : v = ![v 0] := by ext i; fin_cases i; rfl
  rw [hv, star_apply]
  simp only [FormMetric.pairing, _root_.map_zero, inner_zero_left, neg_zero,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply]

lemma star_eq_zero (J : E →ₗᵢ[ℝ] E) (hJ : ∀ u, J (J u) = -u)
    (hdim : Module.finrank ℝ E = 4) (F : Form (E := E) 2)
    (hF : ∀ u v, F ![u,v] = ⟪J u,v⟫) (α : Form (E := E) 3) :
    star F α = 0 ↔ α = 0 := by
  rw [← star_zero F]
  exact (star_injective J hJ hdim F hF).eq_iff

end TamingCompatibility.HodgeThree

namespace TamingCompatibility.MetricModel
open RealInnerProductSpace
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

structure Metric where
  bilinear : E →L[ℝ] E →L[ℝ] ℝ
  symm : ∀ u v, bilinear u v = bilinear v u
  positive : ∀ u, u ≠ 0 → 0 < bilinear u u

variable {E}

def Model (_g : Metric E) := E

instance (g : Metric E) : AddCommGroup (Model g) := inferInstanceAs (AddCommGroup E)
instance (g : Metric E) : Module ℝ (Model g) := inferInstanceAs (Module ℝ E)
instance (g : Metric E) [FiniteDimensional ℝ E] : FiniteDimensional ℝ (Model g) :=
  inferInstanceAs (FiniteDimensional ℝ E)

instance core (g : Metric E) : InnerProductSpace.Core ℝ (Model g) where
  inner := fun u v => g.bilinear u v
  conj_inner_symm u v := by exact g.symm v u
  add_left u v w := by
    exact congrArg (fun f : E →L[ℝ] ℝ => f w) (map_add g.bilinear (u : E) (v : E))
  smul_left u v c := by
    change g.bilinear (c • (u : E)) (v : E) = c * g.bilinear u v
    exact congrArg (fun f : E →L[ℝ] ℝ => f v) (map_smul g.bilinear c (u : E))
  re_inner_nonneg u := by
    change 0 ≤ g.bilinear u u
    by_cases hu : u = 0
    · rw [hu]
      change 0 ≤ g.bilinear (0 : E) (0 : E)
      simp
    · exact (g.positive u hu).le
  definite u hu := by
    by_contra hn
    exact (ne_of_gt (g.positive u hn)) hu

instance (g : Metric E) : NormedAddCommGroup (Model g) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance (g : Metric E) : InnerProductSpace ℝ (Model g) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (Model g))

lemma model_inner (g : Metric E) (u v : Model g) : ⟪u,v⟫ = g.bilinear u v := rfl

def ofOriginal (g : Metric E) (u : E) : Model g := u

def toOriginal (g : Metric E) (u : Model g) : E := u

def linearEquiv (g : Metric E) : Model g ≃ₗ[ℝ] E := LinearEquiv.refl ℝ E

def equiv [FiniteDimensional ℝ E] (g : Metric E) : Model g ≃L[ℝ] E :=
  (linearEquiv g).toContinuousLinearEquiv

@[simp] lemma equiv_apply [FiniteDimensional ℝ E] (g : Metric E) (u : Model g) : equiv g u = u := rfl
@[simp] lemma equiv_symm_apply [FiniteDimensional ℝ E] (g : Metric E) (u : E) : (equiv g).symm u = u := rfl

lemma finrank_model [FiniteDimensional ℝ E] (g : Metric E) :
    Module.finrank ℝ (Model g) = Module.finrank ℝ E := (linearEquiv g).finrank_eq

def isometry (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v) :
    Model g →ₗᵢ[ℝ] Model g where
  toLinearMap :=
    { toFun := fun u => ofOriginal g (J (toOriginal g u))
      map_add' := J.map_add
      map_smul' := J.map_smul }
  norm_map' u := by
    have h : ‖ofOriginal g (J (toOriginal g u))‖ ^ 2 = ‖u‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq (x := ofOriginal g (J (toOriginal g u))),
        ← real_inner_self_eq_norm_sq (x := u)]
      exact hJ u u
    exact (sq_eq_sq₀ (norm_nonneg (ofOriginal g (J (toOriginal g u)))) (norm_nonneg u)).mp h

@[simp] lemma isometry_apply (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v) (u : Model g) :
    isometry g J hJ u = J u := rfl

end TamingCompatibility.MetricModel

end

end OAI
