import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.MetricDensity
import OAI.Geometry.TamingCompatibility.DifferentialForms.Form
import OAI.Geometry.TamingCompatibility.DifferentialForms.TopForms

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
namespace TamingCompatibility.VolumeNormalization
open ContinuousAlternatingMap MetricModel MetricForms ExteriorForms MetricDensity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma gram_orthonormal_basis (g : Metric E) (b c : Module.Basis (Fin 4) ℝ E)
    (hc : ∀ i j, g.bilinear (c i) (c j) = if i = j then 1 else 0) :
    gram b g.bilinear = (c.toMatrix b).transpose * c.toMatrix b := by
  ext i j
  change g.bilinear (b i) (b j) = _
  conv_lhs => rw [← c.sum_repr (b i), ← c.sum_repr (b j)]
  simp only [_root_.map_sum,_root_.map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul,hc,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,
    Matrix.mul_apply,Matrix.transpose_apply,Module.Basis.toMatrix_apply]
  apply Finset.sum_congr rfl
  intro l _
  ring

omit [FiniteDimensional ℝ E] in
lemma abs_eval_of_orthonormal (g : Metric E) (b c : Module.Basis (Fin 4) ℝ E)
    (hc : ∀ i j, g.bilinear (c i) (c j) = if i = j then 1 else 0)
    (ν : MetricForms.Form E 4) (hν : ν c = 1) :
    |ν b| = density (gram b g.bilinear) := by
  rw [TopForms.eval_eq_det_mul c ν b,hν,one_mul,Module.Basis.det_apply,
    gram_orthonormal_basis g b c hc,density,Matrix.det_mul,Matrix.det_transpose]
  rw [← pow_two,Real.sqrt_sq_eq_abs]

lemma exists_metric_unitary_basis (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u, J (J u) = -u)
    (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) :
    ∃ b : Module.Basis (Fin 4) ℝ E,
      (∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0) ∧
      J (b 0) = b 1 ∧ J (b 1) = -b 0 ∧ J (b 2) = b 3 ∧ J (b 3) = -b 2 := by
  obtain ⟨b,h0,h1,h2,h3⟩ := UnitaryBasis.exists_unitary_basis (isometry g J horth) hJ
    ((finrank_model g).trans hdim)
  refine ⟨b.toBasis.map (linearEquiv g), ?_,h0,h1,h2,h3⟩
  intro i j
  exact orthonormal_iff_ite.mp b.orthonormal i j

omit [FiniteDimensional ℝ E] in
lemma volume_on_frame (g : Metric E) (J : E →L[ℝ] E)
    (b : Module.Basis (Fin 4) ℝ E)
    (hb : ∀ i j, g.bilinear (b i) (b j) = if i = j then 1 else 0)
    (h0 : J (b 0) = b 1) (h1 : J (b 1) = -b 0)
    (h2 : J (b 2) = b 3) (_h3 : J (b 3) = -b 2)
    (F : MetricForms.Form E 2) (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v) :
    volumeSquare F b = 1 := by
  have he : (b : Fin 4 → E) = ![b 0,b 1,b 2,b 3] := by ext i; fin_cases i <;> rfl
  rw [he,volumeSquare_apply]
  simp [hF,h0,h1,h2,hb]

lemma abs_volume_eq_density (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u, J (J u) = -u)
    (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form E 2)
    (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v)
    (b : Module.Basis (Fin 4) ℝ E) :
    |volumeSquare F b| = density (gram b g.bilinear) := by
  obtain ⟨c,hc,h0,h1,h2,h3⟩ := exists_metric_unitary_basis g J hJ horth hdim
  exact abs_eval_of_orthonormal g b c hc _ (volume_on_frame g J c hc h0 h1 h2 h3 F hF)

lemma volume_ne_zero (g : Metric E) (J : E →L[ℝ] E)
    (hJ : ∀ u, J (J u) = -u)
    (horth : ∀ u v, g.bilinear (J u) (J v) = g.bilinear u v)
    (hdim : Module.finrank ℝ E = 4) (F : MetricForms.Form E 2)
    (hF : ∀ u v, F ![u,v] = g.bilinear (J u) v) : volumeSquare F ≠ 0 := by
  obtain ⟨c,hc,h0,h1,h2,h3⟩ := exists_metric_unitary_basis g J hJ horth hdim
  intro h
  have he := volume_on_frame g J c hc h0 h1 h2 h3 F hF
  rw [h] at he
  change (0 : ℝ) = 1 at he
  norm_num at he

end TamingCompatibility.VolumeNormalization

end

end OAI
