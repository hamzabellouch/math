import Mathlib
import OAI.Combinatorics.RamseyFive.Geometry.Q

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace SharpRamseyFive.ProjectiveIncidence
open Module
open scoped LinearAlgebra.Projectivization Classical
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

noncomputable def projectiveEquiv (e : V ≃ₗ[K] W) : ℙ K V ≃ ℙ K W :=
  Equiv.ofBijective (Projectivization.map e.toLinearMap e.injective) ⟨
    Projectivization.map_injective e.toLinearMap e.injective, by
      intro p
      refine ⟨Projectivization.mk K (e.symm p.rep) (fun h => p.rep_nonzero ?_), ?_⟩
      · have he := congrArg e h
        simpa only [e.apply_symm_apply,map_zero] using he
      · rw [Projectivization.map_mk]
        simp only [LinearEquiv.coe_coe,e.apply_symm_apply,Projectivization.mk_rep]⟩

lemma incident_mk_right (a : ℙ K V) (f : Module.Dual K V) (hf : f ≠ 0) :
    Incident a (Projectivization.mk K f hf) ↔ f a.rep = 0 := by
  obtain ⟨c,hc⟩ := Projectivization.exists_smul_eq_mk_rep K f hf
  rw [incident_iff,←hc]
  simp only [LinearMap.smul_apply,Units.smul_def,smul_eq_mul,mul_eq_zero,
    Units.ne_zero,false_or]

variable [FiniteDimensional K V]

lemma incident_eval (a : ℙ K V) (b : ℙ K (Module.Dual K V)) :
    Incident b (projectiveEquiv (Module.evalEquiv K V) a) ↔ Incident a b := by
  change Incident b (Projectivization.map (Module.evalEquiv K V).toLinearMap (Module.evalEquiv K V).injective a) ↔ _
  conv_lhs => rw [←a.mk_rep,Projectivization.map_mk,incident_mk_right]
  rw [incident_iff]
  rfl

variable [Finite K] [Fintype (ℙ K V)] [Fintype (ℙ K (Module.Dual K V))]

noncomputable def weightOnPencil (w : ℙ K (Module.Dual K V) → ℝ) (a : ℙ K V) : ℝ :=
  ∑ b, incidenceEntry a b * w b

omit [Finite K] [Fintype (ℙ K V)] in
lemma weightOnPencil_eq (w : ℙ K (Module.Dual K V) → ℝ) (a : ℙ K V) :
    weightOnPencil w a = weightOnHyperplane w (projectiveEquiv (Module.evalEquiv K V) a) := by
  unfold weightOnPencil weightOnHyperplane
  apply Finset.sum_congr rfl
  intro b _
  simp only [incidenceEntry,incident_eval]

theorem pencil_variance {d : ℕ} (hdim : finrank K V = d+1) (hd : 1 ≤ d)
    (w : ℙ K (Module.Dual K V) → ℝ) :
    ∑ a, (weightOnPencil w a -
      ((Q (Nat.card K) (d-1):ℝ)/Q (Nat.card K) d)*(∑ b,w b))^2 ≤
      (Nat.card K:ℝ)^(d-1)*∑ b,w b^2 := by
  let : Finite (Module.Dual K (Module.Dual K V)) := Module.finite_of_finite K
  let := Fintype.ofFinite (ℙ K (Module.Dual K (Module.Dual K V)))
  have hd' : finrank K (Module.Dual K V) = d+1 := by simpa only [Subspace.dual_finrank_eq] using hdim
  have h := incidence_variance hd' hd w
  rw [←(projectiveEquiv (Module.evalEquiv K V)).sum_comp] at h
  simpa only [←weightOnPencil_eq] using h

end SharpRamseyFive.ProjectiveIncidence

end OAI
