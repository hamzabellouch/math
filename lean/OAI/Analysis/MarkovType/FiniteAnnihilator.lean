import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Tactic.Abel

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

open NormedSpace StrongDual

universe u

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local instance normStrongDualSubmodule (A : Submodule ℝ (StrongDual ℝ Y)) :
    Norm (StrongDual ℝ A) :=
  ContinuousLinearMap.hasOpNorm
    (𝕜 := ℝ) (𝕜₂ := ℝ) (E := A) (F := ℝ) (σ₁₂ := RingHom.id ℝ)

theorem finite_double_annihilator
    (E : Submodule ℝ Y) [FiniteDimensional ℝ E]
    (w : StrongDual ℝ (StrongDual ℝ Y))
    (hw : ∀ f : polarSubmodule ℝ E, w (f : StrongDual ℝ Y) = 0) :
    ∃ e : E, w = inclusionInDoubleDual ℝ Y (e : Y) := by
  classical
  let R : StrongDual ℝ Y →ₗ[ℝ] StrongDual ℝ E :=
    { toFun := fun f => f.comp E.subtypeL
      map_add' := by intro f g; ext e; rfl
      map_smul' := by intro c f; ext e; rfl }
  have hR : Function.Surjective R := by
    intro g
    obtain ⟨G, hG, _⟩ := exists_extension_norm_eq E g
    refine ⟨G, ?_⟩
    ext e
    exact hG e
  obtain ⟨S, hS⟩ :=
    R.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hR)
  have hS_apply (g : StrongDual ℝ E) : R (S g) = g := by
    exact congrArg (fun L : StrongDual ℝ E →ₗ[ℝ] StrongDual ℝ E => L g) hS
  let C : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
  let L : (E →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    w.toLinearMap.comp (S.comp C.toLinearMap)
  have hEval : Function.Surjective (Module.Dual.eval ℝ E) :=
    LinearMap.range_eq_top.mp (Module.Basis.ofVectorSpace ℝ E).eval_range
  obtain ⟨e, he⟩ := hEval L
  refine ⟨e, ?_⟩
  ext f
  have hker : f - S (R f) ∈ polarSubmodule ℝ E := by
    apply (mem_polarSubmodule ℝ E (f - S (R f))).mpr
    intro y hy
    have hvalue := congrArg (fun g : StrongDual ℝ E => g ⟨y, hy⟩) (hS_apply (R f))
    change S (R f) y = f y at hvalue
    change f y - S (R f) y = 0
    exact sub_eq_zero.mpr hvalue.symm
  have hzero : w f - w (S (R f)) = 0 := by
    simpa only [map_sub] using hw ⟨f - S (R f), hker⟩
  have heval := congrArg
    (fun q : (E →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ => q (R f).toLinearMap) he
  change f (e : Y) = w (S (R f)) at heval
  change w f = f (e : Y)
  exact (sub_eq_zero.mp hzero).trans heval.symm

theorem restriction_norm_eq_infDist_finite_image
    (E : Submodule ℝ Y) [FiniteDimensional ℝ E]
    (v : StrongDual ℝ (StrongDual ℝ Y)) :
    ‖(v.comp (polarSubmodule ℝ E).subtypeL : StrongDual ℝ (polarSubmodule ℝ E))‖ =
      Metric.infDist v
        (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)) := by
  let A := polarSubmodule ℝ E
  let r : StrongDual ℝ A := v.comp A.subtypeL
  have hnonempty :
      (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)).Nonempty :=
    ⟨inclusionInDoubleDual ℝ Y (0 : Y), ⟨0, rfl⟩⟩
  change ‖r‖ = _
  apply le_antisymm
  · apply (Metric.le_infDist hnonempty).mpr
    rintro z ⟨e, rfl⟩
    rw [dist_eq_norm v (inclusionInDoubleDual ℝ Y (e : Y))]
    change sInf {c : ℝ | 0 ≤ c ∧ ∀ f : A, ‖r f‖ ≤ c * ‖f‖} ≤
      ‖v - inclusionInDoubleDual ℝ Y (e : Y)‖
    refine csInf_le ⟨0, fun c hc => hc.1⟩
      ⟨ContinuousLinearMap.opNorm_nonneg
        (𝕜 := ℝ) (𝕜₂ := ℝ) (E := StrongDual ℝ Y) (F := ℝ)
        (σ₁₂ := RingHom.id ℝ) (v - inclusionInDoubleDual ℝ Y (e : Y)), ?_⟩
    intro f
    have hfe : (f : StrongDual ℝ Y) (e : Y) = 0 :=
      (mem_polarSubmodule ℝ E (f : StrongDual ℝ Y)).mp f.property (e : Y) e.property
    have hvalue : (v - inclusionInDoubleDual ℝ Y (e : Y)) (f : StrongDual ℝ Y) = r f := by
      change v (f : StrongDual ℝ Y) - (f : StrongDual ℝ Y) (e : Y) = v (f : StrongDual ℝ Y)
      rw [hfe, sub_zero]
    rw [← hvalue]
    exact (v - inclusionInDoubleDual ℝ Y (e : Y)).le_opNorm (f : StrongDual ℝ Y)
  · obtain ⟨V, hV, hnorm⟩ := exists_extension_norm_eq A r
    have hvanish : ∀ f : polarSubmodule ℝ E, (v - V) (f : StrongDual ℝ Y) = 0 := by
      intro f
      change v (f : StrongDual ℝ Y) - V (f : StrongDual ℝ Y) = 0
      exact sub_eq_zero.mpr (hV f).symm
    obtain ⟨e, he⟩ := finite_double_annihilator E (v - V) hvanish
    have hsub : v - inclusionInDoubleDual ℝ Y (e : Y) = V := by
      rw [← he]
      abel
    calc
      Metric.infDist v (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y))
          ≤ dist v (inclusionInDoubleDual ℝ Y (e : Y)) :=
        Metric.infDist_le_dist_of_mem ⟨e, rfl⟩
      _ = ‖V‖ := by rw [dist_eq_norm v (inclusionInDoubleDual ℝ Y (e : Y)), hsub]
      _ = ‖r‖ := hnorm

theorem exists_annihilating_functional
    (E : Submodule ℝ Y) [FiniteDimensional ℝ E]
    (v : StrongDual ℝ (StrongDual ℝ Y)) {d : ℝ} (hd : 0 < d)
    (hgap : d < Metric.infDist v (Set.range (inclusionInDoubleDual ℝ Y))) :
    ∃ f : StrongDual ℝ Y,
      ‖f‖ ≤ 1 ∧ (∀ e : E, f (e : Y) = 0) ∧ v f = d := by
  classical
  let A := polarSubmodule ℝ E
  let r : StrongDual ℝ A := v.comp A.subtypeL
  have hsubset :
      (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)) ⊆
        Set.range (inclusionInDoubleDual ℝ Y) := by
    rintro z ⟨e, rfl⟩
    exact ⟨(e : Y), rfl⟩
  have hnonempty :
      (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)).Nonempty :=
    ⟨inclusionInDoubleDual ℝ Y (0 : Y), ⟨0, rfl⟩⟩
  have hr : d < ‖r‖ := by
    calc
      d < Metric.infDist v (Set.range (inclusionInDoubleDual ℝ Y)) := hgap
      _ ≤ Metric.infDist v
          (Set.range fun e : E => inclusionInDoubleDual ℝ Y (e : Y)) :=
        Metric.infDist_le_infDist_of_subset hsubset hnonempty
      _ = ‖r‖ := (restriction_norm_eq_infDist_finite_image E v).symm
  have hex : ∃ g : A, ‖g‖ = 1 ∧ d < ‖r g‖ := by
    by_contra h
    have hbound : ‖r‖ ≤ d :=
      ContinuousLinearMap.opNorm_le_of_unit_norm hd.le fun g hg =>
        le_of_not_gt fun hgt => h ⟨g, hg, hgt⟩
    exact (not_le_of_gt hr) hbound
  obtain ⟨g, hg, hvalue⟩ := hex
  have habs : d < |v (g : StrongDual ℝ Y)| := by
    change d < ‖v (g : StrongDual ℝ Y)‖ at hvalue
    simpa only [Real.norm_eq_abs] using hvalue
  have hvg : v (g : StrongDual ℝ Y) ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at habs
    exact (not_lt_of_ge hd.le) habs
  refine ⟨(d / v (g : StrongDual ℝ Y)) • (g : StrongDual ℝ Y), ?_, ?_, ?_⟩
  · have hg' : ‖(g : StrongDual ℝ Y)‖ = 1 := hg
    rw [norm_smul (d / v (g : StrongDual ℝ Y)) (g : StrongDual ℝ Y),
      Real.norm_eq_abs, abs_div, abs_of_pos hd, hg', mul_one]
    apply (div_le_iff₀ (hd.trans habs)).mpr
    simpa only [one_mul] using habs.le
  · intro e
    have hge : (g : StrongDual ℝ Y) (e : Y) = 0 :=
      (mem_polarSubmodule ℝ E (g : StrongDual ℝ Y)).mp g.property (e : Y) e.property
    change (d / v (g : StrongDual ℝ Y)) * (g : StrongDual ℝ Y) (e : Y) = 0
    rw [hge, mul_zero]
  · rw [map_smul, smul_eq_mul]
    exact div_mul_cancel₀ d hvg

theorem exists_bidual_gap [CompleteSpace Y]
    (hNR : ¬ Function.Surjective (inclusionInDoubleDual ℝ Y)) :
    ∃ (v : StrongDual ℝ (StrongDual ℝ Y)) (d : ℝ),
      ‖v‖ ≤ 1 ∧ 0 < d ∧
      d < Metric.infDist v (Set.range (inclusionInDoubleDual ℝ Y)) := by
  classical
  let J := inclusionInDoubleDual ℝ Y
  obtain ⟨w, hw⟩ := not_forall.mp hNR
  have hw_range : w ∉ Set.range J := hw
  have hw0 : w ≠ 0 := by
    intro hzero
    apply hw_range
    exact ⟨0, by simp [J, hzero]⟩
  let v : StrongDual ℝ (StrongDual ℝ Y) := ‖w‖⁻¹ • w
  have hvnorm : ‖v‖ = 1 := by
    simpa only [v, RCLike.ofReal_real_eq_id, id_eq] using
      (norm_smul_inv_norm (𝕜 := ℝ) (x := w) hw0)
  have hv_range : v ∉ Set.range J := by
    rintro ⟨y, hy⟩
    apply hw_range
    refine ⟨‖w‖ • y, ?_⟩
    rw [map_smul, hy]
    dsimp only [v]
    have hcancel : ‖w‖ * ‖w‖⁻¹ = (1 : ℝ) :=
      mul_inv_cancel₀ ((norm_ne_zero_iff (a := w)).mpr hw0)
    rw [smul_smul, hcancel, one_smul]
  have hJ : Isometry J := (inclusionInDoubleDualLi ℝ (E := Y)).isometry
  have hclosed : IsClosed (Set.range J) :=
    hJ.isClosedEmbedding.isClosed_range
  have hnonempty : (Set.range J).Nonempty := ⟨J 0, ⟨0, rfl⟩⟩
  have hdist : 0 < Metric.infDist v (Set.range J) :=
    (hclosed.notMem_iff_infDist_pos hnonempty).mp hv_range
  exact ⟨v, Metric.infDist v (Set.range J) / 2, hvnorm.le,
    half_pos hdist, half_lt_self hdist⟩

end MarkovSuperreflexivity

end

end OAI
