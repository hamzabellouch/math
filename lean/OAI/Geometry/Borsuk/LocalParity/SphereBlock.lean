import Mathlib
import OAI.Geometry.Borsuk.LocalParity.ChartRegular
import OAI.Geometry.Borsuk.LocalParity.LocalRegular

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace
section SphereBlock
variable {k : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)
noncomputable def sphereBlock (s : ℝ) (v : W) : E := WithLp.toLp 2 (Fin.cases s (fun i => v i))
lemma sphereBlock_zero (s : ℝ) (v : W) : sphereBlock s v 0 = s := rfl
lemma sphereBlock_succ (s : ℝ) (v : W) (i : Fin k) : sphereBlock s v i.succ = v i := rfl
lemma sphereBlock_continuous {X : Type*} [TopologicalSpace X] {s : X → ℝ} {v : X → W}
    (hs : Continuous s) (hv : Continuous v) : Continuous (fun x => sphereBlock (s x) (v x)) := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hs
  · exact (PiLp.continuous_apply 2 _ j).comp hv
lemma sphereBlock_neg (s : ℝ) (v : W) : sphereBlock (-s) (-v) = -sphereBlock s v := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl
lemma sphereBlock_eq_zero {s : ℝ} {v : W} (h : sphereBlock s v = 0) : s = 0 ∧ v = 0 := by
  refine ⟨congrArg (fun u : E => u 0) h,?_⟩
  ext i
  exact congrArg (fun u : E => u i.succ) h
noncomputable def sphereBlockModel (c : E) (e : W →ₗᵢ[ℝ] E) (D : W ≃L[ℝ] W) (u : E) : E :=
  sphereBlock ⟪c,u⟫ (D (e.toContinuousLinearMap.adjoint u))
lemma sphereBlockModel_continuous (c : E) (e : W →ₗᵢ[ℝ] E) (D : W ≃L[ℝ] W) : Continuous (sphereBlockModel c e D) :=
  sphereBlock_continuous (continuous_const.inner continuous_id) (D.continuous.comp (e.toContinuousLinearMap.adjoint.continuous))
lemma sphereBlockModel_odd (c : E) (e : W →ₗᵢ[ℝ] E) (D : W ≃L[ℝ] W) (u : E) :
    sphereBlockModel c e D (-u) = -sphereBlockModel c e D u := by
  simp only [sphereBlockModel,inner_neg_right,map_neg,sphereBlock_neg]
lemma hemisphereInverse_eq_zero_iff {c u : E} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    (hcu : 0 < ⟪c,u⟫) : hemisphereInverse c e u = 0 ↔ u = c := by
  constructor
  · intro hv
    have hh := hemisphereChart_inverse c e hc he hes hu hcu
    rw [hv,hemisphereChart_zero hc] at hh
    exact hh.symm
  · intro hh
    subst u
    rw [hemisphereInverse,adjoint_normal c e he,smul_zero]
lemma sphereBlockModel_ne_zero {c u : E} (hc : ‖c‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    (D : W ≃L[ℝ] W) (hu : u ≠ 0) : sphereBlockModel c e D u ≠ 0 := by
  intro hz
  obtain ⟨h1,h2⟩ := sphereBlock_eq_zero hz
  have he0 : e.toContinuousLinearMap.adjoint u = 0 := D.injective (h2.trans D.map_zero.symm)
  have hd := frame_decomposition c e hc he hes u
  rw [h1,he0,zero_smul,map_zero,sub_zero] at hd
  exact hu hd.symm
lemma sphereBlockModel_ray {c u : E} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    (D : W ≃L[ℝ] W) {b : ℝ} (hb : 0 < b)
    (h : sphereBlockModel c e D u = b • sphereBlock 1 (0 : W)) : u = c := by
  have hs : ⟪c,u⟫ = b := by
    have hh := congrArg (fun v : E => v 0) h
    simpa only [sphereBlockModel,sphereBlock_zero,PiLp.smul_apply,mul_one,smul_eq_mul] using hh
  have ht : D (e.toContinuousLinearMap.adjoint u) = 0 := by
    ext i
    have hh := congrArg (fun v : E => v i.succ) h
    simpa only [sphereBlockModel,sphereBlock_succ,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul,mul_zero] using hh
  apply (hemisphereInverse_eq_zero_iff hc hu e he hes (hs ▸ hb)).mp
  rw [hemisphereInverse,D.injective (ht.trans D.map_zero.symm),smul_zero]
lemma sphereBlock_mix_nonzero {c w u : E} (e : W →ₗᵢ[ℝ] E) (D : W ≃L[ℝ] W)
    (g : W) (hw : 0 < ⟪w,u⟫) (hc : 0 < ⟪c,u⟫) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    (1-t) • sphereBlock ⟪w,u⟫ g + t • sphereBlockModel c e D u ≠ 0 := by
  intro hz
  have hh := congrArg (fun v : E => v 0) hz
  simp only [PiLp.add_apply,PiLp.smul_apply,sphereBlockModel,sphereBlock_zero,smul_eq_mul,PiLp.zero_apply] at hh
  rcases lt_or_eq_of_le ht.2 with hl | rfl
  · have hp : 0 < (1-t)*⟪w,u⟫ := mul_pos (sub_pos.mpr hl) hw
    have hn : 0 ≤ t*⟪c,u⟫ := mul_nonneg ht.1 hc.le
    linarith
  · linarith
lemma sphereBlock_mix_ray {c w u : E} (hc : ‖c‖ = 1) (hu : ‖u‖ = 1)
    (e : W →ₗᵢ[ℝ] E) (he : ∀ v, ⟪c,e v⟫ = 0) (hes : ∀ u, ⟪c,u⟫ = 0 → ∃ v, e v = u)
    (D : W ≃L[ℝ] W) (g : W) (hcu : 0 < ⟪c,u⟫)
    (hr : hemisphereInverse c e u ≠ 0 → 0 < ⟪hemisphereInverse c e u,D.symm g⟫)
    {t b : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hm : (1-t) • sphereBlock ⟪w,u⟫ g + t • sphereBlockModel c e D u = b • sphereBlock 1 (0 : W)) :
    u = c := by
  have hz : (1-t) • g + t • D (e.toContinuousLinearMap.adjoint u) = 0 := by
    ext i
    have hh := congrArg (fun v : E => v i.succ) hm
    simpa only [PiLp.add_apply,PiLp.smul_apply,sphereBlockModel,sphereBlock_succ,PiLp.zero_apply,smul_eq_mul,mul_zero] using hh
  have hb : hemisphereInverse c e u ≠ 0 → 0 < ⟪hemisphereInverse c e u,e.toContinuousLinearMap.adjoint u⟫ := by
    intro hv
    have hvv : e.toContinuousLinearMap.adjoint u = ⟪c,u⟫ • hemisphereInverse c e u := by
      rw [hemisphereInverse,smul_smul,mul_inv_cancel₀ (ne_of_gt hcu),one_smul]
    rw [hvv,inner_smul_right,real_inner_self_eq_norm_sq]
    exact mul_pos hcu (sq_pos_of_pos (norm_pos_iff.mpr hv))
  have hv := regular_mixed_zero D (g := fun _ : W => g) (v := hemisphereInverse c e u)
    (b := e.toContinuousLinearMap.adjoint u) hr hb (show (0:ℝ)<1 from zero_lt_one) ht (by simpa only [one_smul] using hz)
  exact (hemisphereInverse_eq_zero_iff hc hu e he hes hcu).mp hv
end SphereBlock
end BorsukNine

end OAI
