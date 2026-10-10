import Mathlib

namespace OAI

section
section
noncomputable section
namespace WeakMTWTransport

lemma posSemidef_apply_eq_zero_of_inner_eq_zero {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : E →L[ℝ] E} (hAs : ∀ u v, inner ℝ (A u) v=inner ℝ u (A v))
    (hA : ∀ v, 0 ≤ inner ℝ (A v) v) {v : E} (hv : inner ℝ (A v) v=0) : A v=0 := by
  have hquad (t : ℝ) :
      0 ≤ inner ℝ (A (A v)) (A v)*(t*t)+(2*inner ℝ (A v) (A v))*t+0 := by
    have H := hA (v+t • A v)
    simp only [map_add,map_smul,inner_add_left,inner_add_right,real_inner_smul_left,
      real_inner_smul_right,hv] at H
    rw [hAs (A v) v] at H
    nlinarith
  have hd := discrim_le_zero hquad
  simp only [discrim,mul_zero,sub_zero] at hd
  have hs : inner ℝ (A v) (A v)=0 := by nlinarith [sq_nonneg (inner ℝ (A v) (A v))]
  exact (inner_self_eq_zero).mp hs

lemma posDef_of_posSemidef_injective {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {A : E →L[ℝ] E} (hAs : ∀ u v, inner ℝ (A u) v=inner ℝ u (A v))
    (hA : ∀ v, 0 ≤ inner ℝ (A v) v) (hAi : Function.Injective A) :
    ∀ v, v≠0 → 0 < inner ℝ (A v) v := by
  intro v hv
  apply lt_of_le_of_ne (hA v)
  intro he
  have hz := posSemidef_apply_eq_zero_of_inner_eq_zero hAs hA he.symm
  exact hv (hAi (by simpa only [map_zero] using hz))

lemma injective_middle_of_det_comp_ne_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (hdim : Module.finrank ℝ E=Module.finrank ℝ F)
    (R : E →L[ℝ] F) (S : F →L[ℝ] E) (W : F →L[ℝ] F)
    (hdet : (S.comp (W.comp R)).det≠0) : Function.Injective W := by
  have hFi : Function.Injective (S.comp (W.comp R)) := by
    apply LinearMap.ker_eq_bot.mp
    exact not_not.mp (LinearMap.det_eq_zero_iff_ker_ne_bot.not.mp hdet)
  have hRi : Function.Injective R := by
    intro u v huv
    apply hFi
    simp only [ContinuousLinearMap.comp_apply,huv]
  have hRs : Function.Surjective R :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hRi
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  obtain ⟨u,rfl⟩ := hRs v
  change W (R u)=0 at hv
  have hu : u=0 := hFi (by
    change S (W (R u))=S (W (R 0))
    simp only [hv,map_zero])
  simp only [hu,map_zero]

end WeakMTWTransport

end

end

end

end OAI
