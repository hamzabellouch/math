import Mathlib
import OAI.Analysis.Commutator.NormalGNS

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology ComplexOrder NNReal

open Filter

namespace Kadison.NormalGNS

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma wot_tendsto_of_dense {ι B : Type*} {l : Filter ι} (v : B → E) (hv : DenseRange v)
    (T : ι → E →L[ℂ] E) (S : E →L[ℂ] E) (C : ℝ≥0) (hT : ∀ i,‖T i‖≤C)
    (hlim : ∀ a b,Tendsto (fun i => inner ℂ (v a) (T i (v b))) l
      (𝓝 (inner ℂ (v a) (S (v b))))) (x y : E) :
    Tendsto (fun i => inner ℂ x (T i y)) l (𝓝 (inner ℂ x (S y))) := by
  have hfirst (b : B) (x : E) : Tendsto (fun i => inner ℂ x (T i (v b))) l
      (𝓝 (inner ℂ x (S (v b)))) := by
    have hequi : Equicontinuous (fun i x => inner ℂ x (T i (v b))) := by
      apply (LipschitzWith.uniformEquicontinuous _ (C*‖v b‖₊) ?_).equicontinuous
      intro i
      apply LipschitzWith.of_dist_le_mul
      intro x y
      rw [dist_eq_norm,←inner_sub_left]
      apply (norm_inner_le_norm _ _).trans
      have hn : ‖T i (v b)‖≤C*‖v b‖ :=
        (T i).le_opNorm (v b) |>.trans (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
      simpa only [NNReal.coe_mul,coe_nnnorm,dist_eq_norm,mul_comm] using
        mul_le_mul_of_nonneg_left hn (norm_nonneg (x-y))
    exact (hequi x).tendsto_of_mem_closure
      ((continuous_id.inner continuous_const).continuousAt.mono_left inf_le_left)
      (by rintro _ ⟨a,rfl⟩; exact hlim a b) (hv x)
  have hequi : Equicontinuous (fun i y => inner ℂ x (T i y)) := by
    apply (LipschitzWith.uniformEquicontinuous _ (‖x‖₊*C) ?_).equicontinuous
    intro i
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [dist_eq_norm,←inner_sub_right,←map_sub]
    apply (norm_inner_le_norm _ _).trans
    have hn : ‖T i (y-z)‖≤C*‖y-z‖ :=
      (T i).le_opNorm (y-z) |>.trans (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg _))
    simpa only [NNReal.coe_mul,coe_nnnorm,dist_eq_norm,mul_assoc] using
      mul_le_mul_of_nonneg_left hn (norm_nonneg x)
  exact (hequi y).tendsto_of_mem_closure
    ((continuous_const.inner S.continuous).continuousAt.mono_left inf_le_left)
    (by rintro _ ⟨b,rfl⟩; exact hfirst b x) (hv y)

open TracialGNS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : VonNeumannAlgebra H) (τ : M →ₚ[ℂ] ℂ)

lemma tendsto_gns (hnormal : BoundedWOTContinuous M τ)
    {ι : Type*} {l : Filter ι} (a : ι → M) (b : M) (C : ℝ≥0)
    (ha : ∀ i,‖a i‖≤C) (hb : ‖b‖≤C)
    (hlim : ∀ x y,Tendsto (fun i => inner ℂ ((a i:H →L[ℂ] H) x) y) l
      (𝓝 (inner ℂ ((b:H →L[ℂ] H) x) y))) (x y : τ.GNS) :
    Tendsto (fun i => inner ℂ x (τ.gnsStarAlgHom (a i) y)) l
      (𝓝 (inner ℂ x (τ.gnsStarAlgHom b y))) := by
  apply wot_tendsto_of_dense (algebraVector τ) (algebraVector_dense τ)
    (fun i => τ.gnsStarAlgHom (a i)) (τ.gnsStarAlgHom b) C
    (fun i => (NonUnitalStarAlgHom.norm_apply_le τ.gnsStarAlgHom (a i)).trans (ha i))
  intro c d
  have he : ∀ z : M, inner ℂ (algebraVector τ c) (τ.gnsStarAlgHom z (algebraVector τ d))=
      τ (star c*z*d) := by
    intro z
    have hz : τ.gnsStarAlgHom z (algebraVector τ d)=algebraVector τ (z*d) := left_coe τ z d
    rw [hz,inner_algebraVector,mul_assoc]
  simp_rw [he]
  apply tendsto_trace M τ hnormal (fun i => star c*a i*d) (star c*b*d) (‖c‖*C*‖d‖)
  · intro i
    have hn : ‖star c*a i‖≤‖c‖*C := (norm_mul_le _ _).trans
      (by simpa only [norm_star] using mul_le_mul_of_nonneg_left (ha i) (norm_nonneg (star c)))
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg d))
  · have hn : ‖star c*b‖≤‖c‖*C := (norm_mul_le _ _).trans
      (by simpa only [norm_star] using mul_le_mul_of_nonneg_left hb (norm_nonneg (star c)))
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg d))
  · intro ξ η
    change Tendsto (fun i => inner ℂ ((star (c:H →L[ℂ] H)) ((a i:H →L[ℂ] H) ((d:H →L[ℂ] H) ξ))) η)
      l (𝓝 (inner ℂ ((star (c:H →L[ℂ] H)) ((b:H →L[ℂ] H) ((d:H →L[ℂ] H) ξ))) η))
    simpa only [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_left] using
      hlim ((d:H →L[ℂ] H) ξ) ((c:H →L[ℂ] H) η)

end Kadison.NormalGNS

end

end
end

end OAI
