import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.SmoothGeometricInverse

namespace OAI


noncomputable section
namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V H Z : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

lemma exists_energy_kernel_projection (i : V →L[ℝ] H) (hi : Function.Injective i)
    (D : V →L[ℝ] Z) (K : Submodule ℝ H) [CompleteSpace K]
    (hgraph : ∀ u, ‖u‖^2 = ‖i u‖^2 + ‖D u‖^2)
    (hker : ∀ k : K, ∃ v : V, i v = k.val ∧ D v = 0) :
    ∃ PiH : V →L[ℝ] V,
      (∀ u, i (PiH u) = K.starProjection (i u)) ∧
      (∀ u, D (PiH u) = 0) ∧ (∀ u, ‖PiH u‖ ≤ ‖i u‖) := by
  let hs : ∀ k : K, ∃ v : V, i v = k.val := fun k => (hker k).imp (fun _ h => h.1)
  let L := InjectiveLinearLift.lift i.toLinearMap hi K.subtype hs
  have hL (k : K) : i (L k) = k.val := InjectiveLinearLift.lift_spec _ _ _ _ _
  have hD (k : K) : D (L k) = 0 := by
    obtain ⟨v,hiv,hdv⟩ := hker k
    have he : L k = v := hi ((hL k).trans hiv.symm)
    rw [he,hdv]
  have hn (k : K) : ‖L k‖ = ‖k‖ := by
    have hg := hgraph (L k)
    rw [hL,hD,norm_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero] at hg
    change ‖L k‖^2 = ‖k‖^2 at hg
    nlinarith [norm_nonneg (L k),norm_nonneg k]
  let T : K →L[ℝ] V := L.mkContinuous 1 (by intro k; rw [hn,one_mul])
  let PiH := T ∘L K.orthogonalProjectionOnto ∘L i
  refine ⟨PiH,fun u => hL _,fun u => hD _,fun u => ?_⟩
  change ‖L (K.orthogonalProjectionOnto (i u))‖ ≤ ‖i u‖
  rw [hn]
  exact K.norm_orthogonalProjectionOnto_apply_le (i u)

lemma energy_kernel_subtraction (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (K : Submodule ℝ H) [CompleteSpace K] (PiH : V →L[ℝ] V)
    (hiPiH : ∀ u, i (PiH u) = K.starProjection (i u))
    (hDPiH : ∀ u, D (PiH u) = 0) (u : V) :
    D (u-PiH u) = D u ∧ K.starProjection (i (u-PiH u)) = 0 := by
  constructor
  · rw [map_sub,hDPiH,sub_zero]
  · rw [map_sub,hiPiH,map_sub,K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem _),sub_self]

lemma augmented_energy_on_subtracted_test (i : V →L[ℝ] H) (D : V →L[ℝ] Z)
    (K : Submodule ℝ H) [CompleteSpace K] (PiH : V →L[ℝ] V)
    (hiPiH : ∀ u, i (PiH u) = K.starProjection (i u))
    (hDPiH : ∀ u, D (PiH u) = 0) (v u : V) :
    energy (K.starProjection ∘L i) D v (u-PiH u) = ⟪D v,D u⟫ := by
  obtain ⟨hd,hp⟩ := energy_kernel_subtraction i D K PiH hiPiH hDPiH u
  simp only [energy_apply,ContinuousLinearMap.comp_apply,hp,hd,inner_zero_right,zero_add]
end TamingCompatibility.Variational

end

end OAI
