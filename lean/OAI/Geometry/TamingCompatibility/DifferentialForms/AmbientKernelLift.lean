import Mathlib
import OAI.Geometry.TamingCompatibility.Elliptic.AugmentedCoercive
import OAI.Geometry.TamingCompatibility.Functional.EnergyKernelProjection

namespace OAI

section
section
section

section
noncomputable section
namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V H Z : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

lemma exists_ambient_kernel_lift (i : V →L[ℝ] H) (hi : Function.Injective i)
    (D : V →L[ℝ] Z) (K : Submodule ℝ H) [CompleteSpace K]
    (hgraph : ∀ u, ‖u‖^2 = ‖i u‖^2 + ‖D u‖^2)
    (hker : ∀ k : K, ∃ v : V, i v = k.val ∧ D v = 0) :
    ∃ J : H →L[ℝ] V,
      (∀ u, i (J u) = K.starProjection u) ∧
      (∀ u, D (J u) = 0) ∧ (∀ u, ‖J u‖ ≤ ‖u‖) := by
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
  let J := T ∘L K.orthogonalProjectionOnto
  refine ⟨J,fun u => hL _,fun u => hD _,fun u => ?_⟩
  change ‖L (K.orthogonalProjectionOnto u)‖ ≤ ‖u‖
  rw [hn]
  exact K.norm_orthogonalProjectionOnto_apply_le u

end TamingCompatibility.Variational

end
end

section
noncomputable section
namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem exists_uniform_energy_representer (B : V →L[ℝ] V →L[ℝ] ℝ)
    (hc : IsCoercive B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Submodule ℝ V) (φ : S →ₗ[ℝ] ℝ)
      (M : ℝ), 0 ≤ M → (∀ u, ‖φ u‖ ≤ M * ‖u‖) →
      ∃ v : V, ‖v‖ ≤ C*M ∧ ∀ u : S, B v u = φ u := by
  let A := hc.continuousLinearEquivOfBilin
  let C := ‖A.symm.toContinuousLinearMap‖ + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,fun S φ M hM hφ => ?_⟩
  let f : StrongDual ℝ S := φ.mkContinuous M hφ
  obtain ⟨g,hg,hgn⟩ := exists_extension_norm_eq S f
  let w := (InnerProductSpace.toDual ℝ V).symm g
  let v := A.symm w
  have hw : ‖w‖ = ‖g‖ := (InnerProductSpace.toDual ℝ V).symm.norm_map g
  have hf : ‖f‖ ≤ M := LinearMap.mkContinuous_norm_le φ hM hφ
  refine ⟨v,?_,fun u => ?_⟩
  · calc
      ‖v‖ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖w‖ :=
        A.symm.toContinuousLinearMap.le_opNorm w
      _ ≤ ‖A.symm.toContinuousLinearMap‖ * M := by
        rw [hw,hgn]
        exact mul_le_mul_of_nonneg_left hf (norm_nonneg _)
      _ ≤ C*M := by dsimp only [C]; nlinarith
  · rw [← hc.continuousLinearEquivOfBilin_apply]
    change ⟪A (A.symm w),u.val⟫ = φ u
    rw [A.apply_symm_apply]
    exact InnerProductSpace.toDual_symm_apply.trans (hg u)

omit [CompleteSpace V] in

lemma energy_representer_annihilates (B : V →L[ℝ] V →L[ℝ] ℝ)
    (S : Submodule ℝ V) (φ : S →ₗ[ℝ] ℝ) (v : V)
    (hv : ∀ u : S, B v u = φ u) (u : S) (hu : φ u = 0) : B v u = 0 :=
  (hv u).trans hu
end TamingCompatibility.Variational

end
end

section
noncomputable section
namespace TamingCompatibility.Variational
open scoped RealInnerProductSpace
variable {V H Z : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

theorem exists_green_observation
    (i : V →L[ℝ] H) (hi : Function.Injective i) (D : V →L[ℝ] Z)
    (K : Submodule ℝ H) [CompleteSpace K] (G : H →L[ℝ] V)
    (hgraph : ∀ u, ‖u‖^2 = ‖i u‖^2 + ‖D u‖^2)
    (hker : ∀ k : K, ∃ v : V, i v = k.val ∧ D v = 0)
    (hweak : ∀ f v, ⟪D (G f),D v⟫ = ⟪f-K.starProjection f,i v⟫)
    (horth : ∀ f, i (G f) ∈ Kᗮ) :
    ∃ PiH : V →L[ℝ] V, ∃ C : ℝ, 0 < C ∧
      (∀ u, i (PiH u) = K.starProjection (i u)) ∧
      (∀ u, D (PiH u) = 0) ∧
      ∀ (S : Submodule ℝ V) (φ : S →ₗ[ℝ] ℝ) (M : ℝ),
        0 ≤ M → (∀ u, ‖φ u‖ ≤ M*‖u‖) →
        ∃ v : V, ‖v‖ ≤ C*M ∧ K.starProjection (i v) = 0 ∧
          (∀ f : H, ∀ hf : G f ∈ S, φ ⟨G f,hf⟩ = ⟪f,i v⟫) ∧
          (∀ w : V, ∀ hw : w-PiH w ∈ S,
            φ ⟨w-PiH w,hw⟩ = 0 → ⟪D v,D w⟫ = 0) := by
  obtain ⟨PiH,hiP,hDP,hnP⟩ := exists_energy_kernel_projection i hi D K hgraph hker
  let B := energy (K.starProjection ∘L i) D
  have hc : IsCoercive B := projected_energy_coercive i D K G hgraph hweak
  obtain ⟨C₀,hC₀,hrep⟩ := exists_uniform_energy_representer B hc
  refine ⟨PiH,(1+‖i‖)*C₀,mul_pos (by positivity) hC₀,hiP,hDP,fun S φ M hM hφ => ?_⟩
  obtain ⟨v₀,hv₀,hvrep⟩ := hrep S φ M hM hφ
  let v := v₀-PiH v₀
  obtain ⟨hDv,hPv⟩ := energy_kernel_subtraction i D K PiH hiP hDP v₀
  refine ⟨v,?_,hPv,?_,?_⟩
  · calc
      ‖v‖ ≤ ‖v₀‖ + ‖PiH v₀‖ := norm_sub_le _ _
      _ ≤ ‖v₀‖ + ‖i v₀‖ := add_le_add le_rfl (hnP v₀)
      _ ≤ ‖v₀‖ + ‖i‖*‖v₀‖ := add_le_add le_rfl (i.le_opNorm v₀)
      _ = (1+‖i‖)*‖v₀‖ := by ring
      _ ≤ (1+‖i‖)*(C₀*M) := mul_le_mul_of_nonneg_left hv₀ (by positivity)
      _ = _ := by ring
  · intro f hf
    have hz : K.starProjection (i (G f)) = 0 := K.starProjection_apply_eq_zero_iff.mpr (horth f)
    have hp := hvrep ⟨G f,hf⟩
    change energy (K.starProjection ∘L i) D v₀ (G f) = φ ⟨G f,hf⟩ at hp
    simp only [energy_apply,ContinuousLinearMap.comp_apply,hz,inner_zero_right,zero_add] at hp
    rw [real_inner_comm] at hp
    calc
      φ ⟨G f,hf⟩ = ⟪D (G f),D v₀⟫ := hp.symm
      _ = ⟪f-K.starProjection f,i v₀⟫ := hweak f v₀
      _ = ⟪f,i v⟫ := by
        change _ = ⟪f,i (v₀-PiH v₀)⟫
        rw [map_sub,hiP,inner_sub_left,inner_sub_right,K.inner_starProjection_left_eq_right]
  · intro w hw hφw
    have hp := (hvrep ⟨w-PiH w,hw⟩).trans hφw
    change energy (K.starProjection ∘L i) D v₀ (w-PiH w) = 0 at hp
    rw [augmented_energy_on_subtracted_test i D K PiH hiP hDP] at hp
    change ⟪D (v₀-PiH v₀),D w⟫ = 0
    rw [hDv]
    exact hp
end TamingCompatibility.Variational

end
end

end
end
end

end OAI
