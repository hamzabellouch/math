import Mathlib
import OAI.Analysis.Conductivity.Variational.CrossingEllipticity
import OAI.Analysis.Conductivity.Scalarization.CascadeConstitution
import OAI.Analysis.Conductivity.Flux.C1WeakDivergence

namespace OAI

noncomputable section
namespace ScalarConductivity
open Real Set Filter Topology MeasureTheory Matrix

lemma cascade_weak_integrand_ae {L K k : ℝ} (hL : 0<L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (ψ : SmoothScalar Coord3)
    (hs : tsupport ψ.val ⊆ {x : Coord3 | 0≤k*x 0}) :
    (fun x => ∑ i, (cascadeTensor L K k x *ᵥ
        (fun j => direction (Pi.single j 1) (cascadeValue L K k A) x)) i *
          (smoothDirection (Pi.single i 1) ψ).val x) =ᵐ[volume]
    (fun x => ∑ i, cascadeFlux L K k A x i*(smoothDirection (Pi.single i 1) ψ).val x) := by
  filter_upwards [cascadeTensor_constitution_ae hL hK hk A] with x hx
  by_cases h : 0≤k*x 0
  · rw [hx h]
  · have hz (i : Fin 3) : (smoothDirection (Pi.single i 1) ψ).val x=0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hi
      exact h (hs (tsupport_smoothDirection_subset _ _ hi))
    simp only [hz,mul_zero]

theorem cascade_weak_equation {L K k : ℝ} (hL : 1≤L) (hK : 0<K) (hk : k≠0)
    (A : ℝ) (ψ : SmoothScalar Coord3) (hc : HasCompactSupport ψ.val)
    (hs : tsupport ψ.val ⊆ {x : Coord3 | 0≤k*x 0}) :
    Integrable (fun x => ∑ i, (cascadeTensor L K k x *ᵥ
        (fun j => direction (Pi.single j 1) (cascadeValue L K k A) x)) i *
          (smoothDirection (Pi.single i 1) ψ).val x) ∧
    (∫ x, ∑ i, (cascadeTensor L K k x *ᵥ
        (fun j => direction (Pi.single j 1) (cascadeValue L K k A) x)) i *
          (smoothDirection (Pi.single i 1) ψ).val x) = 0 := by
  have he := cascade_weak_integrand_ae (lt_of_lt_of_le (by norm_num) hL) hK hk A ψ hs
  constructor
  · apply Integrable.congr _ he.symm
    apply integrable_finsetSum
    intro i _
    exact ((cascadeFlux_C1 hL hK k A i).continuous.mul
      (smoothScalar_contDiff (smoothDirection (Pi.single i 1) ψ)).continuous).integrable_of_hasCompactSupport
      (compactSupport_smoothDirection (Pi.single i 1) hc).mul_left
  · rw [integral_congr_ae he]
    exact C1_divergence_zero_test volume (fun i : Fin 3 => Pi.single i 1)
      (fun i x => cascadeFlux L K k A x i) (cascadeFlux_C1 hL hK k A)
      (cascadeFlux_divergence hL hK k A) ψ hc

theorem exists_cascade_parameters : ∃ L K : ℝ, 1≤L ∧ 0<K ∧
    ∀ k : ℝ, ∀ x v : Coord3,
      (1/8)*(v ⬝ᵥ v) ≤ v ⬝ᵥ (cascadeTensor L K k x *ᵥ v) ∧
      v ⬝ᵥ (cascadeTensor L K k x *ᵥ v) ≤ 10*(v ⬝ᵥ v) := by
  obtain ⟨L,hL,hl⟩ := exists_elliptic_crossing
  obtain ⟨M,hM,hm⟩ := exists_transition_derivative_bound
  refine ⟨L,20*M,hL,by linarith,fun k x v => cascadeTensor_bounds hl ?_ x v⟩
  intro z
  have hh := connectorAngular_bounds hM (le_refl (20*M)) (fun x => (hm x).1) z
  exact ⟨hh.1,hh.2.trans (by norm_num)⟩

end ScalarConductivity

end

end OAI
