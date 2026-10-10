import OAI.Analysis.KadisonKastler.SpatialBicentralizer
import OAI.Analysis.KadisonKastler.IsometricRestriction

namespace OAI

/-! # State bicentralizers through a reducing isometric embedding -/

namespace KadisonKastler

open Generator.Tracial Filter
open scoped Topology

noncomputable section

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

variable (e : Algebra M ≃⋆ₐ[ℂ] Algebra N) (V : K →ₗᵢ[ℂ] H)
  (hV : ∀ (a : Algebra M) (x : K), V ((e a).val x)=a.val (V x))

include hV in
theorem isometric_vectorFunctional (ξ : K) (a : Algebra M) :
    vectorFunctional (V ξ) a=vectorFunctional ξ (e a) := by
  change inner ℂ (V ξ) (a.val (V ξ))=inner ℂ ξ ((e a).val ξ)
  rw [← hV,V.inner_map_map]

include hV in
theorem isometric_stateCommutator_norm (ξ : K) (a : Algebra M) :
    ‖vectorStateCommutator (V ξ) a‖=‖vectorStateCommutator ξ (e a)‖ := by
  apply functional_norm_eq_of_starEquiv e
  intro b
  change vectorFunctional (V ξ) (a*b-b*a)=vectorFunctional ξ (e a*e b-e b*e a)
  rw [isometric_vectorFunctional e V hV,map_sub e,map_mul e,map_mul e]

include hV in
theorem isometric_vector_separating (ξ : K)
    (hs : Function.Injective (algebraVectorMap N ξ)) :
    Function.Injective (algebraVectorMap M (V ξ)) := by
  intro a b hab
  apply e.injective
  apply hs
  apply V.injective
  change V ((e a).val ξ)=V ((e b).val ξ)
  change a.val (V ξ)=b.val (V ξ) at hab
  simpa only [hV] using hab

include hV in
theorem stateBicentralizerMember.isometric_pullback (ξ : K) (a : Algebra M)
    (ha : stateBicentralizerMember (V ξ) a) :
    stateBicentralizerMember ξ (e a) := by
  apply (stateBicentralizerMember_iff_unitary_tests _ _).mpr
  intro u hu η
  let v (n : ℕ) : unitary (Algebra M) := Unitary.map (StarMonoidHom.ofClass e.symm) (u n)
  have hev (n : ℕ) : e (v n).val=(u n).val := e.apply_symm_apply _
  have hv : Tendsto (fun n => ‖vectorStateCommutator (V ξ) (v n).val‖) atTop (𝓝 0) := by
    simpa only [isometric_stateCommutator_norm e V hV,hev] using hu
  have ht := (stateBicentralizerMember_iff_unitary_tests _ _).mp ha v hv (V η)
  have he (n : ℕ) : V ((e a*(u n).val-(u n).val*e a).val η)=
      (a*(v n).val-(v n).val*a).val (V η) := by
    have hw := hV (a*(v n).val-(v n).val*a) η
    simpa only [map_sub e,map_mul e,hev] using hw
  have h := (V.toContinuousLinearMap.adjoint.continuous.tendsto 0).comp ht
  simpa only [Function.comp_def,← he,isometry_adjoint_apply,map_zero] using h

include hV in
theorem scalar_stateBicentralizer_of_isometric (ξ : K)
    (hscalar : ∀ b : Algebra N, stateBicentralizerMember ξ b → ∃ z : ℂ, b=z • 1)
    (a : Algebra M) (ha : stateBicentralizerMember (V ξ) a) : ∃ z : ℂ, a=z • 1 := by
  obtain ⟨z,hz⟩ := hscalar (e a) (ha.isometric_pullback e V hV ξ a)
  refine ⟨z,e.injective ?_⟩
  change e a=e (z • 1)
  have hm : e (z • (1 : Algebra M))=z • e 1 := e.map_smul' z 1
  rw [map_one] at hm
  exact hz.trans hm.symm

variable {ξ η : H}

theorem stateBicentralizerMember_congr_vectorFunctional
    (h : vectorFunctional (M := M) ξ=vectorFunctional η) (a : Algebra M) :
    stateBicentralizerMember ξ a ↔ stateBicentralizerMember η a := by
  have he (b : Algebra M) : vectorStateCommutator ξ b=vectorStateCommutator η b := by
    ext c
    change vectorFunctional ξ (b*c-c*b)=vectorFunctional η (b*c-c*b)
    rw [h]
  simp only [stateBicentralizerMember,StateAsymptoticallyCentral,he]

end

end KadisonKastler

end OAI
