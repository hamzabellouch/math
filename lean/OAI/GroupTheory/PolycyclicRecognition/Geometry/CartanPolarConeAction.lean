import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarConeKernel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeAmbientAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanConeHaarAction
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanIntegratedAction

namespace OAI

/-! # The ambient action and Haar trace for the actual closed polar cone -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set MeasureTheory
open scoped Manifold BigOperators

variable {EG G W Q : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [Group Q]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

attribute [local instance 100] LieRing.ofAssociativeRing

theorem factor_action_eq_adjoint
    (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ)
    (hN : ∀ x : cartanRootIdeal H,
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h))
    (hNbij : Function.Bijective F.ExpN) (hDbij : Function.Bijective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier) :
    ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      hNbij dynkin (cartanLog H F.D.equiv F.ExpD hDbij d) := by
  obtain ⟨φ, hφ, hconj⟩ := M.exists_integrated_cartan_action T F.N.equiv F.ExpN F.isExpN
    hNbij dynkin F.D.equiv F.ExpD hDbij j ρ hρ F.inclusionN F.closedN.injective
    F.inclusionD hN hD
  intro d
  refine Eq.trans ?_ (hφ d)
  apply MulEquiv.ext
  intro n
  apply F.closedN.injective
  exact (F.conjugation d n).trans (hconj d n).symm

omit [FiniteDimensional ℝ W] in
theorem sum_height_weights_transport (c : Fin M.letterCount → ℕ) :
    (∑ i, (c i : ℝ) • cartanHeightWeight T H (M.weight i)).comp eW.symm.toLinearMap =
      ∑ i, (c i : ℝ) • (M.supportIn T hunimod eW).weight i := by
  ext w
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, supportIn, SupportDatum.transport, supportDatum_weight]

include hunimod in
/-- Salience removes the cone vertex at the generators, giving the actual
ambient action without a false zero-exclusion assumption on a closed cone. -/
theorem exists_polar_cone_ambient_action
    (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ)
    (hN : ∀ x : cartanRootIdeal H,
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h))
    (hNbij : Function.Bijective F.ExpN) (hDsurj : Function.Surjective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (K : ProperCone ℝ (StrongDual ℝ W))
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    (π : F.N.carrier →* Q) (s : Q → F.N.carrier) (hs : Function.RightInverse s π)
    (hker : (π.ker : Set F.N.carrier) = F.ExpN ''
      (F.N.equiv '' (M.coneWordIdeal (heightConePreimage T eW K) : Set (cartanRootIdeal H)))) :
    ∃ (α : F.D.carrier →* MulAut Q) (act : G →* Equiv.Perm Q),
      (∀ d n, α d (π n) = π (F.action d n)) ∧
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = π n * α d q) ∧
      (∀ g, act g 1 = 1 ↔ ∃ n d, n ∈ π.ker ∧ F.inclusionN n * F.inclusionD d = g) ∧
      ∀ g h, act (g * h) 1 = act g (act h 1) := by
  have hker' : (π.ker : Set F.N.carrier) = F.ExpN ''
      (F.N.equiv '' (M.coneWordIdeal (positiveHeightConePreimage T eW K) :
        Set (cartanRootIdeal H))) := by
    rw [M.coneWordIdeal_positiveHeight_eq T hunimod eW K]
    exact hker
  exact exists_cartan_cone_ambient_action M F T j ρ hρ hN hD hNbij hDsurj dynkin
    (positiveHeightConePreimage T eW K)
    (fun _ hx _ hy => positiveHeightConePreimage_add T eW K hK hx hy)
    (zero_not_mem_positiveHeightConePreimage T eW K) π s hs hker'

/-- The descended action comes with its genuine Haar measure and the exact
positive generator multiplicities used by the offset trace separation. -/
theorem exists_polar_cone_action_haar
    (j : GroupLieAlgebra (𝓘(ℝ, EG)) G →ₗ⁅ℝ⁆ A) (ρ : G →* Aˣ)
    (hρ : Function.Injective ρ)
    (hN : ∀ x : cartanRootIdeal H,
      ρ (F.inclusionN (F.ExpN (F.N.equiv x))) = algebraExpUnit (j x))
    (hD : ∀ h : H, ρ (F.inclusionD (F.ExpD (F.D.equiv h))) = algebraExpUnit (j h))
    (hNbij : Function.Bijective F.ExpN) (hDbij : Function.Bijective F.ExpD)
    (dynkin : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (K : ProperCone ℝ (StrongDual ℝ W))
    (hK : (K : ConvexCone ℝ (StrongDual ℝ W)).Salient)
    (Q₀ : NilpotentLieModel ((cartanRootIdeal H) ⧸
      M.coneWordIdeal (heightConePreimage T eW K)))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q₀.modelSpace)) Q₀.carrier → Q₀.carrier)
    (hExpQ : IsGroupExponential ExpQ) (hbijQ : Function.Bijective ExpQ)
    (haarQ : NilpotentExponentialHaarInput Q₀.modelSpace Q₀.carrier)
    (π : F.N.carrier →* Q₀.carrier) (s : Q₀.carrier → F.N.carrier)
    (hs : Function.RightInverse s π)
    (hker : (π.ker : Set F.N.carrier) = F.ExpN ''
      (F.N.equiv '' (M.coneWordIdeal (heightConePreimage T eW K) : Set (cartanRootIdeal H))))
    (hπ : ∀ v, π (F.ExpN (F.N.equiv v)) =
      ExpQ (Q₀.equiv (M.coneProjection (heightConePreimage T eW K) v)))
    (height : G →* Multiplicative W)
    (hheight : ∀ v, (height (Exp v)).toAdd = eW (heightProjection T.character v)) :
    ∃ (α : F.D.carrier →* MulAut Q₀.carrier) (act : G →* Equiv.Perm Q₀.carrier)
      (μ : Measure Q₀.carrier) (c : Fin M.letterCount → ℕ),
      μ.IsHaarMeasure ∧
      (∀ d n, α d (π n) = π (F.action d n)) ∧
      (∀ n d q, act (F.inclusionN n * F.inclusionD d) q = π n * α d q) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∉ K → c i = 0) ∧
      (∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap ∈ K → 0 < c i) ∧
      ∀ g E, μ (act g '' E) = ENNReal.ofReal (Real.exp
        ((∑ i, (c i : ℝ) • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
          (height g).toAdd)) * μ E := by
  obtain ⟨α, act, hα, hact, _, _⟩ := M.exists_polar_cone_ambient_action F T hunimod eW
    j ρ hρ hN hD hNbij hDbij.surjective dynkin K hK π s hs hker
  have hadd : ∀ x ∈ heightConePreimage (H := H) T eW K,
      ∀ y ∈ heightConePreimage T eW K, x + y ∈ heightConePreimage T eW K :=
    fun _ hx _ hy => heightConePreimage_add T eW K hx hy
  obtain ⟨μ, ell, c, hμ, hout, hin, hell, hvol⟩ :=
    M.exists_cone_action_haar_height_multiplier T F (heightConePreimage T eW K) hadd
      Q₀ ExpQ hbijQ hNbij hDbij dynkin π hπ α hα
      (M.factor_action_eq_adjoint F T j ρ hρ hN hD hNbij hDbij dynkin)
      eW height hheight hExpQ haarQ act hact
  have hell' : ell = ∑ i, (c i : ℝ) • (M.supportIn T hunimod eW).weight i := by
    rw [hell, M.sum_height_weights_transport T hunimod eW c]
  refine ⟨α, act, μ, c, hμ, hα, hact, ?_, ?_, ?_⟩
  · intro i hi
    apply hout i
    intro h
    exact hi ((M.weight_mem_heightConePreimage_iff T hunimod eW K i).mp h)
  · intro i hi
    exact hin i ((M.weight_mem_heightConePreimage_iff T hunimod eW K i).mpr hi)
  · intro g E
    have heval : ell (height g).toAdd =
        (∑ i, (c i : ℝ) • ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap)
          (height g).toAdd := by
      rw [hell']
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, sum_apply, smul_apply]
      rfl
    rw [hvol, heval]

end PolycyclicRecognition.CartanWordModel

end

end OAI
