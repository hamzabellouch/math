import Mathlib
import OAI.Geometry.NilpotentCharts.CompactGroups
import OAI.Geometry.NilpotentCharts.GlobalAxes

namespace OAI

/-! Global nilpotent exponentials and their centrality and injectivity properties. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLieIntegration
open RawCompactNilpotent
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G]
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))

lemma central_powers_trivial {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    ∀ g ∈ S, ∀ K : Set G, IsCompact K → (∀ n : ℕ, g^n ∈ K) → g = 1 := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
  let : SimplyConnectedSpace S := central_range_simplyConnected_of_nilpotent hstop
  apply noCompactPowers_vector_subgroup S centralAxesHom_range_isClosed
    (centralHomeomorph (G := G) (E₀ := E₀))
  · exact map_one (centralAxesHom (G := G) (E₀ := E₀)).rangeRestrict
  · intro v w
    exact map_mul (centralAxesHom (G := G) (E₀ := E₀)).rangeRestrict
      (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)

end RawLieIntegration

namespace RawLieIntegration
open RawCompactNilpotent

theorem compactRigidity_dimension_induction (n : ℕ) :
    ∀ (E₀ : Type) [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
      (G : Type) [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
      [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G],
      Module.finrank ℝ E₀ = n → ∀ s : ℕ,
      (⊤ : Subgroup G).lowerCentralSeries s = ⊥ →
      NoCompactPowers G ∧ CompactConjugacyCentral G := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E₀ _ _ _ G _ _ _ _ _ _ hdim s hstop
    let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
    by_cases hz : Module.finrank ℝ E₀ = 0
    · let : Subsingleton E₀ := Module.finrank_zero_iff.mp hz
      let : DiscreteTopology G := ChartedSpace.discreteTopology E₀ G
      let : Subsingleton G := subsingleton_of_preconnected_totallyDisconnected
      constructor
      · intro g _ _ _; exact Subsingleton.elim _ _
      · intro g _ _ _; rw [Subsingleton.elim g 1]; exact Subgroup.one_mem _
    · obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (Nat.pos_of_ne_zero hz)
      let C := RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
      let S := (centralAxesHom (G := G) (E₀ := E₀)).range
      have hC : C ≠ ⊥ := RawLieAdjoint.centralTangent_ne_bot hstop v hv
      obtain ⟨W,hCW⟩ := Submodule.exists_isCompl C
      have hpos : 0 < Module.finrank ℝ C :=
        Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hC)
      have hw : Module.finrank ℝ W < n := by
        have he := Submodule.finrank_add_eq_of_isCompl hCW
        omega
      let : T2Space (G ⧸ S) := central_quotient_t2Space
      let : SimplyConnectedSpace (G ⧸ S) := central_quotient_simplyConnected
      obtain ⟨cs,hLie,hSmooth⟩ := exists_central_quotient_lieChart W hCW.symm
      let := cs
      let := hLie
      have hstopQ : (⊤ : Subgroup (G ⧸ S)).lowerCentralSeries s = ⊥ := by
        have he := congrArg (Subgroup.map (QuotientGroup.mk' S)) hstop
        rw [Subgroup.map_lowerCentralSeries,Subgroup.map_top_of_surjective _
          (QuotientGroup.mk'_surjective S),Subgroup.map_bot] at he
        exact he
      obtain ⟨hp,hc⟩ := ih (Module.finrank ℝ W) hw W (G ⧸ S) rfl s hstopQ
      have hker := central_powers_trivial (E₀ := E₀) hstop
      have hker' : ∀ g ∈ (QuotientGroup.mk' S).ker, ∀ K : Set G,
          IsCompact K → (∀ n : ℕ, g^n ∈ K) → g = 1 := by
        rwa [QuotientGroup.ker_mk']
      constructor
      · exact noCompactPowers_extension (QuotientGroup.mk' S) QuotientGroup.continuous_mk hp hker'
      · apply compactConjugacy_extension (QuotientGroup.mk' S) QuotientGroup.continuous_mk
          (QuotientGroup.mk'_surjective S) hc _ hker'
        rw [QuotientGroup.ker_mk']
        exact centralAxesHom_range_le_center

theorem compactRigidity_of_nilpotent
    {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
    [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G]
    {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    NoCompactPowers G ∧ CompactConjugacyCentral G :=
  compactRigidity_dimension_induction (Module.finrank ℝ E₀) E₀ G rfl s hstop

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G]
local notation "I₀" => 𝓘(ℝ,E₀)
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)

omit [FiniteDimensional ℝ E₀] [T2Space G] in
lemma integralCurve_of_add_hom (γ : ℝ → G) (h0 : γ 0 = 1)
    (ha : ∀ s t, γ (s+t) = γ s * γ t) (v : GroupLieAlgebra I₀ G)
    (hd : HasMFDerivAt 𝓘(ℝ,ℝ) I₀ γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    IsMIntegralCurve γ (mulInvariantVectorField v) := by
  intro t
  have hl : MDifferentiableAt I₀ I₀ (fun x : G => γ t * x) 1 :=
    (contMDiff_mul_left («I» := I₀) (n := 1)).mdifferentiableAt one_ne_zero
  have hl' : HasMFDerivAt I₀ I₀ (fun x : G => γ t*x) (γ 0)
      (mfderiv I₀ I₀ (fun x : G => γ t*x) 1) := by
    unfold HasMFDerivAt
    rw [h0]
    exact hl.hasMFDerivAt
  have H := hl'.comp 0 hd
  have hshift : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun u : ℝ => u-t) t (1 : ℝ →L[ℝ] ℝ) := by
    change HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun u : ℝ => u-t) t (ContinuousLinearMap.id ℝ ℝ)
    exact ((hasFDerivAt_id t).sub_const t).hasMFDerivAt
  have H0 : HasMFDerivAt 𝓘(ℝ,ℝ) I₀ ((fun x : G => γ t*x) ∘ γ) (t-t)
      ((mfderiv I₀ I₀ (fun x : G => γ t*x) 1).comp ((1 : ℝ →L[ℝ] ℝ).smulRight v)) := by
    unfold HasMFDerivAt
    rw [sub_self]
    exact H
  have H' := H0.comp (f := fun u : ℝ => u-t) t hshift
  have he : (fun u : ℝ => γ t * γ (u-t)) = γ := by
    funext u
    rw [← ha]
    congr 1
    ring
  have hder : ((mfderiv I₀ I₀ (fun x : G => γ t*x) 1).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight v)).comp (1 : ℝ →L[ℝ] ℝ) =
      (1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (γ t)) := by
    apply ContinuousLinearMap.ext
    intro a
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self,map_smul]
    rfl
  have hcurve := H'.congr_of_eventuallyEq_abuse (f₁ := γ)
    (Filter.Eventually.of_forall fun u => (congr_fun he u).symm)
  exact hcurve.congr_mfderiv hder

lemma curve_eq_add_hom (γ : ℝ → G) (h0 : γ 0 = 1)
    (ha : ∀ s t, γ (s+t) = γ s * γ t) (v : GroupLieAlgebra I₀ G)
    (hd : HasMFDerivAt 𝓘(ℝ,ℝ) I₀ γ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    γ = curve v := curve_unique v h0 (integralCurve_of_add_hom γ h0 ha v hd)

lemma centralAxes_eq_exp (z : C) : subspaceAxes (G := G) C z = exp (G := G) z.val := by
  let L : ℝ →L[ℝ] C := (1 : ℝ →L[ℝ] ℝ).smulRight z
  let γ : ℝ → G := subspaceAxes C ∘ L
  have hz : γ 0 = 1 := by simp [γ,L]
  have ha : ∀ s t, γ (s+t) = γ s * γ t := by
    intro s t
    exact (congrArg (subspaceAxes (G := G) C) (map_add L s t)).trans (subspaceAxes_central_add _ _)
  have HD : HasMFDerivAt 𝓘(ℝ,C) I₀ (subspaceAxes (G := G) C) (L 0)
      (mfderiv 𝓘(ℝ,C) I₀ (subspaceAxes (G := G) C) 0) := by
    unfold HasMFDerivAt
    rw [map_zero]
    exact ((subspaceAxes_contMDiff (G := G) C).mdifferentiableAt (x := (0 : C)) (by simp)).hasMFDerivAt
  have H := HD.comp 0 L.hasFDerivAt.hasMFDerivAt
  have he : (mfderiv 𝓘(ℝ,C) I₀ (subspaceAxes (G := G) C) 0).comp L =
      (1 : ℝ →L[ℝ] ℝ).smulRight (z.val : GroupLieAlgebra I₀ G) := by
    rw [subspaceAxes_derivative]
    rfl
  have hh := curve_eq_add_hom γ hz ha (z.val : GroupLieAlgebra I₀ G) (H.congr_mfderiv he)
  have := congrFun hh 1
  simpa only [γ,Function.comp_apply,L,ContinuousLinearMap.smulRight_apply,one_apply_eq_self,
    one_smul,exp] using this

lemma exp_add_central (v : GroupLieAlgebra I₀ G) (z : C) :
    exp (G := G) (v + (show GroupLieAlgebra I₀ G from z.val)) = exp v * exp (G := G) z.val := by
  let γ : ℝ → G := fun t => curve v t * curve (G := G) z.val t
  have h0 : γ 0 = 1 := by
    dsimp only [γ]
    erw [curve_zero,curve_zero,one_mul]
  have ha : ∀ s t, γ (s+t) = γ s * γ t := by
    intro s t
    dsimp only [γ]
    erw [curve_add,curve_add]
    have hc := Subgroup.mem_center_iff.mp (RawLieAdjoint.centralTangent_curve z s) (curve v t)
    calc
      _ = curve v s * (curve v t * curve (G := G) z.val s) * curve (G := G) z.val t := by group
      _ = curve v s * (curve (G := G) z.val s * curve v t) * curve (G := G) z.val t := by erw [hc]
      _ = _ := by group
  have hv : MDifferentiableAt 𝓘(ℝ,ℝ) I₀ (curve (G := G) v) 0 := (curve_derivative_zero v).mdifferentiableAt
  have hz : MDifferentiableAt 𝓘(ℝ,ℝ) I₀ (curve (G := G) z.val) 0 := (curve_derivative_zero z.val).mdifferentiableAt
  have hm : MDifferentiableAt 𝓘(ℝ,ℝ) I₀ γ 0 :=
    ((curve_contMDiff v).mul (curve_contMDiff (G := G) z.val)).mdifferentiableAt (by simp)
  have he : mfderiv 𝓘(ℝ,ℝ) I₀ γ 0 = (1 : ℝ →L[ℝ] ℝ).smulRight (v+(show GroupLieAlgebra I₀ G from z.val)) := by
    have H := product_derivative_zero (curve_zero v) (curve_zero (G := G) z.val) hv hz
    change mfderiv 𝓘(ℝ,ℝ) I₀ γ 0 = _ at H
    dsimp only [vectorDerivative] at H
    rw [(curve_derivative_zero v).mfderiv,(curve_derivative_zero (G := G) z.val).mfderiv] at H
    exact H.trans (by
      apply ContinuousLinearMap.ext
      intro a
      change a • v + a • (show GroupLieAlgebra I₀ G from z.val) =
        a • (v + (show GroupLieAlgebra I₀ G from z.val))
      exact (smul_add a v _).symm)
  have hh := curve_eq_add_hom γ h0 ha (v+(show GroupLieAlgebra I₀ G from z.val)) (hm.hasMFDerivAt.congr_mfderiv he)
  exact (congrFun hh 1).symm

end RawLieIntegration

namespace RawLieIntegration
open RawCompactNilpotent RawPowerExtension

theorem exponential_dimension_induction (n : ℕ) :
    ∀ (E₀ : Type) [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
      (G : Type) [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
      [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G],
      Module.finrank ℝ E₀ = n → ∀ s : ℕ,
      (⊤ : Subgroup G).lowerCentralSeries s = ⊥ →
      (∀ k : ℕ, k ≠ 0 → Injective (fun x : G => x^k)) ∧
        Surjective (exp (G := G) (E₀ := E₀)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E₀ _ _ _ G _ _ _ _ _ _ hdim s hstop
    let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘(ℝ,E₀) ∞
    by_cases hz : Module.finrank ℝ E₀ = 0
    · let : Subsingleton E₀ := Module.finrank_zero_iff.mp hz
      let : DiscreteTopology G := ChartedSpace.discreteTopology E₀ G
      let : Subsingleton G := subsingleton_of_preconnected_totallyDisconnected
      constructor
      · intro _ _ _ _ _; exact Subsingleton.elim _ _
      · intro g; exact ⟨0,Subsingleton.elim _ _⟩
    · obtain ⟨v,hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (Nat.pos_of_ne_zero hz)
      let C := RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
      let S := (centralAxesHom (G := G) (E₀ := E₀)).range
      have hC : C ≠ ⊥ := RawLieAdjoint.centralTangent_ne_bot hstop v hv
      obtain ⟨W,hCW⟩ := Submodule.exists_isCompl C
      have hpos : 0 < Module.finrank ℝ C :=
        Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hC)
      have hw : Module.finrank ℝ W < n := by
        have he := Submodule.finrank_add_eq_of_isCompl hCW
        omega
      let : T2Space (G ⧸ S) := central_quotient_t2Space
      let : SimplyConnectedSpace (G ⧸ S) := central_quotient_simplyConnected
      obtain ⟨cs,hLie,hSmooth,hSurj⟩ := exists_central_quotient_submersion W hCW.symm
      let := cs
      let := hLie
      have hstopQ : (⊤ : Subgroup (G ⧸ S)).lowerCentralSeries s = ⊥ := by
        have he := congrArg (Subgroup.map (QuotientGroup.mk' S)) hstop
        rw [Subgroup.map_lowerCentralSeries,Subgroup.map_top_of_surjective _
          (QuotientGroup.mk'_surjective S),Subgroup.map_bot] at he
        exact he
      obtain ⟨hp,he⟩ := ih (Module.finrank ℝ W) hw W (G ⧸ S) rfl s hstopQ
      constructor
      · apply pow_injective_extension (QuotientGroup.mk' S) hp
        · rw [QuotientGroup.ker_mk']; exact centralAxesHom_range_le_center
        · intro c _ k hk hck
          exact no_torsion_of_no_compact_powers (compactRigidity_of_nilpotent (E₀ := E₀) hstop).1 c k hk hck
      · intro g
        obtain ⟨q,hq⟩ := he (QuotientGroup.mk' S g)
        obtain ⟨v,hv⟩ := hSurj q
        have hvproj : QuotientGroup.mk' S (exp (G := G) v) = QuotientGroup.mk' S g := by
          change QuotientGroup.mk' S (curve v 1) = _
          rw [curve_map (QuotientGroup.mk' S) (hSmooth.mdifferentiable (by simp)),hv]
          exact hq
        have hc : (exp (G := G) v)⁻¹ * g ∈ S := by
          rw [← QuotientGroup.ker_mk' S]
          simp only [MonoidHom.mem_ker,map_mul,map_inv,hvproj,inv_mul_cancel]
        obtain ⟨z,hz⟩ := hc
        refine ⟨v + (show GroupLieAlgebra 𝓘(ℝ,E₀) G from z.toAdd.val),?_⟩
        rw [exp_add_central v z.toAdd,← centralAxes_eq_exp]
        change exp v * centralAxesHom z = g
        rw [hz]
        group

 
theorem exponential_of_nilpotent
    {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
    {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
    [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G]
    {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    (∀ k : ℕ, k ≠ 0 → Injective (fun x : G => x^k)) ∧
      Surjective (exp (G := G) (E₀ := E₀)) :=
  exponential_dimension_induction (Module.finrank ℝ E₀) E₀ G rfl s hstop

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀]
  {G : Type} [Group G] [TopologicalSpace G] [ChartedSpace E₀ G]
  [LieGroup 𝓘(ℝ,E₀) ∞ G] [T2Space G] [SimplyConnectedSpace G]
local notation "I₀" => 𝓘(ℝ,E₀)
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)

lemma exp_injective_of_nilpotent {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    Injective (exp (G := G) (E₀ := E₀)) := by
  intro v w hvw
  have H := RawPowerExtension.real_oneparameter_unique (exponential_of_nilpotent (E₀ := E₀) hstop).1
    (oneParameter v) (oneParameter w) (oneParameter_continuous v) (oneParameter_continuous w) hvw
  apply curve_injective
  funext t
  exact congrArg (fun f : Multiplicative ℝ →* G => f (Multiplicative.ofAdd t)) H

omit [SimplyConnectedSpace G] in
lemma exp_conjugate (g : G) (v : GroupLieAlgebra I₀ G) :
    g * exp v * g⁻¹ = exp (G := G) (show GroupLieAlgebra I₀ G from RawLieAdjoint.adjoint (E₀ := E₀) g v) :=
  curve_hom (MulAut.conj g).toMonoidHom
    ((RawLieAdjoint.conjugation_smooth (E₀ := E₀) g).mdifferentiable one_ne_zero) v 1

lemma commMap_kernel_iff {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (g : G) (v : GroupLieAlgebra I₀ G) :
    RawLieAdjoint.derivative (E₀ := E₀) (RawLieAdjoint.commMap g) 1 v = 0 ↔
      g * exp v = exp v * g := by
  have H := congrArg (fun A : E₀ →L[ℝ] E₀ => A v)
    (RawLieAdjoint.commMap_add_adjoint (E₀ := E₀) g)
  change RawLieAdjoint.derivative (E₀ := E₀) (RawLieAdjoint.commMap g) 1 v +
    RawLieAdjoint.adjoint (E₀ := E₀) g v = v at H
  constructor
  · intro hz
    have had : RawLieAdjoint.adjoint (E₀ := E₀) g v = v := by simpa only [hz,zero_add] using H
    have hc := exp_conjugate g v
    rw [had] at hc
    exact mul_inv_eq_iff_eq_mul.mp hc
  · intro hc
    have had := exp_injective_of_nilpotent hstop ((exp_conjugate g v).symm.trans
      (mul_inv_eq_iff_eq_mul.mpr hc))
    have hh : RawLieAdjoint.adjoint (E₀ := E₀) g v = v := had
    have hk : RawLieAdjoint.derivative (E₀ := E₀) (RawLieAdjoint.commMap g) 1 v +
        RawLieAdjoint.adjoint (E₀ := E₀) g v = 0 + RawLieAdjoint.adjoint (E₀ := E₀) g v := by
      rw [zero_add,H,hh]
    exact add_right_cancel hk

lemma exp_mem_center_iff {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (v : GroupLieAlgebra I₀ G) : exp v ∈ Subgroup.center G ↔ (show E₀ from v) ∈ C := by
  rw [RawLieAdjoint.mem_centralTangent]
  constructor
  · intro hv g
    exact (commMap_kernel_iff hstop g v).mpr (Subgroup.mem_center_iff.mp hv g)
  · intro hv
    apply Subgroup.mem_center_iff.mpr
    intro g
    exact (commMap_kernel_iff hstop g v).mp (hv g)

lemma centralAxesHom_range_eq_center {s : ℕ} (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    (centralAxesHom (G := G) (E₀ := E₀)).range = Subgroup.center G := by
  apply le_antisymm centralAxesHom_range_le_center
  intro g hg
  obtain ⟨v,rfl⟩ := (exponential_of_nilpotent (E₀ := E₀) hstop).2 g
  let z : C := ⟨v,(exp_mem_center_iff hstop v).mp hg⟩
  refine ⟨Multiplicative.ofAdd z,?_⟩
  exact centralAxes_eq_exp z

include E₀

 

theorem finite_lattice_centralizer {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (Γ : Subgroup G) [CompactSpace (G ⧸ Γ)] :
    ∃ A : Finset Γ, ∀ g : G, (∀ a ∈ A, (a : G)*g = g*a) → g ∈ Subgroup.center G := by
  classical
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup I₀ ∞
  let P : Γ → Submodule ℝ E₀ := fun a =>
    (RawLieAdjoint.derivative (E₀ := E₀) (RawLieAdjoint.commMap a.val) 1).ker
  obtain ⟨A,hA⟩ := RawLieAdjoint.exists_finite_inf P
  refine ⟨A,?_⟩
  intro g hg
  obtain ⟨v,rfl⟩ := (exponential_of_nilpotent (E₀ := E₀) hstop).2 g
  have hvA : (show E₀ from v) ∈ A.inf P := by
    have hh : ∀ a ∈ A, (show E₀ from v) ∈ P a := fun a ha =>
      (commMap_kernel_iff hstop a.val v).mpr (hg a ha)
    exact Submodule.mem_finsetInf.mpr hh
  rw [hA] at hvA
  have hvall : ∀ a : Γ, (show E₀ from v) ∈ P a := (Submodule.mem_iInf P).mp hvA
  apply RawCompactNilpotent.centralizer_cocompact_le_center Γ (compactRigidity_of_nilpotent (E₀ := E₀) hstop).2
  intro a ha
  exact (commMap_kernel_iff hstop a v).mp (hvall ⟨a,ha⟩)

end RawLieIntegration
end

end OAI
