import Mathlib
import OAI.Geometry.NilpotentCharts.Flows

namespace OAI

/-! Central tangent directions, central axes and local quotient slices. -/

noncomputable section
open scoped Manifold ContDiff Topology BigOperators commutatorElement
open Function Set Manifold Topology Filter

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G] [T2Space G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀
omit [FiniteDimensional ℝ E₀] [T2Space G] in
lemma invariantField_hom (φ : G →* G) (hφ : MDifferentiable 𝓘ₙ 𝓘ₙ φ)
    (v : GroupLieAlgebra 𝓘ₙ G) (h : G) :
    mfderiv 𝓘ₙ 𝓘ₙ φ h (mulInvariantVectorField v h) =
      mulInvariantVectorField (I := 𝓘ₙ) (mfderiv 𝓘ₙ 𝓘ₙ φ 1 v : GroupLieAlgebra 𝓘ₙ G) (φ h) := by
  have hL : MDifferentiableAt 𝓘ₙ 𝓘ₙ (fun x : G => h*x) 1 :=
    (contMDiff_mul_left (I := 𝓘ₙ) (n := 1)).mdifferentiableAt one_ne_zero
  have hL' : MDifferentiableAt 𝓘ₙ 𝓘ₙ (fun x : G => φ h*x) (φ 1) :=
    (contMDiff_mul_left (I := 𝓘ₙ) (n := 1)).mdifferentiableAt one_ne_zero
  have hc := mfderiv_comp (I' := 𝓘ₙ) (f := fun x : G => h*x) (g := φ) (1 : G)
    (hφ (h*1)) hL
  have hc' := mfderiv_comp (I' := 𝓘ₙ) (f := φ) (g := fun x : G => φ h*x) (1 : G)
    hL' (hφ 1)
  have hp := mfderiv_congr_point (I := 𝓘ₙ) (I' := 𝓘ₙ) (f := φ) (mul_one h)
  have hp' := mfderiv_congr_point (I := 𝓘ₙ) (I' := 𝓘ₙ)
    (f := fun x : G => φ h*x) φ.map_one
  have he := mfderiv_congr (I := 𝓘ₙ) (I' := 𝓘ₙ) (x := (1 : G))
    (show (φ ∘ (fun x : G => h*x)) = (fun x : G => φ h*x) ∘ φ by
      funext x; exact φ.map_mul h x)
  change (mfderiv 𝓘ₙ 𝓘ₙ φ h) ((mfderiv 𝓘ₙ 𝓘ₙ (fun x : G => h*x) 1) v) =
    (mfderiv 𝓘ₙ 𝓘ₙ (fun x : G => φ h*x) 1) ((mfderiv 𝓘ₙ 𝓘ₙ φ 1) v)
  exact (congrArg
    (fun D : E →L[ℝ] E => D ((mfderiv 𝓘ₙ 𝓘ₙ (fun x : G => h*x) 1) v)) hp.symm).trans
    ((congrArg (fun D : E →L[ℝ] E => D v) hc).symm.trans
      ((congrArg (fun D : E →L[ℝ] E => D v) he).trans
        ((congrArg (fun D : E →L[ℝ] E => D v) hc').trans
          (congrArg (fun D : E →L[ℝ] E => D ((mfderiv 𝓘ₙ 𝓘ₙ φ 1) v)) hp'))))

lemma integralCurve_hom (φ : G →* G) (hφ : MDifferentiable 𝓘ₙ 𝓘ₙ φ)
    (v : GroupLieAlgebra 𝓘ₙ G) :
    IsMIntegralCurve (I := 𝓘ₙ) (φ ∘ curve v)
      (mulInvariantVectorField (I := 𝓘ₙ) (mfderiv 𝓘ₙ 𝓘ₙ φ 1 v : GroupLieAlgebra 𝓘ₙ G)) := by
  intro t
  have hc := (hφ (curve v t)).hasMFDerivAt.comp t (curve_integral v t)
  have hm : (mfderiv 𝓘ₙ 𝓘ₙ φ (curve v t)).comp
      ((1 : ℝ →L[ℝ] ℝ).smulRight (mulInvariantVectorField v (curve v t))) =
      (1 : ℝ →L[ℝ] ℝ).smulRight
        (mulInvariantVectorField (I := 𝓘ₙ) (mfderiv 𝓘ₙ 𝓘ₙ φ 1 v : GroupLieAlgebra 𝓘ₙ G) (φ (curve v t))) := by
    apply ContinuousLinearMap.ext
    intro a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, map_smul, invariantField_hom φ hφ]
  exact hc.congr_mfderiv hm

lemma curve_hom (φ : G →* G) (hφ : MDifferentiable 𝓘ₙ 𝓘ₙ φ)
    (v : GroupLieAlgebra 𝓘ₙ G) (t : ℝ) :
    φ (curve v t) = curve (mfderiv 𝓘ₙ 𝓘ₙ φ 1 v : GroupLieAlgebra 𝓘ₙ G) t := by
  exact congrFun (curve_unique _ (by simp only [Function.comp_apply, curve_zero, map_one]) (integralCurve_hom φ hφ v)) t

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G] [T2Space G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀

lemma curve_central (w : GroupLieAlgebra 𝓘ₙ G)
    (hw : ∀ g : G, RawLieAdjoint.adjoint (E₀ := E₀) g w = w) (t : ℝ) :
    curve w t ∈ Subgroup.center G := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  have h := curve_hom (MulAut.conj g).toMonoidHom
    ((RawLieAdjoint.conjugation_smooth (E₀ := E₀) g).mdifferentiable one_ne_zero) w t
  have he : (mfderiv 𝓘ₙ 𝓘ₙ (MulAut.conj g : G → G) 1 w : E) = w := hw g
  have hc := congrArg (fun v : E => curve (G := G) (E₀ := E₀) v t) he
  have hconj : g * curve w t * g⁻¹ = curve w t := h.trans hc
  exact mul_inv_eq_iff_eq_mul.mp hconj

lemma curve_nonconstant {w : GroupLieAlgebra 𝓘ₙ G} (hw : w ≠ 0) :
    curve w ≠ fun _ => (1 : G) := by
  have hz : curve (G := G) (E₀ := E₀) 0 = fun _ => (1 : G) := by
    funext t
    simpa only [zero_smul, mul_zero, curve_zero] using
      curve_smul (0 : GroupLieAlgebra 𝓘ₙ G) 0 t
  intro hc
  exact hw (curve_injective (hc.trans hz.symm))

 

theorem exists_central_axis {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
    (v : GroupLieAlgebra 𝓘ₙ G) (hv : v ≠ 0) :
    ∃ w : GroupLieAlgebra 𝓘ₙ G, w ≠ 0 ∧ ∃ γ : ℝ → G,
      Continuous γ ∧ γ 0 = 1 ∧
      (∀ a b : ℝ, γ (a + b) = γ a * γ b) ∧
      IsMIntegralCurve γ (mulInvariantVectorField w) ∧
      (∀ t : ℝ, γ t ∈ Subgroup.center G) ∧ γ ≠ fun _ => 1 := by
  obtain ⟨w, hw, hfix⟩ := RawLieAdjoint.exists_adjoint_fixed (E₀ := E₀) hstop v hv
  exact ⟨w, hw, curve w, curve_continuous w, curve_zero w, curve_add w,
    curve_integral w, curve_central w hfix, curve_nonconstant hw⟩

end RawLieIntegration

namespace RawLieAdjoint
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀

 
def centralTangent : Submodule ℝ E :=
  ⨅ g : G, (derivative (E₀ := E₀) (commMap g) 1).ker

omit [FiniteDimensional ℝ E₀] [LieGroup 𝓘ₙ ∞ G] in
lemma mem_centralTangent (v : E) : v ∈ centralTangent (G := G) (E₀ := E₀) ↔
    ∀ g : G, derivative (E₀ := E₀) (commMap g) 1 v = 0 := by
  simp only [centralTangent, Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

lemma exists_finite_inf {ι R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [IsArtinian R V] (p : ι → Submodule R V) :
    ∃ s : Finset ι, s.inf p = ⨅ i, p i := by
  classical
  let S : Set (Submodule R V) := {M | ∃ s : Finset ι, M = s.inf p}
  have hS : S.Nonempty := ⟨⊤, ∅, by simp⟩
  obtain ⟨M, ⟨s, hs⟩, hmin⟩ := IsArtinian.set_has_minimal S hS
  subst M
  refine ⟨s, le_antisymm ?_ ?_⟩
  · apply le_iInf
    intro i
    by_contra hle
    have hlt : (insert i s).inf p < s.inf p := by
      rw [Finset.inf_insert]
      apply lt_of_le_of_ne inf_le_right
      intro he
      apply hle
      rw [← he]
      exact inf_le_left
    exact hmin ((insert i s).inf p) ⟨insert i s, rfl⟩ hlt
  · exact Finset.le_inf (fun i _ => iInf_le p i)

 

omit [LieGroup 𝓘ₙ ∞ G] in
lemma centralTangent_finite_test : ∃ s : Finset G, ∀ v : E,
    v ∈ centralTangent (G := G) (E₀ := E₀) ↔
      ∀ g ∈ s, derivative (E₀ := E₀) (commMap g) 1 v = 0 := by
  obtain ⟨s, hs⟩ := exists_finite_inf (fun g : G => (derivative (E₀ := E₀) (commMap g) 1).ker)
  refine ⟨s, fun v => ?_⟩
  change v ∈ (⨅ g : G, (derivative (E₀ := E₀) (commMap g) 1).ker) ↔ _
  rw [← hs]
  simp

lemma centralTangent_curve [T2Space G] (v : centralTangent (G := G) (E₀ := E₀)) (t : ℝ) :
    RawLieIntegration.curve (G := G) (E₀ := E₀) (v : E) t ∈ Subgroup.center G := by
  apply RawLieIntegration.curve_central
  intro g
  have hc := congrArg (fun A : E →L[ℝ] E => A v) (commMap_add_adjoint (E₀ := E₀) g)
  have hk := (mem_centralTangent (v : E)).mp v.property g
  simpa only [add_apply, hk, zero_add, ContinuousLinearMap.id_apply] using hc

omit [FiniteDimensional ℝ E₀] in
lemma centralTangent_ne_bot {s : ℕ}
    (hstop : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) (v : E) (hv : v ≠ 0) :
    centralTangent (G := G) (E₀ := E₀) ≠ ⊥ := by
  obtain ⟨w, hw, hker⟩ := exists_commutator_kernel hstop v hv
  intro hz
  have hm := (mem_centralTangent w).mpr hker
  rw [hz, Submodule.mem_bot] at hm
  exact hw hm
end RawLieAdjoint

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G] [T2Space G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)

lemma orderedAxes_mem_center {n : ℕ} (v : Fin n → GroupLieAlgebra 𝓘ₙ G)
    (hv : ∀ i t, curve (v i) t ∈ Subgroup.center G) (a : Fin n → ℝ) :
    orderedAxes v a ∈ Subgroup.center G := by
  apply (Subgroup.center G).list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact hv i (a i)

lemma orderedAxes_add_of_central {n : ℕ} (v : Fin n → GroupLieAlgebra 𝓘ₙ G)
    (hv : ∀ i t, curve (v i) t ∈ Subgroup.center G) (a a' : Fin n → ℝ) :
    orderedAxes v (a + a') = orderedAxes v a * orderedAxes v a' := by
  have hlist : ∀ l : List (Fin n),
      (l.map (fun i => curve (v i) ((a + a') i))).prod =
        (l.map (fun i => curve (v i) (a i))).prod *
          (l.map (fun i => curve (v i) (a' i))).prod := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih =>
      have hcomm : ∀ g : G, curve (v i) (a' i) * g = g * curve (v i) (a' i) :=
        fun g => (Subgroup.mem_center_iff.mp (hv i (a' i)) g).symm
      simp only [List.map_cons, List.prod_cons]
      rw [ih]
      simp only [Pi.add_apply, curve_add]
      rw [mul_assoc, ← mul_assoc (curve (v i) (a' i)), hcomm,
        mul_assoc, ← mul_assoc]
  simpa only [orderedAxes, List.ofFn_eq_map] using hlist (List.finRange n)

lemma subspaceAxes_central (z : C) :
    subspaceAxes (G := G) C z ∈ Subgroup.center G :=
  orderedAxes_mem_center _ (fun i t => RawLieAdjoint.centralTangent_curve ((Module.finBasis ℝ C) i) t) _

lemma subspaceAxes_central_add (z z' : C) :
    subspaceAxes (G := G) C (z+z') = subspaceAxes C z * subspaceAxes C z' := by
  simp only [subspaceAxes, Function.comp_apply, map_add]
  exact orderedAxes_add_of_central _
    (fun i t => RawLieAdjoint.centralTangent_curve ((Module.finBasis ℝ C) i) t) _ _

 

def centralAxesHom : Multiplicative C →* G where
  toFun z := subspaceAxes C z.toAdd
  map_one' := subspaceAxes_zero C
  map_mul' z z' := subspaceAxes_central_add z.toAdd z'.toAdd

lemma centralAxesHom_continuous : Continuous (centralAxesHom (G := G) (E₀ := E₀)) :=
  (subspaceAxes_contMDiff C).continuous

lemma centralAxesHom_range_le_center : (centralAxesHom (G := G) (E₀ := E₀)).range ≤ Subgroup.center G := by
  rintro g ⟨z,rfl⟩
  exact subspaceAxes_central z.toAdd

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G] [T2Space G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
open RawLieAdjoint

lemma transverse_test_derivative (W : Submodule ℝ E) (g : G) :
    HasFDerivAt ((chartAt E (1 : G)) ∘ (commMap g) ∘ (subspaceAxes W))
      ((derivative (E₀ := E₀) (commMap g) 1).comp W.subtypeL) 0 := by
  have hW := (subspaceAxes_contMDiff_one (G := G) W).mdifferentiableAt (x := 0) one_ne_zero
  have hg := (commMap_smooth (E₀ := E₀) g).mdifferentiableAt (x := 1) one_ne_zero
  have hc := mfderiv_comp_of_eq (I' := 𝓘ₙ) hg hW (subspaceAxes_zero (G := G) W)
  have hp := mfderiv_congr_point (I := 𝓘ₙ) (I' := 𝓘ₙ) (f := commMap g)
    (subspaceAxes_zero (G := G) W)
  rw [hp, subspaceAxes_derivative] at hc
  exact chart_comp_hasFDerivAt_one (commMap g ∘ subspaceAxes W)
    (by simp) (hg.comp_of_eq 0 hW (subspaceAxes_zero W)) _ hc

lemma transverse_test_contDiffAt (W : Submodule ℝ E) (g : G) :
    ContDiffAt ℝ 1 ((chartAt E (1 : G)) ∘ (commMap g) ∘ (subspaceAxes W)) 0 := by
  have hf : ContMDiff 𝓘(ℝ,W) 𝓘ₙ 1 (commMap g ∘ subspaceAxes W) :=
    (commMap_smooth (E₀ := E₀) g).comp (subspaceAxes_contMDiff_one W)
  have hc : ContMDiffAt 𝓘ₙ 𝓘ₙ 1 (chartAt E (1 : G)) ((commMap g ∘ subspaceAxes W) 0) := by
    simp only [Function.comp_apply, subspaceAxes_zero, commMap_one]
    exact (contMDiffOn_chart (I := 𝓘ₙ) (n := 1)).contMDiffAt
      ((chartAt E (1 : G)).open_source.mem_nhds (mem_chart_source _ _))
  exact (hc.comp 0 (hf 0)).contDiffAt

 

theorem exists_transverse_neighbourhood (W : Submodule ℝ E) (hWC : IsCompl W C) :
    ∃ U : Set W, U ∈ 𝓝 (0 : W) ∧ ∀ w ∈ U,
      (∀ g : G, commMap g (subspaceAxes W w) = 1) → w = 0 := by
  classical
  obtain ⟨s, hs⟩ := centralTangent_finite_test (G := G) (E₀ := E₀)
  let A : W →L[ℝ] (s → E) := ContinuousLinearMap.pi
    (fun g => (derivative (E₀ := E₀) (commMap (g : G)) 1).comp W.subtypeL)
  have hA : A.toLinearMap.ker = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro w hw
    have hw0 : A w = 0 := hw
    have hC : (w : E) ∈ C := (hs _).mpr (by
      intro g hg
      exact congrFun hw0 ⟨g,hg⟩)
    have hi : (w : E) ∈ W ⊓ C := ⟨w.property,hC⟩
    rw [hWC.disjoint.eq_bot, Submodule.mem_bot] at hi
    exact Subtype.ext hi
  obtain ⟨B₀, hB₀⟩ := A.toLinearMap.exists_leftInverse_of_injective hA
  let B := B₀.toContinuousLinearMap
  have hBA : B.comp A = ContinuousLinearMap.id ℝ W := by
    apply ContinuousLinearMap.ext
    intro w
    exact LinearMap.congr_fun hB₀ w
  let F : W → (s → E) := fun w g => (chartAt E (1 : G)) (commMap (g : G) (subspaceAxes W w))
  have hDF : HasFDerivAt F A 0 := by
    apply hasFDerivAt_pi.mpr
    intro g
    exact transverse_test_derivative W (g : G)
  have hCF : ContDiffAt ℝ 1 F 0 := contDiffAt_pi.mpr (fun g => transverse_test_contDiffAt W (g : G))
  have hD : HasFDerivAt (B ∘ F) (ContinuousLinearEquiv.refl ℝ W).toContinuousLinearMap 0 := by
    have hh := B.hasFDerivAt.comp 0 hDF
    exact hh.congr_fderiv hBA
  have hC : ContDiffAt ℝ 1 (B ∘ F) 0 := B.contDiff.contDiffAt.comp 0 hCF
  have hstrict := hC.hasStrictFDerivAt' hD one_ne_zero
  let e := hstrict.toOpenPartialHomeomorph (B ∘ F)
  have h0 : (0 : W) ∈ e.source := hstrict.mem_toOpenPartialHomeomorph_source
  refine ⟨e.source, e.open_source.mem_nhds h0, fun w hw hcent => ?_⟩
  apply e.injOn hw h0
  change B (F w) = B (F 0)
  apply congrArg B
  funext g
  simp only [F, hcent, subspaceAxes_zero, commMap_one]

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G] [T2Space G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)

 
theorem centralAxesHom_locally_surjective :
    ∃ V : Set G, V ∈ 𝓝 (1 : G) ∧ ∀ g ∈ V, g ∈ Subgroup.center G →
      g ∈ (centralAxesHom (G := G) (E₀ := E₀)).range := by
  obtain ⟨W,hCW⟩ := Submodule.exists_isCompl C
  obtain ⟨e,h0,he⟩ := exists_productSlice_localChart (G := G) W C hCW.symm
  obtain ⟨U,hU,htrans⟩ := exists_transverse_neighbourhood (G := G) W hCW.symm
  have he0 : e 0 = (1 : G) := (he h0).trans (productSlice_zero W C)
  have h1 : (1 : G) ∈ e.target := he0 ▸ e.map_source h0
  have he1 : e.symm (1 : G) = 0 := by rw [← he0, e.left_inv h0]
  have hpre : (fun g : G => (e.symm g).1) ⁻¹' U ∈ 𝓝 (1 : G) := by
    have hc := continuous_fst.continuousAt.comp (e.continuousAt_symm h1)
    apply hc
    simpa only [Function.comp_apply, he1, Prod.fst_zero] using hU
  refine ⟨e.target ∩ (fun g : G => (e.symm g).1) ⁻¹' U,
    Filter.inter_mem (e.open_target.mem_nhds h1) hpre, ?_⟩
  intro g hg hgcent
  have hdecomp : productSlice W C (e.symm g) = g :=
    (he (e.map_target hg.1)).symm.trans (e.right_inv hg.1)
  have hzc : subspaceAxes (G := G) C (e.symm g).2 ∈ Subgroup.center G := subspaceAxes_central _
  have hwc : subspaceAxes (G := G) W (e.symm g).1 ∈ Subgroup.center G := by
    have hprod : subspaceAxes W (e.symm g).1 * subspaceAxes C (e.symm g).2 ∈ Subgroup.center G :=
      (congrArg (fun x : G => x ∈ Subgroup.center G) hdecomp).mpr hgcent
    have hh := (Subgroup.center G).mul_mem hprod ((Subgroup.center G).inv_mem hzc)
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hh
  have hw : (e.symm g).1 = 0 := htrans _ hg.2 (fun a =>
    commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp hwc a).symm))
  refine ⟨Multiplicative.ofAdd (e.symm g).2, ?_⟩
  change subspaceAxes C (e.symm g).2 = g
  simpa only [productSlice, hw, subspaceAxes_zero, one_mul] using hdecomp

 

theorem centralAxesHom_range_isClosed :
    IsClosed ((centralAxesHom (G := G) (E₀ := E₀)).range : Set G) := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘ₙ ∞
  let Z := Subgroup.center G
  let S := (centralAxesHom (G := G) (E₀ := E₀)).range
  let H := S.subgroupOf Z
  have hZ : IsClosed (Z : Set G) := by
    have hc : IsClosed (⋂ a : G, {g : G | a*g = g*a}) :=
      isClosed_iInter fun a => isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)
    convert hc using 1
    ext g
    simp [Z, Subgroup.mem_center_iff]
  obtain ⟨V,hV,honto⟩ := centralAxesHom_locally_surjective (G := G) (E₀ := E₀)
  have hH : (H : Set Z) ∈ 𝓝 (1 : Z) := by
    have hp : (fun z : Z => (z : G)) ⁻¹' V ∈ 𝓝 (1 : Z) :=
      continuous_subtype_val.tendsto (1 : Z) hV
    exact Filter.mem_of_superset hp (fun z hz => honto z hz z.property)
  have hHC : IsClosed (H : Set Z) := H.isClosed_of_isOpen (H.isOpen_of_mem_nhds hH)
  have hclosed := hZ.isClosedMap_subtype_val (H : Set Z) hHC
  convert hclosed using 1
  ext g
  constructor
  · intro hg
    exact ⟨⟨g, centralAxesHom_range_le_center hg⟩, hg, rfl⟩
  · rintro ⟨z,hz,rfl⟩
    exact hz

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G] [T2Space G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))
open scoped Pointwise

 
theorem exists_quotient_injective_neighbourhood (W : Submodule ℝ E) (hWC : IsCompl W C) :
    ∃ U : Set W, IsOpen U ∧ 0 ∈ U ∧
      InjOn ((QuotientGroup.mk : G → G ⧸ S) ∘ subspaceAxes W) U := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘ₙ ∞
  obtain ⟨e,h0,he⟩ := exists_productSlice_localChart (G := G) W C hWC
  obtain ⟨A,T,hA,hA0,hT,hT0,hAT⟩ := mem_nhds_prod_iff'.mp (e.open_source.mem_nhds h0)
  obtain ⟨V,hV,htrans⟩ := exists_transverse_neighbourhood (G := G) W hWC
  have he0 : e 0 = (1 : G) := (he h0).trans (productSlice_zero W C)
  have h1 : (1 : G) ∈ e.target := he0 ▸ e.map_source h0
  have he1 : e.symm (1 : G) = 0 := by rw [← he0, e.left_inv h0]
  let N := e.target ∩ (e.symm ⁻¹' (V ×ˢ T))
  have hN : N ∈ 𝓝 (1 : G) := by
    apply Filter.inter_mem (e.open_target.mem_nhds h1)
    have hp : V ×ˢ T ∈ 𝓝 ((0 : W), (0 : C)) := prod_mem_nhds hV (hT.mem_nhds hT0)
    apply e.continuousAt_symm h1
    simpa only [he1, Prod.zero_eq_mk] using hp
  obtain ⟨B,hB,_,hBi,hBB⟩ := exists_closed_nhds_one_inv_eq_mul_subset hN
  have hpre : subspaceAxes (G := G) W ⁻¹' B ∈ 𝓝 (0 : W) := by
    have hc := (subspaceAxes_contMDiff (G := G) W).continuous.tendsto 0
    apply hc
    simpa only [subspaceAxes_zero] using hB
  obtain ⟨U,hUsub,hU,hU0⟩ := mem_nhds_iff.mp (Filter.inter_mem (hA.mem_nhds hA0) hpre)
  refine ⟨U,hU,hU0,?_⟩
  intro w hw w' hw' hq
  let g := (subspaceAxes (G := G) W w)⁻¹ * subspaceAxes W w'
  have hgS : g ∈ S := QuotientGroup.eq.mp hq
  have hgc : g ∈ Subgroup.center G := centralAxesHom_range_le_center hgS
  have hginN : g ∈ N := by
    apply hBB
    apply Set.mul_mem_mul (a := (subspaceAxes (G := G) W w)⁻¹)
      (b := subspaceAxes W w') (s := B) (t := B) ?_ (hUsub hw').2
    rw [← hBi]
    apply Set.mem_inv.mpr
    rw [inv_inv]
    exact (hUsub hw).2
  have hdecomp : productSlice W C (e.symm g) = g :=
    (he (e.map_target hginN.1)).symm.trans (e.right_inv hginN.1)
  have hz : subspaceAxes (G := G) C (e.symm g).2 ∈ Subgroup.center G := subspaceAxes_central _
  have hwc : subspaceAxes (G := G) W (e.symm g).1 ∈ Subgroup.center G := by
    have hprod : subspaceAxes W (e.symm g).1 * subspaceAxes C (e.symm g).2 ∈ Subgroup.center G :=
      (congrArg (fun x : G => x ∈ Subgroup.center G) hdecomp).mpr hgc
    have hh := (Subgroup.center G).mul_mem hprod ((Subgroup.center G).inv_mem hz)
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hh
  have hc0 : (e.symm g).1 = 0 := htrans _ hginN.2.1 (fun a =>
    commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_center_iff.mp hwc a).symm))
  have hcg : subspaceAxes C (e.symm g).2 = g := by
    simpa only [productSlice, hc0, subspaceAxes_zero, one_mul] using hdecomp
  have hwsource : (w, (e.symm g).2) ∈ e.source := hAT ⟨(hUsub hw).1,hginN.2.2⟩
  have hw'source : (w', (0 : C)) ∈ e.source := hAT ⟨(hUsub hw').1,hT0⟩
  have heq : e (w, (e.symm g).2) = e (w', (0 : C)) := by
    rw [he hwsource, he hw'source]
    simp only [productSlice, subspaceAxes_zero, mul_one, hcg, g, mul_inv_cancel_left]
  exact congrArg Prod.fst (e.injOn hwsource hw'source heq)

end RawLieIntegration

namespace RawLieIntegration
variable {E₀ : Type} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀] [FiniteDimensional ℝ E₀] {G : Type} [Group G] [TopologicalSpace G]
  [ChartedSpace (E₀) G]
  [LieGroup (𝓘(ℝ, E₀)) ∞ G] [T2Space G]
local notation "𝓘ₙ" => 𝓘(ℝ, E₀)
local notation "E" => E₀
local notation "C" => RawLieAdjoint.centralTangent (G := G) (E₀ := E₀)
local notation "S" => MonoidHom.range (centralAxesHom (G := G) (E₀ := E₀))
open scoped Pointwise

lemma quotient_productSlice (W : Submodule ℝ E) (p : W × C) :
    QuotientGroup.mk (productSlice (G := G) W C p) =
      (QuotientGroup.mk (subspaceAxes W p.1) : G ⧸ S) := by
  symm
  apply QuotientGroup.eq.mpr
  change (subspaceAxes W p.1)⁻¹ * (subspaceAxes W p.1 * subspaceAxes C p.2) ∈ S
  rw [inv_mul_cancel_left]
  exact ⟨Multiplicative.ofAdd p.2, rfl⟩

 

theorem exists_central_quotient_openChart (W : Submodule ℝ E) (hWC : IsCompl W C) :
    ∃ q : OpenPartialHomeomorph W (G ⧸ S), 0 ∈ q.source ∧
      (q : W → G ⧸ S) = (QuotientGroup.mk : G → G ⧸ S) ∘ subspaceAxes W := by
  let : IsTopologicalGroup G := topologicalGroup_of_lieGroup 𝓘ₙ ∞
  let f : W → G ⧸ S := (QuotientGroup.mk : G → G ⧸ S) ∘ subspaceAxes W
  have hf : Continuous f := QuotientGroup.continuous_mk.comp (subspaceAxes_contMDiff W).continuous
  obtain ⟨e,h0,he⟩ := exists_productSlice_localChart (G := G) W C hWC
  obtain ⟨A,T,hA,hA0,hT,hT0,hAT⟩ := mem_nhds_prod_iff'.mp (e.open_source.mem_nhds h0)
  obtain ⟨V,hV,hV0,hinj⟩ := exists_quotient_injective_neighbourhood (G := G) W hWC
  let U := A ∩ V
  have hU : IsOpen U := hA.inter hV
  have hU0 : (0 : W) ∈ U := ⟨hA0,hV0⟩
  have hUinj : InjOn f U := hinj.mono inter_subset_right
  have hopen : ∀ B : Set W, IsOpen B → B ⊆ U → IsOpen (f '' B) := by
    intro B hB hBU
    have hBT : B ×ˢ T ⊆ e.source := fun p hp => hAT ⟨(hBU hp.1).1,hp.2⟩
    have hh := QuotientGroup.isOpenMap_coe (N := S) _
      (e.isOpen_image_of_subset_source (hB.prod hT) hBT)
    have heq : (QuotientGroup.mk : G → G ⧸ S) '' (e '' (B ×ˢ T)) = f '' B := by
      ext x
      constructor
      · rintro ⟨g,⟨p,hp,rfl⟩,rfl⟩
        refine ⟨p.1,hp.1,?_⟩
        rw [he (hBT hp), quotient_productSlice]
        rfl
      · rintro ⟨w,hw,rfl⟩
        refine ⟨e (w,0), ⟨(w,0), ⟨hw,hT0⟩, rfl⟩, ?_⟩
        rw [he (hBT ⟨hw,hT0⟩), quotient_productSlice]
        rfl
    exact heq ▸ hh
  let q₀ := hUinj.toPartialEquiv f U
  have hqopen : IsOpenMap (q₀.source.domRestrict q₀) := by
    intro B hB
    have hBopen : IsOpen ((Subtype.val : U → W) '' B) :=
      hU.isOpenEmbedding_subtypeVal.isOpenMap _ hB
    have hBsub : (Subtype.val : U → W) '' B ⊆ U := by
      rintro w ⟨a,ha,rfl⟩
      exact a.property
    have hh := hopen _ hBopen hBsub
    change IsOpen ((fun w : U => f w) '' B)
    erw [Set.image_image] at hh
    exact hh
  refine ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict q₀ hf.continuousOn hqopen hU,hU0,rfl⟩

end RawLieIntegration
end

end OAI
