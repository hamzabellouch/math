import Mathlib
import OAI.Analysis.HardSphere.Geometry.KilledEigenvector
import OAI.Analysis.HardSphere.Geometry.SmoothSiteWeight
import OAI.Analysis.HardSphere.Comparison.DensityForcesTwoParticles
import OAI.Analysis.HardSphere.Geometry.BoxWeight

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open MeasureTheory Set Filter HardSphere.Lattice

def siteCube {K : ℕ} [NeZero K] (v : DiscreteTorus K) : CubeCell K :=
  (⟨(v 0).val, ZMod.val_lt _⟩, ⟨(v 1).val, ZMod.val_lt _⟩, ⟨(v 2).val, ZMod.val_lt _⟩)

lemma siteCube_injective {K : ℕ} [NeZero K] : Function.Injective (siteCube (K := K)) := by
  intro v w h
  have h0 := congrArg (fun z : CubeCell K ↦ z.1.val) h
  have h1 := congrArg (fun z : CubeCell K ↦ z.2.1.val) h
  have h2 := congrArg (fun z : CubeCell K ↦ z.2.2.val) h
  funext j
  fin_cases j <;> apply ZMod.val_injective <;> assumption

def siteCubeEmbedding {K : ℕ} [NeZero K] : DiscreteTorus K ↪ CubeCell K :=
  ⟨siteCube, siteCube_injective⟩

lemma unitCenter_siteCube {K : ℕ} [NeZero K] (L : Length) (v : DiscreteTorus K) :
    unitCenter L (siteCube v) = siteCenter L v := by
  funext j
  fin_cases j <;> rfl

lemma spatial_event_siteCube {m K : ℕ} [NeZero K] (L : Length) (s T : ℝ)
    (A : Finset (DiscreteTorus K)) :
    {Y : Configuration m L | ∀ v ∈ A.map siteCubeEmbedding,
      T ≤ ((pairCloseLabels L s (unitCenter L v) Y).card : ℝ)} =
    {Y : Configuration m L | A ⊆ closeSet L s T Y} := by
  classical
  ext Y
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, siteCubeEmbedding,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, unitCenter_siteCube,
    Set.mem_ofPred_eq, Finset.subset_iff, closeSet, Finset.mem_filter, Finset.mem_univ, true_and]

lemma IsGroundVector.positionLaw_ae_allowed {n : ℕ} {L : Length} {r : ℝ}
    {g : Jet n L} (hg : HardSphere.IsGroundVector n L r g) :
    ∀ᵐ X ∂groundPositionLaw n L g, X ∈ allowed n L r := by
  have he := hg.killed_eigenvector (t := 0) (le_refl 0)
  simp only [killedTransition_zero, zero_mul, neg_zero, Real.exp_zero,
    Complex.ofReal_one, one_smul] at he
  have hproj := allowedProjection_ae n L r g.1
  rw [he] at hproj
  rw [groundPositionLaw, ae_withDensity_iff]
  · filter_upwards [hproj] with X hX hpos
    by_contra hnot
    rw [indicator_of_notMem hnot] at hX
    simp [hX] at hpos
  · exact ((Lp.stronglyMeasurable g.1).measurable.norm.pow_const 2).ennreal_ofReal

lemma allowed_restrict {m n : ℕ} {L : Length} {r : ℝ} (e : Fin m ↪ Fin n)
    {X : Configuration n L} (hX : X ∈ allowed n L r) :
    (fun i ↦ X (e i)) ∈ allowed m L r := by
  rw [allowed_iff_ne] at hX ⊢
  intro i j hij
  exact hX (e i) (e j) (fun he ↦ hij (e.injective he))

lemma IsGroundVector.bathLaw_ae_allowed {m n : ℕ} {L : Length} {r : ℝ}
    {g : Jet n L} (hg : HardSphere.IsGroundVector n L r g) (e : Fin m ↪ Fin n) :
    ∀ᵐ Y ∂(groundPositionLaw n L g).map (fun X i ↦ X (e i)), Y ∈ allowed m L r := by
  have hm : Measurable (fun X : Configuration n L ↦ (fun i ↦ X (e i))) :=
    Measurable.of_eval (fun i ↦ measurable_pi_apply (e i))
  exact (ae_map_iff hm.aemeasurable (isOpen_allowed m L r).measurableSet).mpr
    ((IsGroundVector.positionLaw_ae_allowed hg).mono (fun _ hX ↦ allowed_restrict e hX))

theorem physical_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) [NeZero K] (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
    ∀ (g : Jet n L), HardSphere.IsGroundVector n L (α/D) g →
    ∀ (m : ℕ) (e : Fin m ↪ Fin n) (A : Finset (DiscreteTorus K)),
      ((groundPositionLaw n L g).map (fun X i ↦ X (e i)))
        {Y | A ⊆ closeSet L (spatialCloseScale D b) (θ*D) Y} ≤
        (ENNReal.ofReal (((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))))^A.card := by
  obtain ⟨Q,hQ,htail⟩ := spatial_full_and_bath_close_tail
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,Gθ,hb,hb1,hGθ,hlim,hfin⟩ := htail θ hθ
  refine ⟨b,Gθ,hb,hb1,hGθ,hlim,?_⟩
  intro αmax
  obtain ⟨D₀,hD₀,hDfin⟩ := hfin αmax
  refine ⟨D₀,hD₀,?_⟩
  intro n K _ L hL D α hL100 hDeq hD hα hαmax g hg m e A
  have hDp : 0<D := lt_of_lt_of_le (by norm_num) (hD₀.trans hD)
  have h := (hDfin n K L hL D α hL100 hDeq hD hα hαmax g hg
    (A.map siteCubeEmbedding)).2 m e
  rw [spatial_event_siteCube, Finset.card_map, ENNReal.ofReal_pow (by positivity)] at h
  exact h

theorem physical_omitted_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K M : ℕ) [NeZero K] (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
      α/D≤1/4096 → 6*(α/D)≤ spatialCloseScale D b → θ*D≤1/(1372*(α/D)) →
    ∀ (g : Jet n L), HardSphere.IsGroundVector n L (α/D) g →
    ∀ (m : ℕ) (e : Fin m ↪ Fin n), 1≤M → M≤K →
    let p := ENNReal.ofReal (((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))
    8*((2^27:ℕ):ℝ≥0∞)*p≤(2:ℝ≥0∞)⁻¹ →
      (∫⁻ Y, (volume : Measure (Torus L)) (omitted (microMesh (α/D)) (α/D) Y)
        ∂(groundPositionLaw n L g).map (fun X i ↦ X (e i))) ≤
      ENNReal.ofReal (1029*(α/D)^2*m) +
      (K:ℝ≥0∞)^3*(128*(((2^27:ℕ):ℝ≥0∞)*p)) +
      ENNReal.ofReal (L.val^3)*(K:ℝ≥0∞)^3*(((2^27:ℕ):ℝ≥0∞)*p)^M := by
  obtain ⟨Q,hQ,htail⟩ := physical_close_tail
  refine ⟨Q,hQ,?_⟩
  intro θ hθ
  obtain ⟨b,Gθ,hb,hb1,hGθ,hlim,hfin⟩ := htail θ hθ
  refine ⟨b,Gθ,hb,hb1,hGθ,hlim,?_⟩
  intro αmax
  obtain ⟨D₀,hD₀,hDfin⟩ := hfin αmax
  refine ⟨D₀,hD₀,?_⟩
  intro n K M _ L hL D α hL100 hDeq hD hα hαmax hrsmall hrs hT g hg m e hM hMK p hp
  have hDp : 0<D := lt_of_lt_of_le (by norm_num) (hD₀.trans hD)
  have hαp : 0<α := lt_of_lt_of_le (by norm_num) hα
  let := groundPositionLaw_probability g hg.2.2.1
  have hm : Measurable (fun X : Configuration n L ↦ (fun i ↦ X (e i))) :=
    Measurable.of_eval (fun i ↦ measurable_pi_apply (e i))
  let : IsProbabilityMeasure ((groundPositionLaw n L g).map (fun X i ↦ X (e i))) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).mpr inferInstance
  exact omitted_mean_le (div_pos hαp hDp) hrsmall (by linarith) hL hMK hM hrs hT _
    (IsGroundVector.bathLaw_ae_allowed hg e) p
    (hDfin n K L hL D α hL100 hDeq hD hα hαmax g hg m e) hp

end HardSphere.BathSlice

end

end OAI
