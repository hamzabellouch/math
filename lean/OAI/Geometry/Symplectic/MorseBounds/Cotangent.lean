import OAI.Geometry.Symplectic.MorseBounds.Symplectic
import OAI.Geometry.Symplectic.MorseBounds.ManifoldFlow

namespace OAI

noncomputable section
open Set
open scoped Manifold ContDiff

namespace MorseArnold.GenericGeometry
open scoped Manifold ContDiff
noncomputable section

abbrev SmoothModel (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] := 𝓘(ℝ, E)

section Definitions
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {M : Type} [TopologicalSpace M] [ChartedSpace (E) M]

abbrev TwoForm := (x : M) →
  TangentSpace (SmoothModel E) x →L[ℝ] TangentSpace (SmoothModel E) x →L[ℝ] ℝ

noncomputable def chartTwoForm (w : TwoForm (E := E) (M := M)) (x : M)
    (y : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  let c := extChartAt (SmoothModel E) x
  let dc := (mfderiv (SmoothModel E) (SmoothModel E) c.symm y).comp
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) y).symm.toContinuousLinearMap
  (ContinuousLinearMap.precomp ℝ dc).comp ((w (c.symm y)).comp dc)

structure SymplecticForm where
  form : TwoForm (E := E) (M := M)
  alternating : ∀ x v, form x v v = 0
  nondegenerate : ∀ x, Function.Injective (form x)
  smooth : ∀ x, ContDiffOn ℝ ∞ (chartTwoForm form x)
    (extChartAt (SmoothModel E) x).target
  closed : ∀ x y, y ∈ (extChartAt (SmoothModel E) x).target →
    ∀ u v w : E,
      fderiv ℝ (chartTwoForm form x) y u v w +
      fderiv ℝ (chartTwoForm form x) y v w u +
      fderiv ℝ (chartTwoForm form x) y w u v = 0

def criticalSet (f : M → ℝ) : Set M :=
  {x | mfderiv (SmoothModel E) 𝓘(ℝ) f x = 0}

def IsMorse (f : M → ℝ) : Prop :=
  ContMDiff (SmoothModel E) 𝓘(ℝ) ∞ f ∧
  ∀ x ∈ criticalSet (E := E) f,
    Function.Injective (fderiv ℝ
      (fderiv ℝ (f ∘ (extChartAt (SmoothModel E) x).symm))
      ((extChartAt (SmoothModel E) x) x))

def morseCounts : Set ℕ :=
  {c | ∃ f : M → ℝ, IsMorse (E := E) f ∧ (criticalSet (E := E) f).Finite ∧ (criticalSet (E := E) f).ncard = c}

noncomputable def ordinaryMorseNumber : ℕ := sInf (morseCounts (E := E) (M := M))

end Definitions

end
end MorseArnold.GenericGeometry
namespace MorseArnold.GenericGeometry
open scoped Manifold ContDiff
open Filter Topology Set
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {M : Type} [TopologicalSpace M] [ChartedSpace (E) M]
  [IsManifold (SmoothModel E) ∞ M]

omit [FiniteDimensional ℝ E] in
lemma inverse_chart_coordinateVectorField
    (V : (x : M) → TangentSpace (SmoothModel E) x) (p : M) (y : E)
    (hy : y ∈ (extChartAt (SmoothModel E) p).target) :
    mfderiv (SmoothModel E) (SmoothModel E) (extChartAt (SmoothModel E) p).symm y
      (MorseArnold.Dynamics.coordinateVectorField (E := E) V p y) =
      V ((extChartAt (SmoothModel E) p).symm y) := by
  let c := extChartAt (SmoothModel E) p
  have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hy
  simp only [SmoothModel, modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hi
  have hs : c.symm y ∈ (chartAt (E) p).source := by
    simpa only [c, extChartAt_source] using c.map_target hy
  have hd := mfderiv_chartAt_eq_tangentCoordChange (I := SmoothModel E) hs
  have hiv := congrArg (fun L => L (V (c.symm y))) hi
  change mfderiv (SmoothModel E) (SmoothModel E) c.symm y
    (tangentCoordChange (SmoothModel E) (c.symm y) p (c.symm y) (V (c.symm y))) = _
  rw [← hd]
  exact hiv

omit [FiniteDimensional ℝ E] in
lemma chart_hamiltonian_equation
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ)
    (hF : ContMDiff (SmoothModel E) 𝓘(ℝ) ∞ F)
    (V : (x : M) → TangentSpace (SmoothModel E) x)
    (hHam : ∀ x, omega.form x (V x) = mvfderiv (SmoothModel E) F x)
    (p : M) (y : E) (hy : y ∈ (extChartAt (SmoothModel E) p).target) :
    chartTwoForm omega.form p y (MorseArnold.Dynamics.coordinateVectorField (E := E) V p y) =
      fderiv ℝ (F ∘ (extChartAt (SmoothModel E) p).symm) y := by
  let c := extChartAt (SmoothModel E) p
  have hc : MDifferentiableAt (SmoothModel E) (SmoothModel E) c.symm y := by
    have h := mdifferentiableWithinAt_extChartAt_symm hy
    simpa only [SmoothModel, modelWithCornersSelf_coe, range_id,
      mdifferentiableWithinAt_univ] using h
  have he := mvfderiv_comp y (hF.mdifferentiable (by simp) (c.symm y)) hc
  ext v
  change omega.form (c.symm y)
    (mfderiv (SmoothModel E) (SmoothModel E) c.symm y
      (MorseArnold.Dynamics.coordinateVectorField (E := E) V p y))
    (mfderiv (SmoothModel E) (SmoothModel E) c.symm y v) = _
  rw [inverse_chart_coordinateVectorField V p y hy, hHam]
  have hev := (congrArg (fun L => L v) he).symm
  dsimp only [mvfderiv, NormedSpace.fromTangentSpace, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_apply] at hev
  rw [mfderiv_eq_fderiv] at hev
  exact hev

omit [FiniteDimensional ℝ E] in
lemma chartTwoForm_nondegenerate
    (omega : SymplecticForm (E := E) (M := M)) (p : M) (y : E)
    (hy : y ∈ (extChartAt (SmoothModel E) p).target) :
    Function.Injective (chartTwoForm omega.form p y) := by
  let c := extChartAt (SmoothModel E) p
  have hi : (mfderiv (SmoothModel E) (SmoothModel E) c.symm y).IsInvertible := by
    simpa only [SmoothModel, modelWithCornersSelf_coe, range_id,
      mfderivWithin_univ] using isInvertible_mfderivWithin_extChartAt_symm hy
  intro u v huv
  apply hi.injective
  apply omega.nondegenerate (c.symm y)
  ext w
  obtain ⟨z, rfl⟩ := hi.surjective w
  exact congrArg (fun L => L z) huv

theorem hamiltonian_field_coordinate_isUnit
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ) (hF : IsMorse (E := E) F)
    (V : (x : M) → TangentSpace (SmoothModel E) x)
    (hV : ContMDiff (SmoothModel E) (SmoothModel E).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (SmoothModel E) M)))
    (hHam : ∀ x, omega.form x (V x) = mvfderiv (SmoothModel E) F x)
    (p : M) (hp : p ∈ criticalSet (E := E) F) :
    IsUnit (fderiv ℝ (MorseArnold.Dynamics.coordinateVectorField (E := E) V p)
      ((extChartAt (SmoothModel E) p) p)) := by
  let c := extChartAt (SmoothModel E) p
  let W := MorseArnold.Dynamics.coordinateVectorField (E := E) V p
  let w := chartTwoForm omega.form p
  have hcp : c p ∈ c.target := c.map_source (mem_extChartAt_source p)
  have hcN : c.target ∈ 𝓝 (c p) := extChartAt_target_mem_nhds p
  have hEq : (fun y => w y (W y)) =ᶠ[𝓝 (c p)] fderiv ℝ (F ∘ c.symm) := by
    filter_upwards [hcN] with y hy
    exact chart_hamiltonian_equation omega F hF.1 V hHam p y hy
  have hFp : mvfderiv (SmoothModel E) F p = 0 := by
    change mfderiv (SmoothModel E) 𝓘(ℝ) F p = 0 at hp
    simp only [mvfderiv, hp, ContinuousLinearMap.comp_zero]
  have hv0 : V p = 0 := omega.nondegenerate p (by rw [hHam, hFp, map_zero])
  have hW0 : W (c p) = 0 :=
    (MorseArnold.Dynamics.coordinateVectorField_eq_zero_iff V p p
      (mem_extChartAt_source p)).mpr hv0
  have hW : DifferentiableAt ℝ W (c p) :=
    (MorseArnold.Dynamics.coordinateVectorField_contDiffAt V hV p).differentiableAt (by simp)
  have hw : DifferentiableAt ℝ w (c p) :=
    ((omega.smooth p (c p) hcp).contDiffAt hcN).differentiableAt (by simp)
  have hD := hw.hasFDerivAt.clm_apply hW.hasFDerivAt
  simp only [hW0, map_zero, add_zero] at hD
  have hessian := (hD.congr_of_eventuallyEq hEq.symm).fderiv
  have hi : Function.Injective (fderiv ℝ W (c p)) := by
    intro u v huv
    apply hF.2 p hp
    rw [hessian]
    simp only [ContinuousLinearMap.comp_apply, huv]
  have hA : IsUnit (fderiv ℝ W (c p)) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hi, (LinearMap.injective_iff_surjective (f := (fderiv ℝ W (c p)).toLinearMap)).mp hi⟩
  exact hA


theorem hamiltonian_small_time_nondegenerate
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ) (hF : IsMorse (E := E) F)
    (V : (x : M) → TangentSpace (SmoothModel E) x)
    (hV : ContMDiff (SmoothModel E) (SmoothModel E).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (SmoothModel E) M)))
    (hHam : ∀ x, omega.form x (V x) = mvfderiv (SmoothModel E) F x)
    (Φ : ℝ × M → M)
    (hΦ : ContMDiff (𝓘(ℝ).prod (SmoothModel E)) (SmoothModel E) ∞ Φ)
    (hzero : ∀ x, Φ (0, x) = x)
    (hODE : ∀ x, IsMIntegralCurve (fun t => Φ (t, x)) V)
    (p : M) (hp : p ∈ criticalSet (E := E) F) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ →
      let c := extChartAt (SmoothModel E) p
      IsUnit (fderiv ℝ (c ∘ (fun x => Φ (t, x)) ∘ c.symm) (c p) -
        ContinuousLinearMap.id ℝ (E)) := by
  let c := extChartAt (SmoothModel E) p
  let W := MorseArnold.Dynamics.coordinateVectorField (E := E) V p
  let w := chartTwoForm omega.form p
  have hcp : c p ∈ c.target := c.map_source (mem_extChartAt_source p)
  have hcN : c.target ∈ 𝓝 (c p) := extChartAt_target_mem_nhds p
  have hEq : (fun y => w y (W y)) =ᶠ[𝓝 (c p)] fderiv ℝ (F ∘ c.symm) := by
    filter_upwards [hcN] with y hy
    exact chart_hamiltonian_equation omega F hF.1 V hHam p y hy
  have hFp : mvfderiv (SmoothModel E) F p = 0 := by
    change mfderiv (SmoothModel E) 𝓘(ℝ) F p = 0 at hp
    simp only [mvfderiv, hp, ContinuousLinearMap.comp_zero]
  have hv0 : V p = 0 := omega.nondegenerate p (by rw [hHam, hFp, map_zero])
  have hW0 : W (c p) = 0 :=
    (MorseArnold.Dynamics.coordinateVectorField_eq_zero_iff V p p
      (mem_extChartAt_source p)).mpr hv0
  have hW : DifferentiableAt ℝ W (c p) :=
    (MorseArnold.Dynamics.coordinateVectorField_contDiffAt V hV p).differentiableAt (by simp)
  have hw : DifferentiableAt ℝ w (c p) :=
    ((omega.smooth p (c p) hcp).contDiffAt hcN).differentiableAt (by simp)
  have hD := hw.hasFDerivAt.clm_apply hW.hasFDerivAt
  simp only [hW0, map_zero, add_zero] at hD
  have hessian := (hD.congr_of_eventuallyEq hEq.symm).fderiv
  have hi : Function.Injective (fderiv ℝ W (c p)) := by
    intro u v huv
    apply hF.2 p hp
    rw [hessian]
    simp only [ContinuousLinearMap.comp_apply, huv]
  have hA : IsUnit (fderiv ℝ W (c p)) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr
      ⟨hi, (LinearMap.injective_iff_surjective (f := (fderiv ℝ W (c p)).toLinearMap)).mp hi⟩
  exact MorseArnold.Dynamics.manifold_small_time_nondegenerate V Φ hΦ hzero hODE p hA

end
end MorseArnold.GenericGeometry

namespace MorseArnold.GenericGeometry
open scoped Manifold ContDiff
open Filter Topology Set
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {M : Type} [TopologicalSpace M] [ChartedSpace (E) M]
  [IsManifold (SmoothModel E) ∞ M] [T2Space M]

omit [FiniteDimensional ℝ E] [IsManifold (SmoothModel E) ∞ M] [T2Space M] in
lemma hamiltonian_zero_iff_critical
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ)
    (V : (x : M) → TangentSpace (SmoothModel E) x)
    (hHam : ∀ x, omega.form x (V x) = mvfderiv (SmoothModel E) F x) (p : M) :
    V p = 0 ↔ p ∈ criticalSet (E := E) F := by
  constructor
  · intro hp
    have he := hHam p
    rw [hp, map_zero] at he
    change mfderiv (SmoothModel E) 𝓘(ℝ) F p = 0
    ext v
    have hev := congrArg (fun L => L v) he.symm
    dsimp only [mvfderiv, NormedSpace.fromTangentSpace, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_apply] at hev
    exact hev
  · intro hp
    apply omega.nondegenerate p
    rw [hHam, map_zero]
    change mfderiv (SmoothModel E) 𝓘(ℝ) F p = 0 at hp
    simp only [mvfderiv, hp, ContinuousLinearMap.comp_zero]

omit [FiniteDimensional ℝ E] [T2Space M] in
lemma hamiltonian_criticalSet_closed
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ)
    (V : (x : M) → TangentSpace (SmoothModel E) x)
    (hV : ContMDiff (SmoothModel E) (SmoothModel E).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (SmoothModel E) M)))
    (hHam : ∀ x, omega.form x (V x) = mvfderiv (SmoothModel E) F x) :
    IsClosed (criticalSet (E := E) F) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p hp
  let c := extChartAt (SmoothModel E) p
  let W := MorseArnold.Dynamics.coordinateVectorField (E := E) V p
  have hv : V p ≠ 0 := fun hz => hp
    ((hamiltonian_zero_iff_critical omega F V hHam p).mp hz)
  have hw : W (c p) ≠ 0 := fun h => hv
    ((MorseArnold.Dynamics.coordinateVectorField_eq_zero_iff V p p
      (mem_extChartAt_source p)).mp h)
  have hc : ContinuousAt (fun x => W (c x)) p :=
    (MorseArnold.Dynamics.coordinateVectorField_contDiffAt V hV p).continuousAt.comp
      (continuousAt_extChartAt (I := SmoothModel E) p)
  have he : ∀ᶠ x in 𝓝 p, W (c x) ≠ 0 := hc.eventually_ne hw
  filter_upwards [he, extChartAt_source_mem_nhds (I := SmoothModel E) p] with x hx hsrc
  intro hcrit
  have hz := (hamiltonian_zero_iff_critical omega F V hHam x).mpr hcrit
  apply hx
  change MorseArnold.Dynamics.coordinateVectorField (E := E) V p (c x) = 0
  exact (MorseArnold.Dynamics.coordinateVectorField_eq_zero_iff V p x hsrc).mpr hz

omit [T2Space M] in
lemma hamiltonian_criticalSet_discrete
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ) (hF : IsMorse (E := E) F)
    (V : (x : M) → TangentSpace (SmoothModel E) x)
    (hV : ContMDiff (SmoothModel E) (SmoothModel E).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (SmoothModel E) M)))
    (hHam : ∀ x, omega.form x (V x) = mvfderiv (SmoothModel E) F x) :
    IsDiscrete (criticalSet (E := E) F) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro p hp
  let c := extChartAt (SmoothModel E) p
  let W := MorseArnold.Dynamics.coordinateVectorField (E := E) V p
  have hW : DifferentiableAt ℝ W (c p) :=
    (MorseArnold.Dynamics.coordinateVectorField_contDiffAt V hV p).differentiableAt (by simp)
  have hA : IsUnit (fderiv ℝ W (c p)) :=
    hamiltonian_field_coordinate_isUnit omega F hF V hV hHam p hp
  have hi := (ContinuousLinearMap.isUnit_iff_bijective.mp hA).1
  obtain ⟨C, _, hC⟩ := (LinearMap.injective_iff_antilipschitz
    (fderiv ℝ W (c p)).toLinearMap).mp hi
  have hn : ∀ᶠ y in 𝓝[≠] (c p), W y ≠ 0 :=
    hW.hasFDerivAt.eventually_ne ⟨C, hC⟩
  have hnear : ∀ᶠ y in 𝓝 (c p), W y = 0 → y = c p := by
    rw [eventually_nhdsWithin_iff] at hn
    filter_upwards [hn] with y hy hz
    by_contra he
    exact hy he hz
  have hpull := (continuousAt_extChartAt (I := SmoothModel E) p).eventually hnear
  have hpoint : ∀ᶠ q in 𝓝 p, q ∈ criticalSet (E := E) F → q = p := by
    filter_upwards [extChartAt_source_mem_nhds (I := SmoothModel E) p, hpull] with q hq hWq hcrit
    have hz := (hamiltonian_zero_iff_critical omega F V hHam q).mpr hcrit
    apply c.injOn hq (mem_extChartAt_source p)
    apply hWq
    change MorseArnold.Dynamics.coordinateVectorField (E := E) V p (c q) = 0
    exact (MorseArnold.Dynamics.coordinateVectorField_eq_zero_iff V p q hq).mpr hz
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hpoint
  refine ⟨U, hU, ?_⟩
  ext q
  constructor
  · rintro ⟨hqU, hqcrit⟩
    exact hUsub hqU hqcrit
  · rintro rfl
    exact ⟨hpU, hp⟩

omit [T2Space M] in
theorem hamiltonian_criticalSet_finite
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ) (hF : IsMorse (E := E) F)
    (V : (x : M) → TangentSpace (SmoothModel E) x)
    (hV : ContMDiff (SmoothModel E) (SmoothModel E).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (SmoothModel E) M)))
    (hHam : ∀ x, omega.form x (V x) = mvfderiv (SmoothModel E) F x)
    (K : Set M) (hK : IsCompact K) (hcrit : criticalSet (E := E) F ⊆ K)
    : (criticalSet (E := E) F).Finite :=
  (hK.of_isClosed_subset (hamiltonian_criticalSet_closed omega F V hV hHam) hcrit).finite
    (hamiltonian_criticalSet_discrete omega F hF V hV hHam)

theorem compact_hamiltonian_small_time
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ) (hF : IsMorse (E := E) F)
    (V : (x : M) → TangentSpace (SmoothModel E) x)
    (hV : ContMDiff (SmoothModel E) (SmoothModel E).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle (SmoothModel E) M)))
    (hHam : ∀ x, omega.form x (V x) = mvfderiv (SmoothModel E) F x)
    (K : Set M) (hK : IsCompact K) (hcrit : criticalSet (E := E) F ⊆ K)
    (Φ : ℝ × M → M)
    (hΦ : ContMDiff (𝓘(ℝ).prod (SmoothModel E)) (SmoothModel E) ∞ Φ)
    (hzero : ∀ x, Φ (0, x) = x)
    (hInv : ∀ t x, x ∈ K → Φ (t, x) ∈ K)
    (hODE : ∀ x, IsMIntegralCurve (fun t => Φ (t, x)) V) :
    (criticalSet (E := E) F).Finite ∧
    ∃ ε : ℝ, 0 < ε ∧ ε < Real.pi ∧
      (∀ x ∈ K, Φ (ε, x) = x ↔ x ∈ criticalSet (E := E) F) ∧
      (∀ x ∈ criticalSet (E := E) F,
        let c := extChartAt (SmoothModel E) x
        IsUnit (fderiv ℝ (c ∘ (fun y => Φ (ε, y)) ∘ c.symm) (c x) -
          ContinuousLinearMap.id ℝ (E))) := by

  classical
  have hfinite := hamiltonian_criticalSet_finite omega F hF V hV hHam K hK hcrit
  refine ⟨hfinite, ?_⟩
  obtain ⟨τ, hτ, hperiod⟩ := MorseArnold.Dynamics.compact_short_period V hV K hK
    (fun z : ℝ × K => Φ (z.1, z.2))
    (hΦ.continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    (fun x => hzero x) (fun t x => hInv t x x.property) (fun x => hODE x)
  have hsmall : ∀ x ∈ criticalSet (E := E) F, ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ →
      let c := extChartAt (SmoothModel E) x
      IsUnit (fderiv ℝ (c ∘ (fun y => Φ (t, y)) ∘ c.symm) (c x) -
        ContinuousLinearMap.id ℝ (E)) :=
    fun x hx => hamiltonian_small_time_nondegenerate omega F hF V hV hHam Φ hΦ hzero hODE x hx
  let P := fun (δ : ℝ) (x : M) => ∀ t, 0 < t → t < δ →
      let c := extChartAt (SmoothModel E) x
      IsUnit (fderiv ℝ (c ∘ (fun y => Φ (t, y)) ∘ c.symm) (c x) -
        ContinuousLinearMap.id ℝ (E))
  have hb : ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ hfinite.toFinset, P δ x := by
    have hall : ∀ x ∈ hfinite.toFinset, ∃ δ : ℝ, 0 < δ ∧ P δ x := by
      simpa only [Set.Finite.mem_toFinset] using hsmall
    generalize hfinite.toFinset = T at hall ⊢
    induction T using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert x T hx ih =>
      obtain ⟨a, ha, hax⟩ := hall x (Finset.mem_insert_self x T)
      obtain ⟨b, hb, hbT⟩ := ih (fun y hy => hall y (Finset.mem_insert_of_mem hy))
      refine ⟨min a b, lt_min ha hb, ?_⟩
      intro y hy t ht hlt
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hax t ht (hlt.trans_le (min_le_left _ _))
      · exact hbT y hy t ht (hlt.trans_le (min_le_right _ _))
  obtain ⟨δ, hδ, hnd⟩ := hb
  let ε := min (min τ δ) Real.pi / 2
  have he : 0 < ε := half_pos (lt_min (lt_min hτ hδ) Real.pi_pos)
  have heSmall : ε < min (min τ δ) Real.pi := half_lt_self
    (lt_min (lt_min hτ hδ) Real.pi_pos)
  have hep : ε < Real.pi := heSmall.trans_le (min_le_right _ _)
  have heτ : ε < τ := (heSmall.trans_le (min_le_left _ _)).trans_le (min_le_left _ _)
  have heδ : ε < δ := (heSmall.trans_le (min_le_left _ _)).trans_le (min_le_right _ _)
  refine ⟨ε, he, hep, ?_, ?_⟩
  · intro x hx
    exact (hperiod ⟨x, hx⟩ ε he heτ).trans (hamiltonian_zero_iff_critical omega F V hHam x)
  · intro x hx
    exact hnd x (hfinite.mem_toFinset.mpr hx) ε he heδ

end
end MorseArnold.GenericGeometry

namespace MorseArnold.GenericGeometry
open scoped Manifold ContDiff
open Filter Topology Set
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {M : Type} [TopologicalSpace M] [ChartedSpace (E) M]
  [IsManifold (SmoothModel E) ∞ M]

lemma bilinear_invertible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (w : E →L[ℝ] E →L[ℝ] ℝ)
    (hi : Function.Injective w) : w.IsInvertible := by
  have hr : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
    by
    have h := (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (E →L[ℝ] ℝ)).finrank_eq
    rw [Subspace.dual_finrank_eq] at h
    exact h
  have hs : Function.Surjective w :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hr).mp hi
  exact ⟨ContinuousLinearEquiv.ofBijective w (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩

noncomputable def hamiltonianField
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ)
    (x : M) : TangentSpace (SmoothModel E) x :=
  (omega.form x).inverse (mvfderiv (SmoothModel E) F x)

omit [IsManifold (SmoothModel E) ∞ M] in
lemma hamiltonianField_equation
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ) (x : M) :
    omega.form x (hamiltonianField omega F x) = mvfderiv (SmoothModel E) F x := by
  have hi : (omega.form x).IsInvertible :=
    bilinear_invertible (E := E) (omega.form x) (omega.nondegenerate x)
  exact hi.self_apply_inverse _

lemma hamiltonianField_coordinate_smooth
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ)
    (hF : ContMDiff (SmoothModel E) 𝓘(ℝ) ∞ F) (p : M) :
    ContDiffAt ℝ ∞
      (MorseArnold.Dynamics.coordinateVectorField (E := E) (hamiltonianField omega F) p)
      ((extChartAt (SmoothModel E) p) p) := by
  let c := extChartAt (SmoothModel E) p
  let w := chartTwoForm omega.form p
  have hcp : c p ∈ c.target := c.map_source (mem_extChartAt_source p)
  have hcN : c.target ∈ 𝓝 (c p) := extChartAt_target_mem_nhds p
  have hw : ContDiffAt ℝ ∞ w (c p) := (omega.smooth p _ hcp).contDiffAt hcN
  have hcw : (w (c p)).IsInvertible :=
    bilinear_invertible _ (chartTwoForm_nondegenerate omega p _ hcp)
  have hinv : ContDiffAt ℝ ∞ (fun y => (w y).inverse) (c p) :=
    hcw.contDiffAt_map_inverse.comp _ hw
  have hc : ContMDiffAt (SmoothModel E) (SmoothModel E) ∞ c.symm (c p) :=
    (contMDiffOn_extChartAt_symm p _ hcp).contMDiffAt hcN
  have hdF : ContDiffAt ℝ ∞ (fderiv ℝ (F ∘ c.symm)) (c p) :=
    (hF.contMDiffAt.comp _ hc).contDiffAt.fderiv_right (by simp)
  apply (hinv.clm_apply hdF).congr_of_eventuallyEq
  filter_upwards [hcN] with y hy
  have he := chart_hamiltonian_equation omega F hF (hamiltonianField omega F)
    (hamiltonianField_equation omega F) p y hy
  have hi := bilinear_invertible _ (chartTwoForm_nondegenerate omega p y hy)
  exact (hi.inverse_apply_self _).symm.trans (congrArg (fun a => (w y).inverse a) he)

lemma hamiltonianField_smooth
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ)
    (hF : ContMDiff (SmoothModel E) 𝓘(ℝ) ∞ F) :
    ContMDiff (SmoothModel E) (SmoothModel E).tangent ∞
      (fun x => (⟨x, hamiltonianField omega F x⟩ : TangentBundle (SmoothModel E) M)) := by
  intro p
  apply (Bundle.contMDiffAt_section p).mpr
  have hW := (hamiltonianField_coordinate_smooth omega F hF p).contMDiffAt
  have hh := hW.comp p (contMDiffAt_extChartAt (I := SmoothModel E))
  apply hh.congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I := SmoothModel E) p] with x hx
  dsimp only [Function.comp_apply]
  rw [MorseArnold.Dynamics.coordinateVectorField_apply (E := E) _ p x hx]
  rfl

theorem exists_smooth_hamiltonian_field
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ)
    (hF : ContMDiff (SmoothModel E) 𝓘(ℝ) ∞ F) :
    ∃ V : (x : M) → TangentSpace (SmoothModel E) x,
      ContMDiff (SmoothModel E) (SmoothModel E).tangent ∞
        (fun x => (⟨x, V x⟩ : TangentBundle (SmoothModel E) M)) ∧
      ∀ x, omega.form x (V x) = mvfderiv (SmoothModel E) F x :=
  ⟨hamiltonianField omega F, hamiltonianField_smooth omega F hF,
    hamiltonianField_equation omega F⟩

end
end MorseArnold.GenericGeometry
namespace MorseArnold.GenericGeometry
open Set
open scoped Manifold ContDiff

def LocalHamiltonianModelExistence : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (M : Type) [TopologicalSpace M] [ChartedSpace (E) M]
    [IsManifold (SmoothModel E) ∞ M] [T2Space M]
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ),
    IsMorse (E := E) F →
    ∀ U : Set M, IsOpen U → IsCompact Uᶜ →
    ∀ Ψ : ℝ × M → M,
    ContMDiffOn (𝓘(ℝ).prod (SmoothModel E)) (SmoothModel E) ∞ Ψ (univ ×ˢ U) →
    (∀ x ∈ U, Ψ (0,x) = x) →
    (∀ x ∈ U, IsMIntegralCurve (fun t => Ψ (t,x)) (hamiltonianField omega F)) →
    (∀ t x, x ∈ U → Ψ (t,x) ∈ U) →
    (∀ t, 0 < t → t < Real.pi → ∀ x ∈ U, Ψ (t,x) ≠ x) →
    ∃ Φ : ℝ × M → M,
      ContMDiff (𝓘(ℝ).prod (SmoothModel E)) (SmoothModel E) ∞ Φ ∧
      (∀ x, Φ (0,x) = x) ∧
      (∀ s t x, Φ (s+t,x) = Φ (s,Φ (t,x))) ∧
      (∀ x, IsMIntegralCurve (fun t => Φ (t,x)) (hamiltonianField omega F)) ∧
      (∀ t x, x ∈ U → Φ (t,x) = Ψ (t,x)) ∧
      (∀ t x, x ∉ U → Φ (t,x) ∉ U) ∧
      (criticalSet (E := E) F).Finite ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < Real.pi ∧
        (∀ x, Φ (ε,x) = x ↔ x ∈ criticalSet (E := E) F) ∧
        (∀ x, Φ (ε,x) = x →
          let c := extChartAt (SmoothModel E) x
          IsUnit (fderiv ℝ (c ∘ (fun y => Φ (ε,y)) ∘ c.symm) (c x) -
            ContinuousLinearMap.id ℝ (E)))
end MorseArnold.GenericGeometry

namespace MorseArnold.GenericGeometry
open Set
open scoped Manifold ContDiff
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {M : Type} [TopologicalSpace M] [ChartedSpace (E) M]
  [IsManifold (SmoothModel E) ∞ M] [T2Space M]

omit [TopologicalSpace M] [T2Space M] in
lemma flow_core_invariant (Φ Ψ : ℝ × M → M) (U : Set M)
    (hi : ∀ x, Φ (0,x) = x)
    (hadd : ∀ s t x, Φ (s+t,x) = Φ (s,Φ (t,x)))
    (hext : ∀ t x, x ∈ U → Φ (t,x) = Ψ (t,x))
    (hU : ∀ t x, x ∈ U → Ψ (t,x) ∈ U) :
    ∀ t x, x ∉ U → Φ (t,x) ∉ U := by
  intro t x hx htx
  have h := hU (-t) (Φ (t,x)) htx
  rw [← hext (-t) _ htx, ← hadd, neg_add_cancel, hi] at h
  exact hx h

lemma criticalSet_subset_core
    (omega : SymplecticForm (E := E) (M := M)) (F : M → ℝ) (hF : IsMorse (E := E) F)
    (U : Set M) (Ψ : ℝ × M → M)
    (hi : ∀ x ∈ U, Ψ (0,x) = x)
    (hd : ∀ x ∈ U, IsMIntegralCurve (fun t => Ψ (t,x)) (hamiltonianField omega F))
    (hnf : ∀ t, 0 < t → t < Real.pi → ∀ x ∈ U, Ψ (t,x) ≠ x) :
    criticalSet (E := E) F ⊆ Uᶜ := by
  intro x hx hU
  have hz : hamiltonianField omega F x = 0 :=
    (hamiltonian_zero_iff_critical omega F (hamiltonianField omega F)
      (hamiltonianField_equation omega F) x).mpr hx
  have he := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0)
    ((hamiltonianField_smooth omega F hF.1).of_le (by simp))
    (hd x hU) (isMIntegralCurve_const hz) (hi x hU)
  exact hnf (Real.pi/2) (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
    x hU (congrFun he (Real.pi/2))

theorem localHamiltonianModelExistence : LocalHamiltonianModelExistence := by
  intro E _ _ _ M _ _ _ _ omega F hF U hU hK Ψ hΨ hΨi hΨd hΨU hΨnf
  let V := hamiltonianField omega F
  have hV := hamiltonianField_smooth omega F hF.1
  have hHam := hamiltonianField_equation omega F
  obtain ⟨Φ,hΦ,hi,hadd,hd,hext⟩ :=
    MorseArnold.ManifoldFlow.exists_compact_core_smooth_flow V hV Uᶜ U hK hU
      (compl_union_self U) Ψ hΨ hΨi hΨd
  have hInv := flow_core_invariant Φ Ψ U hi hadd hext hΨU
  have hcrit := criticalSet_subset_core omega F hF U Ψ hΨi hΨd hΨnf
  obtain ⟨hfin, ε, he, hep, hfix, hnd⟩ := compact_hamiltonian_small_time
    omega F hF V hV hHam Uᶜ hK hcrit Φ hΦ hi hInv hd
  refine ⟨Φ,hΦ,hi,hadd,hd,hext,hInv,hfin,ε,he,hep,?_,?_⟩
  · intro x
    by_cases hx : x ∈ U
    · constructor
      · intro hf
        exact (hΨnf ε he hep x hx ((hext ε x hx).symm.trans hf)).elim
      · intro hc
        exact (hcrit hc hx).elim
    · exact hfix x hx
  · intro x hx
    apply hnd x
    by_cases hxu : x ∈ U
    · exact (hΨnf ε he hep x hxu ((hext ε x hxu).symm.trans hx)).elim
    · exact (hfix x hxu).mp hx

end
end MorseArnold.GenericGeometry

end

end OAI
