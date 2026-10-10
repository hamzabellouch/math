import Mathlib

namespace OAI

section

open MeasureTheory Set Filter
open scoped ENNReal Topology Manifold ContDiff

namespace SmoothObstruction

/-- Measurable conjugacy on invariant conull measurable subsets, not a
continuous conjugacy and not merely a factor map. -/
def ConullConjugate {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (T : X → X) (ν : Measure Y) (S : Y → Y) : Prop :=
  ∃ (A : Set X) (B : Set Y), MeasurableSet A ∧ MeasurableSet B ∧
    μ Aᶜ = 0 ∧ ν Bᶜ = 0 ∧ T ⁻¹' A = A ∧ S ⁻¹' B = B ∧
    ∃ e : A ≃ᵐ B,
      MeasurePreserving e (μ.comap (Subtype.val : A → X))
        (ν.comap (Subtype.val : B → Y)) ∧
      ∀ (x y : A), T x = y → (e y : Y) = S (e x)

/-- Positive smooth local coordinate densities. In a half-space chart,
`ContDiffOn` includes smoothness up to the boundary. Absolute Lebesgue density
is used; no orientation or volume form is part of the data. -/
def SmoothPositiveDensity {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [MeasurableSpace M]
    (ν : Measure M) : Prop :=
  ∀ x : M, ∃ f : EuclideanSpace ℝ (Fin d) → ℝ,
    ContDiffOn ℝ ∞ f (extChartAt I x).target ∧
    (∀ y ∈ (extChartAt I x).target, 0 < f y) ∧
    Measure.map (extChartAt I x) (ν.restrict (extChartAt I x).source) =
      (volume.withDensity (fun y => ENNReal.ofReal (f y))).restrict
        (extChartAt I x).target

/-- A smooth positive-volume model with a specified Euclidean or half-space
manifold model. All model dimensions will be quantified below. -/
def HasModelWith {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) {d : ℕ} {H : Type} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H) : Prop :=
  ∃ (M : Type) (_ : TopologicalSpace M) (_ : MeasurableSpace M)
      (_ : BorelSpace M) (_ : T2Space M) (_ : SecondCountableTopology M)
      (_ : CompactSpace M) (_ : ChartedSpace H M) (_ : IsManifold I ∞ M)
      (ν : Measure M) (_ : IsProbabilityMeasure ν)
      (S : Diffeomorph I I M M ∞),
    SmoothPositiveDensity I ν ∧ MeasurePreserving S ν ν ∧
      ConullConjugate μ T ν S

/-- Closed manifolds of all dimensions (including zero), and smooth manifolds
with boundary of every positive finite dimension. Nonorientable manifolds
are included: no orientability hypothesis occurs. -/
def HasSmoothPositiveVolumeModel {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : X → X) : Prop :=
  (∃ d : ℕ, HasModelWith μ T (𝓡 d)) ∨
    (∃ d : ℕ, ∃ _ : NeZero d, HasModelWith μ T (𝓡∂ d))


end SmoothObstruction

namespace SmoothObstruction.ConullTransport
open MeasureTheory Set
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- A measurable total representative of the inverse conjugacy; it uses an
arbitrary value only off the given invariant conull subset. -/
noncomputable def inverse (A : Set X) (B : Set Y) (e : A ≃ᵐ B) (x₀ : X) : Y → X :=
  Function.extend (Subtype.val : B → Y) (fun y => (e.symm y : X)) (fun _ => x₀)

lemma inverse_coe (A : Set X) (B : Set Y) (e : A ≃ᵐ B) (x₀ : X) (y : B) :
    inverse A B e x₀ y=(e.symm y : X) :=
  Subtype.val_injective.extend_apply _ _ y

lemma measurable_inverse (A : Set X) (B : Set Y) (e : A ≃ᵐ B) (x₀ : X)
    (hB : MeasurableSet B) : Measurable (inverse A B e x₀) :=
  (MeasurableEmbedding.subtype_coe hB).measurable_extend
    (measurable_subtype_coe.comp e.symm.measurable) measurable_const

/-- The arbitrary extension still pushes the full original probability
measure to exactly μ. No normalization or exceptional-set approximation. -/
theorem preserving_inverse (μ : Measure X) (ν : Measure Y)
    (A : Set X) (B : Set Y) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAc : μ Aᶜ=0) (hBc : ν Bᶜ=0) (e : A ≃ᵐ B)
    (he : MeasurePreserving e (μ.comap (Subtype.val : A → X))
      (ν.comap (Subtype.val : B → Y))) (x₀ : X) :
    MeasurePreserving (inverse A B e x₀) ν μ := by
  have hAr : μ.restrict A=μ := Measure.restrict_eq_self_of_ae_mem hAc
  have hBr : ν.restrict B=ν := Measure.restrict_eq_self_of_ae_mem hBc
  have hincA : MeasurePreserving (Subtype.val : A → X) (μ.comap Subtype.val) μ :=
    ⟨measurable_subtype_coe,(map_comap_subtype_coe hA μ).trans hAr⟩
  have hpre := hincA.comp (he.symm e)
  refine ⟨measurable_inverse A B e x₀ hB,?_⟩
  rw [←hBr,←map_comap_subtype_coe hB ν,
    Measure.map_map (measurable_inverse A B e x₀ hB) measurable_subtype_coe]
  have hh : inverse A B e x₀ ∘ (Subtype.val : B → Y)=
      (Subtype.val : A → X) ∘ e.symm := by
    funext y
    exact inverse_coe A B e x₀ y
  rw [hh]
  exact hpre.map_eq

omit [MeasurableSpace X] [MeasurableSpace Y] in
lemma invariant_iterates (T : X → X) (A : Set X) (hA : T ⁻¹' A=A) :
    ∀ n, ∀ x∈A,(T^[n]) x∈A := by
  intro n x hx
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact show (T^[n]) x∈T ⁻¹' A from by rw [hA]; exact ih

/-- The total representative intertwines every nonnegative iterate on the
original invariant conull set, not merely as unrelated a.e. identities. -/
theorem inverse_iterates (A : Set X) (B : Set Y) (e : A ≃ᵐ B) (x₀ : X)
    (T : X → X) (S : Y → Y) (hA : T ⁻¹' A=A) (hB : S ⁻¹' B=B)
    (heq : ∀ (x y : A),T x=y → (e y : Y)=S (e x)) :
    ∀ n,∀ y∈B,inverse A B e x₀ ((S^[n]) y)=(T^[n]) (inverse A B e x₀ y) := by
  have hstep (y : B) : inverse A B e x₀ (S y)=T (e.symm y) := by
    let x := e.symm y
    let x' : A := ⟨T x,show (x:X)∈T ⁻¹' A from by rw [hA]; exact x.property⟩
    have hey : (e x' : Y)=S y := by
      have hh := heq x x' rfl
      simpa [x] using hh
    rw [←hey,inverse_coe]
    simp [x',x]
  intro n y hy
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    let y' : B := ⟨(S^[n]) y,invariant_iterates S B hB n y hy⟩
    have ht := hstep y'
    rw [←inverse_coe A B e x₀ y'] at ht
    exact ht.trans (congrArg T ih)

/-- Faithful observation transport supplied by the literal conull conjugacy.
In particular ALL finite name distributions can be pushed through r. -/
theorem from_conjugate (μ : Measure X) (ν : Measure Y) (T : X → X) (S : Y → Y)
    (h : SmoothObstruction.ConullConjugate μ T ν S) (x₀ : X) :
    ∃ r : Y → X,MeasurePreserving r ν μ ∧
      ∃ B : Set Y,MeasurableSet B ∧ ν Bᶜ=0 ∧ S ⁻¹' B=B ∧
        ∀ n,∀ y∈B,r ((S^[n]) y)=(T^[n]) (r y) := by
  obtain ⟨A,B,hA,hB,hAc,hBc,hTA,hSB,e,he,heq⟩ := h
  exact ⟨inverse A B e x₀,preserving_inverse μ ν A B hA hB hAc hBc e he x₀,
    B,hB,hBc,hSB,inverse_iterates A B e x₀ T S hTA hSB heq⟩
end SmoothObstruction.ConullTransport

namespace SmoothObstruction.ConullTransport
open MeasureTheory Set
variable {X Y : Type*}

lemma invariant_inverse (S : Y ≃ Y) (B : Set Y) (hB : S ⁻¹' B=B) :
    S.symm ⁻¹' B=B := by
  ext y
  have hh := congrArg (fun A : Set Y => S.symm y∈A) hB
  simpa only [Set.mem_preimage,S.apply_symm_apply] using hh.symm.to_iff

/-- The same original invariant conull set supports both time directions.
No countable collection of unrelated a.e. conjugacies is substituted. -/
theorem inverse_time (r : Y → X) (T : X ≃ X) (S : Y ≃ Y)
    (B : Set Y) (hB : S ⁻¹' B=B)
    (h : ∀ n,∀ y∈B,r ((S^[n]) y)=(T^[n]) (r y)) :
    ∀ n,∀ y∈B,r ((S.symm^[n]) y)=(T.symm^[n]) (r y) := by
  have hBinv := invariant_inverse S B hB
  have hstep (y : Y) (hy : y∈B) : r (S.symm y)=T.symm (r y) := by
    have hy' : S.symm y∈B := by
      change y∈S.symm ⁻¹' B
      rwa [hBinv]
    have hh := h 1 (S.symm y) hy'
    simp only [Function.iterate_one,S.apply_symm_apply] at hh
    simpa only [T.symm_apply_apply] using (congrArg T.symm hh).symm
  intro n y hy
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',
      hstep _ (invariant_iterates S.symm B hBinv n y hy),ih]

variable [MeasurableSpace X] [MeasurableSpace Y]

/-- Faithful bilateral observation transport from the literal main's
conjugacy, including the invariant-conull and exact law clauses. -/
theorem from_conjugate_bilateral (μ : Measure X) (ν : Measure Y)
    (T : X ≃ X) (S : Y ≃ Y) (h : SmoothObstruction.ConullConjugate μ T ν S) (x₀ : X) :
    ∃ r : Y → X,MeasurePreserving r ν μ ∧
      ∃ B : Set Y,MeasurableSet B ∧ ν Bᶜ=0 ∧ S ⁻¹' B=B ∧ S.symm ⁻¹' B=B ∧
        (∀ n,∀ y∈B,r ((S^[n]) y)=(T^[n]) (r y)) ∧
        (∀ n,∀ y∈B,r ((S.symm^[n]) y)=(T.symm^[n]) (r y)) := by
  obtain ⟨r,hr,B,hB,hBc,hSB,he⟩ := from_conjugate μ ν T S h x₀
  exact ⟨r,hr,B,hB,hBc,hSB,invariant_inverse S B hSB,he,inverse_time r T S B hSB he⟩
end SmoothObstruction.ConullTransport

end

end OAI
