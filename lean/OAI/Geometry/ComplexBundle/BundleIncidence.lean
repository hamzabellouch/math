import OAI.Geometry.ComplexBundle.Evaluation
import OAI.Geometry.ComplexBundle.OpenIncidence

namespace OAI

noncomputable section

/-! Rank transport and smooth bundle-incidence families. -/

section
open Module
namespace Kaplansky.Incidence
variable {𝕜 E F D R ι : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F]
  [AddCommGroup D] [Module 𝕜 D] [AddCommGroup R] [Module 𝕜 R]

/-- Strict collective-image rank bounds are invariant under actual fiber
coordinate equivalences. -/
theorem rank_expansion_of_coordinates (T : ι → E →ₗ[𝕜] F) (C : ι → D →ₗ[𝕜] R)
    (e : E ≃ₗ[𝕜] D) (f : F ≃ₗ[𝕜] R)
    (hcomm : ∀ i x, f (T i x)=C i (e x)) {s t : ℕ}
    (hC : ∀ S : Submodule 𝕜 D, finrank 𝕜 S=s →
      t<finrank 𝕜 (⨆ i, S.map (C i) : Submodule 𝕜 R)) :
    ∀ S : Submodule 𝕜 E, finrank 𝕜 S=s →
      t<finrank 𝕜 (⨆ i, S.map (T i) : Submodule 𝕜 F) := by
  intro S hS
  have h := hC (S.map e.toLinearMap) (by simpa only [e.finrank_map_eq] using hS)
  have he : (⨆ i, (S.map e.toLinearMap).map (C i) : Submodule 𝕜 R)=
      (⨆ i, S.map (T i) : Submodule 𝕜 F).map f.toLinearMap := by
    rw [Submodule.map_iSup]
    apply iSup_congr
    intro i
    rw [← Submodule.map_comp,← Submodule.map_comp]
    congr 1
    ext x
    exact (hcomm i x).symm
  rw [he,f.finrank_map_eq] at h
  exact h

end Kaplansky.Incidence

end

section
open Bundle Module Set
open scoped Topology Manifold ContDiff
namespace Kaplansky.Incidence
variable {X B : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace B] [ChartedSpace X B]
  [IsManifold 𝓘(ℝ,X) ∞ B] [T2Space B] [CompactSpace B]
  {q d r : ℕ} (E F : B → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (Fin d → ℂ) E)] [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
  [FiberBundle (Fin d → ℂ) E] [FiberBundle (Fin r → ℂ) F]
  [VectorBundle ℝ (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
  [VectorBundle ℝ (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]
  [ContMDiffVectorBundle ∞ (Fin d → ℂ) E 𝓘(ℝ,X)]
  [ContMDiffVectorBundle ∞ (Fin r → ℂ) F 𝓘(ℝ,X)]

/-- The bundle incidence construction on a compact smooth manifold without
boundary. The conclusion gives actual fiber maps, smooth in every frame,
and strict image-rank bounds for every subspace of each original fiber.
Global generation, incidence nullity and the good tuple are all constructed. -/
theorem exists_bundle_incidence_maps (pairs : Finset (ℕ × ℕ))
    (hpairs : ∀ p ∈ pairs, p.1≤d ∧ p.2≤r ∧
      finrank ℝ X+2*p.1*(d-p.1)+2*p.2*(r-p.2)<2*q*p.1*(r-p.2)) :
    ∃ T : Fin q → ∀ y, E y →L[ℂ] F y,
      (∀ i (e : Trivialization (Fin d → ℂ) (π (Fin d → ℂ) E))
        (f : Trivialization (Fin r → ℂ) (π (Fin r → ℂ) F))
        [MemTrivializationAtlas e] [MemTrivializationAtlas f],
        ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,(Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) ∞
          (complexHomCoordinates E F e f (T i)) (e.baseSet ∩ f.baseSet)) ∧
      ∀ y p, p ∈ pairs → ∀ S : Submodule ℂ (E y), finrank ℂ S=p.1 →
        p.2<finrank ℂ (⨆ i, S.map (T i y).toLinearMap : Submodule ℂ (F y)) := by
  classical
  obtain ⟨n,s,hs,hsm⟩ := exists_finite_smooth_hom_evaluation
    (F₁ := Fin d → ℂ) (F₂ := Fin r → ℂ) 𝓘(ℝ,X) E F
  let e (x : B) := trivializationAt (Fin d → ℂ) E x
  let f (x : B) := trivializationAt (Fin r → ℂ) F x
  let U (x : B) := (e x).baseSet ∩ (f x).baseSet
  have hU : ∀ x, IsOpen (U x) := fun x => (e x).open_baseSet.inter (f x).open_baseSet
  have hxU : ∀ x, x ∈ U x := fun x =>
    ⟨mem_baseSet_trivializationAt (Fin d → ℂ) E x,mem_baseSet_trivializationAt (Fin r → ℂ) F x⟩
  obtain ⟨c,hc,hcover⟩ := exists_countable_local_chart_cover (X := X) U hU hxU
  let := hc.toEncodable
  let V := Fin q → Fin n → ℂ
  let evB (x y : B) : V →L[ℂ] MatrixTuple q d r :=
    tupleEvaluation (homEvaluationCoordinates E F s (e x) (f x) y)
  have heB (x : B) : ContMDiffOn 𝓘(ℝ,X) 𝓘(ℝ,V →L[ℂ] MatrixTuple q d r) ∞ (evB x) (U x) :=
    tupleEvaluation_smooth.contMDiff.comp_contMDiffOn (hsm (e x) (f x)).1
  let ev (x : c) (z : X) := evB x.val ((chartAt X x.val).symm z)
  have hev (x : c) : ContDiffOn ℝ ∞ (ev x) (localChartDomain U x.val) :=
    localChartDomain_smooth U (evB x.val) x.val (heB x.val)
  have hsur (x : c) (z : X) (hz : z ∈ localChartDomain U x.val) :
      Function.Surjective (ev x z) :=
    tupleEvaluation_surjective _ ((hsm (e x.val) (f x.val)).2 _ hz.2)
  obtain ⟨v,hv⟩ := exists_countable_chart_incidence_parameter ev
    (fun x : c => localChartDomain U x.val)
    (fun x => localChartDomain_open U hU x.val) hev hsur pairs hpairs
  let T (i : Fin q) (y : B) := sectionEvaluation s y (v i)
  refine ⟨T,?_,?_⟩
  · intro i e' f' _ _
    have happ : ContDiff ℂ ∞ (fun L : (Fin n → ℂ) →L[ℂ] ((Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) => L (v i)) :=
      contDiff_id.clm_apply contDiff_const
    have hh := (happ.restrict_scalars ℝ).contMDiff.comp_contMDiffOn (hsm e' f').1
    apply hh.congr
    intro y hy
    exact (homEvaluationCoordinates_apply E F s e' f' y (v i)).symm
  · intro y p hp S hS
    obtain ⟨x,hxc,hyU,hyc,hz,hyz⟩ := hcover y
    let x' : c := ⟨x,hxc⟩
    let z := (chartAt X x) y
    have hh := hv x' z hz p hp
    apply rank_expansion_of_coordinates (fun i => (T i y).toLinearMap)
      (fun i => (ev x' z v i).toLinearMap)
      ((e x).toPretrivialization.linearEquivAt ℂ y hyU.1)
      ((f x).toPretrivialization.linearEquivAt ℂ y hyU.2) ?_ hh S hS
    intro i w
    change ((f x).toPretrivialization.linearEquivAt ℂ y hyU.2) (T i y w)=
      (tupleEvaluation (homEvaluationCoordinates E F s (e x) (f x)
        ((chartAt X x).symm ((chartAt X x) y))) v i)
        (((e x).toPretrivialization.linearEquivAt ℂ y hyU.1) w)
    rw [hyz,tupleEvaluation_apply,homEvaluationCoordinates_apply E F s (e x) (f x) y (v i)]
    exact homFrameLinear_commutes E F (e x) (f x) y hyU (T i y) w

end Kaplansky.Incidence

end

open Bundle Module Set
open scoped Topology Manifold ContDiff
namespace Kaplansky.Incidence
variable {X B : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [TopologicalSpace B] [ChartedSpace X B]
  [IsManifold 𝓘(ℝ,X) ∞ B] [T2Space B] [CompactSpace B]
  {q d r : ℕ} (E F : B → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (Fin d → ℂ) E)] [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
  [FiberBundle (Fin d → ℂ) E] [FiberBundle (Fin r → ℂ) F]
  [VectorBundle ℝ (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
  [VectorBundle ℝ (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]
  [ContMDiffVectorBundle ∞ (Fin d → ℂ) E 𝓘(ℝ,X)]
  [ContMDiffVectorBundle ∞ (Fin r → ℂ) F 𝓘(ℝ,X)]

theorem exists_smooth_bundle_incidence_maps (pairs : Finset (ℕ × ℕ))
    (hpairs : ∀ p ∈ pairs, p.1≤d ∧ p.2≤r ∧
      finrank ℝ X+2*p.1*(d-p.1)+2*p.2*(r-p.2)<2*q*p.1*(r-p.2)) :
    ∃ T : Fin q → ∀ y, E y →L[ℂ] F y,
      (∀ i, ContMDiff 𝓘(ℝ,X) (𝓘(ℝ,X).prod 𝓘(ℝ,(Fin d → ℂ) →L[ℝ] (Fin r → ℂ))) ∞
        (fun y => TotalSpace.mk' ((Fin d → ℂ) →L[ℝ] (Fin r → ℂ)) y ((T i y).restrictScalars ℝ))) ∧
      ∀ y p, p ∈ pairs → ∀ S : Submodule ℂ (E y), finrank ℂ S=p.1 →
        p.2<finrank ℂ (⨆ i, S.map (T i y).toLinearMap : Submodule ℂ (F y)) := by
  obtain ⟨T,hT,hExp⟩ := exists_bundle_incidence_maps E F pairs hpairs
  exact ⟨T,fun i => smooth_realHom_of_complex_coordinates 𝓘(ℝ,X) E F (T i) (hT i),hExp⟩

end Kaplansky.Incidence

end

end OAI
