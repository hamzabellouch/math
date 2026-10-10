import Mathlib
import OAI.Geometry.NearbyLagrangian.CylinderFamilies
import OAI.Geometry.NearbyLagrangian.ClosedRealization

namespace OAI

/-! Intrinsic realization data and compatible changes of Euclidean dimension. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.EmbeddedRealization
open scoped Manifold ContDiff InnerProductSpace Topology
open Tubes Tubes.RegularHomogeneous CoreSmoothing Cutoff Scales Set CotangentGeometry
local instance intrinsicRealizationDataFinrank (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1)) = n+1) := ⟨by simp⟩
local instance intrinsicRealizationDataChartedSpace (n : ℕ) : ChartedSpace (BaseVector n) (Base n) :=
  inferInstanceAs (ChartedSpace (ModelProd (Euclidean 9) (Euclidean n)) (Base n))
local instance intrinsicRealizationDataManifold (n : ℕ) : IsManifold 𝓘(ℝ, BaseVector n) ∞ (Base n) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓡 9) (I' := 𝓡 n) (Sphere 9) (Sphere n)

def sourceIntrinsicEquiv {n : ℕ}
    {f : Sphere 9 → RegularHomogeneous (Euclidean (n+1))}
    (hf : SmoothFamily (E := Euclidean 9) f) {R : Sphere 9 → ℝ}
    (hRs : ContMDiff (𝓡 9) 𝓘(ℝ,ℝ) ∞ R) {T c C : ℝ}
    (hT : 1 < T) (hc : 0 < c) (hR : ∀ b, 0 < R b) (hC : ∀ b, C < R b)
    (hscale₁ : ∀ b, R b / c < T)
    (hscale₂ : ∀ b, cutoffControl beta * R b / c < T)
    (hsmall : ∀ b w, ‖w‖ ≤ 1 →
      ‖fderiv ℝ (fun a => smoothCore (fun x : Sphere 9 × Euclidean (n+1) => f x.1 x.2) (b,a)) w‖ < R b)
    (hlower : ∀ b w, c * ‖w‖ ≤ ‖gradient (f b) w‖)
    (hupper : ∀ b w, ‖gradient (f b) w‖ ≤ C * ‖w‖) :
    Base n ≃ IntrinsicCritical (sourceFamily f R T) :=
  (familyCriticalHomeomorph (n:=n) hf hRs hR).toEquiv.trans {
    toFun := fun q => ⟨q.val,(sourceFamily_critical_iff hf hT hc hR hC hscale₁ hscale₂ hsmall hlower hupper
      q.val.1.1 q.val.1.2 q.val.2).mpr q.property⟩
    invFun := fun q => ⟨q.val,(sourceFamily_critical_iff hf hT hc hR hC hscale₁ hscale₂ hsmall hlower hupper
      q.val.1.1 q.val.1.2 q.val.2).mp q.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

lemma intrinsicGenerate_familyCriticalParam {n : ℕ}
    (f : Sphere 9 → RegularHomogeneous (Euclidean (n+1))) (R : Sphere 9 → ℝ) (T : ℝ) (q : Base n) :
    intrinsicGenerate (E:=BaseVector n) (sourceFamily f R T) (familyCriticalParam f R q) =
      realization f R T q := rfl

theorem source_intrinsic_data {n : ℕ}
    {f : Sphere 9 → RegularHomogeneous (Euclidean (n+1))}
    (hf : SmoothFamily (E := Euclidean 9) f) {R : Sphere 9 → ℝ}
    (hRs : ContMDiff (𝓡 9) 𝓘(ℝ,ℝ) ∞ R) {T c C : ℝ}
    (hT : 1 < T) (hc : 0 < c) (hR : ∀ b, 0 < R b) (hC : ∀ b, C < R b)
    (hscale₁ : ∀ b, R b / c < T)
    (hscale₂ : ∀ b, cutoffControl beta * R b / c < T)
    (hsmall : ∀ b w, ‖w‖ ≤ 1 →
      ‖fderiv ℝ (fun a => smoothCore (fun x : Sphere 9 × Euclidean (n+1) => f x.1 x.2) (b,a)) w‖ < R b)
    (hlower : ∀ b w, c * ‖w‖ ≤ ‖gradient (f b) w‖)
    (hupper : ∀ b w, ‖gradient (f b) w‖ ≤ C * ‖w‖)
    (hinj : Function.Injective (realization f R T)) :
    (∀ q : IntrinsicCritical (sourceFamily f R T),
      Function.Surjective (mfderiv ((NearbyLagrangian.baseModel n).prod 𝓘(ℝ,Euclidean (n+1)))
        𝓘(ℝ,Euclidean (n+1) →L[ℝ] ℝ) (sourceVertical f R T) q.val)) ∧
    Function.Injective (fun q : IntrinsicCritical (sourceFamily f R T) =>
      intrinsicGenerate (E:=BaseVector n) (sourceFamily f R T) q.val) ∧
    range (fun q : IntrinsicCritical (sourceFamily f R T) =>
      intrinsicGenerate (E:=BaseVector n) (sourceFamily f R T) q.val) = range (realization f R T) := by
  let e := sourceIntrinsicEquiv hf hRs hT hc hR hC hscale₁ hscale₂ hsmall hlower hupper
  have he (q : Base n) : (e q).val = familyCriticalParam f R q := rfl
  have hg (q : Base n) : intrinsicGenerate (E:=BaseVector n) (sourceFamily f R T) (e q).val =
      realization f R T q := rfl
  refine ⟨?_,?_,?_⟩
  · intro q
    have hcrit := (sourceFamily_critical_iff hf hT hc hR hC hscale₁ hscale₂ hsmall hlower hupper
      q.val.1.1 q.val.1.2 q.val.2).mp q.property
    obtain ⟨hlo,hup⟩ := critical_annulus hc q.val.1.1 (hR _) (hC _) (hscale₁ _)
      (hlower _) (hupper _) q.val.1.2 q.val.2 hcrit
    exact sourceVertical_regular hf hRs (zero_lt_one.trans hT) q.val.1.1 (hR _)
      ⟨(q.val.2,q.val.1.2),hcrit⟩ hlo hup
  · intro q r h
    obtain ⟨x,rfl⟩ := e.surjective q
    obtain ⟨y,rfl⟩ := e.surjective r
    apply congrArg e (hinj ?_)
    exact (hg x).symm.trans (h.trans (hg y))
  · ext z
    constructor
    · rintro ⟨q,rfl⟩
      obtain ⟨x,rfl⟩ := e.surjective q
      exact ⟨x,(hg x).symm⟩
    · rintro ⟨q,rfl⟩
      exact ⟨e q,hg q⟩

end NearbyLagrangian.EmbeddedRealization

namespace NearbyLagrangian.Tubes
open RegularHomogeneous InnerProductSpace

def euclideanCast {m n : ℕ} (h : m=n) : Euclidean m ≃L[ℝ] Euclidean n := by
  subst n
  exact ContinuousLinearEquiv.refl ℝ (Euclidean m)

@[simp] lemma pullback_euclideanCast_refl {n : ℕ} (f : RegularHomogeneous (Euclidean n))
    (h : n=n) : f.pullback (euclideanCast h) = f := by
  ext w
  rfl

lemma smoothFamily_pullback_euclideanCast {m n : ℕ} (h : m=n)
    {f : NearbyLagrangian.Sphere 9 → RegularHomogeneous (Euclidean n)}
    (hf : SmoothFamily (E:=Euclidean 9) f) :
    SmoothFamily (E:=Euclidean 9) (fun b => (f b).pullback (euclideanCast h)) := by
  subst n
  simpa only [pullback_euclideanCast_refl] using hf

lemma gradient_injective_pullback_euclideanCast {m n : ℕ} (h : m=n)
    {f : RegularHomogeneous (Euclidean n)} (hf : Function.Injective (gradient f)) :
    Function.Injective (gradient (f.pullback (euclideanCast h))) := by
  subst n
  simpa only [pullback_euclideanCast_refl] using hf
end NearbyLagrangian.Tubes

namespace NearbyLagrangian.CotangentGeometry
open scoped Manifold ContDiff Topology
open Set Tubes
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def verticalCast {k l : ℕ} (h : k=l) (A : M × Euclidean k → ℝ) : M × Euclidean l → ℝ :=
  fun q => A (q.1,(euclideanCast h).symm q.2)

omit [TopologicalSpace M] in
@[simp] lemma verticalCast_refl {k : ℕ} (h : k=k) (A : M × Euclidean k → ℝ) :
    verticalCast h A = A := rfl

lemma contMDiff_verticalCast {k l : ℕ} (h : k=l) {A : M × Euclidean k → ℝ}
    {s : ℕ∞ω} (hA : ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,Euclidean k)) 𝓘(ℝ,ℝ) s A) :
    ContMDiff (𝓘(ℝ,E).prod 𝓘(ℝ,Euclidean l)) 𝓘(ℝ,ℝ) s (verticalCast h A) := by
  subst l
  exact hA

lemma verticalCast_regular {k l : ℕ} (h : k=l) {A : M × Euclidean k → ℝ}
    (hA : ∀ q : IntrinsicCritical A,
      Function.Surjective (mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,Euclidean k)) 𝓘(ℝ,Euclidean k →L[ℝ] ℝ)
        (fun y : M × Euclidean k => fderiv ℝ (fun v => A (y.1,v)) y.2) q.val)) :
    ∀ q : IntrinsicCritical (verticalCast h A),
      Function.Surjective (mfderiv (𝓘(ℝ,E).prod 𝓘(ℝ,Euclidean l)) 𝓘(ℝ,Euclidean l →L[ℝ] ℝ)
        (fun y : M × Euclidean l => fderiv ℝ (fun v => verticalCast h A (y.1,v)) y.2) q.val) := by
  subst l
  exact hA

lemma verticalCast_injective {k l : ℕ} (h : k=l) {A : M × Euclidean k → ℝ}
    (hA : Function.Injective (fun q : IntrinsicCritical A => intrinsicGenerate (E:=E) A q.val)) :
    Function.Injective (fun q : IntrinsicCritical (verticalCast h A) =>
      intrinsicGenerate (E:=E) (verticalCast h A) q.val) := by
  subst l
  exact hA

lemma verticalCast_range {k l : ℕ} (h : k=l) (A : M × Euclidean k → ℝ) :
    range (fun q : IntrinsicCritical (verticalCast h A) =>
      intrinsicGenerate (E:=E) (verticalCast h A) q.val) =
      range (fun q : IntrinsicCritical A => intrinsicGenerate (E:=E) A q.val) := by
  subst l
  rfl

omit [TopologicalSpace M] in
lemma verticalCast_tail {k l : ℕ} (h : k=l) {A : M × Euclidean k → ℝ} {f : M → Euclidean l → ℝ}
    {R : ℝ} (ht : ∀ q w, R ≤ ‖w‖ → A (q,w) = f q (euclideanCast h w)) :
    ∀ q w, R ≤ ‖w‖ → verticalCast h A (q,w) = f q w := by
  subst l
  exact ht

omit [TopologicalSpace M] in
lemma verticalCast_reference {k l : ℕ} (h : k=l) (f : M → Euclidean l → ℝ) :
    verticalCast h (fun q : M × Euclidean k => f q.1 (euclideanCast h q.2)) =
      fun q : M × Euclidean l => f q.1 q.2 := by
  subst l
  rfl

end NearbyLagrangian.CotangentGeometry

namespace NearbyLagrangian.EmbeddedRealization
open scoped Manifold ContDiff InnerProductSpace Topology
open Tubes Tubes.RegularHomogeneous CoreSmoothing Cutoff Scales Set
local instance intrinsicRealizationExistenceFinrank (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1)) = n+1) := ⟨by simp⟩
local instance intrinsicRealizationExistenceChartedSpace (n : ℕ) : ChartedSpace (BaseVector n) (Base n) :=
  inferInstanceAs (ChartedSpace (ModelProd (Euclidean 9) (Euclidean n)) (Base n))
local instance intrinsicRealizationExistenceManifold (n : ℕ) : IsManifold 𝓘(ℝ, BaseVector n) ∞ (Base n) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓡 9) (I' := 𝓡 n) (Sphere 9) (Sphere n)

theorem exists_realization_with_intrinsic_data {n : ℕ}
    {f : Sphere 9 → RegularHomogeneous (Euclidean (n+1))}
    (hf : Continuous f) (hfs : SmoothFamily (E := Euclidean 9) f)
    {e : Euclidean 10} (he : ‖e‖ = 1) {a : ℝ} (ha : 0 ≤ a) (ha1 : a < 1)
    (hcap : ∀ b, a < |SphereDirection.height e b| → Function.Injective (gradient (f b))) :
    ∃ K Λ T : ℝ, 0 < K ∧ 0 < Λ ∧ 1 < T ∧
      IsClosedExactLagrangian
        (realization f (exponentialScale (SphereDirection.height e) K Λ) T) ∧
      (∀ q : CotangentGeometry.IntrinsicCritical
          (sourceFamily f (exponentialScale (SphereDirection.height e) K Λ) T),
        Function.Surjective (mfderiv ((NearbyLagrangian.baseModel n).prod 𝓘(ℝ,Euclidean (n+1)))
          𝓘(ℝ,Euclidean (n+1) →L[ℝ] ℝ)
          (sourceVertical f (exponentialScale (SphereDirection.height e) K Λ) T) q.val)) ∧
      Function.Injective (fun q : CotangentGeometry.IntrinsicCritical
          (sourceFamily f (exponentialScale (SphereDirection.height e) K Λ) T) =>
        CotangentGeometry.intrinsicGenerate (E:=BaseVector n)
          (sourceFamily f (exponentialScale (SphereDirection.height e) K Λ) T) q.val) ∧
      range (fun q : CotangentGeometry.IntrinsicCritical
          (sourceFamily f (exponentialScale (SphereDirection.height e) K Λ) T) =>
        CotangentGeometry.intrinsicGenerate (E:=BaseVector n)
          (sourceFamily f (exponentialScale (SphereDirection.height e) K Λ) T) q.val) =
        range (realization f (exponentialScale (SphereDirection.height e) K Λ) T) := by
  let : Nonempty (Sphere 9) := ⟨⟨e,by simpa only [Metric.mem_sphere,dist_zero_right] using he⟩⟩
  let θ : Sphere 9 → ℝ := SphereDirection.height e
  obtain ⟨c, C, hc, hC, hgrad⟩ := uniform_gradient_bounds hf
  obtain ⟨M, hM, hcore⟩ := exists_core_bound (contMDiff_smoothCore hfs)
  have hhomo : ∀ b (r : ℝ), 0 < r → ∀ w, f b (r • w) = r ^ 2 * f b w :=
    fun b r hr w => (f b).homogeneity r hr w
  obtain ⟨C₁, hC₁, hmixed⟩ := HeightSeparation.exists_momentum_scale_bound
    (n := 9) he (fun b => (f b).map_zero) hhomo hfs
  have hδ : 0 < 1 - a ^ 2 := by nlinarith
  obtain ⟨K, Λ, T, bmin, bmax, hK, hΛ, hchoice, hmin, hmax, hT⟩ :=
    exists_source_scales (θ := θ) (HeightSeparation.contMDiff_height (n := 9) e).continuous
      (c := c) (C := C) (C₁ := C₁) (M := M) (δ := 1-a^2) (D := cutoffControl beta)
      hc hC.le hC₁ hM hδ
  let R := exponentialScale θ K Λ
  have hR : ∀ b, 0 < R b := fun b => exponentialScale_pos hΛ b
  have hRs : ContMDiff (𝓡 9) 𝓘(ℝ, ℝ) ∞ R :=
    contMDiff_exponentialScale K Λ (HeightSeparation.contMDiff_height (n := 9) e)
  have hCR : ∀ b, C < R b := fun b =>
    (le_max_left C M).trans_lt (hmin.trans_le (hmax b).1)
  have hMR : ∀ b, M < R b := fun b =>
    (le_max_right C M).trans_lt (hmin.trans_le (hmax b).1)
  have hT₁ : 1 < T := (le_max_left _ _).trans_lt hT
  have hcap₁ : ∀ b, R b / c < T := by
    intro b
    exact (div_le_div_of_nonneg_right (hmax b).2 hc.le).trans_lt
      (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hT)
  have hcap₂ : ∀ b, cutoffControl beta * R b / c < T := by
    intro b
    have hD : 0 ≤ cutoffControl beta := zero_le_one.trans one_le_beta_control
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hmax b).2 hD) hc.le).trans_lt
      (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hT)
  have hsmall : ∀ b w, ‖w‖ ≤ 1 →
      ‖fderiv ℝ (fun z => smoothCore (fun x : Sphere 9 × Euclidean (n+1) => f x.1 x.2)
        (b, z)) w‖ < R b :=
    fun b w hw => (hcore b w hw).trans_lt (hMR b)
  have hlower : ∀ b w, c * ‖w‖ ≤ ‖gradient (f b) w‖ := fun b w => (hgrad b w).1
  have hupper : ∀ b w, ‖gradient (f b) w‖ ≤ C * ‖w‖ := fun b w => (hgrad b w).2
  have hinj : Function.Injective (realization f R T) := by
    apply sourceGeneratingMap_injective hfs hRs (zero_lt_one.trans hT₁) hc hR hCR
      hcap₁ hlower hupper
    intro b
    by_cases hb : a < |θ b|
    · exact Or.inl (hcap b hb)
    · right
      obtain ⟨hbder, hbderbound, hbdom⟩ :=
        hmixed a c K Λ ha ha1 hK hΛ hchoice b (le_of_not_gt hb)
      exact ⟨SphereDirection.tangent (n := 9) e b, C₁, hC₁, hbder, hbderbound, hbdom⟩
  exact ⟨K, Λ, T, hK, hΛ, hT₁,
    closedExact_realization_of_bounds hfs hRs hT₁ hc hR hCR hcap₁ hcap₂ hsmall
      hlower hupper hinj,
    source_intrinsic_data hfs hRs hT₁ hc hR hCR hcap₁ hcap₂ hsmall hlower hupper hinj⟩

end NearbyLagrangian.EmbeddedRealization

end

end OAI
