import Mathlib
import OAI.Geometry.NearbyLagrangian.StandardNegative
import OAI.Geometry.NearbyLagrangian.CylinderRegularity
import OAI.Geometry.NearbyLagrangian.IntrinsicRealization

namespace OAI

/-! Localized tube realization and restored endpoints under Hamiltonian isotopy. -/

noncomputable section
open Set Filter Metric ContinuousLinearMap InnerProductSpace TopologicalSpace MeasureTheory
open scoped Manifold ContDiff Topology NNReal Convolution

namespace NearbyLagrangian.Tubes
open RegularHomogeneous ContinuousMap InnerProductSpace
open scoped Manifold ContDiff Topology InnerProductSpace

def heightAxis : Euclidean 10 := EuclideanSpace.basisFun (Fin 10) ℝ 0

def capEquator : UnitSphere 10 :=
  ⟨EuclideanSpace.basisFun (Fin 10) ℝ 1, by
    simpa only [Metric.mem_sphere,dist_zero_right] using
      (EuclideanSpace.basisFun (Fin 10) ℝ).norm_eq_one 1⟩

lemma heightAxis_norm : ‖heightAxis‖ = 1 :=
  (EuclideanSpace.basisFun (Fin 10) ℝ).norm_eq_one 0

lemma heightAxis_inner_capEquator : ⟪heightAxis,(capEquator:Euclidean 10)⟫_ℝ = 0 :=
  (EuclideanSpace.basisFun (Fin 10) ℝ).orthonormal.inner_eq_zero (by decide :
    (0:Fin 10) ≠ 1)

def realizationFamily {m : ℕ} (hm : 0 < m) (a : C(UnitSphere 10,Tube m m)) :
    Sphere 9 → RegularHomogeneous (Euclidean ((2*m-1)+1)) :=
  fun b => (a b).val.pullback (euclideanCast (by omega : (2*m-1)+1 = m+m))

end NearbyLagrangian.Tubes

namespace NearbyLagrangian.Tubes
open Transport CotangentGeometry EmbeddedRealization Cutoff Scales RegularHomogeneous Set
open scoped Manifold ContDiff Topology

def HasRestoredEndpoint {m : ℕ} (a : C(Sphere 9,Tube m m)) (d : ℕ) : Prop :=
    ∃ (t : ℕ) (R : ℝ)
      (δ : C(Sphere 9,Tube (transportIndex m d t) (transportIndex m d t)))
      (H : Sphere 9 × Euclidean (transportIndex m d t + transportIndex m d t) → ℝ)
      (σ : Sphere 9 → Euclidean (transportIndex m d t + transportIndex m d t)),
      1 ≤ R ∧ ((addBalancedFor m d t).comp a).Homotopic δ ∧
      (∀ q : Sphere 9 × Euclidean (transportIndex m d t + transportIndex m d t), q.2 ≠ 0 →
        ContMDiffAt ((𝓡 9).prod 𝓘(ℝ,Euclidean (transportIndex m d t + transportIndex m d t)))
          𝓘(ℝ,ℝ) ∞ (fun q => (δ q.1).val q.2) q) ∧
      ContMDiff ((𝓡 9).prod 𝓘(ℝ,Euclidean (transportIndex m d t + transportIndex m d t)))
        𝓘(ℝ,ℝ) ∞ H ∧
      (∀ q, 2*R ≤ ‖q.2‖ → H q = (δ q.1).val q.2) ∧
      ContMDiff (𝓡 9) 𝓘(ℝ,Euclidean (transportIndex m d t + transportIndex m d t)) ∞ σ ∧
      (∀ b w, fderiv ℝ (fun w => H (b,w)) w = 0 ↔ w = σ b) ∧
      (∀ b, Function.Bijective (fderiv ℝ (fderiv ℝ (fun w => H (b,w))) (σ b)))

local instance (n : ℕ) : Fact (Module.finrank ℝ (Euclidean (n+1)) = n+1) := ⟨by simp⟩
local instance (n : ℕ) : ChartedSpace (BaseVector n) (Base n) :=
  inferInstanceAs (ChartedSpace (ModelProd (Euclidean 9) (Euclidean n)) (Base n))
local instance (n : ℕ) : IsManifold 𝓘(ℝ, BaseVector n) ∞ (Base n) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓡 9) (I' := 𝓡 n) (Sphere 9) (Sphere n)

theorem source_analytic_obstruction {m : ℕ} (hm : 0 < m)
    (a : C(Sphere 9,Tube m m))
    (hs : SmoothFamily (E:=Euclidean 9) (fun b => (a b).val))
    (hj : ContMDiff ((𝓡 9).prod 𝓘(ℝ,Euclidean (m+m))) 𝓘(ℝ,ℝ) 1
      (fun q : Sphere 9 × Euclidean (m+m) => (a q.1).val q.2))
    (hcap : ∀ x : Sphere 9, (31:ℝ)/32 < |SphereDirection.height heightAxis x| →
      Function.Injective (gradient (a x).val)) :
    ∃ K Λ T : ℝ, 0 < K ∧ 0 < Λ ∧ 1 < T ∧
      IsClosedExactLagrangian (realization (realizationFamily hm a)
        (exponentialScale (SphereDirection.height heightAxis) K Λ) T) ∧
      (IsHamiltonianImage (realization (realizationFamily hm a)
        (exponentialScale (SphereDirection.height heightAxis) K Λ) T) →
        HasRestoredEndpoint a (10+((2*m-1)+1))) := by
  let n := 2*m-1
  have hn : n+1=m+m := by dsimp [n]; omega
  let f := realizationFamily hm a
  have hf : Continuous f :=
    (continuous_pullback _).comp (continuous_subtype_val.comp a.continuous)
  have hfs : SmoothFamily (E:=Euclidean 9) f := smoothFamily_pullback_euclideanCast _ hs
  have hcap' : ∀ x : Sphere 9, (31:ℝ)/32 < |SphereDirection.height heightAxis x| →
      Function.Injective (gradient (f x)) := by
    intro x hx
    exact gradient_injective_pullback_euclideanCast hn (hcap x hx)
  obtain ⟨K,Λ,T,hK,hΛ,hT,hL,hreg,hinj,hrange⟩ := exists_realization_with_intrinsic_data
    hf hfs heightAxis_norm (by norm_num : (0:ℝ) ≤ 31/32) (by norm_num : (31:ℝ)/32 < 1) hcap'
  refine ⟨K,Λ,T,hK,hΛ,hT,hL,?_⟩
  intro hi
  let R := exponentialScale (SphereDirection.height heightAxis) K Λ
  let A := sourceFamily f R T
  let A' := verticalCast hn A
  have hRs : ContMDiff (𝓡 9) 𝓘(ℝ,ℝ) ∞ R :=
    contMDiff_exponentialScale K Λ (HeightSeparation.contMDiff_height (n:=9) heightAxis)
  have hA : ContMDiff ((NearbyLagrangian.baseModel n).prod 𝓘(ℝ,Euclidean (m+m))) 𝓘(ℝ,ℝ) ∞ A' := by
    rw [baseModel_eq]
    apply contMDiff_verticalCast
    rw [← baseModel_eq]
    exact contMDiff_sourceFamily hfs hRs (zero_lt_one.trans hT)
  have hG : ContMDiff ((NearbyLagrangian.baseModel n).prod 𝓘(ℝ,Euclidean (m+m))) 𝓘(ℝ,ℝ) 1
      (fun q : Base n × Euclidean (m+m) => (a q.1.1).val q.2) :=
    hj.comp ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd)
  have hreg' : ∀ q : IntrinsicCritical A',
      Function.Surjective (mfderiv ((NearbyLagrangian.baseModel n).prod 𝓘(ℝ,Euclidean (m+m)))
        𝓘(ℝ,Euclidean (m+m) →L[ℝ] ℝ)
        (fun y : Base n × Euclidean (m+m) => fderiv ℝ (fun v => A' (y.1,v)) y.2) q.val) := by
    rw [baseModel_eq] at hreg ⊢
    exact verticalCast_regular hn hreg
  have hinj' : Function.Injective (fun q : IntrinsicCritical A' => intrinsicGenerate (E:=BaseVector n) A' q.val) :=
    verticalCast_injective hn hinj
  have hrange' : range (fun q : IntrinsicCritical A' => intrinsicGenerate (E:=BaseVector n) A' q.val) =
      range (realization f R T) := (verticalCast_range hn A).trans hrange
  have htail : ∀ q : Base n, ∀ w, 2*T ≤ ‖w‖ → A' (q,w) = (a q.1).val w := by
    apply verticalCast_tail hn
    intro q w hw
    exact sourceFamily_eq_outside hT q.1 q.2 w hw
  let v₀ : Sphere n := ⟨EuclideanSpace.basisFun (Fin (n+1)) ℝ 0,by
    simpa only [Metric.mem_sphere,dist_zero_right] using
      (EuclideanSpace.basisFun (Fin (n+1)) ℝ).norm_eq_one 0⟩
  exact IntrinsicCylinder.exists_intrinsic_restored_endpoint
    (νc:=1/4) (ν:=1/2) (by norm_num) (by norm_num) (by norm_num)
    v₀ a hA hG hreg' hinj' (2*T) htail hrange' hi

end NearbyLagrangian.Tubes

end

end OAI
