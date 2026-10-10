import Mathlib
import OAI.Analysis.FreeWords.FactorBase
import OAI.Analysis.FreeWords.FactorHullGeneric

namespace OAI

noncomputable section

namespace KKFactorSupport

open KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def algebraConj (u : unitary A) : A →ₗ[ℂ] A where
  toFun x := (u : A) * x * star (u : A)
  map_add' x y := by simp only [mul_add, add_mul]
  map_smul' c x := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] theorem algebraConj_apply (u : unitary A) (x : A) :
    algebraConj u x = (u : A) * x * star (u : A) := rfl

omit [StarOrderedRing A] in
theorem trace_algebraConj (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y) = τ (y*x)) (u : unitary A) (x : A) :
    τ (algebraConj u x) = τ x := by
  change τ ((u : A) * x * star (u : A)) = τ x
  rw [htr, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]

omit [PartialOrder A] [StarOrderedRing A] in
theorem star_conj_mul_conj (u : unitary A) (x : A) :
    star (algebraConj u x) * algebraConj u x = algebraConj u (star x * x) := by
  simp only [algebraConj_apply, star_mul, star_star]
  calc
    (u : A) * (star x * star (u : A)) * ((u : A) * x * star (u : A)) =
        (u : A) * star x * (star (u : A) * (u : A)) * x * star (u : A) := by
          simp only [mul_assoc]
    _ = (u : A) * (star x * x) * star (u : A) := by
      rw [Unitary.coe_star_mul_self, mul_one]
      simp only [mul_assoc]

theorem preGNS_conj_norm (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y) = τ (y*x)) (u : unitary A) (x : A) :
    ‖τ.toPreGNS (algebraConj u x)‖ = ‖τ.toPreGNS x‖ := by
  change Real.sqrt (τ (star (algebraConj u x) * algebraConj u x)).re =
    Real.sqrt (τ (star x * x)).re
  rw [star_conj_mul_conj, trace_algebraConj τ htr]

def preGNSConj (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y) = τ (y*x)) (u : unitary A) : τ.PreGNS →L[ℂ] τ.PreGNS :=
  ((τ.toPreGNS.toLinearMap.comp (algebraConj u)).comp τ.ofPreGNS.toLinearMap).mkContinuous 1
    (fun x => by simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, one_mul,
      preGNS_conj_norm τ htr u, PositiveLinearMap.toPreGNS_ofPreGNS] using le_refl ‖x‖)

def gnsConj (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y) = τ (y*x)) (u : unitary A) : τ.GNS →L[ℂ] τ.GNS :=
  (preGNSConj τ htr u).completion

@[simp] theorem gnsConj_vector (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y) = τ (y*x)) (u : unitary A) (x : A) :
    gnsConj τ htr u (gnsVector τ x) = gnsVector τ (algebraConj u x) := by
  change (preGNSConj τ htr u).completion (τ.toPreGNS x : τ.GNS) =
    (τ.toPreGNS (algebraConj u x) : τ.GNS)
  rw [ContinuousLinearMap.completion_apply_coe]
  rfl

theorem gnsConj_norm (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ x y, τ (x*y) = τ (y*x)) (u : unitary A) (v : τ.GNS) :
    ‖gnsConj τ htr u v‖ = ‖v‖ := by
  induction v using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq ((gnsConj τ htr u).continuous.norm) continuous_norm
  | ih a =>
    change ‖(preGNSConj τ htr u).completion (a : τ.GNS)‖ = ‖(a : τ.GNS)‖
    rw [ContinuousLinearMap.completion_apply_coe,
      UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
    exact preGNS_conj_norm τ htr u (τ.ofPreGNS a)

end

end KKFactorSupport

namespace KKFactorSupport

open KKTraceTransfer KKUltraTrace

open scoped ComplexOrder InnerProductSpace BoundedContinuousFunction

open Filter Topology

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem tracePositive_tracial {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) :
    ∀ x y, tracePositive τ (x*y) = tracePositive τ (y*x) := τ.tracial

theorem gnsVector_injective {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M) :
    Function.Injective (gnsVector (tracePositive τ)) := by
  intro a b hab
  have hz : gnsVector (tracePositive τ) (a-b) = 0 := by rw [map_sub, hab, sub_self]
  have hτ : τ.map (star (a-b) * (a-b)) = 0 := by
    change (tracePositive τ) (star (a-b) * (a-b)) = 0
    rw [← gnsVector_inner (tracePositive τ), hz, inner_zero_left]
  have hs : star (a-b) * (a-b) = 0 :=
    τ.faithful _ (ContinuousLinearMap.isPositive_adjoint_comp_self _) hτ
  exact sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff (a-b)).mp hs)

theorem tendsto_gnsMean_inner {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (ω : Ultrafilter ℕ) (x : ℕ →ᵇ ConcreteAlgebra M) (a : ConcreteAlgebra M) :
    Tendsto (fun j => ⟪gnsVector (tracePositive τ) a, gnsVector (tracePositive τ) (x j)⟫_ℂ)
      (ω : Filter ℕ) (𝓝 ⟪gnsVector (tracePositive τ) a,
        gnsVector (tracePositive τ) (sequenceMean M ω x)⟫_ℂ) := by
  let s := BoundedContinuousFunction.const ℕ (star a) * x * BoundedContinuousFunction.const ℕ 1
  have hs : sequenceMean M ω s = star a * sequenceMean M ω x := by
    simpa only [mul_one] using sequenceMean_bimodule ω (star a) 1 x
  have ht := tendsto_ultraTraceValue (tracePositive τ) ω s
  change Tendsto (fun j => (tracePositive τ) (s j)) (ω : Filter ℕ)
    (𝓝 (ultraTrace (tracePositive τ) ω s)) at ht
  rw [← trace_sequenceMean τ ω s, hs] at ht
  simp only [gnsVector_inner]
  change Tendsto (fun j => τ.map (star a * x j)) (ω : Filter ℕ)
    (𝓝 (τ.map (star a * sequenceMean M ω x)))
  have heval : (fun j => (tracePositive τ) (s j)) =
      (fun j => τ.map (star a * x j)) := by
    funext j
    change τ.map (star a * x j * 1) = _
    rw [mul_one]
  rw [heval] at ht
  exact ht

theorem gnsVector_closedBall_isClosed {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (R : ℝ) :
    IsClosed (gnsVector (tracePositive τ) '' Metric.closedBall (0 : ConcreteAlgebra M) R) := by
  apply isClosed_of_closure_subset
  intro y hy
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp hy
  choose a ha heq using hv
  have hR : 0 ≤ R := (norm_nonneg (a 0)).trans (by simpa using ha 0)
  let x : ℕ →ᵇ ConcreteAlgebra M := BoundedContinuousFunction.ofNormedAddCommGroup a
    continuous_of_discreteTopology R (fun j => by simpa using ha j)
  have hx : ‖x‖ ≤ R := (BoundedContinuousFunction.norm_le hR).mpr
    (fun j => by change ‖a j‖ ≤ R; simpa using ha j)
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  refine ⟨sequenceMean M ω x, ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using (norm_sequenceMean_le ω x).trans hx
  · apply ext_inner_left ℂ
    intro z
    induction z using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_id.inner continuous_const) (continuous_id.inner continuous_const)
    | ih z =>
      let b := (tracePositive τ).ofPreGNS z
      have hseq : Tendsto (fun j => gnsVector (tracePositive τ) (x j))
          (ω : Filter ℕ) (𝓝 y) := by
        have hh : (fun j => gnsVector (tracePositive τ) (x j)) = v := by
          funext j
          exact heq j
        rw [hh]
        exact hlim.mono_left (Ultrafilter.of_le atTop)
      have h1 : Tendsto (fun j => ⟪gnsVector (tracePositive τ) b,
          gnsVector (tracePositive τ) (x j)⟫_ℂ) (ω : Filter ℕ)
          (𝓝 ⟪gnsVector (tracePositive τ) b, y⟫_ℂ) := tendsto_const_nhds.inner hseq
      have h2 := tendsto_gnsMean_inner τ ω x b
      exact (tendsto_nhds_unique h2 h1)

end

end KKFactorSupport

namespace KKFreeLiftFrontier

open KKTraceTransfer

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def IsFactor (M : VonNeumannAlgebra H) : Prop :=
  ∀ x : ConcreteAlgebra M, (∀ y : ConcreteAlgebra M, Commute x y) →
    ∃ c : ℂ, x = c • 1

end KKFreeLiftFrontier

namespace KKFactorSupport

open KKTraceTransfer KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

def conjugacyOrbit {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (x : ConcreteAlgebra M) : Set (tracePositive τ).GNS :=
  Set.range (fun u : unitary (ConcreteAlgebra M) =>
    gnsVector (tracePositive τ) ((u : ConcreteAlgebra M) * x * star (u : ConcreteAlgebra M)))

def conjugacyHull {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (x : ConcreteAlgebra M) : Set (tracePositive τ).GNS :=
  closure (convexHull ℝ (conjugacyOrbit τ x))

end

end KKFactorSupport

namespace KKFactorSupport

open KKTraceTransfer KKUltraTrace

open scoped ComplexOrder InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (M : VonNeumannAlgebra H) : PartialOrder (ConcreteAlgebra M) := concreteOrder M

local instance (M : VonNeumannAlgebra H) : Preorder (ConcreteAlgebra M) := (concreteOrder M).toPreorder

local instance (M : VonNeumannAlgebra H) : LE (ConcreteAlgebra M) := (concreteOrder M).toLE

local instance (M : VonNeumannAlgebra H) : StarOrderedRing (ConcreteAlgebra M) := concreteSOR M

theorem norm_minimizer_unique {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {K : Set F} (hK : Convex ℝ K) {a b : F} (ha : a ∈ K) (hb : b ∈ K)
    (hmin : ‖(0 : F) - a‖ = ⨅ z : K, ‖(0 : F) - z‖) (hn : ‖b‖ = ‖a‖) : a = b := by
  have hbmin : ‖(0 : F) - b‖ = ⨅ z : K, ‖(0 : F) - z‖ := by
    simpa only [zero_sub, norm_neg, hn] using hmin
  have h₁ := (norm_eq_iInf_iff_real_inner_le_zero hK ha).mp hmin b hb
  have h₂ := (norm_eq_iInf_iff_real_inner_le_zero hK hb).mp hbmin a ha
  simp only [zero_sub, inner_neg_left, inner_sub_right] at h₁ h₂
  have hz : ⟪a-b,a-b⟫_ℝ ≤ 0 := by
    simp only [inner_sub_left, inner_sub_right]
    linarith
  rw [real_inner_self_eq_norm_sq] at hz
  apply eq_of_norm_sub_eq_zero
  nlinarith [norm_nonneg (a-b)]

theorem mapsTo_hull {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F →L[ℝ] F) {S : Set F} (hf : Set.MapsTo f S S) :
    Set.MapsTo f (closure (convexHull ℝ S)) (closure (convexHull ℝ S)) := by
  apply Set.MapsTo.closure _ f.continuous
  intro x hx
  have hh : f x ∈ f '' convexHull ℝ S := ⟨x, hx, rfl⟩
  rw [show f '' convexHull ℝ S = convexHull ℝ (f '' S) from
    f.toLinearMap.image_convexHull S] at hh
  exact convexHull_mono hf.image_subset hh

theorem conjugacyHull_bounded {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (x : ConcreteAlgebra M) : conjugacyHull τ x ⊆
      gnsVector (tracePositive τ) '' Metric.closedBall (0 : ConcreteAlgebra M) ‖x‖ := by
  apply closure_minimal
  · apply convexHull_min
    · rintro _ ⟨u, rfl⟩
      refine ⟨algebraConj u x, ?_, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      change ‖algebraConj u x - 0‖ ≤ ‖x‖
      simp only [algebraConj_apply, sub_zero, ← Unitary.coe_star]
      rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
    · exact (convex_closedBall (0 : ConcreteAlgebra M) ‖x‖).linear_image
        ((gnsVector (tracePositive τ)).restrictScalars ℝ)
  · exact gnsVector_closedBall_isClosed τ ‖x‖

theorem conjugacyHull_trace {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (x : ConcreteAlgebra M) (v : (tracePositive τ).GNS) (hv : v ∈ conjugacyHull τ x) :
    ⟪gnsVector (tracePositive τ) 1, v⟫_ℂ = τ.map x := by
  let φ : (tracePositive τ).GNS →L[ℝ] ℂ :=
    (innerSL ℂ (gnsVector (tracePositive τ) 1)).restrictScalars ℝ
  have hc : Convex ℝ {v | φ v = τ.map x} := by
    intro a ha b hb c d hc hd hcd
    change φ (c • a+d • b) = τ.map x
    rw [map_add, map_smul, map_smul, ha, hb, ← add_smul, hcd, one_smul]
  have ho : conjugacyOrbit τ x ⊆ {v | φ v = τ.map x} := by
    rintro _ ⟨u,rfl⟩
    change ⟪gnsVector (tracePositive τ) 1, gnsVector (tracePositive τ) (algebraConj u x)⟫_ℂ = _
    rw [gnsVector_inner, star_one, one_mul]
    exact trace_algebraConj (tracePositive τ) (tracePositive_tracial τ) u x
  exact closure_minimal (convexHull_min ho hc)
    (isClosed_eq φ.continuous continuous_const) hv

theorem gnsConj_hull {M : VonNeumannAlgebra H} (τ : FaithfulNormalTrace M)
    (x : ConcreteAlgebra M) (u : unitary (ConcreteAlgebra M)) :
    Set.MapsTo (gnsConj (tracePositive τ) (tracePositive_tracial τ) u) (conjugacyHull τ x)
      (conjugacyHull τ x) := by
  apply mapsTo_hull ((gnsConj (tracePositive τ) (tracePositive_tracial τ) u).restrictScalars ℝ)
  rintro _ ⟨w,rfl⟩
  refine ⟨u*w, ?_⟩
  change gnsVector (tracePositive τ) (algebraConj (u*w) x) =
    gnsConj (tracePositive τ) (tracePositive_tracial τ) u (gnsVector (tracePositive τ) (algebraConj w x))
  rw [gnsConj_vector]
  congr 1
  simp only [algebraConj_apply, Submonoid.coe_mul, star_mul, mul_assoc]

theorem commute_all_of_unitary {A : Type*} [CStarAlgebra A] (a : A)
    (ha : ∀ u : unitary A, Commute a (u : A)) : ∀ b, Commute a b := by
  intro b
  have hb : b ∈ Submodule.span ℂ (unitary A : Set A) := by
    rw [CStarAlgebra.span_unitary]; trivial
  induction hb using Submodule.span_induction with
  | mem y hy => exact ha ⟨y,hy⟩
  | zero => exact Commute.zero_right _
  | add x y hx hy hx' hy' => exact hx'.add_right hy'
  | smul c x hx hx' => exact hx'.smul_right c

theorem factor_trace_in_conjugacyHull {M : VonNeumannAlgebra H}
    (τ : FaithfulNormalTrace M) (hM : KKFreeLiftFrontier.IsFactor M)
    (x : ConcreteAlgebra M) :
    gnsVector (tracePositive τ) (τ.map x • 1) ∈ conjugacyHull τ x := by
  let : InnerProductSpace ℝ (tracePositive τ).GNS :=
    InnerProductSpace.rclikeToReal ℂ (tracePositive τ).GNS
  have hc : Convex ℝ (conjugacyHull τ x) := (convex_convexHull ℝ _).closure
  have hn : (conjugacyHull τ x).Nonempty := by
    refine ⟨gnsVector (tracePositive τ) x, subset_closure (subset_convexHull ℝ _ ?_)⟩
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, star_one, one_mul, mul_one]
  obtain ⟨v,hv,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hn isClosed_closure.isComplete hc 0
  obtain ⟨a,ha,hav⟩ := conjugacyHull_bounded τ x hv
  have hf (u : unitary (ConcreteAlgebra M)) :
      gnsConj (tracePositive τ) (tracePositive_tracial τ) u v = v := by
    exact (norm_minimizer_unique hc hv (gnsConj_hull τ x u hv) hmin
      (gnsConj_norm (tracePositive τ) (tracePositive_tracial τ) u v)).symm
  have hcentral : ∀ b, Commute a b := by
    apply commute_all_of_unitary
    intro u
    have he : algebraConj u a = a := by
      apply gnsVector_injective τ
      rw [← gnsConj_vector, hav]
      exact hf u
    have he' := congrArg (fun z => z * (u : ConcreteAlgebra M)) he
    simp only [algebraConj_apply, mul_assoc, Unitary.coe_star_mul_self, mul_one] at he'
    exact he'.symm
  obtain ⟨c,hc⟩ := hM a hcentral
  have ht := conjugacyHull_trace τ x v hv
  rw [← hav, gnsVector_inner, star_one, one_mul] at ht
  change τ.map a = τ.map x at ht
  rw [hc, map_smul, τ.normalized, smul_eq_mul, mul_one] at ht
  rw [← ht, ← hc]
  exact hav.symm ▸ hv

end

end KKFactorSupport
end

end OAI
