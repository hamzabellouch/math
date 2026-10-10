import Mathlib
import OAI.Analysis.SymmetricDomains.SmallSlopeGoodSupported
import OAI.Analysis.SymmetricDomains.JointZeroConeProper

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory
open scoped Classical

def NoncollapsedGoodNashBoundary {d N : ℕ} (m : ℕ)
    (U V : Set (Affine N)) (B : Set (Fin d → ℝ))
    (q : (Fin d → ℝ) → Affine N) (x : Fin d → ℝ) : Prop :=
  ∃ c : NashBoundaryChart (m := m) U V B q,
    c.GoodAt x ∧ ‖fderiv ℝ c.normal.graph (c.normal.parameters x)‖ < 1/2 ∧
      ∀ f : (Fin c.normal.normalDim → ℝ) → ℝ,
        (∀ y, Tendsto (fun p : (Fin (c.normal.tangentDim+c.normal.tangentDim+c.normal.normalDim) → ℝ) × ℝ =>
            offsetDistance c.family p.1 p.2 y)
          (𝓝[{p | 0 < p.2}] (c.normal.parameters x,0)) (𝓝 (f y))) → {y | f y = 0} ≠ univ

lemma SmallSlopeGoodNashBoundary.noncollapsed {d m N : ℕ} {Γ : Type*}
    {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
    {q : (Fin d → ℝ) → Affine N} {x : Fin d → ℝ}
    (hgood : SmallSlopeGoodNashBoundary m U V B q x)
    (hUV : U ⊆ V) (hU : IsOpen ((Subtype.val : V → Affine N) ⁻¹' U))
    [LocallyCompactSpace U] (hbounded : Bornology.IsBounded U)
    [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ] [MulAction Γ U] [ProperSMul Γ U]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val))
    (K : Set U) (hK : IsCompact K) (hrep : ∀ x : U, ∃ k ∈ K, ∃ γ : Γ, γ • k = x) :
    NoncollapsedGoodNashBoundary m U V B q x := by
  obtain ⟨c,hc,hd⟩ := hgood
  exact ⟨c,hc,hd,fun f hf => c.joint_zero_cone_proper hc.2.1 hd hc.2.2 hUV hU hbounded hhol K hK hrep f hf⟩

theorem original_noncollapsed_supported_boundary {n : ℕ} (V U : Set (Affine n))
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsConnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U)
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) :
    ∃ (m : ℕ) (C : Finset (NashPatch (n+n))),
      ∀ (bad : ∀ p : C, Set (Fin p.val.dim → ℝ)), (∀ p, volume (bad p) = 0) →
        ∃ (p : C) (x : Fin p.val.dim → ℝ) (k : ℕ)
          (F : Affine m → Affine n) (G : Affine n → Affine m)
          (h : Fin k → Affine n → ℂ),
          x ∈ p.val.domain ∧ x ∉ bad p ∧ p.val.complexMap x ∈ closure U \ U ∧
          NoncollapsedGoodNashBoundary m U (MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U))
            p.val.domain p.val.complexMap x ∧
          1 ≤ k ∧ k ≤ m ∧ p.val.dim + k = 2*m ∧
          F 0 = p.val.complexMap x ∧ AnalyticAt ℂ F 0 ∧
          AnalyticAt ℂ G (p.val.complexMap x) ∧
          (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id ∧
          (∀ᶠ y in 𝓝[MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)] (p.val.complexMap x), F (G y) = y) ∧
          (∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ U)) ∧
          Submodule.span ℂ (range (fderiv ℝ (G ∘ p.val.complexMap) x)) = ⊤ ∧
          (∀ i, AnalyticOnNhd ℂ (h i) univ) ∧
          (∀ i, h i (p.val.complexMap x) = 1) ∧
          (∀ i, ∀ z ∈ closure U, ‖h i z‖ ≤ Real.exp (-(dist z (p.val.complexMap x))^2)) ∧
          (∀ i, AnalyticAt ℂ (fun z => Complex.log (h i (F z))) 0) ∧
          LinearIndependent ℝ (fun i => (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).toLinearMap) ∧
          LinearIndependent ℂ (fun i => (fderiv ℂ (fun z => Complex.log (h i (F z))) 0).toLinearMap) ∧
          ∀ i, (fderiv ℝ (fun z => Real.log ‖h i (F z)‖) 0).comp (fderiv ℝ (G ∘ p.val.complexMap) x) = 0 := by
  let : LocallyCompactSpace U := locallyCompact_of_relative_open hV hUV hU
  let : ContinuousConstSMul Γ U := ⟨fun γ => ((hhol γ).continuous).subtype_mk _⟩
  obtain ⟨K,hK,hrep⟩ := exists_compact_orbit_representatives (X := U) (Γ := Γ)
  let I := MvPolynomial.vanishingIdeal ℂ U
  have hUI : U ⊆ MvPolynomial.zeroLocus ℂ I := fun z hz p hp => hp z hz
  have hIV : MvPolynomial.zeroLocus ℂ I ⊆ V := by
    obtain ⟨R,hR⟩ := hV
    intro z hz
    rw [hR]
    intro p hp
    apply hz p
    intro y hy
    exact (hR ▸ hUV hy) p hp
  have hUIopen : IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U) :=
    hU.preimage (continuous_inclusion hIV)
  obtain ⟨m,C,he⟩ := original_small_slope_good_supported_boundary V U hV hUV hU hc hn hb hs Γ hhol
  refine ⟨m,C,fun bad hbad => ?_⟩
  obtain ⟨p,x,k,F,G,h,hxp,hxb,hbd,hgood,hrest⟩ := he bad hbad
  exact ⟨p,x,k,F,G,h,hxp,hxb,hbd,hgood.noncollapsed hUI hUIopen hb hhol K hK hrep,hrest⟩
end Release061

end

end OAI
