import Mathlib
import OAI.Probability.UnimodularPercolation.Kernel.ContactTrace

namespace OAI

/-! Russo Rows for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section PairFunctionalAlgebra
attribute [local instance] Classical.propDecidable Classical.decEq

theorem clusterPairFunctional_mono_distinct (G : BondGraph V E) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (F H : Set E → V → V → ℝ≥0∞)
    (h : ∀ ω x y, ¬Conn G ω x y → F ω x y ≤ H ω x y) :
    clusterPairFunctional G p root weight F ≤ clusterPairFunctional G p root weight H := by
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_right
  apply lintegral_mono
  intro ω
  unfold clusterPairDensity
  apply mul_le_mul_right
  apply ENNReal.tsum_le_tsum
  intro y
  apply mul_le_mul_right
  by_cases hc : Conn G ω (root i) y
  · simp only [hc,not_true_eq_false,ite_false,le_refl]
  · simpa only [ite_eq_left hc] using h ω (root i) y hc

theorem clusterPairFunctional_congr_ae (G : BondGraph V E) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (F H : Set E → V → V → ℝ≥0∞)
    (h : ∀ᵐ ω ∂law p, ∀ x y, ¬Conn G ω x y → F ω x y = H ω x y) :
    clusterPairFunctional G p root weight F = clusterPairFunctional G p root weight H := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply lintegral_congr_ae
  filter_upwards [h] with ω hω
  unfold clusterPairDensity
  congr 1
  apply tsum_congr
  intro y
  congr 1
  by_cases hc : Conn G ω (root i) y
  · simp only [hc,not_true_eq_false,ite_false]
  · rw [ite_eq_left hc,ite_eq_left hc,hω (root i) y hc]

theorem clusterPairFunctional_add [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (F H : Set E → V → V → ℝ≥0∞)
    (hF : ∀ x y, Measurable (fun ω => F ω x y))
    (hH : ∀ x y, Measurable (fun ω => H ω x y)) :
    clusterPairFunctional G p root weight (fun ω x y => F ω x y+H ω x y) =
      clusterPairFunctional G p root weight F + clusterPairFunctional G p root weight H := by
  let : MeasurableSpace V := ⊤
  let : MeasurableSingletonClass V := ⟨fun _ => trivial⟩
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  rw [clusterPairFunctional_eq_lintegral G hloc p root weight _ hF,
    clusterPairFunctional_eq_lintegral G hloc p root weight _ hH,
    clusterPairFunctional_eq_lintegral G hloc p root weight (fun ω x y => F ω x y+H ω x y) (fun x y => (hF x y).add (hH x y))]
  exact lintegral_add_left (measurable_from_prod_countable_left (fun q => hF (root q.1) q.2)) _

theorem clusterPairKernel_symm (G : BondGraph V E) (ω : Set E)
    (J : V → V → ℝ≥0∞) (hJ : ∀ x y, J x y = J y x) (x y : V) :
    clusterPairKernel G ω J x y = clusterPairKernel G ω J y x := by
  unfold clusterPairKernel
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro a
  apply tsum_congr
  intro b
  simp only [and_comm,hJ b a]

end PairFunctionalAlgebra
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section LargeContactCauchySchwarz
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def largeContactKernel (G : BondGraph V E) (L : ℝ)
    (ω : Set E) (x y : V) : ℝ≥0∞ :=
  if L ≤ min ((cluster G ω x).ncard:ℝ) ((cluster G ω y).ncard:ℝ) then
    clusterPairKernel G ω (indexedEdgeKernel G) x y else 0

theorem measurable_largeContactKernel [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (L : ℝ) (x y : V) :
    Measurable (fun ω => largeContactKernel G L ω x y) := by
  have hm (z : V) : Measurable (fun ω : Set E => ((cluster G ω z).ncard:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc z)
  exact (measurable_clusterPairKernel G (indexedEdgeKernel G) x y).ite
    (measurableSet_le measurable_const ((hm x).min (hm y))) measurable_const

theorem clusterPairFunctional_largeContact_sq [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (L : ℝ) (p : unitInterval)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite) :
    clusterPairFunctional G p root weight (fun ω x y => (largeContactKernel G L ω x y)^2) =
      clusterPairFunctional G p root weight (contactSquareLargeReal G L) := by
  apply clusterPairFunctional_congr_ae G p root weight
  filter_upwards [ae_all_iff.mpr hfin] with ω hω
  intro x y hxy
  dsimp only [largeContactKernel,contactSquareLargeReal]
  split_ifs
  · rw [clusterPairKernel_edge G hloc ω x y hxy (hω x)]
  · rw [zero_pow (by decide : 2 ≠ 0)]

theorem clusterPairFunctional_largeContact_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T) (L : ℝ) (B : ℝ≥0∞)
    (hB : clusterPairFunctional G p root weight (contactSquareLargeReal G L) ≤ B) :
    clusterPairFunctional G p root weight (fun ω x y =>
      largeContactKernel G L ω x y * clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y) ≤
      B^((1:ℝ)/2)* (ENNReal.ofReal (‖T‖^3*(rootTrace root weight (T^3)).re))^((1:ℝ)/2) := by
  have hh := clusterPairFunctional_cauchy_schwarz G hloc p root weight
    (largeContactKernel G L) (fun ω x y => clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y)
    (measurable_largeContactKernel G hloc L) (measurable_clusterPairKernel G _)
  rw [clusterPairFunctional_largeContact_sq G hloc L p root weight hfin] at hh
  exact hh.trans (mul_le_mul
    (ENNReal.rpow_le_rpow hB (by positivity))
    (ENNReal.rpow_le_rpow (clusterPairFunctional_twoPoint_square_bound G hconn hloc root weight Γ hΓ htr hw p hfin T hT) (by positivity))
    bot_le bot_le)

end LargeContactCauchySchwarz
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal ComplexOrder
section SmallTraceTerm
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contact_smallTwoPoint_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (L α C : ℝ) (hL : 0 ≤ L) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hI : ∀ x, Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p))
    (hC : ∀ x, (∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) ≤ C)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) :
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * smallPairKernel G (ennMatrixCoeff (T^2)) L x y ω) ≤
      ENNReal.ofReal ((d:ℝ)*c*C*L^(1-α)*(rootTrace root weight (T^3)).re) := by
  have hTI : KernelInvariant Γ T := fun a ha => hT.invariant G p T a (hΓ ha)
  have hJ : ∀ a ∈ Γ, ∀ x y, ennMatrixCoeff (T^2) (a x) (a y) = ennMatrixCoeff (T^2) x y := by
    intro a ha x y
    unfold ennMatrixCoeff
    rw [(hTI.pow 2) a ha]
  have hpos : 0 ≤ T := ContinuousLinearMap.nonneg_iff_isPositive.mpr (hT.isPositive G p T)
  have hMt : 0 ≤ c*(rootTrace root weight (T^3)).re := mul_nonneg hc
    (Complex.nonneg_iff.mp (rootTrace_nonneg root weight hw _ (CStarAlgebra.pow_nonneg T 3 hpos))).1
  have hh := contact_smallPairKernel_bound G hconn hloc root weight Γ hΓ htr hw hw1 p hfin
    (ennMatrixCoeff (T^2)) hJ L d hd (c*C*L^(1-α)*(rootTrace root weight (T^3)).re) (fun x y => by
      refine (smallPairKernel_twoPoint_bound G hloc root weight Γ hΓ hcov hw c hc hmin x y p T hT L α hL hα0 hα1 (hfin x) (hfin y) (hI x)).trans ?_
      apply ENNReal.ofReal_le_ofReal
      calc
        _ ≤ (c*(rootTrace root weight (T^3)).re)*(L^(1-α)*C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC x) (Real.rpow_nonneg hL _)) hMt
        _ = _ := by ring)
  convert hh using 1; congr 1; ring

end SmallTraceTerm
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal ComplexOrder
section MixedTraceTerm
attribute [local instance] Classical.propDecidable Classical.decEq

theorem contact_smallPairKernel_swap [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hw : ∀ i, 0 ≤ weight i) (p : unitInterval)
    (J : V → V → ℝ≥0∞) (hJ : ∀ a ∈ Γ, ∀ x y, J (a x) (a y) = J x y) (L : ℝ) :
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) y x * smallPairKernel G J L y x ω) =
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * smallPairKernel G J L x y ω) := by
  symm
  apply clusterPairFunctional_swap G hconn hloc root weight Γ hΓ htr hw p
    (fun ω x y => clusterPairKernel G ω (indexedEdgeKernel G) x y * smallPairKernel G J L x y ω)
  · intro x y
    exact (measurable_clusterPairKernel G _ x y).mul (measurable_smallPairKernel G hloc J L x y)
  · intro a ha b hab ω x y
    rw [clusterPairKernel_aut G hab _ (indexedEdgeKernel_aut G hab),smallPairKernel_aut G hab J (hJ a ha)]

 

theorem clusterPairFunctional_twoPoint_mixed_bound [Countable V] [Countable E]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ a ∈ Γ, a (root i) = x)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hfin : ∀ x, ∀ᵐ ω ∂law p, (cluster G ω x).Finite)
    (T : Hilbert V →L[ℂ] Hilbert V) (hT : HasKernel G p T)
    (L α C : ℝ) (hL : 0 ≤ L) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hI : ∀ x, Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^α) (law p))
    (hC : ∀ x, (∫ ω, ((cluster G ω x).ncard:ℝ)^α ∂law p) ≤ C)
    (d : ℕ) (hd : ∀ x, degree G x ≤ d) (B : ℝ≥0∞)
    (hB : clusterPairFunctional G p root weight (contactSquareLargeReal G L) ≤ B) :
    clusterPairFunctional G p root weight (fun ω x y =>
      clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y) ≤
    2*ENNReal.ofReal ((d:ℝ)*c*C*L^(1-α)*(rootTrace root weight (T^3)).re) +
      B^((1:ℝ)/2)* (ENNReal.ofReal (‖T‖^3*(rootTrace root weight (T^3)).re))^((1:ℝ)/2) := by
  let J := ennMatrixCoeff (T^2)
  let A := fun ω x y => clusterPairKernel G ω (indexedEdgeKernel G) x y*smallPairKernel G J L x y ω
  let D := fun ω x y => largeContactKernel G L ω x y*clusterPairKernel G ω J x y
  have heS (ω : Set E) (x y : V) : clusterPairKernel G ω (indexedEdgeKernel G) y x =
      clusterPairKernel G ω (indexedEdgeKernel G) x y := clusterPairKernel_symm G ω _ (indexedEdgeKernel_symm G) y x
  have hpos : 0 ≤ T := ContinuousLinearMap.nonneg_iff_isPositive.mpr (hT.isPositive G p T)
  have hJS (ω : Set E) (x y : V) : clusterPairKernel G ω J y x = clusterPairKernel G ω J x y :=
    clusterPairKernel_symm G ω J (ennMatrixCoeff_symm ((IsSelfAdjoint.of_nonneg hpos).pow 2)) y x
  have hTI : KernelInvariant Γ T := fun a ha => hT.invariant G p T a (hΓ ha)
  have hJI : ∀ a ∈ Γ, ∀ x y, J (a x) (a y) = J x y := by
    intro a ha x y
    dsimp [J,ennMatrixCoeff]
    rw [(hTI.pow 2) a ha]
  have hA (x y : V) : Measurable (fun ω => A ω x y) :=
    (measurable_clusterPairKernel G _ x y).mul (measurable_smallPairKernel G hloc J L x y)
  have hD (x y : V) : Measurable (fun ω => D ω x y) :=
    (measurable_largeContactKernel G hloc L x y).mul (measurable_clusterPairKernel G J x y)
  have hpw (ω : Set E) (x y : V) (hxy : ¬Conn G ω x y) :
      clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω J x y ≤ A ω x y + A ω y x + D ω x y := by
    have hyx : ¬Conn G ω y x := fun h => hxy (conn_symm G ω h)
    by_cases hx : ((cluster G ω x).ncard:ℝ) < L
    · have ha : A ω x y = clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω J x y := by
        dsimp [A,smallPairKernel]; rw [ite_eq_left ⟨hx,hxy⟩]
      rw [←ha]
      exact le_add_of_le_left (le_add_right le_rfl)
    · by_cases hy : ((cluster G ω y).ncard:ℝ) < L
      · have ha : A ω y x = clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω J x y := by
          dsimp [A,smallPairKernel]; rw [ite_eq_left ⟨hy,hyx⟩,heS ω x y,hJS ω x y]
        rw [←ha]
        exact le_add_of_le_left (le_add_left le_rfl)
      · have hg : L ≤ min ((cluster G ω x).ncard:ℝ) ((cluster G ω y).ncard:ℝ) := le_min (le_of_not_gt hx) (le_of_not_gt hy)
        have hh : D ω x y = clusterPairKernel G ω (indexedEdgeKernel G) x y * clusterPairKernel G ω J x y := by
          dsimp [D,largeContactKernel]; rw [ite_eq_left hg]
        rw [←hh]
        exact le_add_left le_rfl
  have ha := contact_smallTwoPoint_bound G hconn hloc root weight Γ hΓ htr hcov hw hw1 c hc hmin p hfin T hT L α C hL hα0 hα1 hI hC d hd
  have hb := clusterPairFunctional_largeContact_bound G hconn hloc root weight Γ hΓ htr hw p hfin T hT L B hB
  calc
    _ ≤ clusterPairFunctional G p root weight (fun ω x y => A ω x y+A ω y x+D ω x y) :=
      clusterPairFunctional_mono_distinct G p root weight _ _ hpw
    _ = (clusterPairFunctional G p root weight A + clusterPairFunctional G p root weight A) + clusterPairFunctional G p root weight D := by
      rw [clusterPairFunctional_add G hloc p root weight (fun ω x y => A ω x y+A ω y x) D (fun x y => (hA x y).add (hA y x)) hD,
        clusterPairFunctional_add G hloc p root weight A (fun ω x y => A ω y x) hA (fun x y => hA y x)]
      rw [contact_smallPairKernel_swap G hconn hloc root weight Γ hΓ htr hw p J hJI L]
    _ ≤ _ := by simpa only [two_mul] using add_le_add (add_le_add ha ha) hb

end MixedTraceTerm
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section UniformMixedTrace
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem critical_mixed_trace_bound
    [Countable V] [Countable E] [Nonempty V] [Nonempty E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hconn : Connected G)
    (hqt : QuasiTransitive G) (hh : 0 < hV G)
    {ι : Type*} [Fintype ι] [Nonempty ι] (root : ι → V) (weight : ι → ℝ)
    (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G) (htr : RootTransport root weight Γ)
    (hcov : ∀ x, ∃ i, ∃ e ∈ Γ, e (root i) = x)
    (hw : ∀ i, 0 < weight i) (hw1 : ∑ i, weight i = 1)
    (hp₀ : 0 < (pc G:ℝ)) (hp₁ : (pc G:ℝ) < 1)
    (hfin : ∀ i, ∀ᵐ ω ∂law (pc G), (cluster G ω (root i)).Finite)
    (α ε : ℝ) (hα : 0 < α) (hα1 : α < 1/2) (hε : 0 < ε)
    (hr : (1:ℝ)/2+ε-2*α < 0) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ (p : unitInterval),
      (pc G:ℝ)/2 ≤ (p:ℝ) → p ≤ pc G →
      ∀ (T : Hilbert V →L[ℂ] Hilbert V), HasKernel G p T →
      ∀ L : ℝ, 1 ≤ L →
        clusterPairFunctional G p root weight (fun ω x y =>
          clusterPairKernel G ω (indexedEdgeKernel G) x y *
          clusterPairKernel G ω (ennMatrixCoeff (T^2)) x y) ≤
        2*ENNReal.ofReal (A*L^(1-α)*(rootTrace root weight (T^3)).re) +
          (ENNReal.ofReal (B*L^((1:ℝ)/2+ε-2*α)))^((1:ℝ)/2) *
          (ENNReal.ofReal (‖T‖^3*(rootTrace root weight (T^3)).re))^((1:ℝ)/2) := by
  have hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i) := by
    intro x
    obtain ⟨i,a,ha,hax⟩ := hcov x
    obtain ⟨b,hab⟩ := hΓ ha
    exact ⟨i,a,b,hab,hax⟩
  have hfinite : ∀ x, ∀ᵐ ω ∂law (pc G), (cluster G ω x).Finite := by
    intro x
    obtain ⟨i,a,b,hab,rfl⟩ := hcover x
    exact cluster_finite_ae_covariant G (pc G) hab (root i) (hfin i)
  obtain ⟨C,hC,hCb⟩ := uniform_cluster_power_of_root G hloc (pc G) root hcover α
    (critical_root_power_integrable G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α hα hα1)
  obtain ⟨B,hB,hBb⟩ := critical_contact_square_bound G hloc hconn hqt hh root weight Γ hΓ htr hcov hw hw1 hp₀ hp₁ hfin α ε hα hα1 hε hr
  obtain ⟨d,hd,hdg⟩ := exists_degree_bound G hqt
  let c : ℝ := ∑ i, 1/weight i
  have hc : 0 < c := Finset.sum_pos (fun i _ => one_div_pos.mpr (hw i)) Finset.univ_nonempty
  have hmin (i : ι) : 1 ≤ c*weight i := by
    apply (div_le_iff₀ (hw i)).mp
    exact Finset.single_le_sum (fun j _ => (one_div_pos.mpr (hw j)).le) (Finset.mem_univ i)
  refine ⟨(d:ℝ)*c*C,B,mul_pos (mul_pos (by exact_mod_cast hd) hc) hC,hB,?_⟩
  intro p hp hpq T hT L hL
  have hm (x : V) := cluster_power_mono_integral G hloc x p (pc G) hpq α hα.le (hfinite x) (hCb x).1
  exact clusterPairFunctional_twoPoint_mixed_bound G hconn hloc root weight Γ hΓ htr hcov
    (fun i => (hw i).le) hw1 c hc.le hmin p
    (fun x => cluster_finite_ae_mono G x p (pc G) hpq (hfinite x))
    T hT L α C (by linarith) hα.le (by linarith)
    (fun x => (hm x).1) (fun x => (hm x).2.trans (hCb x).2) d hdg _ (hBb p hp hpq L hL)

end UniformMixedTrace
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ConnectionRussoContacts
attribute [local instance] Classical.propDecidable Classical.decEq

theorem closedPivotal_connection_iff (G : BondGraph V E) (ω : Set E) (x y : V) (e : E) :
    ω ∈ closedPivotal {η | Conn G η x y} e ↔
      ¬Conn G ω x y ∧ e ∈ closedContactSet G (cluster G ω x) (cluster G ω y) := by
  constructor
  · rintro ⟨_,hxy,hins⟩
    refine ⟨hxy,?_⟩
    obtain ⟨⟨a,b⟩,hab⟩ := Quot.exists_rep (G e)
    have he : G e = s(a,b) := hab.symm
    rcases (conn_insert_iff G ω e a b x y he).mp hins with h | h | h
    · exact (hxy h).elim
    · exact ⟨a,h.1,b,conn_symm G ω h.2,he⟩
    · exact ⟨b,h.1,a,conn_symm G ω h.2,by rw [he,Sym2.eq_swap]⟩
  · rintro ⟨hxy,a,hxa,b,hyb,he⟩
    have hclosed : e ∉ ω := by
      intro heω
      exact hxy (hxa.trans ((Relation.ReflTransGen.single ⟨e,heω,he⟩).trans (conn_symm G ω hyb)))
    refine ⟨hclosed,hxy,?_⟩
    exact (conn_insert_iff G ω e a b x y he).mpr (Or.inr (Or.inl ⟨hxa,conn_symm G ω hyb⟩))

noncomputable def finiteClosedContact (G : BondGraph V E) (Q : Finset E) (x y : V)
    (ω : Finset E) : ℝ :=
  if ¬Conn G (ω:Set E) x y then
    (contactBonds G Q (finiteRootComponent G ω x) (finiteRootComponent G ω y)).card else 0

theorem finiteClosedContact_eq_sum (G : BondGraph V E) (Q : Finset E) (x y : V)
    (ω : Finset E) :
    finiteClosedContact G Q x y ω =
      ∑ e ∈ Q, if (ω:Set E) ∈ closedPivotal {η | Conn G η x y} e then (1:ℝ) else 0 := by
  have hm (z a : V) : a ∈ finiteRootComponent G ω z ↔ Conn G (ω:Set E) z a := by
    change a ∈ (finiteRootComponent G ω z:Set V) ↔ _
    rw [coe_finiteRootComponent]
    rfl
  simp only [closedPivotal_connection_iff,closedContactSet,Set.mem_ofPred_eq,finiteClosedContact]
  by_cases hxy : Conn G (ω:Set E) x y
  · simp only [hxy,not_true_eq_false,false_and,ite_false,Finset.sum_const_zero]
  · rw [ite_eq_left hxy]
    simp only [hxy,not_false_eq_true,true_and,contactBonds,hm,cluster,Set.mem_ofPred_eq]
    rw [Finset.sum_boole]

theorem finite_connection_russo_contacts (G : BondGraph V E) (Q : Finset E)
    (x y : V) (p : ℝ) :
    (1-p)*deriv (finiteEventPolynomial Q {ω | Conn G ω x y}) p =
      bernoulliPolynomial Q (finiteClosedContact G Q x y) p := by
  change (1-p)*deriv (bernoulliPolynomial Q (fun ω => if Conn G (ω:Set E) x y then 1 else 0)) p = _
  rw [closed_difference_russo]
  have he : finiteClosedContact G Q x y = fun (ω : Finset E) =>
      ∑ e ∈ Q, if (ω:Set E) ∈ closedPivotal {η | Conn G η x y} e then (1:ℝ) else 0 :=
    funext (finiteClosedContact_eq_sum G Q x y)
  rw [he,bernoulliPolynomial_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply bernoulliPolynomial_congr
  intro ω _
  exact (closedPivotal_difference {η | Conn G η x y}
    (fun _ _ h hc => conn_mono G h hc) e ω).symm

end ConnectionRussoContacts
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section UniformContactApproximation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem finiteClosedContact_eq_full (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω : Set E) (x y : V) (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite)
    (Q : Finset E) (hQx : incidentSupport G hloc hx.toFinset ⊆ Q)
    (hQy : incidentSupport G hloc hy.toFinset ⊆ Q) :
    finiteClosedContact G Q x y (domainBits Q ω) = fullLargeContact G x y 0 ω := by
  have hcluster (z : V) (hz : (cluster G ω z).Finite) (hQ : incidentSupport G hloc hz.toFinset ⊆ Q) :
      cluster G (domainBits Q ω:Set E) z = cluster G ω z := by
    rw [coe_domainBits]
    have hh := (cluster_restrict_incident_eq_iff G hloc hz.toFinset Q hQ ω z).mpr
      (Set.Finite.coe_toFinset hz).symm
    simpa only [Set.Finite.coe_toFinset] using hh
  have hcx := hcluster x hx hQx
  have hcy := hcluster y hy hQy
  have hFx : finiteRootComponent G (domainBits Q ω) x = hx.toFinset := by
    apply Finset.coe_injective
    rw [coe_finiteRootComponent,hcx,Set.Finite.coe_toFinset]
  have hFy : finiteRootComponent G (domainBits Q ω) y = hy.toFinset := by
    apply Finset.coe_injective
    rw [coe_finiteRootComponent,hcy,Set.Finite.coe_toFinset]
  have hconn : Conn G (domainBits Q ω:Set E) x y ↔ Conn G ω x y := by
    change y ∈ cluster G (domainBits Q ω:Set E) x ↔ y ∈ cluster G ω x
    rw [hcx]
  have hc : (contactBonds G Q hx.toFinset hy.toFinset).card = clusterContactCount G ω x y := by
    rw [←Set.ncard_coe_finset,coe_contactBonds_eq G hloc Q _ _ hQx]
    simp only [Set.Finite.coe_toFinset,clusterContactCount]
  simp only [finiteClosedContact,fullLargeContact,hconn,hFx,hFy,hc,Nat.zero_le,and_true]

theorem finiteClosedContact_nonneg (G : BondGraph V E) (Q : Finset E) (x y : V) (ω : Finset E) :
    0 ≤ finiteClosedContact G Q x y ω := by
  unfold finiteClosedContact
  split_ifs <;> positivity

theorem finiteClosedContact_le_size (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (Q η : Finset E) (ω : Set E)
    (hη : (η:Set E) ⊆ ω) (x y : V) (hfin : (cluster G ω x).Finite) :
    finiteClosedContact G Q x y η ≤ (d:ℝ)*(cluster G ω x).ncard := by
  have hdQ (z : V) : (Q.filter fun e => z ∈ G e).card ≤ d :=
    (incident_filter_card_le_degree G hloc Q z).trans (hd z)
  have hs : (finiteRootComponent G η x).card ≤ (cluster G ω x).ncard := by
    rw [←Set.ncard_coe_finset,coe_finiteRootComponent]
    exact Set.ncard_le_ncard (fun z hz => conn_mono G hη hz) hfin
  unfold finiteClosedContact
  split_ifs
  · positivity
  · exact_mod_cast (contactBonds_card_le G Q d hdQ _ _).trans
      (Nat.mul_le_mul_left d ((min_le_left _ _).trans hs))

 

theorem lower_cluster_restrict_eq (G : BondGraph V E) (hloc : LocallyFinite G)
    (ω η : Set E) (hη : η ⊆ ω) (x : V) (hx : (cluster G ω x).Finite)
    (Q : Finset E) (hQ : incidentSupport G hloc hx.toFinset ⊆ Q) :
    cluster G (η ∩ (Q:Set E)) x = cluster G η x := by
  have hfin : (cluster G η x).Finite := hx.subset (fun z hz => conn_mono G hη hz)
  have hs : hfin.toFinset ⊆ hx.toFinset := by
    intro z hz
    exact hx.mem_toFinset.mpr (conn_mono G hη (hfin.mem_toFinset.mp hz))
  have hQ' := (incidentSupport_mono G hloc hs).trans hQ
  have hh := (cluster_restrict_incident_eq_iff G hloc hfin.toFinset Q hQ' η x).mpr
    (Set.Finite.coe_toFinset hfin).symm
  simpa only [Set.Finite.coe_toFinset] using hh

end UniformContactApproximation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section ContactRegularity
attribute [local instance] Classical.propDecidable Classical.decEq

theorem fullLargeContact_zero_le_size (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (ω : Set E) (x y : V)
    (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite) :
    fullLargeContact G x y 0 ω ≤ (d:ℝ)*(cluster G ω x).ncard := by
  let Q := incidentSupport G hloc hx.toFinset ∪ incidentSupport G hloc hy.toFinset
  rw [←finiteClosedContact_eq_full G hloc ω x y hx hy Q Finset.subset_union_left Finset.subset_union_right]
  exact finiteClosedContact_le_size G hloc d hd Q (domainBits Q ω) ω
    (by rw [coe_domainBits]; exact Set.inter_subset_left) x y hx

theorem integrable_fullContact_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (fullLargeContact G x y 0) (law p) := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  apply ((susceptibility_eq_integral G hloc hqt p hp x).1.const_mul (d:ℝ)).mono'
    (measurable_fullLargeContact G hloc x y 0).aestronglyMeasurable
  filter_upwards [subcritical_cluster_finite_ae G p hp x,subcritical_cluster_finite_ae G p hp y] with ω hx hy
  rw [Real.norm_of_nonneg (fullLargeContact_nonneg G x y 0 ω)]
  exact fullLargeContact_zero_le_size G hloc d hd ω x y hx hy

theorem fullContact_label_integral [Countable E] [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y : V) :
    (∫ labels, fullLargeContact G x y 0 (openEdges labels p) ∂labelLaw) =
      ∫ ω, fullLargeContact G x y 0 ω ∂law p := by
  rw [←map_openEdges p]
  exact (integral_map (measurable_openEdges p).aemeasurable
    (measurable_fullLargeContact G hloc x y 0).aestronglyMeasurable).symm

theorem fullContact_label_integrable [Countable E] [Countable V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y : V) :
    Integrable (fun labels => fullLargeContact G x y 0 (openEdges labels p)) labelLaw ↔
      Integrable (fullLargeContact G x y 0) (law p) := by
  rw [←map_openEdges p]
  exact (integrable_map_measure (measurable_fullLargeContact G hloc x y 0).aestronglyMeasurable
    (measurable_openEdges p).aemeasurable).symm

theorem fullContact_eq_of_clusters (G : BondGraph V E) (ω η : Set E) (x y : V)
    (hx : cluster G ω x = cluster G η x) (hy : cluster G ω y = cluster G η y) :
    fullLargeContact G x y 0 ω = fullLargeContact G x y 0 η := by
  have hc : Conn G ω x y ↔ Conn G η x y := by
    change y ∈ cluster G ω x ↔ y ∈ cluster G η x
    rw [hx]
  simp only [fullLargeContact,clusterContactCount,hx,hy,hc]

 

theorem continuousAt_fullContact_expectation [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    ContinuousAt (fun q => ∫ ω, fullLargeContact G x y 0 ω ∂law q) p := by
  obtain ⟨r,hpr,hr⟩ := exists_between hp
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  let F (q : unitInterval) (labels : E → unitInterval) := fullLargeContact G x y 0 (openEdges labels q)
  let B (labels : E → unitInterval) : ℝ := (d:ℝ)*(cluster G (openEdges labels r) x).ncard
  have hm (q : unitInterval) : Measurable (F q) :=
    (measurable_fullLargeContact G hloc x y 0).comp (measurable_openEdges q)
  have hc : ContinuousAt (fun q => ∫ labels, F q labels ∂labelLaw) p := by
    apply continuousAt_of_dominated (bound := B)
      (Eventually.of_forall (fun q => (hm q).aestronglyMeasurable))
    · filter_upwards [eventually_lt_nhds hpr] with q hqr
      filter_upwards [label_cluster_finite_ae_subcritical G r hr x,label_cluster_finite_ae_subcritical G r hr y] with labels hx hy
      have hsub (z : V) : cluster G (openEdges labels q) z ⊆ cluster G (openEdges labels r) z :=
        fun w hw => conn_mono G (openEdges_mono labels hqr.le) hw
      rw [Real.norm_of_nonneg (fullLargeContact_nonneg G x y 0 _)]
      calc
        _ ≤ (d:ℝ)*(cluster G (openEdges labels q) x).ncard :=
          fullLargeContact_zero_le_size G hloc d hd _ x y (hx.subset (hsub x)) (hy.subset (hsub y))
        _ ≤ B labels := mul_le_mul_of_nonneg_left (by exact_mod_cast Set.ncard_le_ncard (hsub x) hx) (Nat.cast_nonneg _)
    · exact (susceptibility_eq_label_integral G hloc hqt r hr x).1.const_mul (d:ℝ)
    · filter_upwards [ae_labels_ne (E := E) p,label_cluster_finite_ae_subcritical G p hp x,
        label_cluster_finite_ae_subcritical G p hp y] with labels hneq hx hy
      apply Filter.EventuallyEq.continuousAt
      filter_upwards [eventually_cluster_eq_at_finite G hloc labels p x hneq hx,
        eventually_cluster_eq_at_finite G hloc labels p y hneq hy] with q hqx hqy
      exact fullContact_eq_of_clusters G _ _ x y hqx hqy
  simpa only [F,fullContact_label_integral G hloc] using hc

end ContactRegularity
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section UniformContactError
attribute [local instance] Classical.propDecidable Classical.decEq

def ClusterSupportIn (G : BondGraph V E) (Q : Finset E) (ω : Set E) (x : V) : Prop :=
  ∀ a, Conn G ω x a → ∀ e, a ∈ G e → e ∈ Q

theorem measurableSet_clusterSupportIn [Countable V] [Countable E]
    (G : BondGraph V E) (Q : Finset E) (x : V) :
    MeasurableSet {ω : Set E | ClusterSupportIn G Q ω x} := by
  simp only [ClusterSupportIn,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro a
  have he : {ω : Set E | Conn G ω x a → ∀ e, a ∈ G e → e ∈ Q} =
      {ω | ¬Conn G ω x a} ∪ {ω | ∀ e, a ∈ G e → e ∈ Q} := by ext ω; simp only [Set.mem_union,Set.mem_ofPred_eq]; tauto
  rw [he]
  apply (measurableSet_conn G x a).compl.union
  by_cases h : ∀ e, a ∈ G e → e ∈ Q
  · convert (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Set E))) using 1
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_univ,iff_true]
    exact h
  · convert (MeasurableSet.empty : MeasurableSet (∅ : Set (Set E))) using 1
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
    exact h

theorem clusterSupportIn_of_incident (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (ω : Set E) (x : V) (hx : (cluster G ω x).Finite)
    (hQ : incidentSupport G hloc hx.toFinset ⊆ Q) : ClusterSupportIn G Q ω x := by
  intro a ha e he
  exact hQ ((mem_incidentSupport G hloc hx.toFinset e).mpr ⟨a,hx.mem_toFinset.mpr ha,he⟩)

theorem finiteClosedContact_eq_full_of_support (G : BondGraph V E) (hloc : LocallyFinite G)
    (Q : Finset E) (ω η : Set E) (hη : η ⊆ ω) (x y : V)
    (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite)
    (hQx : ClusterSupportIn G Q ω x) (hQy : ClusterSupportIn G Q ω y) :
    finiteClosedContact G Q x y (domainBits Q η) = fullLargeContact G x y 0 η := by
  have hsub (z : V) : cluster G η z ⊆ cluster G ω z := fun a ha => conn_mono G hη ha
  have hfx := hx.subset (hsub x)
  have hfy := hy.subset (hsub y)
  apply finiteClosedContact_eq_full G hloc η x y hfx hfy
  · intro e he
    obtain ⟨a,ha,he⟩ := (mem_incidentSupport G hloc hfx.toFinset e).mp he
    exact hQx a (hsub x (hfx.mem_toFinset.mp ha)) e he
  · intro e he
    obtain ⟨a,ha,he⟩ := (mem_incidentSupport G hloc hfy.toFinset e).mp he
    exact hQy a (hsub y (hfy.mem_toFinset.mp ha)) e he

noncomputable def contactApproxError (G : BondGraph V E) (Q : Finset E) (d : ℕ)
    (x y : V) (ω : Set E) : ℝ :=
  if ClusterSupportIn G Q ω x ∧ ClusterSupportIn G Q ω y then 0
  else (d:ℝ)*(cluster G ω x).ncard

theorem measurable_contactApproxError [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (Q : Finset E) (d : ℕ) (x y : V) :
    Measurable (contactApproxError G Q d x y) := by
  exact measurable_const.ite ((measurableSet_clusterSupportIn G Q x).inter
    (measurableSet_clusterSupportIn G Q y))
    (measurable_const.mul ((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc x)))

theorem contactApproxError_nonneg (G : BondGraph V E) (Q : Finset E) (d : ℕ) (x y : V) (ω : Set E) :
    0 ≤ contactApproxError G Q d x y ω := by unfold contactApproxError; split_ifs <;> positivity

theorem contactApproxError_le (G : BondGraph V E) (Q : Finset E) (d : ℕ) (x y : V) (ω : Set E) :
    contactApproxError G Q d x y ω ≤ (d:ℝ)*(cluster G ω x).ncard := by
  unfold contactApproxError; split_ifs <;> first | positivity | exact le_rfl

theorem contact_uniform_error_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (Q : Finset E) (ω η : Set E)
    (hη : η ⊆ ω) (x y : V) (hx : (cluster G ω x).Finite) (hy : (cluster G ω y).Finite) :
    ‖finiteClosedContact G Q x y (domainBits Q η) - fullLargeContact G x y 0 η‖ ≤
      contactApproxError G Q d x y ω := by
  unfold contactApproxError
  split_ifs with h
  · rw [finiteClosedContact_eq_full_of_support G hloc Q ω η hη x y hx hy h.1 h.2,sub_self,norm_zero]
  · have hsub (z : V) : cluster G η z ⊆ cluster G ω z := fun a ha => conn_mono G hη ha
    have hf := finiteClosedContact_le_size G hloc d hd Q (domainBits Q η) ω
      (by rw [coe_domainBits]; exact Set.inter_subset_left.trans hη) x y hx
    have hg : fullLargeContact G x y 0 η ≤ (d:ℝ)*(cluster G ω x).ncard := by
      exact (fullLargeContact_zero_le_size G hloc d hd η x y (hx.subset (hsub x)) (hy.subset (hsub y))).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast Set.ncard_le_ncard (hsub x) hx) (Nat.cast_nonneg _))
    rw [Real.norm_eq_abs,abs_sub_le_iff]
    have hfn := finiteClosedContact_nonneg G Q x y (domainBits Q η)
    have hgn := fullLargeContact_nonneg G x y 0 η
    constructor <;> linarith

end UniformContactError
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section UniformContactExpectation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integrable_contactApproxError [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (Q : Finset E) (d : ℕ) (x y : V) :
    Integrable (contactApproxError G Q d x y) (law p) := by
  apply ((susceptibility_eq_integral G hloc hqt p hp x).1.const_mul (d:ℝ)).mono'
    (measurable_contactApproxError G hloc Q d x y).aestronglyMeasurable
  exact Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (contactApproxError_nonneg G Q d x y ω)]; exact contactApproxError_le G Q d x y ω)

theorem contactApproxError_integral_tendsto_zero [Countable V] [Encodable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (d : ℕ) (x y : V) :
    Tendsto (fun n => ∫ ω, contactApproxError G (vertexExhaustion n) d x y ω ∂law p) atTop (nhds 0) := by
  have ht : ∀ᵐ ω ∂law p, Tendsto (fun n => contactApproxError G (vertexExhaustion n) d x y ω) atTop (nhds 0) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x,subcritical_cluster_finite_ae G p hp y] with ω hx hy
    obtain ⟨nx,hnx⟩ := subset_vertexExhaustion (incidentSupport G hloc hx.toFinset)
    obtain ⟨ny,hny⟩ := subset_vertexExhaustion (incidentSupport G hloc hy.toFinset)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max nx ny)] with n hn
    exact (ite_eq_left ⟨clusterSupportIn_of_incident G hloc _ ω x hx
      (hnx.trans (vertexExhaustion_mono ((le_max_left nx ny).trans hn))),
      clusterSupportIn_of_incident G hloc _ ω y hy
      (hny.trans (vertexExhaustion_mono ((le_max_right nx ny).trans hn)))⟩).symm
  have hh := tendsto_integral_of_dominated_convergence (fun ω : Set E => (d:ℝ)*(cluster G ω x).ncard)
    (fun n => (measurable_contactApproxError G hloc (vertexExhaustion n) d x y).aestronglyMeasurable)
    ((susceptibility_eq_integral G hloc hqt p hp x).1.const_mul (d:ℝ))
    (fun n => Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (contactApproxError_nonneg G _ d x y ω)]; exact contactApproxError_le G _ d x y ω)) ht
  simpa only [integral_zero] using hh

theorem finiteClosedContact_label_integral [Countable E] (G : BondGraph V E)
    (Q : Finset E) (p : unitInterval) (x y : V) :
    (∫ labels, finiteClosedContact G Q x y (domainBits Q (openEdges labels p)) ∂labelLaw) =
      bernoulliPolynomial Q (finiteClosedContact G Q x y) p := by
  rw [←integral_domainBits Q p (finiteClosedContact G Q x y),←map_openEdges p]
  exact (integral_map (measurable_openEdges p).aemeasurable
    (measurable_finite_local Q (fun ω => finiteClosedContact G Q x y (domainBits Q ω)) (fun ω => by rw [domainBits_local])).aestronglyMeasurable).symm

theorem contactApproxError_label_integral [Countable V] [Countable E] (G : BondGraph V E)
    (hloc : LocallyFinite G) (Q : Finset E) (p : unitInterval) (d : ℕ) (x y : V) :
    (∫ labels, contactApproxError G Q d x y (openEdges labels p) ∂labelLaw) =
      ∫ ω, contactApproxError G Q d x y ω ∂law p := by
  rw [←map_openEdges p]
  exact (integral_map (measurable_openEdges p).aemeasurable
    (measurable_contactApproxError G hloc Q d x y).aestronglyMeasurable).symm

theorem contact_expectation_uniform_error [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (Q : Finset E) (b q : unitInterval)
    (hb : b < pc G) (hq : q ≤ b) (x y : V) :
    ‖bernoulliPolynomial Q (finiteClosedContact G Q x y) q -
      ∫ ω, fullLargeContact G x y 0 ω ∂law q‖ ≤
      ∫ ω, contactApproxError G Q d x y ω ∂law b := by
  have hf : Integrable (fun labels => finiteClosedContact G Q x y (domainBits Q (openEdges labels q))) labelLaw := by
    have hi := integrable_finite_local Q q (fun ω => finiteClosedContact G Q x y (domainBits Q ω))
      (fun ω => by rw [domainBits_local])
    rw [←map_openEdges q] at hi
    exact hi.comp_measurable (measurable_openEdges q)
  have hg := (fullContact_label_integrable G hloc q x y).mpr
    (integrable_fullContact_subcritical G hloc hqt q (hq.trans_lt hb) x y)
  have hi : Integrable (fun labels => contactApproxError G Q d x y (openEdges labels b)) labelLaw := by
    have hh := integrable_contactApproxError G hloc hqt b hb Q d x y
    rw [←map_openEdges b] at hh
    exact hh.comp_measurable (measurable_openEdges b)
  rw [←finiteClosedContact_label_integral G Q q x y,←fullContact_label_integral G hloc q x y,
    ←integral_sub hf hg,←contactApproxError_label_integral G hloc Q b d x y]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (hf.sub hg).norm hi
  filter_upwards [label_cluster_finite_ae_subcritical G b hb x,label_cluster_finite_ae_subcritical G b hb y] with labels hx hy
  exact contact_uniform_error_bound G hloc d hd Q _ _ (openEdges_mono labels hq) x y hx hy

end UniformContactExpectation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section PointwiseRussoLimit
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realContactExpectation (G : BondGraph V E) (x y : V) (t : ℝ) : ℝ :=
  ∫ ω, fullLargeContact G x y 0 ω ∂law (Set.projIcc 0 1 zero_le_one t)

@[simp] theorem realContactExpectation_coe (G : BondGraph V E) (x y : V) (p : unitInterval) :
    realContactExpectation G x y (p:ℝ) = ∫ ω, fullLargeContact G x y 0 ω ∂law p := by
  simp only [realContactExpectation,Set.projIcc_val]

noncomputable def realTwoPoint (G : BondGraph V E) (x y : V) (t : ℝ) : ℝ :=
  twoPoint G (Set.projIcc 0 1 zero_le_one t) x y

@[simp] theorem realTwoPoint_coe (G : BondGraph V E) (x y : V) (p : unitInterval) :
    realTwoPoint G x y (p:ℝ) = twoPoint G p x y := by
  simp only [realTwoPoint,Set.projIcc_val]

theorem finite_connection_deriv_eq (G : BondGraph V E) (Q : Finset E)
    (x y : V) (t : ℝ) (ht : t ≠ 1) :
    deriv (finiteEventPolynomial Q {ω | Conn G ω x y}) t =
      bernoulliPolynomial Q (finiteClosedContact G Q x y) t / (1-t) := by
  apply (eq_div_iff (sub_ne_zero.mpr (Ne.symm ht))).mpr
  rw [mul_comm]
  exact finite_connection_russo_contacts G Q x y t

theorem finite_connection_deriv_tendstoUniformlyOn [Countable V] [Encodable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x y : V) :
    TendstoUniformlyOn (fun n => deriv (finiteEventPolynomial (vertexExhaustion n) {ω | Conn G ω x y}))
      (fun t => realContactExpectation G x y t / (1-t)) atTop (Set.Icc 0 (b:ℝ)) := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  have hb1 : (b:ℝ) < 1 := lt_of_lt_of_le hb (pc G).2.2
  have hden : 0 < 1-(b:ℝ) := sub_pos.mpr hb1
  have ht := (contactApproxError_integral_tendsto_zero G hloc hqt b hb d x y).div_const (1-(b:ℝ))
  rw [zero_div] at ht
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [ht.eventually (eventually_lt_nhds hε)] with n hn t ht
  let q : unitInterval := ⟨t,ht.1,ht.2.trans b.2.2⟩
  have hqb : q ≤ b := ht.2
  have hqt1 : t < 1 := ht.2.trans_lt hb1
  have he := contact_expectation_uniform_error G hloc hqt d hd (vertexExhaustion n) b q hb hqb x y
  have hn0 : 0 ≤ ∫ ω, contactApproxError G (vertexExhaustion n) d x y ω ∂law b :=
    integral_nonneg (contactApproxError_nonneg G _ d x y)
  rw [dist_comm,Real.dist_eq,finite_connection_deriv_eq G _ x y t (ne_of_lt hqt1),←sub_div,abs_div,
    abs_of_pos (sub_pos.mpr hqt1)]
  change |bernoulliPolynomial _ _ (q:ℝ) - realContactExpectation G x y (q:ℝ)| / (1-t) < ε
  rw [realContactExpectation_coe]
  apply lt_of_le_of_lt _ hn
  exact div_le_div₀ hn0 (by simpa only [Real.norm_eq_abs] using he) hden (sub_le_sub_left ht.2 1)

theorem finite_connection_polynomial_tendsto_twoPoint [Encodable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) :
    Tendsto (fun n => finiteEventPolynomial (vertexExhaustion n) {ω | Conn G ω x y} p)
      atTop (nhds (twoPoint G p x y)) := by
  have ht := finite_connection_polynomial_tendsto G Set.univ (vertexExhaustion (V := E))
    vertexExhaustion_mono (fun _ => Set.subset_univ _) (fun e _ => by
      obtain ⟨n,hn⟩ := subset_vertexExhaustion ({e}:Finset E)
      exact ⟨n,hn (by simp)⟩) p x y
  simpa only [Set.inter_univ,finiteEventPolynomial,Set.mem_ofPred_eq,twoPoint,Measure.real] using ht

 

theorem hasDerivAt_realTwoPoint_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (x y : V) :
    HasDerivAt (realTwoPoint G x y)
      ((∫ ω, fullLargeContact G x y 0 ω ∂law p)/(1-(p:ℝ))) (p:ℝ) := by
  let : Encodable E := Encodable.ofCountable E
  obtain ⟨b,hpb,hb⟩ := exists_between hp
  have hu := (finite_connection_deriv_tendstoUniformlyOn G hloc hqt b hb x y).mono
    (show Set.Ioo 0 (b:ℝ) ⊆ Set.Icc 0 (b:ℝ) from Set.Ioo_subset_Icc_self)
  have hh := hasDerivAt_of_tendstoUniformlyOn (f := fun n => finiteEventPolynomial (vertexExhaustion n) {ω | Conn G ω x y})
    (g := realTwoPoint G x y) (g' := fun t => realContactExpectation G x y t/(1-t)) isOpen_Ioo hu
    (Eventually.of_forall (fun n t _ => by
      change HasDerivAt (bernoulliPolynomial (vertexExhaustion n) (fun (ω : Finset E) => if Conn G (ω:Set E) x y then (1:ℝ) else 0)) _ t
      exact (hasDerivAt_bernoulliPolynomial (vertexExhaustion n)
        (fun (ω : Finset E) => if Conn G (ω:Set E) x y then (1:ℝ) else 0) t).differentiableAt.hasDerivAt))
    (fun t ht => by
      let q : unitInterval := ⟨t,ht.1.le,ht.2.le.trans b.2.2⟩
      simpa only [←realTwoPoint_coe G x y q] using finite_connection_polynomial_tendsto_twoPoint G q x y)
    (show (p:ℝ) ∈ Set.Ioo 0 (b:ℝ) from ⟨hp0,hpb⟩)
  simpa only [realContactExpectation_coe] using hh

end PointwiseRussoLimit
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section RussoDiagram
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def russoDiagram (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, indexedEdgeKernel G a b *
    (law p {ω | Conn G ω x a} * law p {ω | Conn G ω y b})

theorem conn_probability_symm (G : BondGraph V E) (p : unitInterval) (x y : V) :
    law p {ω | Conn G ω x y} = law p {ω | Conn G ω y x} := by
  congr 1
  ext ω
  exact ⟨conn_symm G ω,conn_symm G ω⟩

theorem conn_probability_mono [Countable V] [Countable E] (G : BondGraph V E)
    (p q : unitInterval) (hpq : p ≤ q) (x y : V) :
    law p {ω | Conn G ω x y} ≤ law q {ω | Conn G ω x y} := by
  rw [←ENNReal.ofReal_toReal (measure_ne_top (law p) _),←ENNReal.ofReal_toReal (measure_ne_top (law q) _)]
  exact ENNReal.ofReal_le_ofReal (twoPoint_mono G x y hpq)

theorem fullContact_lintegral_eq_kernel [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval) (x y : V)
    (hx : ∀ᵐ ω ∂law p, (cluster G ω x).Finite) :
    (∫⁻ ω, ENNReal.ofReal (fullLargeContact G x y 0 ω) ∂law p) =
      ∫⁻ ω, if ¬Conn G ω x y then clusterPairKernel G ω (indexedEdgeKernel G) x y else 0 ∂law p := by
  apply lintegral_congr_ae
  filter_upwards [hx] with ω hω
  by_cases hxy : Conn G ω x y
  · simp only [fullLargeContact,hxy,not_true_eq_false,false_and,ite_false,ENNReal.ofReal_zero]
  · rw [ite_eq_left hxy,clusterPairKernel_edge G hloc ω x y hxy hω]
    simp only [fullLargeContact,hxy,Nat.zero_le,not_false_eq_true,and_self,ite_true,ENNReal.ofReal_natCast]

theorem fullContact_expectation_le_diagram [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    ENNReal.ofReal (∫ ω, fullLargeContact G x y 0 ω ∂law p) ≤ russoDiagram G p x y := by
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_fullContact_subcritical G hloc hqt p hp x y)
    (Eventually.of_forall (fullLargeContact_nonneg G x y 0))]
  rw [fullContact_lintegral_eq_kernel G hloc p x y (subcritical_cluster_finite_ae G p hp x)]
  exact clusterPairKernel_distinct_bound G p (indexedEdgeKernel G) x y

theorem russoDiagram_mono [Countable V] [Countable E] (G : BondGraph V E)
    (p q : unitInterval) (hpq : p ≤ q) (x y : V) : russoDiagram G p x y ≤ russoDiagram G q x y := by
  exact ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b =>
    mul_le_mul_right (mul_le_mul' (conn_probability_mono G p q hpq x a)
      (conn_probability_mono G p q hpq y b)) _))

theorem russoDiagram_symm (G : BondGraph V E) (p : unitInterval) (x y : V) :
    russoDiagram G p x y = russoDiagram G p y x := by
  unfold russoDiagram
  rw [ENNReal.tsum_comm]
  apply tsum_congr; intro b
  apply tsum_congr; intro a
  rw [indexedEdgeKernel_symm G a b,mul_comm (law p {ω | Conn G ω x a})]

theorem russoDiagram_row_bound (G : BondGraph V E) (hloc : LocallyFinite G)
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (p : unitInterval) (C : ℝ≥0∞)
    (hC : ∀ x, ∑' y, law p {ω | Conn G ω x y} ≤ C) (x : V) :
    (∑' y, russoDiagram G p x y) ≤ (d:ℝ≥0∞)*C^2 := by
  unfold russoDiagram
  rw [ENNReal.tsum_comm]
  calc
    _ = ∑' a, ∑' b, indexedEdgeKernel G a b * law p {ω | Conn G ω x a} *
        ∑' y, law p {ω | Conn G ω b y} := by
      apply tsum_congr; intro a
      rw [ENNReal.tsum_comm]
      apply tsum_congr; intro b
      simp_rw [←mul_assoc,conn_probability_symm G p _ b]
      rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' a, ∑' b, indexedEdgeKernel G a b * law p {ω | Conn G ω x a} * C := by
      exact ENNReal.tsum_le_tsum (fun a => ENNReal.tsum_le_tsum (fun b => mul_le_mul_right (hC b) _))
    _ = ∑' a, (degree G a:ℝ≥0∞) * law p {ω | Conn G ω x a} * C := by
      apply tsum_congr; intro a
      rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_right,indexedEdgeKernel_row G hloc a]
    _ ≤ ∑' a, (d:ℝ≥0∞) * law p {ω | Conn G ω x a} * C := by
      exact ENNReal.tsum_le_tsum (fun a => mul_le_mul_left (mul_le_mul_left (show (degree G a:ℝ≥0∞) ≤ (d:ℝ≥0∞) by exact_mod_cast hd a) _) _)
    _ = (d:ℝ≥0∞)*(∑' a, law p {ω | Conn G ω x a})*C := by
      rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]
    _ ≤ (d:ℝ≥0∞)*C^2 := by
      rw [pow_two,←mul_assoc]
      exact mul_le_mul_left (mul_le_mul_right (hC x) _) _

end RussoDiagram
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section RussoMajorant
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def russoSlope (G : BondGraph V E) (x y : V) (t : ℝ) : ℝ :=
  realContactExpectation G x y t / (1-t)

noncomputable def russoMajorant (G : BondGraph V E) (b : unitInterval) (x y : V) : ℝ :=
  (russoDiagram G b x y).toReal / (1-(b:ℝ))

theorem russoDiagram_row_ne_top [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x : V) : (∑' y, russoDiagram G b x y) ≠ ⊤ := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  obtain ⟨C,_,hC⟩ := subcritical_ennreal_row_bound G hloc hqt b hb
  exact ne_top_of_le_ne_top (by finiteness) (russoDiagram_row_bound G hloc d hd b _ hC x)

theorem russoDiagram_ne_top [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x y : V) : russoDiagram G b x y ≠ ⊤ :=
  ne_top_of_le_ne_top (russoDiagram_row_ne_top G hloc hqt b hb x) (ENNReal.le_tsum y)

theorem summable_russoMajorant [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x : V) : Summable (russoMajorant G b x) :=
  (ENNReal.summable_toReal (russoDiagram_row_ne_top G hloc hqt b hb x)).div_const _

theorem russoSlope_nonneg (G : BondGraph V E) (x y : V) (t : ℝ) (ht : t ≤ 1) :
    0 ≤ russoSlope G x y t := by
  exact div_nonneg (integral_nonneg (fullLargeContact_nonneg G x y 0)) (sub_nonneg.mpr ht)

theorem russoMajorant_nonneg (G : BondGraph V E) (b : unitInterval) (x y : V) :
    0 ≤ russoMajorant G b x y := div_nonneg ENNReal.toReal_nonneg (sub_nonneg.mpr b.2.2)

theorem russoSlope_le_majorant [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b p : unitInterval) (hb : b < pc G) (hp : p ≤ b) (x y : V) :
    russoSlope G x y (p:ℝ) ≤ russoMajorant G b x y := by
  have hp' := hp.trans_lt hb
  have he := (fullContact_expectation_le_diagram G hloc hqt p hp' x y).trans (russoDiagram_mono G p b hp x y)
  have hn : 0 ≤ ∫ ω, fullLargeContact G x y 0 ω ∂law p := integral_nonneg (fullLargeContact_nonneg G x y 0)
  have hc : (∫ ω, fullLargeContact G x y 0 ω ∂law p) ≤ (russoDiagram G b x y).toReal := by
    simpa only [ENNReal.toReal_ofReal hn] using ENNReal.toReal_mono (russoDiagram_ne_top G hloc hqt b hb x y) he
  simp only [russoSlope,realContactExpectation_coe,russoMajorant]
  exact div_le_div₀ ENNReal.toReal_nonneg hc (sub_pos.mpr ((show (b:ℝ) < (pc G:ℝ) from hb).trans_le (pc G).2.2)) (sub_le_sub_left (show (p:ℝ) ≤ (b:ℝ) from hp) 1)

theorem hasDerivAt_realTwoPoint_slope [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 (pc G:ℝ)) (x y : V) :
    HasDerivAt (realTwoPoint G x y) (russoSlope G x y t) t := by
  let p : unitInterval := ⟨t, ht.1.le,ht.2.le.trans (pc G).2.2⟩
  change HasDerivAt (realTwoPoint G x y) (russoSlope G x y (p:ℝ)) (p:ℝ)
  simpa only [russoSlope,realContactExpectation_coe] using hasDerivAt_realTwoPoint_subcritical G hloc hqt p ht.1 ht.2 x y

end RussoMajorant
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped ENNReal
section RussoRows
attribute [local instance] Classical.propDecidable Classical.decEq

theorem russoMajorant_symm (G : BondGraph V E) (b : unitInterval) (x y : V) :
    russoMajorant G b x y = russoMajorant G b y x := by
  rw [russoMajorant,russoDiagram_symm,russoMajorant]

theorem russoMajorant_uniform_row_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x, ∑' y, russoMajorant G b x y ≤ R := by
  obtain ⟨d,_,hd⟩ := exists_degree_bound G hqt
  obtain ⟨C,_,hC⟩ := subcritical_ennreal_row_bound G hloc hqt b hb
  let R : ℝ≥0∞ := (d:ℝ≥0∞)*(ENNReal.ofReal C)^2
  have hR : R ≠ ⊤ := by dsimp [R]; finiteness
  have hden : 0 < 1-(b:ℝ) := sub_pos.mpr ((show (b:ℝ) < (pc G:ℝ) from hb).trans_le (pc G).2.2)
  refine ⟨R.toReal/(1-(b:ℝ)),div_nonneg ENNReal.toReal_nonneg hden.le,fun x => ?_⟩
  simp only [russoMajorant,tsum_div_const]
  rw [←ENNReal.tsum_toReal_eq (russoDiagram_ne_top G hloc hqt b hb x)]
  exact div_le_div_of_nonneg_right (ENNReal.toReal_mono hR (russoDiagram_row_bound G hloc d hd b _ hC x)) hden.le

 

theorem summable_kernel_pair (A B : V → V → ℝ)
    (hA : ∀ x y, 0 ≤ A x y) (hB : ∀ x y, 0 ≤ B x y)
    (hsA : ∀ x, Summable (A x)) (hsB : ∀ x, Summable (B x))
    (C : ℝ) (hC : ∀ x, ∑' y, B x y ≤ C) (x : V) :
    Summable (fun ab : V×V => A x ab.1 * B ab.1 ab.2) := by
  apply (summable_prod_of_nonneg (f := fun ab : V×V => A x ab.1 * B ab.1 ab.2)
    (fun ab => mul_nonneg (hA x ab.1) (hB ab.1 ab.2))).mpr
  refine ⟨fun a => (hsB a).mul_left (A x a),?_⟩
  simp only [tsum_mul_left]
  exact Summable.of_nonneg_of_le (fun a => mul_nonneg (hA x a) (tsum_nonneg (hB a)))
    (fun a => mul_le_mul_of_nonneg_left (hC a) (hA x a)) ((hsA x).mul_right C)

theorem summable_twoPoint_pair [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (fun ab : V×V => twoPoint G p x ab.1 * twoPoint G p ab.1 ab.2) := by
  obtain ⟨C,_,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  have hs := summable_twoPoint_subcritical G hloc hqt p hp
  exact summable_kernel_pair (twoPoint G p) (twoPoint G p) (twoPoint_nonneg G p)
    (twoPoint_nonneg G p) hs hs C (fun x => (hs x).tsum_le_of_sum_le (hrow x)) x

theorem summable_russoMajorant_pair [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (fun ab : V×V => russoMajorant G p x ab.1 * twoPoint G p ab.1 ab.2) ∧
    Summable (fun ab : V×V => twoPoint G p x ab.1 * russoMajorant G p ab.1 ab.2) := by
  obtain ⟨C,_,hrow⟩ := subcritical_row_bound G hloc hqt p hp
  have hs := summable_twoPoint_subcritical G hloc hqt p hp
  have hr := summable_russoMajorant G hloc hqt p hp
  obtain ⟨R,_,hR⟩ := russoMajorant_uniform_row_bound G hloc hqt p hp
  exact ⟨summable_kernel_pair _ _ (russoMajorant_nonneg G p) (twoPoint_nonneg G p) hr hs C
    (fun x => (hs x).tsum_le_of_sum_le (hrow x)) x,
    summable_kernel_pair _ _ (twoPoint_nonneg G p) (russoMajorant_nonneg G p) hs hr R hR x⟩

end RussoRows
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section RealTriangle
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realTriangleTerm (G : BondGraph V E) (x : V) (ab : V×V) (t : ℝ) : ℝ :=
  realTwoPoint G x ab.1 t * realTwoPoint G ab.1 ab.2 t * realTwoPoint G ab.2 x t

noncomputable def realTriangleSlope (G : BondGraph V E) (x : V) (ab : V×V) (t : ℝ) : ℝ :=
  russoSlope G x ab.1 t * realTwoPoint G ab.1 ab.2 t * realTwoPoint G ab.2 x t +
  realTwoPoint G x ab.1 t * russoSlope G ab.1 ab.2 t * realTwoPoint G ab.2 x t +
  realTwoPoint G x ab.1 t * realTwoPoint G ab.1 ab.2 t * russoSlope G ab.2 x t

noncomputable def triangleMajorant (G : BondGraph V E) (b : unitInterval) (x : V) (ab : V×V) : ℝ :=
  russoMajorant G b x ab.1 * twoPoint G b ab.1 ab.2 +
  twoPoint G b x ab.1 * russoMajorant G b ab.1 ab.2 +
  russoMajorant G b x ab.2 * twoPoint G b ab.2 ab.1

theorem summable_triangleMajorant [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b : unitInterval) (hb : b < pc G) (x : V) : Summable (triangleMajorant G b x) := by
  obtain ⟨h₁,h₂⟩ := summable_russoMajorant_pair G hloc hqt b hb x
  have h₃ : Summable (fun ab : V×V => russoMajorant G b x ab.2 * twoPoint G b ab.2 ab.1) := by
    exact h₁.comp_injective (i := fun ab : V×V => (ab.2,ab.1)) (Equiv.prodComm V V).injective
  exact (h₁.add h₂).add h₃

theorem hasDerivAt_realTriangleTerm [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (t : ℝ) (ht : t ∈ Set.Ioo 0 (pc G:ℝ)) (x : V) (ab : V×V) :
    HasDerivAt (realTriangleTerm G x ab) (realTriangleSlope G x ab t) t := by
  have hs := hasDerivAt_realTwoPoint_slope G hloc hqt t ht
  convert! ((hs x ab.1).mul (hs ab.1 ab.2)).mul (hs ab.2 x) using 1
  simp only [realTriangleSlope,Pi.mul_apply]
  ring

theorem realTriangleSlope_nonneg (G : BondGraph V E) (x : V) (ab : V×V) (t : ℝ) (ht : t ≤ 1) :
    0 ≤ realTriangleSlope G x ab t := by
  have hT (a b : V) : 0 ≤ realTwoPoint G a b t := twoPoint_nonneg G _ a b
  dsimp [realTriangleSlope]
  exact add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (russoSlope_nonneg G _ _ t ht) (hT _ _)) (hT _ _))
    (mul_nonneg (mul_nonneg (hT _ _) (russoSlope_nonneg G _ _ t ht)) (hT _ _)))
    (mul_nonneg (mul_nonneg (hT _ _) (hT _ _)) (russoSlope_nonneg G _ _ t ht))

theorem realTriangleSlope_le_majorant [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (b p : unitInterval) (hb : b < pc G) (hp : p ≤ b) (x : V) (ab : V×V) :
    realTriangleSlope G x ab (p:ℝ) ≤ triangleMajorant G b x ab := by
  have hs := russoSlope_le_majorant G hloc hqt b p hb hp
  have hn := russoSlope_nonneg (G := G)
  have hm (a z : V) : twoPoint G p a z ≤ twoPoint G b a z := twoPoint_mono G a z hp
  simp only [realTriangleSlope,realTwoPoint_coe,triangleMajorant]
  apply add_le_add
  · apply add_le_add
    · calc
        _ ≤ russoMajorant G b x ab.1 * twoPoint G b ab.1 ab.2 * 1 :=
          mul_le_mul (mul_le_mul (hs _ _) (hm _ _) (twoPoint_nonneg G p _ _) (russoMajorant_nonneg G b _ _))
            (twoPoint_le_one G p _ _) (twoPoint_nonneg G p _ _) (mul_nonneg (russoMajorant_nonneg G b _ _) (twoPoint_nonneg G b _ _))
        _ = _ := mul_one _
    · calc
        _ ≤ twoPoint G b x ab.1 * russoMajorant G b ab.1 ab.2 * 1 :=
          mul_le_mul (mul_le_mul (hm _ _) (hs _ _) (hn _ _ _ p.2.2) (twoPoint_nonneg G b _ _))
            (twoPoint_le_one G p _ _) (twoPoint_nonneg G p _ _) (mul_nonneg (twoPoint_nonneg G b _ _) (russoMajorant_nonneg G b _ _))
        _ = _ := mul_one _
  · calc
      _ ≤ 1 * twoPoint G b ab.1 ab.2 * russoMajorant G b ab.2 x :=
        mul_le_mul (mul_le_mul (twoPoint_le_one G p _ _) (hm _ _) (twoPoint_nonneg G p _ _) zero_le_one)
          (hs _ _) (hn _ _ _ p.2.2) (mul_nonneg zero_le_one (twoPoint_nonneg G b _ _))
      _ = _ := by rw [one_mul,twoPoint_symm G b,russoMajorant_symm G b]; ring

end RealTriangle
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
section TriangleDerivative
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def realTriangle (G : BondGraph V E) (x : V) (t : ℝ) : ℝ :=
  ∑' ab, realTriangleTerm G x ab t

noncomputable def rootTriangle (G : BondGraph V E) {ι : Type*} [Fintype ι]
    (root : ι → V) (weight : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i, weight i * realTriangle G (root i) t

theorem summable_realTriangleTerm [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (fun ab => realTriangleTerm G x ab (p:ℝ)) := by
  simp only [realTriangleTerm,realTwoPoint_coe]
  apply (summable_twoPoint_pair G hloc hqt p hp x).of_nonneg_of_le
  · intro ab
    exact mul_nonneg (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)) (twoPoint_nonneg G p _ _)
  · intro ab
    exact mul_le_of_le_one_right (mul_nonneg (twoPoint_nonneg G p _ _) (twoPoint_nonneg G p _ _)) (twoPoint_le_one G p _ _)

theorem summable_realTriangleSlope [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    Summable (fun ab => realTriangleSlope G x ab (p:ℝ)) := by
  exact (summable_triangleMajorant G hloc hqt p hp x).of_nonneg_of_le
    (fun ab => realTriangleSlope_nonneg G x ab p p.2.2)
    (fun ab => realTriangleSlope_le_majorant G hloc hqt p p hp le_rfl x ab)

 

theorem hasDerivAt_realTriangle_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G) (x : V) :
    HasDerivAt (realTriangle G x) (∑' ab, realTriangleSlope G x ab (p:ℝ)) (p:ℝ) := by
  obtain ⟨b,hpb,hb⟩ := exists_between hp
  apply hasDerivAt_tsum_of_isPreconnected (summable_triangleMajorant G hloc hqt b hb x)
    isOpen_Ioo isPreconnected_Ioo
    (fun ab t ht => hasDerivAt_realTriangleTerm G hloc hqt t ⟨ht.1,lt_trans ht.2 hb⟩ x ab)
    (fun ab t ht => ?_) (show (p:ℝ) ∈ Set.Ioo 0 (b:ℝ) from ⟨hp0,hpb⟩)
    (summable_realTriangleTerm G hloc hqt p hp x) ⟨hp0,hpb⟩
  let q : unitInterval := ⟨t,ht.1.le,ht.2.le.trans b.2.2⟩
  have hq : q ≤ b := ht.2.le
  rw [Real.norm_eq_abs,abs_of_nonneg (realTriangleSlope_nonneg G x ab t q.2.2)]
  exact realTriangleSlope_le_majorant G hloc hqt b q hb hq x ab

theorem hasDerivAt_rootTriangle_subcritical [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (p : unitInterval) (hp0 : 0 < (p:ℝ)) (hp : p < pc G) :
    HasDerivAt (rootTriangle G root weight)
      (∑ i, weight i * ∑' ab, realTriangleSlope G (root i) ab (p:ℝ)) (p:ℝ) := by
  exact HasDerivAt.fun_sum (fun i _ => (hasDerivAt_realTriangle_subcritical G hloc hqt p hp0 hp (root i)).const_mul (weight i))

end TriangleDerivative
end Percolation

end OAI
