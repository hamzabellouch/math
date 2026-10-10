import Mathlib
import OAI.Probability.UnimodularPercolation.Clusters.KernelMoments

namespace OAI

/-! Exterior Moments for bond percolation. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section BinDiagonalLoss
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def binDiagonalKernel (G : BondGraph V E) (p : unitInterval)
    (o : V) (n : ℕ) (K : V → V → ℝ) (x y : V) : ℝ :=
  ∫ ω, binDiagonalMass G o n K ω x y ∂law p

theorem binDiagonalKernel_covariant (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (K : V → V → ℝ)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b)
    (hK : ∀ x y, K (a x) (a y) = K x y) (x y : V) :
    binDiagonalKernel G p o n K (a x) (a y) = binDiagonalKernel G p o n K x y := by
  have hm : Measurable (fun ω => binDiagonalMass G o n K ω x y) :=
    measurable_finite_local _ _ (fun ω => binDiagonalMass_local G hloc o n K ω x y)
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [binDiagonalKernel,binDiagonalMass_covariant G o n K hab hK] using h.symm

theorem binDiagonalKernel_row_integral (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (K : V → V → ℝ) (x : V) :
    (∑' y, binDiagonalKernel G p o n K x y) =
      ∫ ω, binSizeMass G n ω x ^ 2 * ∑ z ∈ binOrbitClass G o n ω x, K x z ∂law p := by
  rw [←show (∫ ω, ∑' y, binDiagonalMass G o n K ω x y ∂law p) =
      ∑' y, binDiagonalKernel G p o n K x y from
    integral_tsum_of_finite_support (law p) (finite_reachBall hloc x (2*n)).toFinset _
      (fun y => binDiagonalMass_integrable G hloc p o n K x y)
      (fun ω y hy => binDiagonalMass_outside G o n K ω x y (by simpa only [Set.Finite.mem_toFinset] using hy))]
  simp only [binDiagonalMass_row]

theorem binDiagonalKernel_column_integral (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (o : V) (n : ℕ) (K : V → V → ℝ) (x : V) :
    (∑' y, binDiagonalKernel G p o n K y x) =
      ∫ ω, ∑' y, binDiagonalMass G o n K ω y x ∂law p := by
  symm
  exact integral_tsum_of_finite_support (law p) (finite_reachBall hloc x (2*n)).toFinset _
    (fun y => binDiagonalMass_integrable G hloc p o n K y x)
    (fun ω y hy => binDiagonalMass_outside_column G o n K ω y x (by simpa only [Set.Finite.mem_toFinset] using hy))

theorem integral_binDiagonalLoss (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (p : unitInterval) (n : ℕ) (K : V → V → ℝ)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y) :
    (∫ ω, binSizeMass G n ω (root i₀)^2 *
      ∑ z ∈ binOrbitClass G (root i₀) n ω (root i₀), K (root i₀) z ∂law p) =
    ∫ ω, binSizeMass G n ω (root i₀)^2 / (binOrbitClass G (root i₀) n ω (root i₀)).card *
      ∑ y ∈ binOrbitClass G (root i₀) n ω (root i₀),
        ∑ z ∈ binOrbitClass G (root i₀) n ω (root i₀), K y z ∂law p := by
  have hr (x : V) : Summable (binDiagonalKernel G p (root i₀) n K x) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc x (2*n)).toFinset)
    intro y hy
    simp only [binDiagonalKernel,binDiagonalMass_outside G (root i₀) n K _ x y
      (by simpa only [Set.Finite.mem_toFinset] using hy),integral_zero]
  have hc (y : V) : Summable (fun x => binDiagonalKernel G p (root i₀) n K x y) := by
    apply summable_of_ne_finset_zero (s := (finite_reachBall hloc y (2*n)).toFinset)
    intro x hx
    simp only [binDiagonalKernel,binDiagonalMass_outside_column G (root i₀) n K _ x y
      (by simpa only [Set.Finite.mem_toFinset] using hx),integral_zero]
  have ht := orbit_kernel_column_eq_row G root weight Γ htr hΓ hw i₀ hw₀
    (binDiagonalKernel G p (root i₀) n K)
    (fun a b hab x y => binDiagonalKernel_covariant G hloc p (root i₀) n K hab (hcov a b hab) x y)
    (fun x y hx => by simp only [binDiagonalKernel,binDiagonalMass_row_zero G _ n K _ x y hx,integral_zero])
    (fun x y hy => by simp only [binDiagonalKernel,binDiagonalMass_column_zero G _ n K _ x y hy,integral_zero])
    hr hc (root i₀) ⟨Equiv.refl _,Equiv.refl _,fun _ => by simp,rfl⟩
  rw [binDiagonalKernel_row_integral G hloc,binDiagonalKernel_column_integral G hloc] at ht
  simpa only [binDiagonalMass_column] using ht.symm

 

theorem integral_binDiagonalLoss_le (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (p : unitInterval) (n : ℕ) (K : V → V → ℝ)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ)) :
    (∫ ω, binSizeMass G n ω (root i₀)^2 *
      ∑ z ∈ binOrbitClass G (root i₀) n ω (root i₀), K (root i₀) z ∂law p) ≤
      ‖A‖ * ∫ ω, binSizeMass G n ω (root i₀)^2 ∂law p := by
  rw [integral_binDiagonalLoss G hloc root weight Γ htr hΓ hw i₀ hw₀ p n K hcov]
  have hi : Integrable (fun ω => ∑' y, binDiagonalMass G (root i₀) n K ω y (root i₀)) (law p) := by
    have he (ω : Set E) : (∑' y, binDiagonalMass G (root i₀) n K ω y (root i₀)) =
        ∑ y ∈ (finite_reachBall hloc (root i₀) (2*n)).toFinset, binDiagonalMass G (root i₀) n K ω y (root i₀) := by
      apply tsum_eq_sum
      intro y hy
      exact binDiagonalMass_outside_column G (root i₀) n K ω y (root i₀)
        (by simpa only [Set.Finite.mem_toFinset] using hy)
    simp only [he]
    exact integrable_finsetSum _ (fun y _ => binDiagonalMass_integrable G hloc p (root i₀) n K y (root i₀))
  have hs : Integrable (fun ω => binSizeMass G n ω (root i₀)^2) (law p) :=
    integrable_finite_local _ p _ (fun ω => congrArg (fun t : ℝ => t^2) (binSizeMass_local G hloc n ω (root i₀)))
  rw [←integral_const_mul]
  exact integral_mono (by simpa only [binDiagonalMass_column] using hi) (hs.const_mul ‖A‖)
    (fun ω => by simpa only [binDiagonalMass_column] using binDiagonalMass_column_le G (root i₀) n K A hA ω (root i₀))

end BinDiagonalLoss
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section DyadicDiagonalStrata
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def fullOrbitClass (G : BondGraph V E) (o : V) (ω : Set E) (x : V) : Finset V :=
  if h : (cluster G ω x).Finite then h.toFinset.filter (fun y => y ∈ vertexOrbit G o) else ∅

noncomputable def diagonalLossMass (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (ω : Set E) (x : V) : ℝ :=
  ((cluster G ω x).ncard:ℝ)^2 * ∑ z ∈ fullOrbitClass G o ω x, K x z

theorem binSizeMass_zero (G : BondGraph V E) (n : ℕ) (ω : Set E) (x : V)
    (hw : ¬ ClusterWindow G x n (2*n) ω) : binSizeMass G n ω x = 0 := by
  simp only [binSizeMass,binMass_zero_of_not_window G n ω x _ hw,tsum_zero]

theorem binOrbitClass_eq_full (G : BondGraph V E) (o : V) (n : ℕ) (ω : Set E) (x : V)
    (hx : x ∈ vertexOrbit G o) (hw : ClusterWindow G x n (2*n) ω) :
    binOrbitClass G o n ω x = fullOrbitClass G o ω x := by
  simp only [binOrbitClass,ite_eq_left hx,binClusterSlice,dite_eq_left hw,fullOrbitClass,dite_eq_left hw.1]

theorem dyadic_window_iff (G : BondGraph V E) (ω : Set E) (x : V) (j : ℕ)
    (hz : (cluster G ω x).ncard ≠ 0) :
    ClusterWindow G x (2^j) (2*(2^j)) ω ↔ Nat.log 2 (cluster G ω x).ncard = j := by
  constructor
  · intro h
    apply Nat.log_eq_of_pow_le_of_lt_pow h.2.1
    simpa only [pow_succ,Nat.mul_comm] using h.2.2
  · intro h
    refine ⟨Set.finite_of_ncard_ne_zero hz,?_,?_⟩
    · rw [←h]
      exact Nat.pow_log_le_self 2 hz
    · rw [←h,show 2*2^(Nat.log 2 (cluster G ω x).ncard) = 2^(Nat.log 2 (cluster G ω x).ncard+1) by simp only [pow_succ,Nat.mul_comm]]
      exact Nat.lt_pow_succ_log_self (by norm_num) _

theorem dyadic_binSizeMass_sq (G : BondGraph V E) (ω : Set E) (x : V) (j : ℕ) :
    binSizeMass G (2^j) ω x ^ 2 =
      if Nat.log 2 (cluster G ω x).ncard = j then ((cluster G ω x).ncard:ℝ)^2 else 0 := by
  by_cases hz : (cluster G ω x).ncard = 0
  · have hw : ¬ClusterWindow G x (2^j) (2*(2^j)) ω := by
      intro h
      have hp : 0 < 2^j := pow_pos (by omega) _
      have hl := h.2.1
      omega
    simp only [binSizeMass_zero G (2^j) ω x hw,hz,Nat.cast_zero,zero_pow (by omega : 2 ≠ 0),ite_self]
  · by_cases hw : ClusterWindow G x (2^j) (2*(2^j)) ω
    · rw [binSizeMass_eq G (2^j) ω x hw,ite_eq_left ((dyadic_window_iff G ω x j hz).mp hw)]
    · rw [binSizeMass_zero G (2^j) ω x hw,ite_eq_right (fun h => hw ((dyadic_window_iff G ω x j hz).mpr h))]
      norm_num

theorem dyadic_binDiagonalMass (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (ω : Set E) (x : V) (hx : x ∈ vertexOrbit G o) (j : ℕ) :
    binSizeMass G (2^j) ω x ^ 2 * ∑ z ∈ binOrbitClass G o (2^j) ω x, K x z =
      if Nat.log 2 (cluster G ω x).ncard = j then diagonalLossMass G o K ω x else 0 := by
  by_cases hw : ClusterWindow G x (2^j) (2*(2^j)) ω
  · have hz : (cluster G ω x).ncard ≠ 0 := by
      have hp : 0 < 2^j := pow_pos (by omega) _
      have hl := hw.2.1
      omega
    rw [ite_eq_left ((dyadic_window_iff G ω x j hz).mp hw),binOrbitClass_eq_full G o (2^j) ω x hx hw,
      binSizeMass_eq G (2^j) ω x hw]
    rfl
  · rw [binSizeMass_zero G (2^j) ω x hw]
    simp only [zero_pow (by omega : 2 ≠ 0),zero_mul]
    by_cases hz : (cluster G ω x).ncard = 0
    · simp only [diagonalLossMass,hz,Nat.cast_zero,zero_pow (by omega : 2 ≠ 0),zero_mul,ite_self]
    · rw [ite_eq_right (fun h => hw ((dyadic_window_iff G ω x j hz).mpr h))]

theorem diagonalLossMass_nonneg (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (hK : ∀ x y, 0 ≤ K x y) (ω : Set E) (x : V) : 0 ≤ diagonalLossMass G o K ω x :=
  mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun z _ => hK x z))

theorem diagonalLossMass_le (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (L : ℝ) (hrow : ∀ x (S : Finset V), (∑ z ∈ S, K x z) ≤ L) (ω : Set E) (x : V) :
    diagonalLossMass G o K ω x ≤ L*((cluster G ω x).ncard:ℝ)^2 := by
  exact (mul_le_mul_of_nonneg_left (hrow x _) (sq_nonneg _)).trans_eq (mul_comm _ _)

end DyadicDiagonalStrata
end Percolation

 
namespace Percolation
open MeasureTheory Filter
open scoped Topology
section DiscreteStratumIntegral
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem integral_le_of_discrete_strata {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (J : Ω → ℕ) (f g : Ω → ℝ) (C L : ℝ)
    (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hfg : ∀ ω, f ω ≤ L*g ω) (hgi : Integrable g μ)
    (hfi : ∀ j, Integrable (fun ω => if J ω = j then f ω else 0) μ)
    (hgi' : ∀ j, Integrable (fun ω => if J ω = j then g ω else 0) μ)
    (h : ∀ j, (∫ ω, (if J ω = j then f ω else 0) ∂μ) ≤
      C*(∫ ω, (if J ω = j then g ω else 0) ∂μ)) :
    (∫ ω, f ω ∂μ) ≤ C*(∫ ω, g ω ∂μ) := by
  let F : ℕ → Ω → ℝ := fun N ω => ∑ j ∈ Finset.range N, if J ω = j then f ω else 0
  let H : ℕ → Ω → ℝ := fun N ω => ∑ j ∈ Finset.range N, if J ω = j then g ω else 0
  have he (q : Ω → ℝ) (N : ℕ) (ω : Ω) :
      (∑ j ∈ Finset.range N, if J ω = j then q ω else 0) = if J ω < N then q ω else 0 := by
    simp only [Finset.sum_ite_eq,Finset.mem_range]
  have hFi (N : ℕ) : Integrable (F N) μ := integrable_finsetSum _ (fun j _ => hfi j)
  have hHi (N : ℕ) : Integrable (H N) μ := integrable_finsetSum _ (fun j _ => hgi' j)
  have hFbody (N : ℕ) (ω : Ω) : ‖F N ω‖ ≤ L*g ω := by
    dsimp [F]
    rw [he]
    split_ifs
    · simpa only [Real.norm_eq_abs,abs_of_nonneg (hf0 ω)] using hfg ω
    · simpa only [norm_zero,abs_zero] using (hf0 ω).trans (hfg ω)
  have hHbody (N : ℕ) (ω : Ω) : ‖H N ω‖ ≤ g ω := by
    dsimp [H]
    rw [he]
    split_ifs
    · simp only [abs_of_nonneg (hg0 ω),le_refl]
    · simpa only [norm_zero,abs_zero] using hg0 ω
  have ht (q : Ω → ℝ) (ω : Ω) : Tendsto
      (fun N => ∑ j ∈ Finset.range N, if J ω = j then q ω else 0) atTop (𝓝 (q ω)) := by
    have he' : (fun N => ∑ j ∈ Finset.range N, if J ω = j then q ω else 0) =ᶠ[atTop] (fun _ => q ω) := by
      filter_upwards [eventually_ge_atTop (J ω+1)] with N hN
      rw [he,ite_eq_left (by omega)]
    exact tendsto_const_nhds.congr' he'.symm
  have htF := tendsto_integral_of_dominated_convergence (fun ω => L*g ω)
    (fun N => (hFi N).aestronglyMeasurable) (hgi.const_mul L)
    (fun N => Eventually.of_forall (hFbody N)) (Eventually.of_forall (ht f))
  have htH := tendsto_integral_of_dominated_convergence g
    (fun N => (hHi N).aestronglyMeasurable) hgi
    (fun N => Eventually.of_forall (hHbody N)) (Eventually.of_forall (ht g))
  apply le_of_tendsto_of_tendsto htF (tendsto_const_nhds.mul htH)
  exact Eventually.of_forall (fun N => by
    change (∫ ω, F N ω ∂μ) ≤ C*(∫ ω, H N ω ∂μ)
    simp only [F,H,integral_finsetSum _ (fun j _ => hfi j),
      integral_finsetSum _ (fun j _ => hgi' j),Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => h j))

end DiscreteStratumIntegral
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DiagonalLoss
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem integral_diagonalLoss_le (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (p : unitInterval) (K : V → V → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y)
    (L : ℝ) (hrow : ∀ x (S : Finset V), (∑ z ∈ S, K x z) ≤ L)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ))
    (hs : Integrable (fun ω => ((cluster G ω (root i₀)).ncard:ℝ)^2) (law p)) :
    (∫ ω, diagonalLossMass G (root i₀) K ω (root i₀) ∂law p) ≤
      ‖A‖*(∫ ω, ((cluster G ω (root i₀)).ncard:ℝ)^2 ∂law p) := by
  have hx : root i₀ ∈ vertexOrbit G (root i₀) := ⟨Equiv.refl _,Equiv.refl _,fun _ => by simp,rfl⟩
  have hs' (j : ℕ) : Integrable (fun ω => binSizeMass G (2^j) ω (root i₀)^2) (law p) :=
    integrable_finite_local _ p _ (fun ω => congrArg (fun t : ℝ => t^2)
      (binSizeMass_local G hloc (2^j) ω (root i₀)))
  have hf' (j : ℕ) : Integrable (fun ω => binSizeMass G (2^j) ω (root i₀)^2 *
      ∑ z ∈ binOrbitClass G (root i₀) (2^j) ω (root i₀), K (root i₀) z) (law p) := by
    apply integrable_finite_local _ p _
    intro ω
    rw [binOrbitClass_local G hloc (root i₀) (2^j) ω (root i₀),binSizeMass_local G hloc (2^j) ω (root i₀)]
  apply integral_le_of_discrete_strata (law p) (fun ω => Nat.log 2 (cluster G ω (root i₀)).ncard)
    (fun ω => diagonalLossMass G (root i₀) K ω (root i₀))
    (fun ω => ((cluster G ω (root i₀)).ncard:ℝ)^2) ‖A‖ L
    (fun ω => diagonalLossMass_nonneg G (root i₀) K hK ω (root i₀))
    (fun _ => sq_nonneg _) (fun ω => diagonalLossMass_le G (root i₀) K L hrow ω (root i₀)) hs
  · intro j
    simpa only [dyadic_binDiagonalMass G (root i₀) K _ (root i₀) hx] using hf' j
  · intro j
    simpa only [dyadic_binSizeMass_sq] using hs' j
  · intro j
    have h := integral_binDiagonalLoss_le G hloc root weight Γ htr hΓ hw i₀ hw₀ p (2^j) K hcov A hA
    simp only [dyadic_binDiagonalMass G (root i₀) K _ (root i₀) hx] at h
    simpa only [dyadic_binSizeMass_sq] using h

 

theorem subcritical_diagonalLoss_le [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (p : unitInterval) (hp : p < pc G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : V → V → ℝ), (∀ x y, 0 ≤ K x y) →
      (∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y) →
      ∀ (L : ℝ), (∀ x (S : Finset V), (∑ z ∈ S, K x z) ≤ L) →
      ∀ (A : Hilbert V →L[ℂ] Hilbert V),
      (∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ)) →
      (∫ ω, diagonalLossMass G (root i₀) K ω (root i₀) ∂law p) ≤ ‖A‖*C^3 := by
  obtain ⟨C,hC,hs⟩ := subcritical_second_moment G hloc hqt p hp
  refine ⟨C,hC,fun K hK hcov L hrow A hA => ?_⟩
  exact (integral_diagonalLoss_le G hloc root weight Γ htr hΓ hw i₀ hw₀ p K hK hcov L hrow A hA
    (hs (root i₀)).1).trans (mul_le_mul_of_nonneg_left (hs (root i₀)).2 (norm_nonneg _))

end DiagonalLoss
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section RootSecondMoment
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem second_moment_le_rootSusceptibility_cube [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hcov : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (x : V) :
    (∫ ω, ((cluster G ω x).ncard:ℝ)^2 ∂law p) ≤
      (c*rootSusceptibility G root weight p)^3 := by
  let C := c*rootSusceptibility G root weight p
  have hC : 0 ≤ C := mul_nonneg hc (rootSusceptibility_nonneg G root weight hw p)
  have hrow (z : V) : (∑' y, law p {ω | Conn G ω z y}) ≤ ENNReal.ofReal C := by
    rw [←ennreal_susceptibility G hloc hqt p hp]
    exact ENNReal.ofReal_le_ofReal (susceptibility_le_rootSusceptibility G root weight hw hcov c hc hmin p z)
  have hm : Measurable (fun ω : Set E => ((cluster G ω x).ncard:ℝ)^2) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ)^2)).comp (measurable_cluster_ncard G hloc x)
  have hn : 0 ≤ᵐ[law p] (fun ω => ((cluster G ω x).ncard:ℝ)^2) :=
    Filter.Eventually.of_forall (fun _ => sq_nonneg _)
  have he : (fun ω => ENNReal.ofReal (((cluster G ω x).ncard:ℝ)^2)) =ᵐ[law p]
      (fun ω => clusterMass G ω x ^ 2) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
    rw [clusterMass_eq_ncard G ω x hω,ENNReal.ofReal_pow (Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  have hbound : (∫⁻ ω, ENNReal.ofReal (((cluster G ω x).ncard:ℝ)^2) ∂law p) ≤ ENNReal.ofReal (C^3) := by
    rw [lintegral_congr_ae he,ENNReal.ofReal_pow hC]
    exact cluster_second_moment_bound G p _ hrow x
  rw [integral_eq_lintegral_of_nonneg_ae hn hm.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq (ENNReal.toReal_ofReal (pow_nonneg hC _))

theorem diagonalLoss_le_rootSusceptibility_cube [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V))
    (htr : RootTransport root weight Γ) (hΓ : ∀ a ∈ Γ, ∃ b, IsAut G a b)
    (hw : ∀ i, 0 ≤ weight i) (i₀ : ι) (hw₀ : 0 < weight i₀)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i)
    (p : unitInterval) (hp : p < pc G) (K : V → V → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (hcov : ∀ a b, IsAut G a b → ∀ x y, K (a x) (a y) = K x y)
    (L : ℝ) (hrow : ∀ x (S : Finset V), (∑ z ∈ S, K x z) ≤ L)
    (A : Hilbert V →L[ℂ] Hilbert V)
    (hA : ∀ x y, A (lp.single 2 y (1:ℂ)) x = (K x y : ℂ)) :
    (∫ ω, diagonalLossMass G (root i₀) K ω (root i₀) ∂law p) ≤
      ‖A‖*(c*rootSusceptibility G root weight p)^3 := by
  obtain ⟨_,_,hs⟩ := subcritical_second_moment G hloc hqt p hp
  exact (integral_diagonalLoss_le G hloc root weight Γ htr hΓ hw i₀ hw₀ p K hK hcov L hrow A hA
    (hs (root i₀)).1).trans (mul_le_mul_of_nonneg_left
      (second_moment_le_rootSusceptibility_cube G hloc hqt root weight hw hcover c hc hmin p hp (root i₀))
      (norm_nonneg _))

end RootSecondMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DiagonalSeries
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def diagonalLossTerm (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (x y : V) (ω : Set E) : ℝ :=
  if y ∈ vertexOrbit G o ∧ Conn G ω x y then K x y*((cluster G ω x).ncard:ℝ)^2 else 0

theorem diagonalLossTerm_nonneg (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (hK : ∀ x y, 0 ≤ K x y) (x y : V) (ω : Set E) :
    0 ≤ diagonalLossTerm G o K x y ω := by
  unfold diagonalLossTerm
  split_ifs
  · exact mul_nonneg (hK x y) (sq_nonneg _)
  · exact le_rfl

theorem diagonalLossTerm_le (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (hK : ∀ x y, 0 ≤ K x y) (x y : V) (ω : Set E) :
    diagonalLossTerm G o K x y ω ≤ K x y*((cluster G ω x).ncard:ℝ)^2 := by
  unfold diagonalLossTerm
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hK x y) (sq_nonneg _)

theorem diagonalLossMass_eq_tsum (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (x : V) (ω : Set E) :
    diagonalLossMass G o K ω x = ∑' y, diagonalLossTerm G o K x y ω := by
  by_cases hf : (cluster G ω x).Finite
  · let S := fullOrbitClass G o ω x
    have hs (y : V) : y ∈ S ↔ y ∈ vertexOrbit G o ∧ Conn G ω x y := by
      dsimp only [S,fullOrbitClass]
      rw [dite_eq_left hf]
      simp only [Finset.mem_filter,Set.Finite.mem_toFinset,cluster,Set.mem_ofPred_eq]
      exact and_comm
    rw [tsum_eq_sum (s := S) (fun y hy => by
      simp only [diagonalLossTerm,ite_eq_right (fun h => hy ((hs y).mpr h))])]
    rw [diagonalLossMass,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    rw [diagonalLossTerm,ite_eq_left ((hs y).mp hy),mul_comm]
  · have hn := Set.Infinite.ncard hf
    simp only [diagonalLossMass,diagonalLossTerm,hn,Nat.cast_zero,zero_pow (by omega : 2 ≠ 0),
      mul_zero,zero_mul,ite_self,tsum_zero]

theorem integrable_diagonalLossTerm [Countable V] [Countable E] (G : BondGraph V E) (o : V) (K : V → V → ℝ)
    (x y : V) (p : unitInterval)
    (hs : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^2) (law p)) :
    Integrable (diagonalLossTerm G o K x y) (law p) := by
  by_cases hy : y ∈ vertexOrbit G o
  · convert (hs.indicator (measurableSet_conn G x y)).const_mul (K x y) using 1
    ext ω
    simp only [diagonalLossTerm,hy,true_and,Set.indicator,Set.mem_ofPred_eq]
    split_ifs <;> simp only [mul_zero]
  · have he : diagonalLossTerm G o K x y = (fun _ : Set E => (0:ℝ)) := by
      funext ω
      simp only [diagonalLossTerm,hy,false_and,ite_false]
    rw [he]
    exact integrable_const 0

 

theorem integral_diagonalLoss_eq_series [Countable V] [Countable E]
    (G : BondGraph V E) (o : V) (K : V → V → ℝ) (hK : ∀ x y, 0 ≤ K x y)
    (L : ℝ) (hrow : ∀ x (S : Finset V), (∑ z ∈ S, K x z) ≤ L)
    (x : V) (p : unitInterval)
    (hs : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)^2) (law p)) :
    (∫ ω, diagonalLossMass G o K ω x ∂law p) =
      ∑' y, if y ∈ vertexOrbit G o then
        K x y*(∫ ω, (if Conn G ω x y then ((cluster G ω x).ncard:ℝ)^2 else 0) ∂law p) else 0 := by
  have hi (y : V) := integrable_diagonalLossTerm G o K x y p hs
  have hzero (y : V) (ω : Set E) := diagonalLossTerm_nonneg G o K hK x y ω
  have hn : Summable (fun y => ∫ ω, ‖diagonalLossTerm G o K x y ω‖ ∂law p) := by
    simp only [Real.norm_of_nonneg (hzero _ _)]
    apply summable_of_sum_le (fun y => integral_nonneg (hzero y)) (c := L*(∫ ω, ((cluster G ω x).ncard:ℝ)^2 ∂law p))
    intro S
    rw [←integral_finsetSum _ (fun y _ => hi y),←integral_const_mul]
    apply integral_mono (integrable_finsetSum _ (fun y _ => hi y)) (hs.const_mul L)
    intro ω
    calc
      _ ≤ ∑ y ∈ S, K x y*((cluster G ω x).ncard:ℝ)^2 :=
        Finset.sum_le_sum (fun y _ => diagonalLossTerm_le G o K hK x y ω)
      _ = (∑ y ∈ S, K x y)*((cluster G ω x).ncard:ℝ)^2 := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow x S) (sq_nonneg _)
  rw [show (fun ω => diagonalLossMass G o K ω x) = (fun ω => ∑' y, diagonalLossTerm G o K x y ω) from
    funext (diagonalLossMass_eq_tsum G o K x)]
  rw [←integral_tsum_of_summable_integral_norm hi hn]
  apply tsum_congr
  intro y
  by_cases hy : y ∈ vertexOrbit G o
  · simp only [diagonalLossTerm,hy,true_and,ite_true]
    rw [←integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by dsimp only; split_ifs <;> simp only [mul_zero])
  · simp only [diagonalLossTerm,hy,false_and,ite_false,integral_zero]

end DiagonalSeries
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section RootSusceptibilityLower
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem exists_rootSusceptibility_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hconn : Connected G) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hw1 : ∑ i, weight i = 1)
    (hcover : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ∃ a : ℝ, 0 < a ∧ ∀ (p : unitInterval), p₀ ≤ (p:ℝ) → p < pc G → ∀ x,
      a*rootSusceptibility G root weight p ≤ susceptibility G p x := by
  have hex (ij : ι × ι) : ∃ l : List E, Along G (root ij.1) l (root ij.2) := by
    obtain ⟨l,hl,_,_⟩ := conn_exists_bond_trail G (conn_univ_of_connected G hconn (root ij.1) (root ij.2))
    exact ⟨l,hl⟩
  choose path hpath using hex
  let N := ∑ ij : ι × ι, (path ij).length
  have hlen (i j : ι) : (path (i,j)).length ≤ N :=
    Finset.single_le_sum (f := fun ij : ι × ι => (path ij).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (i,j))
  refine ⟨p₀^N,pow_pos hp₀ N,fun p hp hpcrit x => ?_⟩
  obtain ⟨j,a,b,hab,hax⟩ := hcover x
  have hfin (z : V) : Summable (fun y => (law p).real {ω | Conn G (ω ∩ Set.univ) z y}) := by
    simp only [Set.inter_univ]
    exact summable_twoPoint_subcritical G hloc hqt p hpcrit z
  have heq (z : V) : restrictedSusceptibility G Set.univ p z = susceptibility G p z := by
    simp only [restrictedSusceptibility,susceptibility,Set.inter_univ,twoPoint,Measure.real]
  have hb (i : ι) : p₀^N*susceptibility G p (root i) ≤ susceptibility G p (root j) := by
    have h := restrictedSusceptibility_path_lower G Set.univ p (hpath (j,i)) (fun _ _ => Set.mem_univ _) hfin
    rw [heq,heq] at h
    have hpow : p₀^N ≤ (p:ℝ)^(path (j,i)).length :=
      (pow_le_pow_left₀ hp₀.le hp N).trans (pow_le_pow_of_le_one p.2.1 p.2.2 (hlen j i))
    exact (mul_le_mul_of_nonneg_right hpow (susceptibility_nonneg G p _)).trans h
  rw [←hax,susceptibility_aut G p hab]
  calc
    _ = ∑ i, weight i*(p₀^N*susceptibility G p (root i)) := by
      simp only [rootSusceptibility,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, weight i*susceptibility G p (root j) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i))
    _ = susceptibility G p (root j) := by rw [←Finset.sum_mul,hw1,one_mul]

end RootSusceptibilityLower
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
open scoped ENNReal
section ClusterAssociation
attribute [local instance] Classical.propDecidable Classical.decEq

theorem association_finiteWitness_ennreal [Countable E] (p : unitInterval)
    (A B : Set (Set E)) (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : FiniteWitness A) (hfB : FiniteWitness B) :
    law p A * law p B ≤ law p (A ∩ B) := by
  apply (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) (measure_ne_top _ _)).mp
  rw [ENNReal.toReal_mul]
  exact association_finiteWitness p A B hA hB hfA hfB

theorem clusterMass_mul (G : BondGraph V E) (ω : Set E) (x y : V) :
    clusterMass G ω x * clusterMass G ω y =
      ∑' a, ∑' b, if Conn G ω x a ∧ Conn G ω y b then (1:ℝ≥0∞) else 0 := by
  rw [clusterMass,clusterMass,←ENNReal.tsum_mul_right]
  apply tsum_congr
  intro a
  rw [←ENNReal.tsum_mul_left]
  apply tsum_congr
  intro b
  split_ifs <;> simp_all

theorem lintegral_clusterMass_mul [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) :
    (∫⁻ ω, clusterMass G ω x * clusterMass G ω y ∂law p) =
      ∑' a, ∑' b, law p {ω | Conn G ω x a ∧ Conn G ω y b} := by
  have hm (a b : V) : Measurable (fun ω : Set E => if Conn G ω x a ∧ Conn G ω y b then (1:ℝ≥0∞) else 0) :=
    Measurable.ite ((measurableSet_conn G x a).inter (measurableSet_conn G y b)) measurable_const measurable_const
  simp_rw [clusterMass_mul]
  rw [lintegral_tsum (fun a => (Measurable.tsum (fun b => hm a b)).aemeasurable)]
  apply tsum_congr
  intro a
  rw [lintegral_tsum (fun b => (hm a b).aemeasurable)]
  apply tsum_congr
  intro b
  have hs : MeasurableSet {ω : Set E | Conn G ω x a ∧ Conn G ω y b} :=
    (measurableSet_conn G x a).inter (measurableSet_conn G y b)
  simpa only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply] using (lintegral_indicator_one (μ := law p) hs)

theorem clusterMass_association [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) :
    (∑' a, law p {ω | Conn G ω x a})*(∑' b, law p {ω | Conn G ω y b}) ≤
      ∫⁻ ω, clusterMass G ω x * clusterMass G ω y ∂law p := by
  rw [lintegral_clusterMass_mul,←ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro a
  rw [←ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro b
  exact association_finiteWitness_ennreal p _ _
    (fun _ _ hω hc => conn_mono G hω hc) (fun _ _ hω hc => conn_mono G hω hc)
    (finiteWitness_conn G x a) (finiteWitness_conn G y b)

 

theorem subcritical_cluster_association [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (fun ω => ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ)) (law p) ∧
    susceptibility G p x * susceptibility G p y ≤
      ∫ ω, ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) ∂law p := by
  have hm (z : V) : Measurable (fun ω : Set E => ((cluster G ω z).ncard:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc z)
  have hn (ω : Set E) : 0 ≤ ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨_,_,hsecond⟩ := subcritical_second_moment G hloc hqt p hp
  have hi : Integrable (fun ω => ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ)) (law p) := by
    apply ((hsecond x).1.add (hsecond y).1).mono' ((hm x).mul (hm y)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp only [Pi.mul_apply,Pi.add_apply]
      rw [Real.norm_of_nonneg (hn ω)]
      nlinarith [sq_nonneg (((cluster G ω x).ncard:ℝ)-((cluster G ω y).ncard:ℝ))])
  refine ⟨hi,?_⟩
  have he : (fun ω => ENNReal.ofReal (((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ))) =ᵐ[law p]
      (fun ω => clusterMass G ω x * clusterMass G ω y) := by
    filter_upwards [subcritical_cluster_finite_ae G p hp x,subcritical_cluster_finite_ae G p hp y] with ω hx hy
    rw [clusterMass_eq_ncard G ω x hx,clusterMass_eq_ncard G ω y hy,ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp only [ENNReal.ofReal_natCast]
  have hb : ENNReal.ofReal (susceptibility G p x * susceptibility G p y) ≤
      ∫⁻ ω, ENNReal.ofReal (((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ)) ∂law p := by
    rw [lintegral_congr_ae he,ENNReal.ofReal_mul (susceptibility_nonneg G p x),
      ennreal_susceptibility G hloc hqt p hp,ennreal_susceptibility G hloc hqt p hp]
    exact clusterMass_association G p x y
  have htop : (∫⁻ ω, ENNReal.ofReal (((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ)) ∂law p) ≠ ⊤ :=
    ne_of_lt ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hn)).mp hi.hasFiniteIntegral)
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hn) hi.aestronglyMeasurable]
  simpa only [ENNReal.toReal_ofReal (mul_nonneg (susceptibility_nonneg G p x) (susceptibility_nonneg G p y))] using
    ENNReal.toReal_mono htop hb

end ClusterAssociation
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FiniteLocalIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem integral_mul_finite_local (I R : Finset E) (hdis : Disjoint I R)
    (p : unitInterval) (f g : Set E → ℝ)
    (hf : ∀ ω, f ω = f (ω ∩ (I:Set E)))
    (hg : ∀ ω, g ω = g (ω ∩ (R:Set E))) :
    (∫ ω, f ω*g ω ∂law p) = (∫ ω, f ω ∂law p)*(∫ ω, g ω ∂law p) := by
  have hf' := finite_local_of_subset I (I∪R) Finset.subset_union_left f hf
  have hg' := finite_local_of_subset R (I∪R) Finset.subset_union_right g hg
  rw [integral_eq_bernoulliPolynomial (I∪R) p _ (fun ω => by rw [hf' ω,hg' ω]),
    integral_eq_bernoulliPolynomial I p f hf,integral_eq_bernoulliPolynomial R p g hg,
    bernoulliPolynomial_union I R hdis]
  have hi (a b : Finset E) (ha : a ⊆ I) (hb : b ⊆ R) :
      ((a ∪ b : Finset E):Set E) ∩ (I:Set E) = a := by
    ext e
    simp only [Finset.coe_union,Set.mem_inter_iff,Set.mem_union,Finset.mem_coe]
    constructor
    · rintro ⟨he,hI⟩
      rcases he with he | he
      · exact he
      · exact ((Finset.disjoint_left.mp hdis) hI (hb he)).elim
    · intro he
      exact ⟨Or.inl he,ha he⟩
  have hr (a b : Finset E) (ha : a ⊆ I) (hb : b ⊆ R) :
      ((a ∪ b : Finset E):Set E) ∩ (R:Set E) = b := by
    ext e
    simp only [Finset.coe_union,Set.mem_inter_iff,Set.mem_union,Finset.mem_coe]
    constructor
    · rintro ⟨he,hR⟩
      rcases he with he | he
      · exact ((Finset.disjoint_left.mp hdis) (ha he) hR).elim
      · exact he
    · intro he
      exact ⟨Or.inr he,hb he⟩
  trans bernoulliPolynomial I (fun a => f a*bernoulliPolynomial R (fun b => g b) p) p
  · apply bernoulliPolynomial_congr
    intro a ha
    rw [←bernoulliPolynomial_const_mul]
    apply bernoulliPolynomial_congr
    intro b hb
    rw [hf ((a∪b : Finset E):Set E),hg ((a∪b : Finset E):Set E),hi a b ha hb,hr a b ha hb]
  · exact bernoulliPolynomial_mul_const I _ _ p

theorem complement_incidentSupport (G : BondGraph V E) (hloc : LocallyFinite G) (W : Finset V) :
    ((incidentSupport G hloc W:Set E))ᶜ = internalEdges G (W:Set V)ᶜ := by
  ext e
  simp only [Set.mem_compl_iff,Finset.mem_coe,mem_incidentSupport,internalEdges,Set.mem_ofPred_eq]
  push Not
  constructor
  · intro h x hx hxW
    exact h x hxW hx
  · intro h x hxW hx
    exact h x hx hxW

 

theorem cluster_restrict_incident_eq_iff (G : BondGraph V E) (hloc : LocallyFinite G)
    (W : Finset V) (Q : Finset E) (hQ : incidentSupport G hloc W ⊆ Q)
    (ω : Set E) (x : V) :
    cluster G (ω ∩ (Q:Set E)) x = (W:Set V) ↔ cluster G ω x = W := by
  have ho : ω \ (Q:Set E) ⊆ internalEdges G (W:Set V)ᶜ := by
    rw [←complement_incidentSupport G hloc W]
    exact fun _ h => fun he => h.2 (hQ he)
  have h := cluster_union_external_eq_iff G (ω ∩ (Q:Set E)) (ω \ (Q:Set E)) x W ho
  simpa only [Set.inter_union_sdiff] using h.symm

theorem measurableSet_cluster_eq [Countable V] [Countable E]
    (G : BondGraph V E) (x : V) (W : Set V) : MeasurableSet {ω : Set E | cluster G ω x = W} := by
  have he : {ω : Set E | cluster G ω x = W} = ⋂ y, {ω : Set E | Conn G ω x y ↔ y ∈ W} := by
    ext ω
    simp only [Set.mem_ofPred_eq,Set.mem_iInter,Set.ext_iff,cluster]
  rw [he]
  apply MeasurableSet.iInter
  intro y
  by_cases hy : y ∈ W
  · simpa only [hy,iff_true] using measurableSet_conn G x y
  · simpa only [hy,iff_false,Set.compl_ofPred] using (measurableSet_conn G x y).compl

 

theorem cluster_cell_finite_exterior_independence [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (W : Finset V) (x : V)
    (R : Finset E) (hR : (R:Set E) ⊆ internalEdges G (W:Set V)ᶜ)
    (p : unitInterval) (f : Set E → ℝ) (hf : ∀ ω, f ω = f (ω ∩ (R:Set E))) :
    (∫ ω, (if cluster G ω x = (W:Set V) then (1:ℝ) else 0)*f ω ∂law p) =
      (law p).real {ω | cluster G ω x = (W:Set V)} * (∫ ω, f ω ∂law p) := by
  have hdis : Disjoint (incidentSupport G hloc W) R := by
    rw [←complement_incidentSupport G hloc W] at hR
    exact Finset.disjoint_left.mpr (fun e he h => hR h he)
  have hc (ω : Set E) :
      (if cluster G ω x = (W:Set V) then (1:ℝ) else 0) =
        (if cluster G (ω ∩ (incidentSupport G hloc W:Set E)) x = (W:Set V) then 1 else 0) := by
    simp only [cluster_restrict_incident_eq_iff G hloc W _ (by rfl)]
  rw [integral_mul_finite_local _ R hdis p _ f hc hf]
  congr 1
  have hm : MeasurableSet {ω : Set E | cluster G ω x = (W:Set V)} := measurableSet_cluster_eq G x W
  simpa only [Set.indicator,Set.mem_ofPred_eq,Pi.one_apply] using integral_indicator_one hm

end FiniteLocalIndependence

end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory Filter
open scoped Topology
section ExteriorConnectionIndependence
attribute [local instance] Classical.propDecidable Classical.decEq

theorem measurableSet_restrictedConn [Countable E] (G : BondGraph V E)
    (S : Set E) (x y : V) : MeasurableSet {ω : Set E | Conn G (ω ∩ S) x y} :=
  measurableSet_finiteWitness _
    (fun _ _ hω hc => conn_mono G (Set.inter_subset_inter_left _ hω) hc)
    (finiteWitness_inter _ (finiteWitness_conn G x y) S)

theorem integral_event_indicator (p : unitInterval) (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫ ω, (if ω ∈ A then (1:ℝ) else 0) ∂law p) = (law p).real A := by
  simpa only [Set.indicator,Pi.one_apply] using (integral_indicator_one (μ := law p) hA)

 

theorem cluster_cell_exterior_connection_independent [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (W : Finset V)
    (x y z : V) (p : unitInterval) :
    (law p).real {ω | cluster G ω x = (W:Set V) ∧ Conn G (ω ∩ internalEdges G (W:Set V)ᶜ) y z} =
      (law p).real {ω | cluster G ω x = (W:Set V)} *
        (law p).real {ω | Conn G (ω ∩ internalEdges G (W:Set V)ᶜ) y z} := by
  let := Encodable.ofCountable E
  let S := internalEdges G (W:Set V)ᶜ
  let R := restrictedBondExhaustion S ∅
  have hmono : Monotone R := restrictedBondExhaustion_mono S ∅
  have hsub (n : ℕ) : (R n:Set E) ⊆ S := restrictedBondExhaustion_subset S ∅ (by simp) n
  have hcover (e : E) (he : e ∈ S) : ∃ n, e ∈ R n := restrictedBondExhaustion_cover S ∅ e he
  let A : Set (Set E) := {ω | cluster G ω x = (W:Set V)}
  let B (n : ℕ) : Set (Set E) := {ω | Conn G (ω ∩ (R n:Set E)) y z}
  let Btop : Set (Set E) := {ω | Conn G (ω ∩ S) y z}
  have hB : Monotone B := fun n m h ω hc =>
    conn_mono G (Set.inter_subset_inter_right _ (show (R n:Set E) ⊆ (R m:Set E) from hmono h)) hc
  have hu : (⋃ n, B n) = Btop := by
    ext ω
    simp only [B,Btop,Set.mem_iUnion,Set.mem_ofPred_eq]
    exact ⟨fun ⟨n,hn⟩ => conn_mono G (Set.inter_subset_inter_right _ (hsub n)) hn,
      conn_finite_exhaustion G S R hmono hcover⟩
  have huA : (⋃ n, A ∩ B n) = A ∩ Btop := by rw [←Set.inter_iUnion,hu]
  have htB := tendsto_measure_iUnion_atTop (μ := law p) hB
  have htA := tendsto_measure_iUnion_atTop (μ := law p)
    (show Monotone (fun n => A ∩ B n) from fun _ _ h => Set.inter_subset_inter_right _ (hB h))
  rw [hu] at htB
  rw [huA] at htA
  have htB' := (ENNReal.tendsto_toReal (measure_ne_top (law p) Btop)).comp htB
  have htA' := (ENNReal.tendsto_toReal (measure_ne_top (law p) (A∩Btop))).comp htA
  have he (n : ℕ) : (law p).real (A ∩ B n) = (law p).real A * (law p).real (B n) := by
    have h := cluster_cell_finite_exterior_independence G hloc W x (R n) (hsub n) p
      (fun ω => if Conn G (ω ∩ (R n:Set E)) y z then (1:ℝ) else 0)
      (fun ω => by rw [Set.inter_assoc,Set.inter_self])
    have hf : (∫ ω, (if cluster G ω x = (W:Set V) then (1:ℝ) else 0)*
        (if Conn G (ω ∩ (R n:Set E)) y z then (1:ℝ) else 0) ∂law p) = (law p).real (A ∩ B n) := by
      rw [←integral_event_indicator p (A∩B n)
        ((measurableSet_cluster_eq G x W).inter (measurableSet_restrictedConn G _ y z))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => by
        dsimp only [A,B,Set.mem_inter_iff,Set.mem_ofPred_eq]
        split_ifs <;> simp_all)
    rw [hf] at h
    rw [show (∫ ω, (if Conn G (ω ∩ (R n:Set E)) y z then (1:ℝ) else 0) ∂law p) =
      (law p).real (B n) from integral_event_indicator p (B n) (measurableSet_restrictedConn G _ y z)] at h
    exact h
  exact tendsto_nhds_unique htA' ((tendsto_const_nhds.mul htB').congr (fun n => (he n).symm))

end ExteriorConnectionIndependence
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExposedClusterGeometry
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem conn_exterior_of_cluster_eq (G : BondGraph V E) (ω : Set E)
    (x y z : V) (W : Set V) (hW : cluster G ω x = W) (hy : y ∉ W) :
    Conn G (ω ∩ internalEdges G Wᶜ) y z ↔ Conn G ω y z := by
  refine ⟨conn_mono G Set.inter_subset_left,fun h => ?_⟩
  have hout (a : V) (ha : Conn G ω y a) : a ∉ W := by
    intro haW
    have hxa : Conn G ω x a := by change a ∈ cluster G ω x; rwa [hW]
    exact hy (hW ▸ (hxa.trans (conn_symm G _ ha) : y ∈ cluster G ω x))
  induction h with
  | refl => exact conn_refl G _ y
  | @tail a b hya hab ih =>
    obtain ⟨e,he,heq⟩ := hab
    exact ih.tail ⟨e,⟨he,(mem_internalEdges_of_ends G Wᶜ e a b heq).mpr
      ⟨hout a hya,hout b (hya.tail ⟨e,he,heq⟩)⟩⟩,heq⟩

theorem cluster_size_eq_tsum_real (G : BondGraph V E) (ω : Set E) (y : V)
    (hf : (cluster G ω y).Finite) :
    ((cluster G ω y).ncard:ℝ) = ∑' z, if Conn G ω y z then (1:ℝ) else 0 := by
  rw [tsum_eq_sum (s := hf.toFinset) (fun z hz => by
    exact ite_eq_right (fun hc => hz (hf.mem_toFinset.mpr hc)))]
  rw [show (∑ z ∈ hf.toFinset, if Conn G ω y z then (1:ℝ) else 0) =
      ∑ _z ∈ hf.toFinset, (1:ℝ) from Finset.sum_congr rfl (fun z hz => ite_eq_left (hf.mem_toFinset.mp hz))]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one,←Set.ncard_eq_toFinset_card _ hf]

 

theorem integral_cluster_size_event [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (y : V) (A : Set (Set E)) (hA : MeasurableSet A) :
    (∫ ω, (if ω ∈ A then ((cluster G ω y).ncard:ℝ) else 0) ∂law p) =
      ∑' z, (law p).real {ω | ω ∈ A ∧ Conn G ω y z} := by
  let f (z : V) (ω : Set E) : ℝ := if ω ∈ A ∧ Conn G ω y z then 1 else 0
  have hm (z : V) : MeasurableSet {ω : Set E | ω ∈ A ∧ Conn G ω y z} :=
    hA.inter (measurableSet_conn G y z)
  have hf (z : V) : f z = {ω : Set E | ω ∈ A ∧ Conn G ω y z}.indicator (fun _ => (1:ℝ)) := by
    funext ω
    simp only [f,Set.indicator,Set.mem_ofPred_eq]
  have hi (z : V) : Integrable (f z) (law p) := by
    rw [hf]
    exact (integrable_const (1:ℝ)).indicator (hm z)
  have hn (z : V) (ω : Set E) : 0 ≤ f z ω := by unfold f; split_ifs <;> norm_num
  have he (z : V) : (∫ ω, f z ω ∂law p) = (law p).real {ω | ω ∈ A ∧ Conn G ω y z} := by
    rw [hf]
    exact integral_indicator_one (hm z)
  have hint : Summable (fun z => ∫ ω, ‖f z ω‖ ∂law p) := by
    simp_rw [Real.norm_of_nonneg (hn _ _),he]
    apply (summable_twoPoint_subcritical G hloc hqt p hp y).of_nonneg_of_le
    · exact fun _ => ENNReal.toReal_nonneg
    · intro z
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun ω h => h.2))
  calc
    _ = ∫ ω, ∑' z, f z ω ∂law p := by
      apply integral_congr_ae
      filter_upwards [subcritical_cluster_finite_ae G p hp y] with ω hω
      by_cases hωA : ω ∈ A
      · simp only [hωA,ite_true,f,true_and]
        exact cluster_size_eq_tsum_real G ω y hω
      · simp only [hωA,ite_false,f,false_and,tsum_zero]
    _ = ∑' z, ∫ ω, f z ω ∂law p := (integral_tsum_of_summable_integral_norm hi hint).symm
    _ = _ := tsum_congr he

end ExposedClusterGeometry
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ExteriorCellSusceptibility
attribute [local instance] Classical.propDecidable Classical.decEq

 

theorem cluster_cell_exterior_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (W : Finset V) (x y : V) :
    (∫ ω, (if cluster G ω x = (W:Set V) ∧ ¬Conn G ω x y
      then ((cluster G ω y).ncard:ℝ) else 0) ∂law p) =
      (law p).real {ω | cluster G ω x = (W:Set V)} *
        inducedSusceptibility G (W:Set V)ᶜ p y := by
  by_cases hy : y ∈ (W:Set V)
  · rw [inducedSusceptibility,ite_eq_right (fun h => h hy),mul_zero]
    calc
      _ = ∫ _ω : Set E, (0:ℝ) ∂law p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          dsimp only
          split_ifs with h
          · have hc : Conn G ω x y := by change y ∈ cluster G ω x; rwa [h.1]
            exact (h.2 hc).elim
          · rfl)
      _ = 0 := integral_zero _ _
  · simp only [inducedSusceptibility,Set.mem_compl_iff,hy,not_false_eq_true,ite_true]
    calc
      _ = ∫ ω, (if cluster G ω x = (W:Set V) then ((cluster G ω y).ncard:ℝ) else 0) ∂law p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          dsimp only
          by_cases hc : cluster G ω x = (W:Set V)
          · have hnc : ¬Conn G ω x y := by intro h; exact hy (hc ▸ h)
            simp [hc,hnc]
          · simp only [hc,false_and,ite_false])
      _ = ∑' z, (law p).real {ω | cluster G ω x = (W:Set V) ∧ Conn G ω y z} :=
        integral_cluster_size_event G hloc hqt p hp y _ (measurableSet_cluster_eq G x W)
      _ = ∑' z, (law p).real {ω | cluster G ω x = (W:Set V)} *
          (law p).real {ω | Conn G (ω ∩ internalEdges G (W:Set V)ᶜ) y z} := by
        apply tsum_congr
        intro z
        rw [show {ω : Set E | cluster G ω x = (W:Set V) ∧ Conn G ω y z} =
            {ω | cluster G ω x = (W:Set V) ∧ Conn G (ω ∩ internalEdges G (W:Set V)ᶜ) y z} from by
          ext ω
          exact ⟨fun h => ⟨h.1,(conn_exterior_of_cluster_eq G ω x y z W h.1 hy).mpr h.2⟩,
            fun h => ⟨h.1,conn_mono G Set.inter_subset_left h.2⟩⟩]
        exact cluster_cell_exterior_connection_independent G hloc W x y z p
      _ = _ := tsum_mul_left

theorem restrictedSusceptibility_le_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (S : Set E) (y : V) :
    restrictedSusceptibility G S p y ≤ susceptibility G p y := by
  apply Summable.tsum_le_tsum _ (summable_restrictedTwoPoint G hloc hqt p hp S y)
    (summable_twoPoint_subcritical G hloc hqt p hp y)
  exact fun z => ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun ω hc => conn_mono G Set.inter_subset_left hc))

theorem inducedSusceptibility_le_susceptibility [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (D : Set V) (y : V) :
    inducedSusceptibility G D p y ≤ susceptibility G p y := by
  unfold inducedSusceptibility
  split_ifs
  · exact restrictedSusceptibility_le_susceptibility G hloc hqt p hp _ y
  · exact susceptibility_nonneg G p y

end ExteriorCellSusceptibility
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section ClusterPartition
attribute [local instance] Classical.propDecidable Classical.decEq

theorem tsum_cluster_cells (G : BondGraph V E) (ω : Set E) (x : V)
    (hf : (cluster G ω x).Finite) (a : ℝ) :
    (∑' W : Finset V, if cluster G ω x = (W:Set V) then a else 0) = a := by
  let W := hf.toFinset
  have hW : cluster G ω x = (W:Set V) := hf.coe_toFinset.symm
  rw [tsum_eq_single W (fun U hU => ite_eq_right (fun h => hU (Finset.coe_injective (h.symm.trans hW)))),ite_eq_left hW]

 

theorem integral_cluster_finite_partition [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (hp : p < pc G) (x : V)
    (f : Set E → ℝ) (hf : Integrable f (law p)) :
    (∫ ω, f ω ∂law p) = ∑' W : Finset V,
      ∫ ω, (if cluster G ω x = (W:Set V) then f ω else 0) ∂law p := by
  let F (W : Finset V) (ω : Set E) := if cluster G ω x = (W:Set V) then f ω else 0
  have hi (W : Finset V) : Integrable (F W) (law p) := by
    have he : F W = {ω : Set E | cluster G ω x = (W:Set V)}.indicator f := by
      funext ω
      simp only [F,Set.indicator,Set.mem_ofPred_eq]
      split_ifs <;> rfl
    rw [he]
    exact hf.indicator (measurableSet_cluster_eq G x W)
  have hb (S : Finset (Finset V)) (ω : Set E) : (∑ W ∈ S, ‖F W ω‖) ≤ ‖f ω‖ := by
    by_cases hex : ∃ W ∈ S, cluster G ω x = (W:Set V)
    · obtain ⟨W,hWS,hW⟩ := hex
      rw [Finset.sum_eq_single W]
      · simp only [F,hW,ite_true,le_refl]
      · intro U _ hU
        have hu : cluster G ω x ≠ (U:Set V) := fun h => hU (Finset.coe_injective (h.symm.trans hW))
        simp only [F,ite_eq_right hu,norm_zero]
      · exact fun h => (h hWS).elim
    · have he (W : Finset V) (hW : W ∈ S) : cluster G ω x ≠ (W:Set V) := fun h => hex ⟨W,hW,h⟩
      calc
        _ = 0 := Finset.sum_eq_zero (fun W hW => by simp only [F,ite_eq_right (he W hW),norm_zero])
        _ ≤ _ := norm_nonneg _
  have hn : Summable (fun W => ∫ ω, ‖F W ω‖ ∂law p) := by
    apply summable_of_sum_le (fun _ => integral_nonneg (fun _ => norm_nonneg _))
      (c := ∫ ω, ‖f ω‖ ∂law p)
    intro S
    rw [←integral_finsetSum _ (fun W _ => (hi W).norm)]
    exact integral_mono (integrable_finsetSum _ (fun W _ => (hi W).norm)) hf.norm (hb S)
  calc
    _ = ∫ ω, ∑' W : Finset V, F W ω ∂law p := by
      apply integral_congr_ae
      filter_upwards [subcritical_cluster_finite_ae G p hp x] with ω hω
      exact (tsum_cluster_cells G ω x hω (f ω)).symm
    _ = _ := (integral_tsum_of_summable_integral_norm hi hn).symm

end ClusterPartition
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section FreshExteriorMoment
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def freshExteriorMoment (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) : ℝ :=
  ((cluster G ω x).ncard:ℝ) * inducedSusceptibility G (cluster G ω x)ᶜ p y

theorem freshExteriorMoment_eq_tsum (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) :
    freshExteriorMoment G p x y ω = ∑' W : Finset V, if cluster G ω x = (W:Set V)
      then (W.card:ℝ)*inducedSusceptibility G (W:Set V)ᶜ p y else 0 := by
  by_cases hf : (cluster G ω x).Finite
  · let W := hf.toFinset
    have hW : cluster G ω x = (W:Set V) := hf.coe_toFinset.symm
    rw [tsum_eq_single W (fun U hU => ite_eq_right (fun h => hU (Finset.coe_injective (h.symm.trans hW)))),ite_eq_left hW]
    simp only [freshExteriorMoment,hW,Set.ncard_coe_finset]
  · have he (W : Finset V) : cluster G ω x ≠ (W:Set V) := fun h => hf (h ▸ W.finite_toSet)
    simp only [freshExteriorMoment,Set.Infinite.ncard hf,Nat.cast_zero,zero_mul,ite_eq_right (he _),tsum_zero]

theorem measurable_freshExteriorMoment [Countable V] [Countable E]
    (G : BondGraph V E) (p : unitInterval) (x y : V) : Measurable (freshExteriorMoment G p x y) := by
  simp_rw [show freshExteriorMoment G p x y = (fun ω => ∑' W : Finset V, if cluster G ω x = (W:Set V)
      then (W.card:ℝ)*inducedSusceptibility G (W:Set V)ᶜ p y else 0) from funext (freshExteriorMoment_eq_tsum G p x y)]
  apply Measurable.tsum
  intro W
  exact Measurable.ite (measurableSet_cluster_eq G x W) measurable_const measurable_const

theorem freshExteriorMoment_nonneg (G : BondGraph V E) (p : unitInterval)
    (x y : V) (ω : Set E) : 0 ≤ freshExteriorMoment G p x y ω :=
  mul_nonneg (Nat.cast_nonneg _) (inducedSusceptibility_nonneg G _ p y)

theorem integrable_freshExteriorMoment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (freshExteriorMoment G p x y) (law p) := by
  apply ((susceptibility_eq_integral G hloc hqt p hp x).1.mul_const (susceptibility G p y)).mono'
    (measurable_freshExteriorMoment G p x y).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_of_nonneg (freshExteriorMoment_nonneg G p x y ω)]
    exact mul_le_mul_of_nonneg_left (inducedSusceptibility_le_susceptibility G hloc hqt p hp _ y) (Nat.cast_nonneg _))

theorem integrable_distinct_cluster_product [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    Integrable (fun ω => if ¬Conn G ω x y
      then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) (law p) := by
  have he : (fun ω : Set E => if ¬Conn G ω x y
      then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) =
      {ω : Set E | Conn G ω x y}ᶜ.indicator
        (fun ω => ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ)) := by
    funext ω
    simp only [Set.indicator,Set.mem_compl_iff,Set.mem_ofPred_eq]
  rw [he]
  exact (subcritical_cluster_association G hloc hqt p hp x y).1.indicator
    (measurableSet_conn G x y).compl

 

theorem integral_freshExteriorMoment [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (hqt : QuasiTransitive G)
    (p : unitInterval) (hp : p < pc G) (x y : V) :
    (∫ ω, freshExteriorMoment G p x y ω ∂law p) =
      ∫ ω, (if ¬Conn G ω x y then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) ∂law p := by
  rw [integral_cluster_finite_partition G p hp x _ (integrable_freshExteriorMoment G hloc hqt p hp x y),
    integral_cluster_finite_partition G p hp x _ (integrable_distinct_cluster_product G hloc hqt p hp x y)]
  apply tsum_congr
  intro W
  have hl : (∫ ω, (if cluster G ω x = (W:Set V) then freshExteriorMoment G p x y ω else 0) ∂law p) =
      (W.card:ℝ)*inducedSusceptibility G (W:Set V)ᶜ p y * (law p).real {ω | cluster G ω x = (W:Set V)} := by
    rw [←integral_event_indicator p _ (measurableSet_cluster_eq G x W),←integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp only [Set.mem_ofPred_eq]
      by_cases hc : cluster G ω x = (W:Set V)
      · simp only [hc,ite_true,freshExteriorMoment,Set.ncard_coe_finset,mul_one]
      · simp only [hc,ite_false,mul_zero])
  have hr : (∫ ω, (if cluster G ω x = (W:Set V) then
      (if ¬Conn G ω x y then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) else 0) ∂law p) =
      (W.card:ℝ)*((law p).real {ω | cluster G ω x = (W:Set V)} * inducedSusceptibility G (W:Set V)ᶜ p y) := by
    rw [←cluster_cell_exterior_susceptibility G hloc hqt p hp W x y,←integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by
      dsimp only
      by_cases hc : cluster G ω x = (W:Set V)
      · simp only [hc,true_and,ite_true,Set.ncard_coe_finset]
        split_ifs <;> simp only [mul_zero]
      · simp only [hc,false_and,ite_false,mul_zero])
  rw [hl,hr]
  ring

end FreshExteriorMoment
end Percolation

 
namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
open MeasureTheory
section DistinctClusterMoments
attribute [local instance] Classical.propDecidable Classical.decEq

noncomputable def distinctClusterMoment (G : BondGraph V E) (p : unitInterval) (x y : V) : ℝ :=
  ∫ ω, (if ¬Conn G ω x y then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) ∂law p

theorem distinctClusterMoment_nonneg (G : BondGraph V E) (p : unitInterval) (x y : V) :
    0 ≤ distinctClusterMoment G p x y := by
  apply integral_nonneg
  intro ω
  dsimp only [Pi.zero_apply]
  split_ifs <;> positivity

theorem cluster_ncard_covariant (G : BondGraph V E) {a : V ≃ V} {b : E ≃ E}
    (hab : IsAut G a b) (ω : Set E) (x : V) :
    (cluster G (b ⁻¹' ω) x).ncard = (cluster G ω (a x)).ncard := by
  rw [←cluster_aut G hab,Set.ncard_image_of_injective _ a.injective]

theorem distinctClusterMoment_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x y : V) :
    distinctClusterMoment G p (a x) (a y) = distinctClusterMoment G p x y := by
  have hs (z : V) : Measurable (fun ω : Set E => ((cluster G ω z).ncard:ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp (measurable_cluster_ncard G hloc z)
  have hm : Measurable (fun ω : Set E => if ¬Conn G ω x y
      then ((cluster G ω x).ncard:ℝ)*((cluster G ω y).ncard:ℝ) else 0) :=
    Measurable.ite (measurableSet_conn G x y).compl ((hs x).mul (hs y)) measurable_const
  have h := integral_map (μ := law p) (measurable_set_preimage b).aemeasurable hm.aestronglyMeasurable
  rw [law_map_preimage_equiv p b] at h
  simpa only [distinctClusterMoment,conn_aut_iff G hab,cluster_ncard_covariant G hab] using h.symm

noncomputable def neighborClusterMoment (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x : V) : ℝ :=
  ∑ y ∈ neighbors G hloc x, distinctClusterMoment G p x y

theorem neighborClusterMoment_nonneg (G : BondGraph V E) (hloc : LocallyFinite G)
    (p : unitInterval) (x : V) : 0 ≤ neighborClusterMoment G hloc p x :=
  Finset.sum_nonneg (fun y _ => distinctClusterMoment_nonneg G p x y)

theorem neighbors_covariant (G : BondGraph V E) (hloc : LocallyFinite G)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) :
    neighbors G hloc (a x) = (neighbors G hloc x).map a.toEmbedding := by
  ext y
  simp only [mem_neighbors,Finset.mem_map,Equiv.coe_toEmbedding]
  constructor
  · intro h
    refine ⟨a.symm y,?_,by simp⟩
    simpa only [a.symm_apply_apply] using adj_aut G (isAut_symm G hab) h
  · rintro ⟨z,hz,rfl⟩
    exact adj_aut G hab hz

theorem neighborClusterMoment_covariant [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G) (p : unitInterval)
    {a : V ≃ V} {b : E ≃ E} (hab : IsAut G a b) (x : V) :
    neighborClusterMoment G hloc p (a x) = neighborClusterMoment G hloc p x := by
  simp only [neighborClusterMoment,neighbors_covariant G hloc hab,Finset.sum_map,Equiv.coe_toEmbedding,
    distinctClusterMoment_covariant G hloc p hab]

noncomputable def rootNeighborMoment (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ) (p : unitInterval) : ℝ :=
  ∑ i, weight i * neighborClusterMoment G hloc p (root i)

theorem neighborMoment_le_rootMoment [Countable V] [Countable E]
    (G : BondGraph V E) (hloc : LocallyFinite G)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (hw : ∀ i, 0 ≤ weight i) (hcov : ∀ x, ∃ i, x ∈ vertexOrbit G (root i))
    (c : ℝ) (hc : 0 ≤ c) (hmin : ∀ i, 1 ≤ c*weight i) (p : unitInterval) (x : V) :
    neighborClusterMoment G hloc p x ≤ c*rootNeighborMoment G hloc root weight p := by
  obtain ⟨i,a,b,hab,hax⟩ := hcov x
  rw [←hax,neighborClusterMoment_covariant G hloc p hab]
  calc
    _ ≤ (c*weight i)*neighborClusterMoment G hloc p (root i) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hmin i) (neighborClusterMoment_nonneg G hloc p _)
    _ = c*(weight i*neighborClusterMoment G hloc p (root i)) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun j _ => mul_nonneg (hw j) (neighborClusterMoment_nonneg G hloc p _)) (Finset.mem_univ i)) hc

end DistinctClusterMoments
end Percolation

end OAI
