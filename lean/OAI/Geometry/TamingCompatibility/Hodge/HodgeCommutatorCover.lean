import Mathlib
import OAI.Geometry.TamingCompatibility.Hodge.HodgeWeightNorm

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev EuclideanSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)

structure HodgeCommutatorPatch (k : ℕ) where
  chart : A.centers
  reciprocal : 𝓢(Space,ℝ)
  neighborhood : Set Space
  neighborhood_open : IsOpen neighborhood
  neighborhood_subset : neighborhood ⊆ (D chart).domain
  reciprocal_spec : ∀ z ∈ neighborhood, reciprocal z * coordinateWeight A chart z = 1
  estimate : ∀ χ : 𝓢(Space,ℂ), HasCompactSupport (χ : Space → ℂ) → tsupport χ ⊆ neighborhood →
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∃ T : L2 A J α hs ht true →L[ℝ] H Space (C 6) 0,
        (∀ f : PreL2 A J α hs ht true,
          toDistribution Space (C 6) 0
            (T (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) f))) =
            smulLeftCLM (C 6) χ (hodgeRawDistribution A J α hs ht D hD chart reciprocal
              (hodgeSmooth A J α hs ht (hodgePowerCommutator A J α hs ht (k+1) f)))) ∧
        ∀ v, ‖T v‖ ≤ B * (r⁻¹)^(2*k+1) * ‖v‖

namespace HodgeCommutatorPatch
variable {A J α hs ht D hD} {k : ℕ}
variable (P : HodgeCommutatorPatch A J α hs ht D hD k)
def source : Set X := (extChartAt Model P.chart.val).source ∩
  (extChartAt Model P.chart.val) ⁻¹' P.neighborhood
omit [T2Space X] in
lemma source_open : IsOpen P.source :=
  (continuousOn_extChartAt P.chart.val).isOpen_inter_preimage
    (isOpen_extChartAt_source P.chart.val) P.neighborhood_open
end HodgeCommutatorPatch

lemma exists_hodgeCommutatorPatch (k : ℕ) (hk : k ≤ 2) (x : X) :
    ∃ P : HodgeCommutatorPatch A J α hs ht D hD k, x ∈ P.source := by
  obtain ⟨p,hp,hxp⟩ := exists_nonzero_weight_chart A J α ht (fun p => (D p).toData) hD x
  have hxs : x ∈ (extChartAt Model p.val).source := (A.subordinate p) (subset_closure hp)
  have hw : coordinateWeight A p (extChartAt Model p.val x) ≠ 0 := by
    simpa only [coordinateWeight,(extChartAt Model p.val).left_inv hxs] using hp
  obtain ⟨τ,U,hU,hqU,hUD,hτ,hbound⟩ :=
    hodge_commutator_uniform_local_bound A J α hs ht D hD k hk p _ hxp hw
  exact ⟨⟨p,τ,U,hU,hUD,hτ,hbound⟩,hxs,hqU⟩

structure HodgeCommutatorCover (k : ℕ) where
  centers : Finset X
  patch : centers → HodgeCommutatorPatch A J α hs ht D hD k
  partition : SmoothPartitionOfUnity centers Model X
  subordinate : partition.IsSubordinate (fun i => (patch i).source)

lemma hodgeCommutatorCover_nonempty (k : ℕ) (hk : k ≤ 2) :
    Nonempty (HodgeCommutatorCover A J α hs ht D hD k) := by
  classical
  choose P hP using exists_hodgeCommutatorPatch A J α hs ht D hD k hk
  obtain ⟨s,hcover⟩ := isCompact_univ.elim_finite_subcover (fun x : X => (P x).source)
    (fun x => (P x).source_open) (fun x _ => mem_iUnion_of_mem x (hP x))
  have hc : (univ : Set X) ⊆ ⋃ i : s, (P i.val).source := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcover hx)
    exact mem_iUnion_of_mem ⟨i,hi⟩ hxi
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate Model isClosed_univ
    (fun i : s => (P i.val).source) (fun i => (P i.val).source_open) hc
  exact ⟨⟨s,fun i => P i.val,ρ,hρ⟩⟩

def hodgeCommutatorCover (k : ℕ) (hk : k ≤ 2) : HodgeCommutatorCover A J α hs ht D hD k :=
  Classical.choice (hodgeCommutatorCover_nonempty A J α hs ht D hD k hk)
end TamingCompatibility.GeometricHilbert

end
end

section
noncomputable section
namespace TamingCompatibility.GeometricHilbert
open GeometricChart (coordinateWeight)
open ManifoldForms ManifoldHodge ManifoldLocalization HodgeChart ManifoldVolume
open Set Filter MeasureTheory ComplexMatrix TemperedDistribution HilbertSobolev
open scoped Manifold ContDiff Topology SchwartzMap RealInnerProductSpace
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable {A : FiniteCharts X} {J : AlmostComplexStructure X} {α : TwoForm X}
  {hs : IsSmooth α} {ht : Tames α J}
  {D : ∀ p : A.centers, HodgeChart.Data J α ht p.val}
  {hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source}
namespace HodgeCommutatorCover
variable {k : ℕ} (C : HodgeCommutatorCover A J α hs ht D hD k)

def weight (i : C.centers) : 𝓢(Space,ℝ) :=
  LocalWeight.halfDensity A J α hs ht D (C.patch i).chart (C.patch i).neighborhood
    (C.patch i).neighborhood_open (C.patch i).neighborhood_subset
    (C.partition i) (C.partition i).contMDiff (C.subordinate i)

omit [T2Space X] in
lemma weight_support (i : C.centers) : tsupport (C.weight i) ⊆ (C.patch i).neighborhood :=
  LocalWeight.halfDensity_support A J α hs ht D (C.patch i).chart (C.patch i).neighborhood
    (C.patch i).neighborhood_open (C.patch i).neighborhood_subset
    (C.partition i) (C.partition i).contMDiff (C.subordinate i)

omit [T2Space X] in
lemma weight_compact (i : C.centers) : HasCompactSupport (C.weight i : Space → ℝ) :=
  LocalWeight.halfDensity_compact A J α hs ht D (C.patch i).chart (C.patch i).neighborhood
    (C.patch i).neighborhood_open (C.patch i).neighborhood_subset
    (C.partition i) (C.partition i).contMDiff (C.subordinate i)

def weightedSquare (i : C.centers) (a : PreL2 A J α hs ht true) : ℝ :=
  ∫ x, (C.partition i x)^2 * GeometricAdjoint.pairing J α ht a.val a.val x
    ∂geometricVolume A J α

omit [T2Space X] in

lemma weighted_norm_eq (i : C.centers) (a : PreL2 A J α hs ht true)
    (u : H Space (ComplexMatrix.C 6) 0)
    (hu : toDistribution Space (ComplexMatrix.C 6) 0 u =
      smulLeftCLM (ComplexMatrix.C 6)
        (SchwartzMap.postcompCLM Complex.ofRealCLM (C.weight i))
        (hodgeRawDistribution A J α hs ht D hD (C.patch i).chart (C.patch i).reciprocal
          (hodgeSmooth A J α hs ht a))) :
    (∫ x, (C.partition i x)^2 * GeometricAdjoint.pairing J α ht a.val a.val x
      ∂geometricVolume A J α) = ‖u‖^2 :=
  LocalWeight.integral_weight_H0_norm A J α hs ht D hD
    (C.patch i).chart (C.patch i).neighborhood (C.patch i).neighborhood_open
    (C.patch i).neighborhood_subset (C.partition i) (C.partition i).contMDiff
    (C.subordinate i) (C.patch i).reciprocal (C.patch i).reciprocal_spec a u hu

omit [T2Space X] in

lemma local_integral_bound (i : C.centers) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ f : PreL2 A J α hs ht true,
        C.weightedSquare i (hodgePowerCommutator A J α hs ht (k+1) f) ≤
          (B*(r⁻¹)^(2*k+1)*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖)^2 := by
  let χ := SchwartzMap.postcompCLM Complex.ofRealCLM (C.weight i)
  have hχ : tsupport χ ⊆ (C.patch i).neighborhood :=
    (tsupport_comp_subset (g := Complex.ofRealCLM) (map_zero _) _).trans (C.weight_support i)
  have hc : HasCompactSupport (χ : Space → ℂ) :=
    (C.weight_compact i).of_isClosed_subset (isClosed_tsupport χ)
      (postcomp_real_tsupport (C.weight i))
  obtain ⟨B,hB,hreg⟩ := (C.patch i).estimate χ hc hχ
  refine ⟨B,hB,fun r hr hr1 f => ?_⟩
  obtain ⟨T,hT,hTb⟩ := hreg r hr hr1
  have hTf := hT f
  have hbf := hTb (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) f))
  generalize hfcomm : hodgePowerCommutator A J α hs ht (k+1) f = a at hTf ⊢
  generalize hu : T (smoothL2 A J α hs ht true ((hodgeSmoothShift A J α hs ht r ^ 3) f)) = u at hTf hbf
  rw [weightedSquare,C.weighted_norm_eq i a u hTf]
  have hb := pow_le_pow_left₀ (norm_nonneg _) hbf 2
  simpa only [LinearIsometry.norm_map] using hb

omit [T2Space X] in
lemma partition_sum (x : X) : ∑ i : C.centers, C.partition i x = 1 := by
  rw [← finsum_eq_sum_of_fintype]
  exact C.partition.sum_eq_one (mem_univ x)

include C in
omit [T2Space X] in

lemma global_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
    ∀ f : PreL2 A J α hs ht true,
      ‖hodgePowerCommutator A J α hs ht (k+1) f‖ ≤
        B*(r⁻¹)^(2*k+1)*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖ := by
  classical
  let := geometricVolume_finite A J α hs ht
  choose b hb hbound using C.local_integral_bound
  let N : ℝ := Fintype.card C.centers
  let K : ℝ := N * ∑ i : C.centers, (b i)^2
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hK : 0 ≤ K := mul_nonneg hN (Finset.sum_nonneg fun i _ => sq_nonneg (b i))
  refine ⟨Real.sqrt K,Real.sqrt_nonneg _,fun r hr hr1 f => ?_⟩
  let a := hodgePowerCommutator A J α hs ht (k+1) f
  let F : X → ℝ := GeometricAdjoint.pairing J α ht a.val a.val
  have hFc : Continuous F := (GeometricAdjoint.pairing_two_smooth J α hs ht a.property a.property).continuous
  have hF : Integrable F (geometricVolume A J α) :=
    hFc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hW (i : C.centers) : Integrable (fun x => (C.partition i x)^2*F x) (geometricVolume A J α) :=
    (((C.partition i).contMDiff.continuous.pow 2).mul hFc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp (x : X) : F x ≤ N * ∑ i : C.centers, (C.partition i x)^2*F x := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : C.centers => C.partition i x)
    rw [C.partition_sum x,one_pow] at h
    have hn : 0 ≤ F x := MetricForms.pairing_self_nonneg (GeometricAdjoint.pointMetric J α ht x) (a.val x)
    simpa only [N,one_mul,Finset.card_univ,Finset.sum_mul,mul_assoc] using mul_le_mul_of_nonneg_right h hn
  have hI := integral_mono hF ((integrable_finsetSum Finset.univ (fun i _ => hW i)).const_mul N) hp
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun i _ => hW i)] at hI
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset C.centers)) => hbound i r hr hr1 f)
  have hsquared : ‖a‖^2 ≤ K * ((r⁻¹)^(2*k+1)*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖)^2 := by
    rw [preL2_norm_sq]
    exact hI.trans ((mul_le_mul_of_nonneg_left hsum hN).trans_eq (by
      simp_rw [mul_pow]
      rw [← Finset.sum_mul,← Finset.sum_mul]
      dsimp [K]
      ring))
  have hroot : (Real.sqrt K*(r⁻¹)^(2*k+1)*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖)^2 =
      K * ((r⁻¹)^(2*k+1)*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖)^2 := by
    rw [mul_assoc,mul_pow,Real.sq_sqrt hK]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  exact hsquared.trans_eq hroot.symm
end HodgeCommutatorCover

lemma hodge_power_commutator_global_bound
    (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
    (hs : IsSmooth α) (ht : Tames α J)
    (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
    (hD : ∀ p : A.centers, tsupport (A.partition p) ⊆ (D p).toData.source)
    (k : ℕ) (hk : k ≤ 2) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (r : ℝ) (_hr : 0 < r), r ≤ 1 →
      ∀ f : PreL2 A J α hs ht true,
        ‖hodgePowerCommutator A J α hs ht (k+1) f‖ ≤
          B*(r⁻¹)^(2*k+1)*‖(hodgeSmoothShift A J α hs ht r ^ 3) f‖ :=
  (hodgeCommutatorCover A J α hs ht D hD k hk).global_bound
end TamingCompatibility.GeometricHilbert

end
end

end
end

end OAI
