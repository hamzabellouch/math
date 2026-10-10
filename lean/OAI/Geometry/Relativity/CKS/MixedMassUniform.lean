import OAI.Geometry.Relativity.CKS.MixedMassCoefficient

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant determinant_smooth)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def massMetricRegion : Set (MassParameter) :=
  {p | determinant (fun i k => (coefficientMetric p.1 p.2 i k).1.1) ≠ 0}

def massDenominator (p : MassParameter) : ℝ :=
  (constantJet 1+productJet (powJet p.1.1 3) (coefficientV p.1 p.2)).1

def massRegion : Set (MassParameter) := massMetricRegion ∩ massDenominator ⁻¹' ({0}ᶜ)

lemma massMetricRegion_open : IsOpen massMetricRegion := by
  have hf : Continuous (fun q : MatrixThreeJet => determinant (fun i k => (q i k).1.1)) :=
    determinant_smooth.continuous.comp (by fun_prop)
  exact isOpen_ne_fun (hf.comp coefficientMetric_smooth.continuous) continuous_const

lemma massDenominator_continuousOn : ContinuousOn massDenominator massMetricRegion := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  have hV := (coefficientV_smooth hp).continuousAt
  unfold massDenominator
  have hp : ContinuousAt (fun t : MassParameter => powJet t.1.1 3) p :=
    (powJet_smooth 3).continuous.continuousAt.comp ((continuousAt_fst).fst)
  exact (continuousAt_const.add (productJet_smooth.continuous.continuousAt.comp (hp.prodMk hV))).fst

lemma massRegion_open : IsOpen massRegion :=
  massDenominator_continuousOn.isOpen_inter_preimage massMetricRegion_open isOpen_compl_singleton

lemma massRegion_zero {j : MassInput}
    (hj : determinant (fun i k => (j.1 0 i k).1.1) ≠ 0) : (0,j) ∈ massRegion := by
  refine ⟨?_,?_⟩
  · simpa [massMetricRegion,coefficientMetric_zero] using hj
  · simp [massDenominator,constantJet]

lemma massRegion_locallyLipschitz : LocallyLipschitzOn massRegion
    (fun p : MassParameter => cksMassJet p.1 p.2) := by
  intro p hp
  have hdiff := (cksMassJet_smooth hp.1 hp.2).of_le (by simp : (1:ℕ∞ω) ≤ ∞)
  obtain ⟨C,u,hu,hC⟩ := hdiff.exists_lipschitzOnWith
  exact ⟨C,u,mem_nhdsWithin_of_mem_nhds hu,hC⟩

lemma mass_uniform_lipschitz {K : Set MassInput} (hK : IsCompact K)
    (hreg : ∀ j ∈ K, determinant (fun i k => (j.1 0 i k).1.1) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ≥0, LipschitzOnWith C
      (fun p : MassParameter => cksMassJet p.1 p.2)
      (Metric.cthickening δ ((fun j : MassInput => ((0:ScalarThreeJet),j)) '' K)) := by
  let : FiniteDimensional ℝ ScalarThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixScalarJet := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixThreeJet) := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixScalarJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarThreeJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarJet) := inferInstance
  let : FiniteDimensional ℝ MassInput := inferInstance
  let : ProperSpace (MassParameter) := FiniteDimensional.proper ℝ (MassParameter)
  let K₀ : Set (MassParameter) := (fun j : MassInput => ((0:ScalarThreeJet),j)) '' K
  have hK₀ : IsCompact K₀ := hK.image (by fun_prop)
  have hsub : K₀ ⊆ massRegion := by
    rintro p ⟨j,hj,rfl⟩
    exact massRegion_zero (hreg j hj)
  obtain ⟨δ,hδ,hδsub⟩ := hK₀.exists_cthickening_subset_open massRegion_open hsub
  exact ⟨δ,hδ,(massRegion_locallyLipschitz.mono hδsub).exists_lipschitzOnWith_of_compact
    (hK₀.cthickening (r := δ))⟩

lemma parameter_lipschitz_zero_estimate {Z E F : Type*} [NormedAddCommGroup Z]
    [NormedAddCommGroup E] [NormedAddCommGroup F] {f : Z × E → F} {K : Set E} {δ : ℝ} {C : ℝ≥0}
    (hC : LipschitzOnWith C f (Metric.cthickening δ ((fun j : E => ((0:Z),j)) '' K)))
    {z : Z} {j : E} (hj : j ∈ K) (hz : ‖z‖ ≤ δ) :
    ‖f (z,j)-f (0,j)‖ ≤ (C:ℝ)*‖z‖ := by
  let K₀ : Set (Z × E) := (fun j : E => ((0:Z),j)) '' K
  have hj₀ : (0,j) ∈ K₀ := ⟨j,hj,rfl⟩
  have hzero : ((0:Z),j) ∈ Metric.cthickening δ K₀ := (Metric.self_subset_cthickening K₀) hj₀
  have hzj : (z,j) ∈ Metric.cthickening δ K₀ := by
    apply Metric.mem_cthickening_of_dist_le (z,j) (0,j) δ K₀ hj₀
    simpa only [Prod.dist_eq,dist_zero_right,dist_self,max_eq_left (norm_nonneg z)] using hz
  have hh := hC.norm_sub_le hzj hzero
  have heq : ‖(z,j)-((0:Z),j)‖ = ‖z‖ := by
    change max ‖z-0‖ ‖j-j‖ = ‖z‖
    rw [sub_zero,sub_self,norm_zero,max_eq_left (norm_nonneg z)]
  rwa [heq] at hh

attribute [local irreducible] cksMassJet leadingMassJet

theorem cks_mass_uniform {K : Set MassInput} (hK : IsCompact K)
    (hreg : ∀ j ∈ K, determinant (fun i k => (j.1 0 i k).1.1) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ScalarThreeJet, ∀ j ∈ K, ‖z‖ ≤ δ →
      ‖cksMassJet z j-leadingMassJet j‖ ≤ C*‖z‖ := by
  obtain ⟨δ,hδ,C,hC⟩ := mass_uniform_lipschitz hK hreg
  refine ⟨δ,hδ,C,C.coe_nonneg,?_⟩
  intro z j hj hz
  have hh : ‖cksMassJet z j-cksMassJet 0 j‖ ≤ (C:ℝ)*‖z‖ :=
    parameter_lipschitz_zero_estimate (E := MassInput) (F := ScalarJet)
      (f := fun p : MassParameter => cksMassJet p.1 p.2) (K := K) (δ := δ) (C := C)
      (z := z) (j := j) hC hj hz
  exact (congrArg (fun v : ScalarJet => ‖cksMassJet z j-v‖) (cksMassJet_zero j).symm).trans_le hh

end
end CKSMixedGeometry

end

end OAI
