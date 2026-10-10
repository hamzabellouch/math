import OAI.Geometry.Relativity.CKS.MixedMassCompact
import OAI.Geometry.Relativity.CKS.MixedSqrtJet

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def foliationDen (p : MassParameter) : ScalarJet :=
  constantJet 1+productJet (powJet p.1.1 3) (coefficientV p.1 p.2)
def lapseCorrection (p : MassParameter) : ScalarJet :=
  -productJet (coefficientV p.1 p.2) (reciprocalJet
    (productJet (sqrtJet (foliationDen p)) (constantJet 1+sqrtJet (foliationDen p))))
def uCorrection (p : MassParameter) : ScalarJet :=
  coefficientD p.1 p.2+lapseCorrection p+
    productJet (powJet p.1.1 3) (productJet (coefficientD p.1 p.2) (lapseCorrection p))
def foliationCoefficients (p : MassParameter) :
    ScalarJet × ScalarJet × (A → ScalarThreeJet) × ScalarJet × ScalarJet :=
  (coefficientD p.1 p.2,coefficientT p.1 p.2,coefficientShift p.1 p.2,lapseCorrection p,uCorrection p)
def foliationRegion : Set MassParameter := massMetricRegion ∩ {p | 0 < massDenominator p}

lemma foliationRegion_open : IsOpen foliationRegion :=
  massDenominator_continuousOn.isOpen_inter_preimage massMetricRegion_open (isOpen_Ioi (a := (0:ℝ)))
lemma foliationRegion_zero {j : MassInput}
    (hj : determinant (fun i k => (j.1 0 i k).1.1) ≠ 0) : (0,j) ∈ foliationRegion := by
  constructor
  · simpa only [massMetricRegion,mem_ofPred_eq,coefficientMetric_zero] using hj
  · simp [massDenominator,constantJet]
lemma foliationDen_smooth {p : MassParameter} (hp : p ∈ foliationRegion) :
    ContDiffAt ℝ ∞ foliationDen p := by
  have hV := coefficientV_smooth hp.1
  unfold foliationDen
  fun_prop
lemma lapseCorrection_smooth {p : MassParameter} (hp : p ∈ foliationRegion) :
    ContDiffAt ℝ ∞ lapseCorrection p := by
  have hd : 0 < (foliationDen p).1 := hp.2
  have hs := (sqrtJet_smooth hd).comp p (foliationDen_smooth hp)
  have hs1 : ContDiffAt ℝ ∞ (fun t : MassParameter => constantJet 1+sqrtJet (foliationDen t)) p := contDiffAt_const.add hs
  have hmul := productJet_contDiffAt hs hs1
  have hpos : 0 < (productJet (sqrtJet (foliationDen p)) (constantJet 1+sqrtJet (foliationDen p))).1 := by
    change 0 < Real.sqrt (foliationDen p).1*(1+Real.sqrt (foliationDen p).1)
    positivity
  have hi := (reciprocalJet_smooth hpos.ne').comp p hmul
  exact (productJet_contDiffAt (coefficientV_smooth hp.1) hi).neg
attribute [local irreducible] lapseCorrection
lemma uCorrection_smooth {p : MassParameter} (hp : p ∈ foliationRegion) :
    ContDiffAt ℝ ∞ uCorrection p := by
  have hd := coefficientD_smooth hp.1
  have hl := lapseCorrection_smooth hp
  unfold uCorrection
  fun_prop
lemma foliationCoefficients_smooth {p : MassParameter} (hp : p ∈ foliationRegion) :
    ContDiffAt ℝ ∞ foliationCoefficients p :=
  (coefficientD_smooth hp.1).prodMk ((coefficientT_smooth hp.1).prodMk
    ((coefficientShift_smooth hp.1).prodMk ((lapseCorrection_smooth hp).prodMk (uCorrection_smooth hp))))

lemma foliation_family_bound {K : Set MassInput} (hK : IsCompact K)
    (hreg : ∀ j ∈ K, determinant (fun i k => (j.1 0 i k).1.1) ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ScalarThreeJet,
      ∀ j ∈ K, ‖z‖ ≤ δ → ‖foliationCoefficients (z,j)‖ ≤ C := by
  let : FiniteDimensional ℝ ScalarThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixThreeJet := inferInstance
  let : FiniteDimensional ℝ MatrixScalarJet := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixThreeJet) := inferInstance
  let : FiniteDimensional ℝ (Fin 3 → MatrixScalarJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarThreeJet) := inferInstance
  let : FiniteDimensional ℝ (A → ScalarJet) := inferInstance
  let : FiniteDimensional ℝ MassInput := inferInstance
  let : ProperSpace MassParameter := FiniteDimensional.proper ℝ MassParameter
  let K₀ : Set MassParameter := (fun j : MassInput => ((0:ScalarThreeJet),j)) '' K
  have hK₀ : IsCompact K₀ := hK.image (by fun_prop)
  have hs : K₀ ⊆ foliationRegion := by
    rintro p ⟨j,hj,rfl⟩
    exact foliationRegion_zero (hreg j hj)
  obtain ⟨δ,hδ,hδs⟩ := hK₀.exists_cthickening_subset_open foliationRegion_open hs
  obtain ⟨C,hC⟩ := (hK₀.cthickening (r := δ)).exists_bound_of_continuousOn
    (fun p hp => (foliationCoefficients_smooth (hδs hp)).continuousAt.continuousWithinAt)
  refine ⟨δ,hδ,max C 0,le_max_right _ _,?_⟩
  intro z j hj hz
  apply (hC (z,j) ?_).trans (le_max_left _ _)
  apply Metric.mem_cthickening_of_dist_le (z,j) (0,j) δ K₀ ⟨j,hj,rfl⟩
  simpa only [Prod.dist_eq,dist_zero_right,dist_self,max_eq_left (norm_nonneg z)] using hz

theorem cks_foliation_coefficients_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0) (B : ℝ) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      ∀ z : ScalarThreeJet, ∀ j : MassInput, R₀ ≤ r → ‖z‖ ≤ 1/r →
      j.1 0 ∈ K → ‖j‖ ≤ B → ‖foliationCoefficients (z,j)‖ ≤ C := by
  obtain ⟨δ,hδ,C,hC,hh⟩ := foliation_family_bound (boundedMassFamily_compact hK B)
    (fun j hj => hreg _ hj.1)
  refine ⟨max 1 (1/δ),le_max_left _ _,C,hC,?_⟩
  intro r z j hr hz hq hj
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hr)
  have hd : 1/r ≤ δ := by
    apply (div_le_iff₀ hr0).mpr
    simpa only [mul_comm] using ((div_le_iff₀ hδ).mp ((le_max_right _ _).trans hr))
  exact hh z j (boundedMassFamily_mem hq hj) (hz.trans hd)

end
end CKSMixedGeometry

end

end OAI
