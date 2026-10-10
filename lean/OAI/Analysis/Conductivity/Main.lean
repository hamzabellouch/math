import Mathlib
import OAI.Analysis.Conductivity.Sources.WeightedGaugeDN
import OAI.Analysis.Conductivity.Sobolev.CriticalWallParticularC0
import OAI.Analysis.Conductivity.Fourier.PoissonGreen
import OAI.Analysis.Conductivity.Walls.SeamCubicRate
import OAI.Analysis.Conductivity.Walls.PhysicalCollarCutoff
import OAI.Analysis.Conductivity.Geometry.CylinderPhysicalEquiv
import OAI.Analysis.Conductivity.Branching.ChildFullEndEnergy
import OAI.Analysis.Conductivity.Variational.BoundedPiolaCorrection
import OAI.Analysis.Conductivity.Geometry.RegularPatchLinear
import OAI.Analysis.Conductivity.Variational.PhysicalCentralRegularPair
import OAI.Analysis.Conductivity.Fourier.GeneralModeRecombinedEnding
import OAI.Analysis.Conductivity.Geometry.RegularPatchCoordinates
import OAI.Analysis.Conductivity.Variational.CentralCorrectedRepresentative
import OAI.Analysis.Conductivity.Branching.PhysicalBlockRepresentative
import OAI.Analysis.Conductivity.Sources.PhysicalPatching
import OAI.Analysis.Conductivity.Sources.IteratedAverages

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma WeightedAnnihilation.smul {a : R3 → ℝ} {w u : H1} {c : ℝ}
    (hw : WeightedAnnihilation a w u c) (δ : ℝ) :
    WeightedAnnihilation a (δ • w) u c := by
  intro f hf hc hs
  calc
    (∫ x,a x*inner ℝ (weakGradient (δ • w) x)
      ((weakValue u x-c) • gradient f x+f x • weakGradient u x) ∂ballMeasure)=
        ∫ x,δ*(a x*inner ℝ (weakGradient w x)
          ((weakValue u x-c) • gradient f x+f x • weakGradient u x)) ∂ballMeasure := by
      apply integral_congr_ae
      filter_upwards [weakGradient_smul δ w] with x hx
      rw [hx,Pi.smul_apply,real_inner_smul_left]
      ring
    _=0 := by rw [integral_const_mul,hw f hf hc hs,mul_zero]

theorem actual_nested_weighted_source_exists :
    ∃ (a : R3 → ℝ) (c C : ℝ) (w : H1),
      Measurable a ∧ 0<c ∧ c<C ∧
      (∀ᵐ x∂ballMeasure,c ≤ a x ∧ a x ≤ C) ∧ EqualOneNearBoundary a ∧
      w∈H10 ∧ (∀ᵐ x∂ballMeasure,abs (weakValue w x) ≤ 1/2) ∧
      0<ballMeasure {x | weakValue w x≠0} ∧
      (∀ᵐ x∂ballMeasure,(5/2:ℝ)<‖x‖ → weakValue w x=0 ∧ weakGradient w x=0) ∧
      ∀ u : H1,Harmonic a u → (∃ M : ℝ,∀ᵐ x∂ballMeasure,abs (weakValue u x) ≤ M) →
        ∃ d : ℝ,WeightedAnnihilation a w u d := by
  let r : BoundedRootSources := Classical.choice boundedRootSources_nonempty
  obtain ⟨w,hw,⟨M,hM,hMb⟩,ht⟩ := r.nested_source_limit_exists
  let δ : ℝ := 1/(2*M)
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδM : δ*M=1/2 := by dsimp [δ]; field_simp
  have hwne := r.nested_source_nonzero ht
  have hvne : δ • w.val≠(0:H1) := smul_ne_zero hδ.ne' hwne.1
  refine ⟨r.coefficient,min r.c 1,max r.C 1+1,δ • w.val,
    r.coefficient_measurable,lt_min r.c_pos (by norm_num),?_,?_,
    copiedScalarCoefficient_collar r.b,H10.smul_mem δ w.property,?_,
    nonzero_h1_positive_value_measure hvne,sourceSupported_collar (hw.smul δ),?_⟩
  · have hmin := min_le_left r.c 1
    have hmax := le_max_left r.C 1
    have hcc := r.c_lt_C
    linarith
  · exact Eventually.of_forall (fun x => ⟨(copiedScalarCoefficient_bounds r.bounds x).1,
      (copiedScalarCoefficient_bounds r.bounds x).2.trans (by linarith)⟩)
  · have hh := weakValue_bound_smul hMb δ
    simpa only [abs_of_pos hδ,hδM] using hh
  · intro u hu hb
    exact ⟨sourceMeanCLM 0 u,(r.nested_source_weighted ht hu hb).smul δ⟩

theorem main_nonuniqueness : MainStatement := by
  obtain ⟨a,c,C,w,ha,hc,hcC,hab,hnear,hw0,hw,hwne,hsupp,hweighted⟩ :=
    actual_nested_weighted_source_exists
  exact MainStatement_of_weighted_source a ha c C hc hcC hab hnear w hw0 hw hwne
    (5/2) (by norm_num) (by norm_num) hsupp hweighted

end ScalarConductivity

end
end

end OAI
