import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalJoin
import OAI.Analysis.Conductivity.Sobolev.FiniteEndPhysicalH1
import OAI.Analysis.Conductivity.Branching.PhysicalNullTransport
import OAI.Analysis.Conductivity.Geometry.PhysicalCollarRegularity
import OAI.Analysis.Conductivity.Geometry.RegularPatchCoordinates
import OAI.Analysis.Conductivity.Variational.FlatSpliceRegularity

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
open scoped Matrix.Norms.Elementwise

lemma branchCollar_regular_ae {s : Fin 3 → ℝ} {f : Fin 2 → TorusL2}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (i : Fin 3) (z : TorusEndingData s (branchNormalize i f))
    {a b l r : ℝ} (ha : a≠0) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Ioo l r,0<a*(t-b)) :
    ∀ᵐ y∂volume.restrict (sourceClosedCollarBand l r),
      y∈regularRegion (variableCollarField (fun x j => branchSplicedField i z j x) a b)
        (fun x => ⟨variableCollarTensor (branchSplicedTensor i z) a b x,
          variableCollarTensor_symm (branchSplicedTensor_symm i z) a b x⟩) univ := by
  apply sourceClosedCollarBand_ae_faces hl hr
  intro m n
  have hh := sourceFaceAngles_ae (flatEndCoordinates_ae ha b (branchSpliced_regular hs i z)) m n
  filter_upwards [ae_restrict_of_ae hh,sourceExtendedBox_open_ae hl hr,
    sourceExtendedBox_axial_strict_ae l r] with x hx hxo hxt
  have hh := variableCollar_regular_at (branchSplicedTensor_symm i z) ha b m n hxo
    (hx (hT _ hxt))
  exact mem_regularRegion_congr_nhds hh Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl
    isOpen_univ (mem_univ _)

lemma sourceChildInverse_fderiv_surjective (k : Fin 2) (y : Coord3) :
    Function.Surjective (fderiv ℝ (sourceChildHomeomorph (actualChildSign k)).symm y) := by
  rw [(sourceChildInverse_hasFDeriv _ y).fderiv]
  intro v
  refine ⟨sourceChildDerivative v,?_⟩
  rw [sourceChildInverseDerivative_apply,sourceChildDerivative_apply]
  ext i
  fin_cases i <;> simp only [Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] <;> norm_num [sourceScale]

lemma sourceChildTensorPush_contDiffOn (k : Fin 2) {K : Coord3 → Mat3} {U : Set Coord3}
    (hK : ContDiffOn ℝ (↑(⊤:ℕ∞)) K U) :
    ContDiffOn ℝ (↑(⊤:ℕ∞)) (sourceChildTensorPush k K)
      ((sourceChildHomeomorph (actualChildSign k)).symm ⁻¹' U) := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  exact contDiffOn_const.mul (((contDiffOn_pi.mp
    (contDiffOn_pi.mp hK (childAxis i)) (childAxis j))).comp
      (sourceChildInverse_contDiff _).contDiffOn (fun _ hx => hx))

lemma sourceChild_regular_at (k : Fin 2) {u : Coord3 → Fin 2 → ℝ} {K : Coord3 → Mat3}
    (hK : ∀ x,(K x).IsSymm) {U : Set Coord3} {y : Coord3}
    (hy : (sourceChildHomeomorph (actualChildSign k)).symm y∈
      regularRegion u (fun x => ⟨K x,hK x⟩) U) :
    y∈regularRegion (fun x => u ((sourceChildHomeomorph (actualChildSign k)).symm x))
      (fun x => ⟨sourceChildTensorPush k K x,sourceChildTensorPush_symmetric k K hK x⟩)
      ((sourceChildHomeomorph (actualChildSign k)).symm ⁻¹' U) := by
  obtain ⟨O,hOU,hO,hyO⟩ := mem_regularRegion_iff.mp hy
  refine mem_regularRegion_iff.mpr ⟨(sourceChildHomeomorph (actualChildSign k)).symm ⁻¹' O,
    preimage_mono hOU,?_,hyO⟩
  exact RegularPatch.comp hO (hO.1.preimage (sourceChildHomeomorph _).symm.continuous)
    (sourceChildInverse_contDiff _).contDiffOn (fun _ hx => hx)
    (fun x _ => sourceChildInverse_fderiv_surjective k x)
    (sourceChildTensorPush_contDiffOn k hO.2.2.1)

end ScalarConductivity

end


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory

def periodicCorrectionJet (f : Coord3 → ℝ) (a : ℝ) (i : Fin 3) (x : R3) : JetFiber :=
  Fin.cases
    (physicalJet (attachedPeriodicField f a centralThickness (WithLp.ofLp x))
      (fun j => lineDeriv ℝ (attachedPeriodicField f a centralThickness)
        (WithLp.ofLp x) (Pi.single j 1)))
    (fun k => physicalJet
      (attachedPeriodicField f a (-centralThickness)
        ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x)))
      (fun j => sourceScale⁻¹*lineDeriv ℝ (attachedPeriodicField f a (-centralThickness))
        ((sourceChildHomeomorph (actualChildSign k)).symm (WithLp.ofLp x))
        (Pi.single (childAxis j) 1))) i

lemma parentPeriodicCorrection_exists {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : ContDiff ℝ 1 f)
    {τ a : ℝ} (hτ : 0<τ) (hz : ∀ x,x 0<τ → f x=0) (ha : a<0) :
    ∃ d : H1,d∈H10 ∧ H1JetOn d centralPhysical (fun _ => 0) ∧
      H1JetOn d (physicalEndRegion 0) (periodicCorrectionJet f a 0) ∧
      ∀ k : Fin 2,H1JetOn d (physicalEndRegion k.succ) (fun _ => 0) := by
  obtain ⟨d,hd,hdz,hde⟩ := attachedPeriodicCorrection_H10 hp hf
    (a:=a) (b:=centralThickness) (l₀:= -centralThickness/2) (l:=0)
    (r:=centralThickness) (r₀:=2*centralThickness) hτ hz
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
  have hm : H1JetOn d {y | centralThickness ≤ sourceCollarTime y} (fun _ => 0) := by
    apply H1JetOn.zero_of_weak
    filter_upwards [hdz] with x hx hy
    exact hx (mul_nonpos_of_nonpos_of_nonneg ha.le (sub_nonneg.mpr hy))
  exact ⟨d,hd,hm.mono (fun y hy => ((centralPhysical_time_iff y).mp hy).1),
    H1JetOn.of_weak hde,fun k => hm.mono (fun y hy =>
      (show centralThickness≤2*centralThickness by norm_num [centralThickness]).trans
        (physicalChildEnd_parent_time k hy))⟩

lemma childPeriodicCorrection_exists {f : Coord3 → ℝ}
    (hp : AngularPeriodic (2*Real.pi) f) (hf : ContDiff ℝ 1 f)
    {τ a : ℝ} (hτ : 0<τ) (hz : ∀ x,x 0<τ → f x=0) (ha : 0<a) (k : Fin 2) :
    ∃ d : H1,d∈H10 ∧ H1JetOn d centralPhysical (fun _ => 0) ∧
      H1JetOn d (physicalEndRegion k.succ) (periodicCorrectionJet f a k.succ) ∧
      ∀ i : Fin 3,i≠k.succ → H1JetOn d (physicalEndRegion i) (fun _ => 0) := by
  obtain ⟨d,hd,hdz,hde⟩ := attachedPeriodicCorrection_H10 hp hf
    (a:=a) (b:= -centralThickness) (l₀:= -2*centralThickness) (l:= -centralThickness)
    (r:=0) (r₀:=centralThickness/2) hτ hz
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
    (by norm_num [centralThickness]) (by norm_num [centralThickness])
  have hz' : ∀ᵐ x∂ballMeasure, WithLp.ofLp x∈{y | sourceCollarTime y≤-centralThickness} →
      weakValue d x=0 ∧ ∀ j,weakGradient d x j=0 := by
    filter_upwards [hdz] with x hx hy
    exact hx (mul_nonpos_of_nonneg_of_nonpos ha.le (sub_nonpos.mpr hy))
  have hm := H1JetOn.zero_of_weak
    (D:={y | sourceCollarTime ((sourceChildHomeomorph (actualChildSign k)).symm y)≤-centralThickness})
    (childH10Transport_zero_on k ⟨d,hd⟩
    {y | sourceCollarTime y≤-centralThickness} hz')
  refine ⟨childH10Transport k ⟨d,hd⟩,childH10Transport_mem_H10 k _,
    hm.mono (fun y hy => ((centralPhysical_time_iff y).mp hy).2 k),?_,?_⟩
  · exact H1JetOn.of_weak (childH10Transport_local_jet k ⟨d,hd⟩
      (D:=sourceClosedCollarBand (-centralThickness) 0)
      (fun y hy => sourceBand_mem_ball ⟨
        (show -(1:ℝ)/100≤-centralThickness by norm_num [centralThickness]).trans hy.1,
        hy.2.trans (by norm_num)⟩)
      (attachedPeriodicField f a (-centralThickness))
      (fun y j => lineDeriv ℝ (attachedPeriodicField f a (-centralThickness)) y (Pi.single j 1)) hde)
  · exact fun i hik => hm.mono (fun y hy =>
      (physicalOtherEnd_child_time k i hik hy).le.trans (by norm_num [centralThickness]))

theorem triplePeriodicCorrection_exists (f : Fin 3 → Coord3 → ℝ)
    (hp : ∀ i,AngularPeriodic (2*Real.pi) (f i)) (hf : ∀ i,ContDiff ℝ 1 (f i))
    (τ a : Fin 3 → ℝ) (hτ : ∀ i,0<τ i) (hz : ∀ i x,x 0<τ i → f i x=0)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) :
    ∃ d : H1,d∈H10 ∧ H1JetOn d centralPhysical (fun _ => 0) ∧
      ∀ i,H1JetOn d (physicalEndRegion i) (periodicCorrectionJet (f i) (a i) i) := by
  obtain ⟨dp,hdp,hpc,hpe,hpo⟩ := parentPeriodicCorrection_exists (hp 0) (hf 0) (hτ 0) (hz 0) ha₀
  have hex (k : Fin 2) := childPeriodicCorrection_exists (hp k.succ) (hf k.succ)
    (hτ k.succ) (hz k.succ) (ha k) k
  choose dc hdc hcc hce hco using hex
  refine ⟨dp+(dc 0+dc 1),H10.add_mem hdp (H10.add_mem (hdc 0) (hdc 1)),
    hpc.add_zero ((hcc 0).add_zero (hcc 1)),?_⟩
  intro i
  fin_cases i
  · exact hpe.add_zero ((hco 0 0 (by decide)).add_zero (hco 1 0 (by decide)))
  · exact (hpo 0).zero_add ((hce 0).add_zero (hco 1 1 (by decide)))
  · exact (hpo 1).zero_add ((hco 0 2 (by decide)).zero_add (hce 1))

end ScalarConductivity

end

end OAI
