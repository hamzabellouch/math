import OAI.Geometry.Relativity.CKS.CKSCollarSourceData
import OAI.Geometry.Relativity.CKS.CKSPhysicalSmooth
import OAI.Geometry.Relativity.CKS.CollarLogRegular
import OAI.Geometry.Relativity.CKS.CollarFieldRegion

namespace OAI

noncomputable section
namespace CKSAngularSlice
noncomputable section
open CKSCalculus Set Filter
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def restrictMatrixThree (q : CKSMixedGeometry.MatrixThreeJet) : CKSAngularGeometry.MatrixScalarJet :=
  fun a b => restrictJet (q a b).1

lemma restrictMatrixThree_continuous : Continuous restrictMatrixThree := by
  unfold restrictMatrixThree restrictJet
  fun_prop

lemma sigma_slice_jets {f : MP → CKSAngularGeometry.Mat} {ρ : ℝ} {x : AP}
    (hf : ContDiffAt ℝ 3 f (slice ρ x)) :
    CKSAngularGeometry.matrixScalarJets (fun y => f (slice ρ y)) x=
      restrictMatrixThree (CKSMixedGeometry.matrixThreeJets f (slice ρ x)) := by
  funext a b
  exact actualScalarJet_slice ρ ((CKSMixedGeometry.component_diff hf a b).of_le (by norm_num))

end
end CKSAngularSlice

end

noncomputable section
namespace CKSAngularGeometry
noncomputable section
open scoped Matrix.Norms.Elementwise
lemma CollarCoefficientFields.ThinBoundedAt.mono {f : CollarCoefficientFields} {x : Point}
    {B C : ℝ} (hf : f.ThinBoundedAt B x) (hBC : B ≤ C) : f.ThinBoundedAt C x := by
  rcases hf with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩
  exact ⟨fun i => (h1 i).trans hBC,h2.trans hBC,h3.trans hBC,
    fun i hi => (h4 i hi).trans hBC,h5.trans hBC,h6.trans hBC,h7.trans hBC,
    h8.trans hBC,h9.trans hBC,h10.trans hBC⟩
end
end CKSAngularGeometry

end

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix CKSAngularSlice
open CKSAngularGeometry (determinant determinant_eq)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

lemma logQError_scaled (f : MassFields) (x : Point) :
    logQError f x=(1/Real.exp (x 0)^2) • logGamma f x-f.sigma x := by
  funext a b
  simp only [logQError,logGamma,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  rw [show (-3:ℝ)=-(3:ℕ) by norm_num,show (-2:ℝ)=-(2:ℕ) by norm_num,
    radiusPower_neg_nat,radiusPower_neg_nat]
  field_simp
  ring

lemma logQError_symmetric {f : MassFields} {x : Point} (hp : (logMetric f x).PosDef)
    (hs : (f.sigma x).PosDef) : logQError f x 1 0=logQError f x 0 1 := by
  have hγ := (CKSAngularGeometry.metricBlock_leaf_posDef hp).isHermitian.eq
  have hσ := hs.isHermitian.eq
  have hγ' : logGamma f x 1 0=logGamma f x 0 1 := by
    simpa only [Matrix.conjTranspose_apply,star_trivial] using congrFun (congrFun hγ 0) 1
  have hσ' : f.sigma x 1 0=f.sigma x 0 1 := by
    simpa only [Matrix.conjTranspose_apply,star_trivial] using congrFun (congrFun hσ 0) 1
  rw [logQError_scaled]
  change (1/Real.exp (x 0)^2)*logGamma f x 1 0-f.sigma x 1 0 =
    (1/Real.exp (x 0)^2)*logGamma f x 0 1-f.sigma x 0 1
  rw [hγ',hσ']

theorem cks_coordinate_collar_DEC {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, Matrix.PosDef (fun i k => (q i k).1.1))
    {B A P : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) (hP : 0 ≤ P) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ (f : TensorFields) (ρ : ℝ) (x : AP),
      R₀ ≤ Real.exp ρ → f.RegularAt (slice ρ x) →
      ContDiffAt ℝ 3 f.base.mK (slice ρ x) → ContDiffAt ℝ 3 f.base.ek (slice ρ x) →
      (∀ᶠ y in 𝓝 (slice ρ x), (logMetric f.base y).PosDef) →
      matrixThreeJets f.base.sigma (slice ρ x) ∈ K → f.LogComponentBound B (slice ρ x) →
      ∀ b : Fin 5 → ℝ, ‖b‖ ≤ P → b 0=1/Real.exp ρ → 0 ≤ b 4 →
      (∀ i, i ≠ 0 → |b i| ≤ A*b 4) →
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput (CKSAngularGeometry.oldParams b) ((sourceCollarData f).angular ρ) x) (Real.exp ρ) →
      CKSAngularGeometry.coordinateDEC
        (CKSAngularGeometry.fieldNullInput b ((sourceCollarData f).angular ρ) x) (Real.exp ρ) := by
  have hd (q) (hq : q ∈ K) : determinant (fun i k => (q i k).1.1) ≠ 0 := by
    exact (CKSAngularGeometry.determinant_eq (fun i k => (q i k).1.1)).symm ▸ (hreg q hq).det_pos.ne'
  obtain ⟨R,hR,C,hC,hcoeff⟩ := cks_sourceCollarData_bounded hK hd hB
  let L := restrictMatrixThree '' K
  have hL : IsCompact L := hK.image restrictMatrixThree_continuous
  have hpos : ∀ q ∈ L, CKSAngularGeometry.positiveAngular (fun i k => (q i k).1) := by
    rintro _ ⟨q,hq,rfl⟩
    refine ⟨(hreg q hq).diag_pos,?_⟩
    change 0 < determinant (fun i k => (q i k).1.1)
    exact (CKSAngularGeometry.determinant_eq (fun i k => (q i k).1.1)).symm ▸ (hreg q hq).det_pos
  let T := max P (2*C)
  have hT : 0 ≤ T := hP.trans (le_max_left _ _)
  obtain ⟨S,hS,hDEC⟩ := CKSAngularGeometry.bounded_thin_coordinate_DEC hL hpos hT hA
  refine ⟨max R S,hR.trans (le_max_left _ _),?_⟩
  intro f ρ x hr hf hmk hek hp hs hb b hbp hz hw hparams hold
  have hrR : R ≤ Real.exp ρ := (le_max_left _ _).trans hr
  have hrS : S ≤ Real.exp ρ := (le_max_right _ _).trans hr
  have hsig : (f.base.sigma (slice ρ x)).PosDef := hreg _ hs
  have hsd : determinant (f.base.sigma (slice ρ x)) ≠ 0 := hd _ hs
  have hsource := sourceCollarData_regular hf hp hsd
  have hfield := angular_regular hsource (logTError_three_diff hf.base hmk hek hp.self_of_nhds)
  have hbound := hcoeff f (slice ρ x) (by simpa only [slice_zero] using hrR) hf hp hs hb
  have hthin := angular_thin_bounded hC (hR.trans hrR) hsource hbound
  have hmem : CKSAngularGeometry.matrixScalarJets (((sourceCollarData f).angular ρ).metric 0) x ∈ L := by
    change CKSAngularGeometry.matrixScalarJets (fun y => f.base.sigma (slice ρ y)) x ∈ L
    rw [sigma_slice_jets hf.base.sigma]
    exact ⟨_,hs,rfl⟩
  apply hDEC b _ x hfield hmem (hbp.trans (le_max_left _ _))
    (hthin.mono (le_max_right _ _)) (Real.exp ρ) hrS hz hw hparams
  · change f.base.sigma (slice ρ x) 1 0=f.base.sigma (slice ρ x) 0 1
    simpa only [Matrix.conjTranspose_apply,star_trivial] using congrFun (congrFun hsig.isHermitian.eq 0) 1
  · change Real.exp ρ^3*logQError f.base (slice ρ x) 1 0=Real.exp ρ^3*logQError f.base (slice ρ x) 0 1
    rw [logQError_symmetric hp.self_of_nhds hsig]
  · exact hold

end
end CKSMixedGeometry

end

end OAI
