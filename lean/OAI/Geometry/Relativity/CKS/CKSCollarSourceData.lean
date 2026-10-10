import OAI.Geometry.Relativity.CKS.CKSFoliationMixed
import OAI.Geometry.Relativity.CKS.CKSLeadingBound
import OAI.Geometry.Relativity.CKS.CKSPhysicalRegular
import OAI.Geometry.Relativity.CKS.CollarLogSlices

namespace OAI

noncomputable section
namespace CKSMixedGeometry
noncomputable section
open CKSCalculus Set Filter Matrix
open CKSAngularGeometry (determinant)
open scoped Topology ContDiff NNReal Matrix.Norms.Elementwise

def sourceCollarData (f : TensorFields) : CKSAngularSlice.LogCollarData where
  sigma := f.base.sigma
  metricError := logQError f.base
  shift := logShift f.base
  tError := fun y => logT f.base y-1
  LError := fun y => logOriginalL f y-1
  massError := fun y => logPhysicalMass f.base y-cksLeadingField f.base y
  fstar := cksLeadingField f.base
  etaDivR := fun y a => logOriginalEta f y a/Real.exp (y 0)
  tauDivR2 := fun y a b => logOriginalTau f y a b/Real.exp (y 0)^2

structure TensorFields.LogComponentBound (f : TensorFields) (B : ℝ) (x : Point) : Prop where
  sigma : ‖matrixThreeJets f.base.sigma x‖ ≤ B
  mg : ‖matrixThreeJets f.base.mg x‖ ≤ B
  eg : ‖matrixThreeJets f.base.eg x‖ ≤ B/Real.exp (x 0)^2
  mK : ‖matrixScalarJets f.base.mK x‖ ≤ B
  ek : ‖matrixScalarJets f.base.ek x‖ ≤ B/Real.exp (x 0)^2
  b : ‖fun a => actualThreeJet (fun y => f.base.b y a) x‖ ≤ B/Real.exp (x 0)^3
  mr : ‖actualScalarJet f.base.mr x‖ ≤ B
  err : ‖actualScalarJet f.base.err x‖ ≤ B/Real.exp (x 0)^6
  kr : ‖actualScalarJet f.kr x‖ ≤ B/Real.exp (x 0)^5
  kb : ‖fun a => actualScalarJet (fun y => f.kb y a) x‖ ≤ B/Real.exp (x 0)^3

lemma sourceCollarData_regular {f : TensorFields} {x : Point}
    (hf : f.RegularAt x) (hp : ∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef)
    (hs : determinant (f.base.sigma x) ≠ 0) : (sourceCollarData f).RegularAt x := by
  have hlead := cksLeadingField_diff hf.base hs
  exact ⟨hf.base.sigma,logQError_diff hf.base,logShift_diff hf.base hp.self_of_nhds,
    logTError_diff hf.base hp,logOriginalLError_diff hf hp,
    (logPhysicalMass_diff hf.base hp).sub hlead,hlead,
    logOriginalEtaDiv_diff hf hp,logOriginalTauDiv_diff hf hp⟩

theorem cks_sourceCollarData_bounded {K : Set MatrixThreeJet} (hK : IsCompact K)
    (hreg : ∀ q ∈ K, determinant (fun i k => (q i k).1.1) ≠ 0)
    {B : ℝ} (hB : 0 ≤ B) :
    ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ f : TensorFields, ∀ x : Point,
      R₀ ≤ Real.exp (x 0) → f.RegularAt x →
      (∀ᶠ y in 𝓝 x, (logMetric f.base y).PosDef) → matrixThreeJets f.base.sigma x ∈ K →
      f.LogComponentBound B x → (sourceCollarData f).BoundedAt C x := by
  obtain ⟨Rl,hRl,Cl,hCl,hl⟩ := cks_physical_foliation_mixed hK hreg hB
  obtain ⟨Rt,hRt,Ct,hCt,ht⟩ := cks_physical_tensor_mixed hK hreg hB
  obtain ⟨Rm,hRm,Cm,hCm,hm⟩ := cks_physical_mass_mixed hK hreg hB
  obtain ⟨Cf,hCf,hf⟩ := cks_leading_mixed_bounded hK hreg hB
  let R := max Rl (max Rt Rm)
  let C := 281*B+Cl+Ct+Cm+Cf
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBC : B ≤ C := by dsimp [C]; linarith
  have hqC : 280*B ≤ C := by dsimp [C]; linarith
  have hlC : Cl ≤ C := by dsimp [C]; linarith
  have htC : Ct ≤ C := by dsimp [C]; linarith
  have hmC : Cm ≤ C := by dsimp [C]; linarith
  have hfC : Cf ≤ C := by dsimp [C]; linarith
  refine ⟨R,hRl.trans (le_max_left _ _),C,hC,?_⟩
  intro f x hr hregular hp hs hb
  have hrl : Rl ≤ Real.exp (x 0) := (le_max_left _ _).trans hr
  have hrt : Rt ≤ Real.exp (x 0) := (le_max_left Rt Rm).trans ((le_max_right _ _).trans hr)
  have hrm : Rm ≤ Real.exp (x 0) := (le_max_right Rt Rm).trans ((le_max_right _ _).trans hr)
  have hr1 : 1 ≤ Real.exp (x 0) := hRl.trans hrl
  obtain ⟨_,hT,hS,_,_⟩ := hl f.base x hrl hregular.base hp hs hb.sigma hb.mg hb.eg hb.mK hb.ek hb.b hb.mr hb.err
  obtain ⟨hL,hE,hτ⟩ := ht f x hrt hregular hp hs hb.sigma hb.mg hb.eg hb.mK hb.ek hb.b hb.mr hb.err hb.kr hb.kb
  have hF := hm f.base x hrm hregular.base hp hs hb.sigma hb.mg hb.eg hb.mK hb.ek hb.b hb.mr hb.err
  have hfstar := hf f.base x hregular.base hs hb.sigma hb.mg hb.eg hb.mK hb.ek hb.b hb.mr hb.err
  have hscale {a b : ℝ} (hab : a ≤ b) (n : ℕ) : a/Real.exp (x 0)^n ≤ b/Real.exp (x 0)^n :=
    div_le_div_of_nonneg_right hab (by positivity)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro a b
    exact ((norm_le_pi_norm _ b).trans ((norm_le_pi_norm _ a).trans hb.sigma)).trans hBC
  · intro a b
    exact (logQError_three_bound hB hr1 hregular.base hb.mg hb.eg a b).trans (hscale hqC 3)
  · intro a; exact (hS a).trans (hscale hlC 5)
  · exact hT.trans (hscale hlC 3)
  · exact hL.trans (hscale htC 3)
  · change ‖actualScalarJet (fun y => logPhysicalMass f.base y-cksLeadingField f.base y) x‖ ≤ _
    rw [actualScalarJet_sub (logPhysicalMass_diff hregular.base hp)
      (cksLeadingField_diff hregular.base (hreg _ hs))]
    exact hF.trans (by simpa only [pow_one] using hscale hmC 1)
  · exact hfstar.trans hfC
  · intro a; exact (hE a).trans (hscale htC 3)
  · intro a b; exact (hτ a b).trans (hscale htC 3)

end
end CKSMixedGeometry

end

end OAI
