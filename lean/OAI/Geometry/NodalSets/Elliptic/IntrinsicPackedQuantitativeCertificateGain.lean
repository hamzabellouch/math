import OAI.Geometry.NodalSets.Charts.IntrinsicPackedGlobalSphereStage
import OAI.Geometry.NodalSets.Charts.SphereEnergyCompletion
import OAI.Geometry.NodalSets.Charts.SupportedFiniteAtlasBounds
import OAI.Geometry.NodalSets.Coefficients.IntrinsicCoefficientNeighborhood
import OAI.Geometry.NodalSets.Hausdorff.EnvelopeNodalGain

namespace OAI

namespace Yau.Target
open MeasureTheory Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicGlobalSphereStageLocalInst1 intrinsicGlobalSphereStageLocalInst2 intrinsicGlobalSphereStageLocalInst3 intrinsicGlobalSphereStageLocalInst4 intrinsicGlobalSphereStageLocalInst5 intrinsicGlobalSphereStageLocalInst6 intrinsicGlobalSphereStageLocalInst7 intrinsicGlobalSphereStageLocalInst8 intrinsicGlobalSphereStageLocalInst9 intrinsicGlobalSphereStageLocalInst10 intrinsicGlobalSphereStageLocalInst11 intrinsicGlobalSphereStageLocalInst12 intrinsicGlobalSphereStageLocalInst13 intrinsicGlobalSphereStageLocalInst14 intrinsicGlobalSphereStageLocalInst15 intrinsicGlobalSphereStageLocalInst16

theorem intrinsic_packed_quantitative_certificate_gain :
    ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
      seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
      ∀ (d : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density),
        (∀ y ∈ closedBall (0 : BaseModel) r,
          dist ((intrinsicChartCoefficient d.tensor d.density seedPoint y,
            fderiv ℝ (intrinsicChartCoefficient d.tensor d.density seedPoint) y) : CoefficientFirstJet BaseModel)
            (roundCoefficientJet y) < δ) →
        ∀ K : Set Base, IsCompact K → K ⊆ seedSpherePatch r →
        (∀ x ∉ K, ∀ v w : AmbientBase,
          ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
          d.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) →
        (∀ x ∉ K, d.density x=1) →
        ∀ L > 0, ∀ T > 0, ∀ (P : Finset Base) (J : ℕ) (eps : ℝ), 0 < eps → ∀ n₀ : ℕ,
          ∃ n : ℕ, n₀ ≤ n ∧ 0 < n ∧
            ∃ (d' : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d'.density),
              sphereCoefficientDistance P J d.tensor d.density d'.tensor d'.density < eps ∧
              (∀ y ∈ closedBall (0 : BaseModel) r,
                dist ((intrinsicChartCoefficient d'.tensor d'.density seedPoint y,
                  fderiv ℝ (intrinsicChartCoefficient d'.tensor d'.density seedPoint) y) : CoefficientFirstJet BaseModel)
                  (roundCoefficientJet y) < δ) ∧
              ∃ K' : Set Base, IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ seedSpherePatch r ∧
                (∀ x ∉ K', ∀ v w : AmbientBase,
                  ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
                  d'.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) ∧
                (∀ x ∉ K', d'.density x=1) ∧
                ∃ u : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u ∧ u ≠ 0 ∧
                  (∀ p y, -intrinsicWeightedChartOperator d'.tensor d'.density u p y =
                    seedEigenvalue n*u ((extChartAt (𝓡 4) p).symm y)) ∧
                  ∃ (S : Yau.Jets.Coord → ℝ) (U : Set Yau.Jets.Coord) (M : ℝ),
                    0 < M ∧ 8*(n:ℝ)*L*T < M ∧ U ⊆ seedCoordPatch r ∧
                    LiteralNodalCertificate (intrinsicSeedCoordMetric d.tensor d.density)
                      S (seedCoordCube a) U n (fun x ↦ u (seedSphereFromCoord x)) M := by
  obtain ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,hstage⟩ := intrinsic_packed_global_sphere_stage
  refine ⟨r,a,δ,hr,ha,hδ,hcube,hbranch,?_⟩
  intro d hd hclose K hK hKP hA hrho L hL T hT P J eps heps n₀
  obtain ⟨eta,heta,hpres⟩ := intrinsic_coefficient_neighborhood_preserved
    d.tensor d.smooth d.symm d.pos d.density hd hr.le hclose
  obtain ⟨Cf,hCf,hbound⟩ := supported_finite_atlas_coefficient_bound r P J
  let e : ℝ := min eta (eps/Cf)/2
  have he : 0 < e := by dsimp [e]; positivity
  have heeta : e ≤ eta := by have := min_le_left eta (eps/Cf); dsimp [e]; linarith
  have hCfe : Cf*e < eps := by
    have h := min_le_right eta (eps/Cf)
    have hdv : 0 < eps/Cf := div_pos heps hCf
    have he' : e < eps/Cf := by dsimp [e]; linarith
    simpa [mul_comm] using (lt_div_iff₀ hCf).mp he'
  obtain ⟨c,hc,cn,hcn,hstage⟩ := hstage d.tensor d.smooth d.symm d.pos d.density hd d.positive
    hclose K hK hKP hA hrho
  let Tg := 8*L*T/c+1
  have hTg : 0 < Tg := by dsimp [Tg]; positivity
  obtain ⟨w,b,hb,C,hC,Q,Qw,hQw,hQwΩ,hQ,hQΩ,hUQ,hKQ,hselect⟩ := hstage Tg (max J 1)
  obtain ⟨n,hn,hnSmall,hnlarge,hn0⟩ := (hselect.and ((eventually_inverse_square_small C e he).and
    ((eventually_ge_atTop n₀).and (eventually_gt_atTop (0:ℕ))))).exists
  obtain ⟨hfin,coeff,hcoeff,hu,hjet,hmeasure,hpacking,hf,halpha,hbeta,has,hbs,hsize,heq,
    ug,ag,bg,hug,hugs,hugval,hag,hbg,hags,hbgs,hagval,hbgval,hagB,hbgB,
    hnew,hnewSym,hnewPos,hrnew,hrnewPos,hugne,hfixed,htensor,hall,
    hlifts,hliftne,hlifte,hlam,hnodal,hrobust⟩ := hn
  let := hfin
  let K' := K ∪ seedSphereFromCoord '' (Q ∪ Qw)
  have hK' : IsCompact K' := hK.union ((hQ.union hQw).image seedSphereFromCoord_continuous)
  have hK'P : K' ⊆ seedSpherePatch r := by
    rintro x (hx | ⟨y,hy,rfl⟩)
    · exact hKP hx
    · have hyΩ : y ∈ w.Ω := hy.elim (fun h ↦ hQΩ h) (fun h ↦ hQwΩ h)
      exact ⟨seedCoordEquiv y,w.closure_Ω_patch (subset_closure hyΩ),rfl⟩
  have haK : tsupport ag ⊆ K' := hags.trans ((image_mono subset_union_left).trans subset_union_right)
  have hbK : tsupport bg ⊆ K' := hbgs.trans ((image_mono subset_union_left).trans subset_union_right)
  have hscalar : ∀ x i, i ≤ max J 1 →
      ‖iteratedFDeriv ℝ i (fun y ↦ ag (seedSphereFromCoord y)) x‖ +
      ‖iteratedFDeriv ℝ i (fun y ↦ bg (seedSphereFromCoord y)) x‖ < e := by
    intro x i hi
    simp_rw [hagval,hbgval]
    exact (hsize x i hi).trans_lt hnSmall
  have hagb : ∀ x i, i ≤ max J 1 →
      ‖iteratedFDeriv ℝ i (fun y ↦ ag (seedSphereFromCoord y)) x‖ ≤ e := by
    intro x i hi
    have h := hscalar x i hi
    have h0 := norm_nonneg (iteratedFDeriv ℝ i (fun y ↦ bg (seedSphereFromCoord y)) x)
    linarith
  have hbgb : ∀ x i, i ≤ max J 1 →
      ‖iteratedFDeriv ℝ i (fun y ↦ bg (seedSphereFromCoord y)) x‖ ≤ e := by
    intro x i hi
    have h := hscalar x i hi
    have h0 := norm_nonneg (iteratedFDeriv ℝ i (fun y ↦ ag (seedSphereFromCoord y)) x)
    linarith
  let d' : SphereEnergyData := ⟨_,hnew,hnewSym,hnewPos,_,hrnew.continuous,hrnewPos⟩
  refine ⟨n,hnlarge,hn0,d',hrnew,?_,?_,K',hK',subset_union_left,hK'P,?_,?_,
    ug,hug,hugne,hall,?_⟩
  · exact (hbound d.tensor d.density ag bg hag hbg (haK.trans hK'P) (hbK.trans hK'P)
      e he.le (fun x i hi ↦ hagb x i (hi.trans (le_max_left _ _)))
      (fun x i hi ↦ hbgb x i (hi.trans (le_max_left _ _)))).trans_lt hCfe
  · exact hpres ag bg hag hbg
      (fun x i hi ↦ (hbgb x i (hi.trans (le_max_right _ _))).trans heeta)
      (fun x i j k hi ↦ ((htensor x i j k (hi.trans (le_max_right _ _))).trans hnSmall.le).trans heeta)
  · intro x hx v z hv hz
    change (d.tensor x+roundTensorPerturbation ag x) _ _ = _
    rw [roundTensorPerturbation_zero ag x (fun h ↦ hx (haK h)),add_zero]
    exact hA x (fun h ↦ hx (Or.inl h)) v z hv hz
  · intro x hx
    change d.density x+bg x=1
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hbK h)),add_zero]
    exact hrho x (fun h ↦ hx (Or.inl h))
  · have hreg := intrinsicSeedCoordMetric_regular d.tensor d.smooth d.symm d.pos d.density hd d.positive
    have hgain := w.gain_lt_sign_integral b hreg.1 hreg.2.2
    let I := ∫ x in seedCoordCube a, sourceSignScale (intrinsicSeedCoordMetric d.tensor d.density) w.S x
    have hI : 0 < I := hTg.trans hgain
    have hnreal : (0:ℝ) < n := by exact_mod_cast hn0
    refine ⟨w.S,w.U,c*((n:ℝ)*I),mul_pos hc (mul_pos hnreal hI),?_,?_,?_⟩
    · have hh := mul_lt_mul_of_pos_left hgain hc
      have heq : c*Tg=8*L*T+c := by dsimp [Tg]; field_simp
      rw [heq] at hh
      have hh' : 8*L*T < c*I := by change 8*L*T+c<c*I at hh; linarith
      have hn' := mul_lt_mul_of_pos_left hh' hnreal
      nlinarith only [hn']
    · exact subset_closure.trans (w.closure_U_Ω.trans (subset_closure.trans w.closure_Ω_patch))
    · simpa only [hugval] using hpacking

end
end Yau.Target

end OAI
