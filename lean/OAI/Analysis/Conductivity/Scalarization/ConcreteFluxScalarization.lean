import Mathlib
import OAI.Analysis.Conductivity.Scalarization.UniformMatrixScalarization
import OAI.Analysis.Conductivity.Fourier.FourierFiniteEnding

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal

local instance concreteFluxScalarizationMeasurableSpaceMat3 : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance concreteFluxScalarizationBorelSpaceMat3 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

lemma continuous_memLp_bounded_coord {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    {f : Coord3 → F} (hf : Continuous f) {U : Set Coord3}
    (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U) :
    MemLp f 2 (volume.restrict U) := by
  let : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hUb.measure_lt_top.ne
  obtain ⟨M,hM⟩ := hUb.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.measurable.aestronglyMeasurable M
  filter_upwards [ae_restrict_mem hUm] with x hx
  exact hM x (subset_closure hx)

lemma clm_coord3_expansion (L : Coord3 →L[ℝ] ℝ) (w : Coord3) :
    L w=∑ i,w i*L (Pi.single i 1) := by
  have he : w=∑ i : Fin 3,w i • Pi.single i 1 := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [he]
  simp only [map_sum,map_smul,smul_eq_mul]

theorem scalarization_of_concrete_C1flux
    {v : Coord3 → Fin 2 → ℝ} (hv : ContDiff ℝ 2 v)
    {E : Coord3 → Mat3} (hEm : Measurable E) (hsym : ∀ x,(E x).IsSymm)
    {G : Coord3 → Matrix (Fin 3) (Fin 2) ℝ} (hG : ContDiff ℝ 1 G)
    (hconst : ∀ᵐ x : Coord3,E x*gradientColumns (fderiv ℝ v x)=G x)
    {c C : ℝ} (hc : 0<c) (hcC : c≤C)
    (hb : ∀ x w,c*(w ⬝ᵥ w)≤w ⬝ᵥ (E x*ᵥw) ∧ w ⬝ᵥ (E x*ᵥw)≤C*(w ⬝ᵥ w))
    (hreg : ∀ᵐ x : Coord3,0<x 0 → x∈regularRegion v (fun y => ⟨E y,hsym y⟩) {y : Coord3 | 0<y 0})
    (hweak : ∀ (j : Fin 2) (ψ : SmoothScalar Coord3),HasCompactSupport ψ.val →
      tsupport ψ.val ⊆ {x : Coord3 | 0<x 0} →
      Integrable (fun x => ∑ i,(E x*gradientColumns (fderiv ℝ v x)).col j i*
        (smoothDirection (Pi.single i 1) ψ).val x) ∧
      (∫ x,∑ i,(E x*gradientColumns (fderiv ℝ v x)).col j i*
        (smoothDirection (Pi.single i 1) ψ).val x)=0)
    {U : Set Coord3} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUpos : U⊆{x : Coord3 | 0<x 0}) :
    ∃ (hE : MemLp (voltageGradient v) 2 (volume.restrict U))
      (hF : MemLp (voltageFlux v (fun y => ⟨E y,hsym y⟩)) 2 (volume.restrict U))
      (z : zeroVoltageJets volume U) (F : Lp FieldVector 2 (volume.restrict U)) (s : Coord3 → ℝ),
      Measurable s ∧ MemLp s ∞ (volume.restrict U) ∧
      (∀ᵐ x ∂volume.restrict U,s x∈Icc (laminateLower c C) (laminateUpper C) ∧
        F x=s x • ((hE.toLp _+z.val.2) x)) ∧
      (∀ W∈allVoltageGradients volume U,inner ℝ W F=inner ℝ W (hF.toLp _)) := by
  let A : Coord3 → Symmetric3 := fun y => ⟨E y,hsym y⟩
  let : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hUb.measure_lt_top.ne
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hAm : Measurable A := by
    change @Measurable Coord3 Symmetric3 _ (borel Symmetric3) A
    rw [borel_comap, ← BorelSpace.measurable_eq (α := Mat3)]
    exact hEm.subtype_mk
  have hvg : Continuous (voltageGradient v) :=
    gradientVectorCLM.continuous.comp (hv.continuous_fderiv (by norm_num))
  have hE := continuous_memLp_bounded_coord hvg hUb hU.measurableSet
  have hFg : Continuous (fun x => fieldVector (G x)) := fieldVectorCLM.continuous.comp hG.continuous
  have heq : voltageFlux v A =ᵐ[volume] fun x => fieldVector (G x) := by
    filter_upwards [hconst] with x hx
    exact congrArg fieldVector hx
  have hF : MemLp (voltageFlux v A) 2 (volume.restrict U) :=
    (continuous_memLp_bounded_coord hFg hUb hU.measurableSet).ae_eq
      (heq.filter_mono (ae_mono Measure.restrict_le_self)).symm
  have hw (j : Fin 2) (ψ : Coord3 → ℝ) (hψ : ContDiff ℝ (↑(⊤:ℕ∞)) ψ)
      (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ⊆U) :
      Integrable (fun x => fderiv ℝ ψ x ((conductivityFlux v A x).col j)) ∧
      (∫ x,fderiv ℝ ψ x ((conductivityFlux v A x).col j))=0 := by
    have hh := hweak j ⟨ψ,hψ⟩ hcψ (hsψ.trans hUpos)
    have heqf : (fun x => fderiv ℝ ψ x ((conductivityFlux v A x).col j)) =
        (fun x => ∑ i,(E x*gradientColumns (fderiv ℝ v x)).col j i*
          (smoothDirection (Pi.single i 1) (⟨ψ,hψ⟩ : SmoothScalar Coord3)).val x) := by
      funext x
      rw [clm_coord3_expansion]
      rfl
    rw [heqf]
    exact hh
  have hregU : volume (U\regularRegion v A U)=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hreg] with x hx hh
    exact hh.2 (mem_regularRegion_congr_nhds (hx (hUpos hh.1))
      Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl hU hh.1)
  obtain ⟨z,F,s,hsm,hs,hC⟩ := exact_scalarization_Cauchy_flux volume
    (uniform_laminate_coverage hc hcC).1 (uniform_laminate_coverage hc hcC).2.1
    hUb hU.measurableSet v A hAm hE hF
    (fun j ψ hψ hcψ hsψ => (hw j ψ hψ hcψ hsψ).1)
    (fun j ψ hψ hcψ hsψ => (hw j ψ hψ hcψ hsψ).2) hregU
    (ae_of_all _ (fun x _ => uniform_matrix_laminate_coverage hc hcC (A x) (hb x)))
  refine ⟨hE,hF,z,F,s,hsm,?_,hs,hC⟩
  apply memLp_top_of_bound hsm.aestronglyMeasurable (laminateUpper C)
  filter_upwards [hs] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg ((uniform_laminate_coverage hc hcC).1.le.trans hx.1.1)]
  exact hx.1.2

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal

local instance alignedFourierEndingScalarizationMeasurableSpaceMat3 : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance alignedFourierEndingScalarizationBorelSpaceMat3 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

theorem aligned_fourier_ending_scalarization {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {k : ℤ} (hk : 0<k) {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s ![0,k]+gb≤torusRate s h)
    (hpb : pb ![0,k]=0) {δ : ℝ} (hδ : 0<δ) :
    ∃ p T c C : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧ 7<T ∧ 0<c ∧ c≤C ∧
      ∃ (v : Coord3 → Fin 2 → ℝ) (E : Coord3 → Mat3)
        (hsym : ∀ x,(E x).IsSymm),
        ContDiff ℝ 2 v ∧ Measurable E ∧
        AngularPeriodic (2*Real.pi) v ∧ AngularPeriodic (2*Real.pi) E ∧
        (∀ x w,c*(w ⬝ᵥ w)≤w ⬝ᵥ (E x*ᵥw) ∧ w ⬝ᵥ (E x*ᵥw)≤C*(w ⬝ᵥ w)) ∧
        (∀ x,x 0∈Icc 0 (1/2) → v x=
          ![x 0+flatFourier s (normalizedFourierCoefficients s 0 (10+1/p) a) pa x,
            flatPhaseMode s ![0,k] 0 x+
              flatFourier s (normalizedFourierCoefficients s (torusRate s ![0,k]) (10+1/p) b) pb x]) ∧
        (∀ x,x 0∈Icc 0 (1/2) → E x=flatBackgroundTensor s) ∧
        (∀ x,T≤x 0 → v x=![x 0,0]) ∧
        ∀ (U : Set Coord3),IsOpen U → Bornology.IsBounded U → U⊆{x : Coord3 | 0<x 0} →
          ∃ (hE : MemLp (voltageGradient v) 2 (volume.restrict U))
            (hF : MemLp (voltageFlux v (fun y => ⟨E y,hsym y⟩)) 2 (volume.restrict U))
            (z : zeroVoltageJets volume U) (F : Lp FieldVector 2 (volume.restrict U)) (σ : Coord3 → ℝ),
            Measurable σ ∧ MemLp σ ∞ (volume.restrict U) ∧
            (∀ᵐ x ∂volume.restrict U,σ x∈Icc (laminateLower c C) (laminateUpper C) ∧
              F x=σ x • ((hE.toLp _+z.val.2) x)) ∧
            (∀ W∈allVoltageGradients volume U,inner ℝ W F=inner ℝ W (hF.toLp _)) := by
  obtain ⟨p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hv,hEm,hvp,hEp,⟨hsym,hreg⟩,
    hbound,hvin,hEin,hterm,hr,⟨G,hG,hconst⟩,hw⟩ :=
    aligned_fourier_finite_ending (pa:=pa) hs hk hA hB ha hb hga hgb hra hrb hpb hδ
  refine ⟨p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hsym,hv,hEm,hvp,hEp,hbound,hvin,hEin,hterm,?_⟩
  intro U hU hUb hUpos
  exact scalarization_of_concrete_C1flux hv hEm hsym hG hconst hc hcC hbound hreg hw hU hUb hUpos

end ScalarConductivity

end
end

end OAI
