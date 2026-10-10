import Mathlib
import OAI.Analysis.Conductivity.Variational.C1VoltageApproximation

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal

local instance concreteFluxH1MeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance concreteFluxH1BorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

theorem scalarization_H1_of_concrete_C1flux
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
    ∃ (hu : MemLp v 2 (volume.restrict U))
      (hE : MemLp (voltageGradient v) 2 (volume.restrict U))
      (hF : MemLp (voltageFlux v (fun y => ⟨E y,hsym y⟩)) 2 (volume.restrict U))
      (z : voltageH1Jets volume U) (F : Lp FieldVector 2 (volume.restrict U)) (s : Coord3 → ℝ),
      Measurable s ∧ MemLp s ∞ (volume.restrict U) ∧
      z.val-(hu.toLp _,hE.toLp _)∈zeroVoltageJets volume U ∧
      (∀ᵐ x ∂volume.restrict U,s x∈Icc (laminateLower c C) (laminateUpper C) ∧
        F x=s x • (z.val.2 x)) ∧
      (∀ W : voltageH1Jets volume U,inner ℝ W.val.2 F=inner ℝ W.val.2 (hF.toLp _)) ∧
      (∀ W : zeroVoltageJets volume U,inner ℝ W.val.2 F=0) := by
  let A : Coord3 → Symmetric3 := fun y => ⟨E y,hsym y⟩
  let : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hUb.measure_lt_top.ne
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hAm : Measurable A := by
    change @Measurable Coord3 Symmetric3 _ (borel Symmetric3) A
    rw [borel_comap, ← BorelSpace.measurable_eq (α := Mat3)]
    exact hEm.subtype_mk
  obtain ⟨hu,hE,huH1⟩ := C1_voltageJet_mem (hv.of_le (by norm_num)) hUb hU.measurableSet
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
  obtain ⟨z,F,s,hres⟩ := finite_field_scalarization volume hc hcC hUb hU.measurableSet
    v A hAm hu hE hF huH1
    (fun j ψ hψ hcψ hsψ => (hw j ψ hψ hcψ hsψ).1)
    (fun j ψ hψ hcψ hsψ => (hw j ψ hψ hcψ hsψ).2) hregU
    (ae_of_all _ (fun x _ => hb x))
  exact ⟨hu,hE,hF,z,F,s,hres⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology TopologicalSpace MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise ENNReal

local instance alignedFourierEndingH1MeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance alignedFourierEndingH1BorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

theorem aligned_fourier_ending_H1_scalarization {s : Fin 3 → ℝ}
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
          ∃ (hu : MemLp v 2 (volume.restrict U))
            (hE : MemLp (voltageGradient v) 2 (volume.restrict U))
            (hF : MemLp (voltageFlux v (fun y => ⟨E y,hsym y⟩)) 2 (volume.restrict U))
            (z : voltageH1Jets volume U) (F : Lp FieldVector 2 (volume.restrict U)) (σ : Coord3 → ℝ),
            Measurable σ ∧ MemLp σ ∞ (volume.restrict U) ∧
            z.val-(hu.toLp _,hE.toLp _)∈zeroVoltageJets volume U ∧
            (∀ᵐ x ∂volume.restrict U,σ x∈Icc (laminateLower c C) (laminateUpper C) ∧
              F x=σ x • (z.val.2 x)) ∧
            (∀ W : voltageH1Jets volume U,inner ℝ W.val.2 F=inner ℝ W.val.2 (hF.toLp _)) ∧
            (∀ W : zeroVoltageJets volume U,inner ℝ W.val.2 F=0) := by
  obtain ⟨p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hv,hEm,hvp,hEp,⟨hsym,hreg⟩,
    hbound,hvin,hEin,hterm,hr,⟨G,hG,hconst⟩,hw⟩ :=
    aligned_fourier_finite_ending (pa:=pa) hs hk hA hB ha hb hga hgb hra hrb hpb hδ
  refine ⟨p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hsym,hv,hEm,hvp,hEp,hbound,hvin,hEin,hterm,?_⟩
  intro U hU hUb hUpos
  exact scalarization_H1_of_concrete_C1flux hv hEm hsym hG hconst hc hcC hbound hreg hw hU hUb hUpos

end ScalarConductivity

end
end

end OAI
