import Mathlib
import OAI.Analysis.Conductivity.Scalarization.GeneralModeEndingScalarization
import OAI.Analysis.Conductivity.Variational.VoltageRecombination

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped ENNReal Matrix.Norms.Elementwise

local instance generalModeRecombinedEndingMeasurableSpaceMat3 : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance generalModeRecombinedEndingBorelSpaceMat3 : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

theorem general_mode_ending_affine_H1_scalarization {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {h₀ : Fin 2 → ℤ} (hh₀ : h₀≠0)
    {a b pa pb : (Fin 2 → ℤ) → ℝ} {A B ga gb : ℝ}
    (hA : 0≤A) (hB : 0≤B) (ha : ∀ h,|a h|≤A) (hb : ∀ h,|b h|≤B)
    (hga : 0<ga) (hgb : 0<gb)
    (hra : ∀ h,a h≠0 → ga≤torusRate s h)
    (hrb : ∀ h,b h≠0 → torusRate s h₀+gb≤torusRate s h)
    {δ : ℝ} (hδ : 0<δ) :
    ∃ (Q : Matrix (Fin 2) (Fin 2) ℤ) (θ : Fin 2 → ℝ) (k : ℤ),
      Q.det=1 ∧ 0<k ∧ h₀ ᵥ* Q=![0,k] ∧
      ∃ p T c C : ℝ,p∈Ioc 0 (1/2) ∧ p<δ ∧ 7<T ∧ 0<c ∧ c≤C ∧
      ∃ (v : Coord3 → Fin 2 → ℝ) (E : Coord3 → Mat3)
        (hsym : ∀ x,(E x).IsSymm),
        ContDiff ℝ 2 v ∧ Measurable E ∧
        AngularPeriodic (2*Real.pi) v ∧ AngularPeriodic (2*Real.pi) E ∧
        (∀ x w,c*(w ⬝ᵥ w)≤w ⬝ᵥ (E x*ᵥw) ∧ w ⬝ᵥ (E x*ᵥw)≤C*(w ⬝ᵥ w)) ∧
        (∀ x,x 0∈Icc 0 (1/2) → v x=
          ![x 0+flatFourier s (normalizedFourierCoefficients s 0
              (Real.sqrt (angularNormalization Q)*(10+1/p)) a) pa
              (angularNormalizedLift Q (angularRealTranslation θ x))/Real.sqrt (angularNormalization Q),
            flatPhaseMode s h₀ (pb h₀) (angularNormalizedLift Q (angularRealTranslation θ x))+
              flatFourier s (normalizedFourierCoefficients s (torusRate s h₀)
                (Real.sqrt (angularNormalization Q)*(10+1/p)) b) pb
                (angularNormalizedLift Q (angularRealTranslation θ x))]) ∧
        (∀ x,x 0∈Icc 0 (1/2) → E x=flatBackgroundTensor (normalizedAngularTensor s Q)) ∧
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
            (∀ W : zeroVoltageJets volume U,inner ℝ W.val.2 F=0) ∧
            ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (d : Fin 2 → ℝ),
              ∃ (hu' : MemLp (fun x => voltageRecombine M (v x)+d) 2 (volume.restrict U))
                (hE' : MemLp (voltageGradient (fun x => voltageRecombine M (v x)+d)) 2 (volume.restrict U))
                (z' : voltageH1Jets volume U) (F' : Lp FieldVector 2 (volume.restrict U)),
                z'.val-(hu'.toLp _,hE'.toLp _)∈zeroVoltageJets volume U ∧
                (∀ᵐ x ∂volume.restrict U,F' x=σ x • z'.val.2 x) ∧
                (∀ W : voltageH1Jets volume U,inner ℝ W.val.2 F'=
                  inner ℝ W.val.2 ((fieldRecombine M).compLpL 2 (volume.restrict U) (hF.toLp _))) ∧
                (∀ W : zeroVoltageJets volume U,inner ℝ W.val.2 F'=0) := by
  obtain ⟨Q,θ,k,hQ,hk,he,p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hsym,hv,hEm,hvp,hEp,hbound,hvin,hEin,hterm,hscalar⟩ :=
    general_mode_ending_H1_scalarization (pa:=pa) (pb:=pb) hs hh₀ hA hB ha hb hga hgb hra hrb hδ
  refine ⟨Q,θ,k,hQ,hk,he,p,T,c,C,hp,hpδ,hT,hc,hcC,v,E,hsym,hv,hEm,hvp,hEp,hbound,hvin,hEin,hterm,?_⟩
  intro U hU hUb hUh
  obtain ⟨hu,hE,hF,z,F,σ,hσm,hσb,hzero,hconst,hcauchy,hweak⟩ := hscalar U hU hUb hUh
  refine ⟨hu,hE,hF,z,F,σ,hσm,hσb,hzero,hconst,hcauchy,hweak,?_⟩
  intro M d
  let : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hUb.measure_lt_top.ne
  obtain ⟨z',F',hz',hF',hzero',hconst',hcauchy',hweak'⟩ :=
    scalar_voltage_affine_recombine volume U M d z (hu.toLp _,hE.toLp _) F (hF.toLp _) σ
      hzero (hconst.mono fun _ hx => hx.2) hcauchy hweak
  obtain ⟨hu',hE',hjet⟩ := voltageJetRecombine_affine_toLp volume U M d
    (hv.differentiable (by norm_num)) hu hE
  refine ⟨hu',hE',z',F',?_,hconst',hcauchy',hweak'⟩
  rwa [hjet] at hzero'

end ScalarConductivity

end
end

end OAI
