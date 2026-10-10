import Mathlib
import OAI.Probability.LogConcave.Numerics.RowTape
import OAI.Probability.LogConcave.OraclePrograms.TerminalMeanProgram
import OAI.Probability.LogConcave.Sampling.SampleCorrelation
import OAI.Probability.LogConcave.OraclePrograms.NoisyCircuit
import OAI.Probability.LogConcave.Sampling.AnchorGauge

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Function
open scoped Classical

variable {d : ℕ}

lemma oneSlot_preserving {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ] :
    MeasurePreserving (fun z : Ω => fun _ : Fin 1 => z) μ (Measure.pi fun _ : Fin 1 => μ) := by
  convert (measurePreserving_piUnique (fun _ : Fin 1 => μ)).symm (MeasurableEquiv.piUnique (fun _ : Fin 1 => Ω)) using 1
  funext z i
  have hi : i=default := Subsingleton.elim _ _
  subst i
  rfl

def prependTape (k : ℕ) (z : Point d × (Fin k → Point d)) : Fin (1+k) → Point d :=
  Fin.append (fun _ => z.1) z.2

lemma prependTape_preserving (k : ℕ) :
    MeasurePreserving (prependTape (d:=d) k) ((stdGaussian (Point d)).prod (gaussianTape d k))
      (gaussianTape d (1+k)) := by
  exact (MeanTree.appendSlots_preserving (stdGaussian (Point d)) 1 k).comp
    ((oneSlot_preserving (stdGaussian (Point d))).prod (MeasurePreserving.id _))

def meanTape (c k : ℕ) (z : (Fin c → Point d) × (Point d × (Fin k → Point d))) :
    Fin (c+(1+k)) → Point d := Fin.append z.1 (prependTape k z.2)

lemma meanTape_preserving (c k : ℕ) :
    MeasurePreserving (meanTape (d:=d) c k)
      ((gaussianTape d c).prod ((stdGaussian (Point d)).prod (gaussianTape d k)))
      (gaussianTape d (c+(1+k))) := by
  exact (MeanTree.appendSlots_preserving (stdGaussian (Point d)) c (1+k)).comp
    ((MeasurePreserving.id _).prod (prependTape_preserving k))

lemma sampleParent_run_prepend (E : Expression (Point d × Point d) d)
    (v : Fin E.slots → ℝ) (T η : ℝ) (V : Point d → ℝ) (x : Point d)
    (z : Point d × (Fin E.slots → Point d)) :
    (sampleParent E v T η).pre.run V (x,prependTape E.slots z)=E.eval V (x,z.1) z.2 := by
  rw [sampleParent_run]
  simp only [prependTape,Fin.append_left,Fin.append_right]

lemma meanParent_run_meanTape (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) (T : ℝ) (V : Point d → ℝ) (x : Point d)
    (z : (Fin S.slots → Point d) × (Point d × (Fin E.slots → Point d))) :
    (meanParent S E u v T).program.run V (x,meanTape S.slots E.slots z)=
      E.eval V (x,(T • S.program.run V (x,z.1),z.2.1)) z.2.2 := by
  rw [meanParent_run]
  simp only [meanTape,prependTape,MeanTree.leftBlock_append,MeanTree.middleBlock_append,
    MeanTree.rightBlock_append]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Coupling Function
open scoped Classical NNReal

variable {d : ℕ}

theorem sampleParent_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) {r T η h : ℝ} (hr : 0≤r) (hl : (lam:ℝ)*r^2≤1/2)
    (hT : 0<T) (hT1 : T<1) (hη : T⁻¹*Real.sqrt (1-T^2)=η/2)
    (n N : ℕ) (e : ProbabilityNode T h n) (_he : probabilityNodeTime T h n e=T)
    (E : Expression (Point d × Point d) d) (v : Fin E.slots → ℝ)
    {Lf Lg err R : ℝ} (hLf : 0≤Lf) (hLg : 0≤Lg) (herr : 0<err)
    (hg : Measurable (sampleMeanCircuit F x r T h n N e))
    (hfl : ∀Y Z g,‖E.eval F (x,Y) g-E.eval F (x,Z) g‖≤Lf*dist Y Z)
    (hgl : ∀Y Z,‖sampleMeanCircuit F x r T h n N e Y-
      sampleMeanCircuit F x r T h n N e Z‖≤Lg*dist Y Z)
    (hc : ∀Y,SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d))
      (E.eval F (x,Y)) (fun z => sampleMeanCircuit F x r T h n N e Y+(η/Real.sqrt 2) • z)
      (err^2*(anchorGauge (circuitD F x) Y)^2))
    (hi : Integrable (fun Y => ‖sampleMeanCircuit F x r T h n N e Y-
      T⁻¹ • fullProbabilityFlow hF x hr hl T Y‖^2) (stdGaussian (Point d)))
    (hnum : (∫Y,‖sampleMeanCircuit F x r T h n N e Y-
      T⁻¹ • fullProbabilityFlow hF x hr hl T Y‖^2 ∂stdGaussian (Point d))≤R) :
    SquaredAt (gaussianTape d (1+E.slots))
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
      (fun g => (sampleParent E v T η).pre.run F (x,g))
      (fun z => z.1+(Real.sqrt 3*η/2) • z.2)
      (40*err^2*(∫z,(anchorGauge (circuitD F x) z)^2 ∂stdGaussian (Point d))+4*R) := by
  have hV : Measurable (fun z => (F z,gradient F z)) :=
    hF.smooth.continuous.measurable.prodMk hF.gradient_lipschitz.continuous.measurable
  have hE := E.measurable_eval F hV
  have hf : Measurable (uncurry (fun Y g => E.eval F (x,Y) g)) :=
    hE.comp (show Measurable (fun z : Point d × (Fin E.slots → Point d) => ((x,z.1),z.2)) by fun_prop)
  have hu : Measurable (fun Y => T⁻¹ • fullProbabilityFlow hF x hr hl T Y) := by
    have hh := (fullProbabilityFlow_lipschitz hF x hr hl ⟨hT.le,hT1.le⟩).continuous.measurable
    fun_prop
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hh := SquaredAt.noisy_circuit_target (stdGaussian (Point d)) (gaussianTape d E.slots)
    ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d)))
    (fun Y g => E.eval F (x,Y) g) (sampleMeanCircuit F x r T h n N e)
    (fun Y => T⁻¹ • fullProbabilityFlow hF x hr hl T Y)
    (fun z => z.1+(Real.sqrt 3*η/2) • z.2) hf hg hu (by fun_prop)
    (anchorGauge (circuitD F x)) (one_le_anchorGauge (circuitD_nonneg F x))
    (anchorGauge_change _) (anchorGauge_gaussian_integrable _) hLf hLg herr hfl hgl hc hi hnum
    (probability_endpoint_noisy_law hF x hr hl hT hT1 hη (sample_noise_variance η))
  have hp := hh.reindex (prependTape E.slots) id (prependTape_preserving E.slots).measurable measurable_id
    (fun g => (sampleParent E v T η).pre.run F (x,g))
    (fun z => z.1+(Real.sqrt 3*η/2) • z.2) ?_ (by fun_prop)
    (fun z => sampleParent_run_prepend E v T η F x z) (fun _ => rfl)
  · simpa only [(prependTape_preserving E.slots).map_eq,Measure.map_id] using hp
  · exact ((sampleParent E v T η).pre.measurable_run F hV).comp (by fun_prop)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory OracleCompiler Coupling Function
open scoped Classical NNReal

variable {d : ℕ}

theorem meanParent_squared {F : Point d → ℝ} {lam : ℝ≥0} (hF : Primitive F lam)
    (x : Point d) (S : SeedProgram d)
    (E : Expression (Point d × (Point d × Point d)) d)
    (u : Fin S.slots → ℝ) (v : Fin E.slots → ℝ) (T : ℝ)
    (μ : Measure (Point d)) [IsProbabilityMeasure μ]
    (g w : Point d × Point d → Point d) (m : Point d) (σ n : ℝ)
    (hg : Measurable g) (hw : Measurable w)
    (ρ : Point d × Point d → ℝ) (hρ : ∀z,1≤ρ z)
    (hρlip : ∀z z',ρ z'≤ρ z+dist z z')
    (hρi : Integrable (fun z => (ρ z)^2) (μ.prod (stdGaussian (Point d))))
    {K Lf Lg err B R : ℝ} (hK : 0≤K) (hLf : 0≤Lf) (hLg : 0≤Lg) (herr : 0<err)
    (hS : SquaredAt (gaussianTape d S.slots) μ
      (fun z => T • S.program.run F (x,z)) id B)
    (hposition : ∀y y' G z,‖E.eval F (x,(y,G)) z-E.eval F (x,(y',G)) z‖≤K*‖y-y'‖)
    (hfl : ∀z z' t,‖E.eval F (x,z) t-E.eval F (x,z') t‖≤Lf*dist z z')
    (hgl : ∀z z',‖g z-g z'‖≤Lg*dist z z')
    (hc : ∀z,SquaredAt (gaussianTape d E.slots) (stdGaussian (Point d))
      (E.eval F (x,z)) (fun t => g z+n • t) (err^2*(ρ z)^2))
    (hi : Integrable (fun z => ‖g z-w z‖^2) (μ.prod (stdGaussian (Point d))))
    (hnum : (∫z,‖g z-w z‖^2 ∂μ.prod (stdGaussian (Point d)))≤R)
    (hlaw : ((μ.prod (stdGaussian (Point d))).prod (stdGaussian (Point d))).map
      (fun z => w z.1+n • z.2)=(stdGaussian (Point d)).map (fun t => m+σ • t)) :
    SquaredAt (gaussianTape d (S.slots+(1+E.slots))) (stdGaussian (Point d))
      (fun z => (meanParent S E u v T).program.run F (x,z))
      (fun t => m+σ • t)
      (2*K^2*B+80*err^2*(∫z,(ρ z)^2 ∂μ.prod (stdGaussian (Point d)))+8*R) := by
  have hV : Measurable (fun z => (F z,gradient F z)) :=
    hF.smooth.continuous.measurable.prodMk hF.gradient_lipschitz.continuous.measurable
  have hE := E.measurable_eval F hV
  have hf : Measurable (uncurry (fun z t => E.eval F (x,z) t)) :=
    hE.comp (show Measurable (fun z : (Point d × Point d) × (Fin E.slots → Point d) =>
      ((x,z.1),z.2)) by fun_prop)
  have hsmeas : Measurable (fun z : Fin S.slots → Point d => T • S.program.run F (x,z)) := by
    have hh := (S.program.measurable_run F hV).comp
      (show Measurable (fun z : Fin S.slots → Point d => (x,z)) by fun_prop)
    exact hh.const_smul T
  let H : Point d → Point d × (Fin E.slots → Point d) → Point d :=
    fun y z => E.eval F (x,(y,z.1)) z.2
  have hH : Measurable (uncurry H) :=
    hE.comp (show Measurable (fun z : Point d × (Point d × (Fin E.slots → Point d)) =>
      ((x,(z.1,z.2.1)),z.2.2)) by fun_prop)
  have hs := hS.shared_lipschitz ((stdGaussian (Point d)).prod (gaussianTape d E.slots))
    hsmeas measurable_id hK H hH (fun a b z => hposition a b z.1 z.2)
  have hn := SquaredAt.noisy_circuit_target (μ.prod (stdGaussian (Point d)))
    (gaussianTape d E.slots) (stdGaussian (Point d)) (fun z t => E.eval F (x,z) t)
    g w (fun t => m+σ • t) hf hg hw (by fun_prop) ρ hρ hρlip hρi hLf hLg herr
    hfl hgl hc hi hnum hlaw
  have hn' := hn.reindex (MeasurableEquiv.prodAssoc (α := Point d) (β := Point d) (γ := Fin E.slots → Point d)) id
    (by fun_prop) measurable_id (uncurry H) (fun t => m+σ • t) hH (by fun_prop)
    (fun _ => rfl) (fun _ => rfl)
  rw [(measurePreserving_prodAssoc μ (stdGaussian (Point d)) (gaussianTape d E.slots)).map_eq,
    Measure.map_id] at hn'
  have hs' : Measurable (fun z : (Fin S.slots → Point d) × (Point d × (Fin E.slots → Point d)) => H (T • S.program.run F (x,z.1)) z.2) :=
    hH.comp ((hsmeas.comp measurable_fst).prodMk measurable_snd)
  have hh := hs.trans hs' (hE.comp (show Measurable (fun z : Point d × (Point d × (Fin E.slots → Point d)) => ((x,(z.1,z.2.1)),z.2.2)) by fun_prop)) (by fun_prop) hn'
  have hp := hh.reindex (meanTape S.slots E.slots) id
    (meanTape_preserving S.slots E.slots).measurable measurable_id
    (fun z => (meanParent S E u v T).program.run F (x,z)) (fun t => m+σ • t)
    (((meanParent S E u v T).program.measurable_run F hV).comp (by fun_prop))
    (by fun_prop) (fun z => meanParent_run_meanTape S E u v T F x z) (fun _ => rfl)
  simp only [(meanTape_preserving S.slots E.slots).map_eq,Measure.map_id] at hp
  convert hp using 1
  ring
end LogConcaveSampling

end

end

end OAI
