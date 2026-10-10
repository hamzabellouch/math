import Mathlib
import OAI.Geometry.PrescribedPotential.NonlinearScale
import OAI.Geometry.PrescribedRicci.CofactorCore
import OAI.Geometry.PrescribedRicci.CofactorCoreEquation
import OAI.Geometry.PrescribedRicci.RoughCutoff
import OAI.Geometry.PrescribedRicci.TameApproximation

namespace OAI

/-! Cofactor Weak Equation. -/

section

 

noncomputable section
open Set Filter Topology Matrix _root_.MeasureTheory _root_.OAI.MeasureTheory TemperedDistribution
open scoped ContDiff SchwartzMap Classical BoundedContinuousFunction Matrix.Norms.Elementwise
namespace MetricLocalization
open EllipticKernel SobolevChart FrozenPoisson
lemma cofactor_cutoff_distribution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (a : SmoothCoefficients (BasisIndex n) (EC n)) (κ f : 𝓢(EC n,ℂ)) :
    frozenDifferential H (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume
      (SchwartzMap.smulLeftCLM ℂ κ f)) +
      (Lp.toTemperedDistributionCLM ℂ volume 2
        (perturbation (stdOrthonormalBasis ℝ (EC n)) (coefficientBCF a)
          (schwartzCoord 2 (SchwartzMap.smulLeftCLM ℂ κ f)))) =
    SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume
      (SchwartzMap.smulLeftCLM ℂ κ (schwartzDifferential (extendedCoefficient H (coefficientBCF a)) f)) +
    SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume
      (schwartzCutoffError (extendedCoefficient H (coefficientBCF a)) κ f) := by
  change frozenDifferential H (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume
    (SchwartzMap.smulLeftCLM ℂ κ f)) +
      ((perturbation (stdOrthonormalBasis ℝ (EC n)) (coefficientBCF a)
        (schwartzCoord 2 (SchwartzMap.smulLeftCLM ℂ κ f)) : L2 (EC n)) : 𝓢'(EC n,ℂ)) = _
  rw [← realize_schwartzCoord 2 (SchwartzMap.smulLeftCLM ℂ κ f),
    ← chartDifferential_extension H (coefficientBCF a) (fun i j => (a i j).hasTemperateGrowth),
    realize_schwartzCoord,← schwartzDifferential_distribution _
      (extendedCoefficient_temperate H (coefficientBCF a) (fun i j => (a i j).hasTemperateGrowth)),← map_add]
  congr 1
  change schwartzDifferential (extendedCoefficient H (coefficientBCF a))
    (SchwartzMap.smulLeftCLM ℂ κ f) =
    SchwartzMap.smulLeftCLM ℂ κ (schwartzDifferential (extendedCoefficient H (coefficientBCF a)) f) +
      (schwartzDifferential (extendedCoefficient H (coefficientBCF a)) (SchwartzMap.smulLeftCLM ℂ κ f) -
       SchwartzMap.smulLeftCLM ℂ κ (schwartzDifferential (extendedCoefficient H (coefficientBCF a)) f))
  abel
end MetricLocalization

namespace GlobalElliptic
open Anticanonical SourceSmooth EllipticKernel SobolevChart FrozenPoisson MetricLocalization
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  {A : ComplexAtlas d X} {ι : Type*} [Fintype ι]
namespace GluingData
variable {g : KaehlerMetric A} (D : GluingData g ι)
local instance cofactorWeakEquationNG (s : ℝ) : NormedAddCommGroup (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedAddCommGroup
local instance cofactorWeakEquationNS (s : ℝ) : NormedSpace ℝ (D.localizers.RealSobolev s) :=
  (D.localizers.realCompletion s).normedSpace
local instance cofactorWeakEquationTG (s : ℝ) : IsTopologicalAddGroup (D.localizers.RealSobolev s) :=
  Submodule.isTopologicalAddGroup _
local instance cofactorWeakEquationCS (s : ℝ) : ContinuousSMul ℝ (D.localizers.RealSobolev s) :=
  SMulMemClass.continuousSMul _

def outerCompleted (s : ℝ) (p : ι) : D.localizers.Sobolev s →L[ℝ] L2 (EC d) :=
  D.completedLocalize s (D.patch p).index (cutoffGlobal (D.patch p).index (D.outerCutoff p))
    (cutoffGlobal_support _ _)

lemma outerCompleted_embed (k : ℕ) (p : ι) (f : Smooth A) :
    D.outerCompleted (k:ℝ) p (D.localizers.embed (k:ℝ) f) =
      schwartzCoord (k:ℝ) (D.outerCore p f) :=
  D.completedLocalize_embed k _ _ _ f

lemma outerCompleted_embed_add_two (k : ℕ) (p : ι) (f : Smooth A) :
    D.outerCompleted ((k:ℝ)+2) p (D.localizers.embed ((k:ℝ)+2) f) =
      schwartzCoord ((k:ℝ)+2) (D.outerCore p f) := by
  have hh := D.outerCompleted_embed (k+2) p f
  have he : ((k+2:ℕ):ℝ) = (k:ℝ)+2 := by push_cast; rfl
  rw [he] at hh
  exact hh

abbrev CofactorPair (k : ℕ) :=
  D.localizers.RealSobolev (((k+1:ℕ):ℝ)+2) × D.localizers.RealSobolev ((k:ℝ)+2)

def cofactorWeakLeft (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*((k+1:ℕ):ℝ)) (p : ι)
    (z : D.CofactorPair k) : 𝓢'(EC d,ℂ) :=
  frozenDifferential (D.patch p).matrix (D.localizers.distribution ((k:ℝ)+2) p z.2.val) +
    (Lp.toTemperedDistributionCLM ℂ volume 2)
      (perturbation (stdOrthonormalBasis ℝ (EC d)) (D.cofactorBCF (k+1) (by omega) hs p z.1.val)
        (lowerCoord ((k:ℝ)+2) 2 (by linarith [Nat.cast_nonneg (α:=ℝ) k]) (z.2.val.val p)))

def cofactorWeakRight (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (p : ι)
    (z : D.CofactorPair k) : 𝓢'(EC d,ℂ) :=
  D.localizers.distribution (k:ℝ) p ((D.realVolumeDerivative k hk
    (D.localizers.realLower (((k+1:ℕ):ℝ)+2) ((k:ℝ)+2) (by push_cast; linarith) z.1) z.2).val) +
  realize ((k+1:ℕ):ℝ) (roughCutoff (D.patch p).matrix (k+1) (by omega) (D.weightCore p)
    (fun i j => D.cofactorLocal (k+1) (by omega) p i j z.1.val)
    (lowerCoord ((k:ℝ)+2) (((k+1:ℕ):ℝ)+1) (by push_cast; linarith)
      (D.outerCompleted ((k:ℝ)+2) p z.2.val)))

lemma cofactorWeakLeft_continuous (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*((k+1:ℕ):ℝ)) (p : ι) :
    Continuous (D.cofactorWeakLeft k hk hs p) := by
  have hw : Continuous (fun z : D.CofactorPair k => z.2.val) :=
    continuous_subtype_val.comp continuous_snd
  have hwp : Continuous (fun z : D.CofactorPair k => z.2.val.val p) :=
    (continuous_apply p).comp (continuous_subtype_val.comp hw)
  have hu : Continuous (fun z : D.CofactorPair k => z.1.val) :=
    continuous_subtype_val.comp continuous_fst
  have hc : Continuous (fun z : D.CofactorPair k => D.cofactorBCF (k+1) (by omega) hs p z.1.val) :=
    (D.cofactorBCF_continuous (k+1) (by omega) hs p).comp hu
  have hl : Continuous (fun z : D.CofactorPair k =>
      lowerCoord ((k:ℝ)+2) 2 (by linarith [Nat.cast_nonneg (α:=ℝ) k]) (z.2.val.val p)) :=
    (lowerCoord ((k:ℝ)+2) 2 (by linarith [Nat.cast_nonneg (α:=ℝ) k])).continuous.comp hwp
  have hp := (continuous_perturbation (stdOrthonormalBasis ℝ (EC d))).comp (hc.prodMk hl)
  exact ((frozenDifferential (D.patch p).matrix).continuous.comp
    ((D.localizers.distribution ((k:ℝ)+2) p).continuous.comp hw)).add
      ((Lp.toTemperedDistributionCLM ℂ volume 2).continuous.comp hp)

lemma cofactorCutoff_continuous (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (p : ι) :
    Continuous (fun z : D.CofactorPair k =>
      roughCutoff (D.patch p).matrix (k+1) (by omega) (D.weightCore p)
        (fun i j => D.cofactorLocal (k+1) (by omega) p i j z.1.val)
        (lowerCoord ((k:ℝ)+2) (((k+1:ℕ):ℝ)+1) (by push_cast; linarith)
          (D.outerCompleted ((k:ℝ)+2) p z.2.val))) := by
  have ha : Continuous (fun z : D.CofactorPair k =>
      fun i j => D.cofactorLocal (k+1) (by omega) p i j z.1.val) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (D.cofactorLocal_continuous (k+1) (by omega) p i j).comp
      (continuous_subtype_val.comp continuous_fst)
  have hw : Continuous (fun z : D.CofactorPair k =>
      lowerCoord ((k:ℝ)+2) (((k+1:ℕ):ℝ)+1) (by push_cast; linarith)
        (D.outerCompleted ((k:ℝ)+2) p z.2.val)) :=
    (lowerCoord ((k:ℝ)+2) (((k+1:ℕ):ℝ)+1) (by push_cast; linarith)).continuous.comp
      ((D.outerCompleted ((k:ℝ)+2) p).continuous.comp (continuous_subtype_val.comp continuous_snd))
  have hp := ha.prodMk hw
  have hc := roughCutoff_continuous (D.patch p).matrix (k+1) (by omega) (D.weightCore p)
  have hr := hc.comp hp
  exact hr

lemma cofactorWeakRight_continuous (k : ℕ) (hk : Module.finrank ℝ (EC d) < k) (p : ι) :
    Continuous (D.cofactorWeakRight k hk p) := by
  have hu : Continuous (fun z : D.CofactorPair k =>
      D.localizers.realLower (((k+1:ℕ):ℝ)+2) ((k:ℝ)+2) (by push_cast; linarith) z.1) :=
    (D.localizers.realLower (((k+1:ℕ):ℝ)+2) ((k:ℝ)+2) (by push_cast; linarith)).continuous.comp continuous_fst
  have hv : Continuous (fun z : D.CofactorPair k => D.realVolumeDerivative k hk
      (D.localizers.realLower (((k+1:ℕ):ℝ)+2) ((k:ℝ)+2) (by push_cast; linarith) z.1) z.2) :=
    ((D.realVolumeDerivative_continuous k hk).comp hu).clm_apply continuous_snd
  have h₁ := (D.localizers.distribution (k:ℝ) p).continuous.comp (continuous_subtype_val.comp hv)
  exact h₁.add ((realize ((k+1:ℕ):ℝ)).continuous.comp (D.cofactorCutoff_continuous k hk p))

lemma cofactorWeak_core (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*((k+1:ℕ):ℝ)) (p : ι) (φ ψ : RealSmooth A) :
    D.cofactorWeakLeft k hk hs p (D.localizers.realEmbed (((k+1:ℕ):ℝ)+2) φ,
      D.localizers.realEmbed ((k:ℝ)+2) ψ) =
    D.cofactorWeakRight k hk p (D.localizers.realEmbed (((k+1:ℕ):ℝ)+2) φ,
      D.localizers.realEmbed ((k:ℝ)+2) ψ) := by
  dsimp only [cofactorWeakLeft,cofactorWeakRight,Prod.fst,Prod.snd,Localizers.realEmbed_val]
  rw [D.cofactorBCF_embed,D.outerCompleted_embed_add_two,lowerCoord_schwartz,
    Localizers.realLower_embed]
  simp_rw [D.cofactorLocal_embed]
  rw [roughCutoff_schwartz,realize_schwartzCoord]
  change _ = realize (k:ℝ) ((D.realVolumeDerivative k hk
    (D.localizers.realEmbed ((k:ℝ)+2) φ) (D.localizers.realEmbed ((k:ℝ)+2) ψ)).val.val p) + _
  rw [← D.cofactor_core_forcing k hk p φ ψ,realize_schwartzCoord,
    D.localizers.distribution_embed]
  change frozenDifferential _ (SchwartzMap.toTemperedDistributionCLM (EC d) ℂ volume (D.forcing p ψ.val)) +
    ((Lp.toTemperedDistributionCLM ℂ volume 2) (perturbation _ _
      (lowerCoord ((k:ℝ)+2) 2 (by linarith [Nat.cast_nonneg (α:=ℝ) k])
        (schwartzCoord ((k:ℝ)+2) (D.forcing p ψ.val))))) = _
  rw [lowerCoord_schwartz,← D.weightCore_outerCore p ψ.val]
  exact cofactor_cutoff_distribution (D.patch p).matrix (D.cofactorLocalCore p · · φ.val)
    (D.weightCore p) (D.outerCore p ψ.val)

lemma cofactor_weak_equation (k : ℕ) (hk : Module.finrank ℝ (EC d) < k)
    (hs : (Module.finrank ℝ (EC d):ℝ) < 2*((k+1:ℕ):ℝ)) (p : ι)
    (u : D.localizers.RealSobolev (((k+1:ℕ):ℝ)+2))
    (w : D.localizers.RealSobolev ((k:ℝ)+2)) :
    D.cofactorWeakLeft k hk hs p (u,w) = D.cofactorWeakRight k hk p (u,w) := by
  have he : D.cofactorWeakLeft k hk hs p = D.cofactorWeakRight k hk p := by
    apply ((D.localizers.realEmbed_dense (((k+1:ℕ):ℝ)+2)).prodMap
      (D.localizers.realEmbed_dense ((k:ℝ)+2))).equalizer
      (D.cofactorWeakLeft_continuous k hk hs p) (D.cofactorWeakRight_continuous k hk p)
    funext z
    exact D.cofactorWeak_core k hk hs p z.1 z.2
  exact congr_fun he (u,w)

end GluingData
end GlobalElliptic

end
end

end OAI
