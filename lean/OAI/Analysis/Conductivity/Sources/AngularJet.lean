import Mathlib
import OAI.Analysis.Conductivity.Fourier.EndPoissonJets
import OAI.Analysis.Conductivity.Sources.AngularCoefficient
import OAI.Analysis.Conductivity.Geometry.TorusDirectionalDerivative

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal
local instance angularJetMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance angularJetIsProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma measurable_torusDirectionalDerivative_joint
    {f : ℝ × UnitAddTorus (Fin 2) → ℂ} (hf : Continuous f) (j : Fin 2) :
    Measurable (fun z : ℝ × UnitAddTorus (Fin 2) =>
      torusDirectionalDerivative (fun θ => f (z.1,θ)) j z.2) := by
  let F : ℝ × TorusRealPlane → ℂ := fun z => f (z.1,torusRealProjection z.2)
  have hc : Continuous F := hf.comp
    (continuous_fst.prodMk (continuous_torusRealProjection.comp continuous_snd))
  have hm := (measurable_lineDeriv (𝕜:=ℝ) hc (v:=(0,Pi.single j 1))).comp
    (measurable_fst.prodMk (measurable_torusRealRepresentative.comp measurable_snd))
  convert hm using 1
  funext z
  unfold torusDirectionalDerivative lineDeriv
  congr 2
  ext t
  simp [F]

def sourceAngularTest (f : (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    (z : ℝ × UnitAddTorus (Fin 2)) : ℂ :=
  (f (sourceAngularCollar (a*z.1+b) z.2) : ℂ)

lemma continuous_sourceAngularTest {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b : ℝ) :
    Continuous (sourceAngularTest f a b) :=
  Complex.continuous_ofReal.comp (hf.continuous.comp
    (contDiff_sourceAngularPolynomial_joint.continuous.comp
      ((continuous_const.mul continuous_fst |>.add continuous_const).prodMk
        (continuous_sourceRayCoordinates.comp continuous_snd))))

theorem sourceAngularTest_lipschitz {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) :
    ∃ K : ℝ≥0, ∀ t∈Icc (0:ℝ) R, ∀ j u θ,
      ‖sourceAngularTest f a b (t,θ+torusCoordinateShift j u)-
        sourceAngularTest f a b (t,θ)‖≤(K:ℝ)*|u| := by
  let G : ℝ × (Fin 4 → ℝ) → ℂ := fun z =>
    (f (sourceAngularPolynomial (a*z.1+b) z.2) : ℂ)
  have hG : ContDiff ℝ (↑(⊤ : ℕ∞)) G :=
    Complex.ofRealCLM.contDiff.comp (hf.comp
      (contDiff_sourceAngularPolynomial_joint.comp
        ((contDiff_const.mul contDiff_fst |>.add contDiff_const).prodMk contDiff_snd)))
  obtain ⟨K,hK⟩ := hG.contDiffOn.exists_lipschitzOnWith (by simp)
    ((convex_Icc (0:ℝ) R).prod (convex_Icc _ _))
    (isCompact_Icc.prod (isCompact_Icc (a:=(fun _ : Fin 4 => (-2:ℝ))) (b:=fun _ => (2:ℝ))))
  refine ⟨K*⟨sourceRayConstant,sourceRayConstant_nonneg⟩,?_⟩
  intro t ht j u θ
  have hh := hK.dist_le_mul (t,sourceRayCoordinates (θ+torusCoordinateShift j u))
    ⟨ht,sourceRayCoordinates_mem _⟩ (t,sourceRayCoordinates θ) ⟨ht,sourceRayCoordinates_mem _⟩
  rw [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg),dist_eq_norm,dist_eq_norm] at hh
  apply hh.trans
  change _ ≤ (K:ℝ)*sourceRayConstant*|u|
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (sourceRayCoordinates_difference j u θ) K.coe_nonneg

def sourceAngularJet (f : (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    (j : Fin 4) (z : ℝ × UnitAddTorus (Fin 2)) : ℂ :=
  ![sourceAngularTest f a b z,sourceAngularAxial f a b z.1 z.2,
    torusDirectionalDerivative (fun θ => sourceAngularTest f a b (z.1,θ)) 0 z.2/(2*Real.pi),
    torusDirectionalDerivative (fun θ => sourceAngularTest f a b (z.1,θ)) 1 z.2/(2*Real.pi)] j

lemma measurable_sourceAngularJet {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b : ℝ) (j : Fin 4) :
    Measurable (sourceAngularJet f a b j) := by
  fin_cases j
  · exact (continuous_sourceAngularTest hf a b).measurable
  · exact (continuous_sourceAngularAxial hf a b).measurable
  · exact (measurable_torusDirectionalDerivative_joint (continuous_sourceAngularTest hf a b) 0).div_const _
  · exact (measurable_torusDirectionalDerivative_joint (continuous_sourceAngularTest hf a b) 1).div_const _

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal NNReal
local instance angularJetFiniteCylinderMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance angularJetFiniteCylinderProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma finiteCylinder_ae_mem (R : ℝ) :
    ∀ᵐ z ∂(FiniteAxisMeasure R).prod (volume : Measure (UnitAddTorus (Fin 2))),
      z.1∈Icc (0:ℝ) R :=
  Measure.quasiMeasurePreserving_fst.ae
    ((ae_restrict_mem measurableSet_Ioc).mono fun _ ht => Ioc_subset_Icc_self ht)

lemma continuous_memLp_finiteCylinder {f : ℝ × UnitAddTorus (Fin 2) → ℂ}
    (hf : Continuous f) (R : ℝ) :
    MemLp f 2 ((FiniteAxisMeasure R).prod volume) := by
  obtain ⟨C,hC⟩ := ((isCompact_Icc (a:=(0:ℝ)) (b:=R)).prod
    (isCompact_univ : IsCompact (univ : Set (UnitAddTorus (Fin 2))))).exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [finiteCylinder_ae_mem R] with z hz
  exact hC z ⟨hz,mem_univ _⟩

lemma sourceAngularJet_memLp {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) (j : Fin 4) :
    MemLp (sourceAngularJet f a b j) 2 ((FiniteAxisMeasure R).prod volume) := by
  obtain ⟨K,hK⟩ := sourceAngularTest_lipschitz hf a b R
  have hang (k : Fin 2) : MemLp (fun z : ℝ × UnitAddTorus (Fin 2) =>
      torusDirectionalDerivative (fun θ => sourceAngularTest f a b (z.1,θ)) k z.2/(2*Real.pi))
        2 ((FiniteAxisMeasure R).prod volume) := by
    apply MemLp.of_bound
      (((measurable_torusDirectionalDerivative_joint (continuous_sourceAngularTest hf a b) k).div_const _).aestronglyMeasurable) ((2:ℝ)*K/‖(2*Real.pi:ℂ)‖)
    filter_upwards [finiteCylinder_ae_mem R] with z hz
    rw [norm_div]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    exact torusDirectionalDerivative_norm
      ⟨fun θ => sourceAngularTest f a b (z.1,θ),
        (continuous_sourceAngularTest hf a b).comp (continuous_const.prodMk continuous_id)⟩
      K (hK z.1 hz) k z.2
  fin_cases j
  · exact continuous_memLp_finiteCylinder (continuous_sourceAngularTest hf a b) R
  · exact continuous_memLp_finiteCylinder (continuous_sourceAngularAxial hf a b) R
  · exact hang 0
  · exact hang 1

def sourceAngularLpJet {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) : FiniteCylinderJets R :=
  WithLp.toLp 2 (fun j => (sourceAngularJet_memLp hf a b R j).toLp _)

lemma sourceAngularLpJet_ae {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) (j : Fin 4) :
    sourceAngularLpJet hf a b R j =ᵐ[(FiniteAxisMeasure R).prod volume]
      sourceAngularJet f a b j :=
  (sourceAngularJet_memLp hf a b R j).coeFn_toLp

lemma mFourierCoeff_div_const (f : UnitAddTorus (Fin 2) → ℂ) (h : TorusModes) (c : ℂ) :
    mFourierCoeff (fun θ => f θ/c) h=mFourierCoeff f h/c := by
  simp only [mFourierCoeff,smul_eq_mul,←mul_div_assoc,integral_div]

lemma torusDirectionalDerivative_scaled_fourier (f : C(UnitAddTorus (Fin 2),ℂ)) (K : ℝ≥0)
    (hLip : ∀ j t θ, ‖f (θ+torusCoordinateShift j t)-f θ‖≤(K:ℝ)*|t|)
    (j : Fin 2) (h : TorusModes) :
    mFourierCoeff (fun θ => torusDirectionalDerivative f j θ/(2*Real.pi)) h=
      (Complex.I*(h j))*mFourierCoeff f h := by
  rw [mFourierCoeff_div_const,torusDirectionalDerivative_fourier f K hLip]
  have hp : (Real.pi:ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

lemma sourceAngularJet_fourier {f : (Fin 3 → ℝ) → ℝ}
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (a b R : ℝ) (h : TorusModes)
    {t : ℝ} (ht : t∈Icc (0:ℝ) R) (j : Fin 4) :
    mFourierCoeff (fun θ => sourceAngularJet f a b j (t,θ)) h=
      ![sourceAngularCoefficient f a b h t,deriv (sourceAngularCoefficient f a b h) t,
        (Complex.I*(h 0))*sourceAngularCoefficient f a b h t,
        (Complex.I*(h 1))*sourceAngularCoefficient f a b h t] j := by
  obtain ⟨K,hK⟩ := sourceAngularTest_lipschitz hf a b R
  have ha (k : Fin 2) := torusDirectionalDerivative_scaled_fourier
    ⟨fun θ => sourceAngularTest f a b (t,θ),
      (continuous_sourceAngularTest hf a b).comp (continuous_const.prodMk continuous_id)⟩
    K (hK t ht) k h
  fin_cases j
  · rfl
  · exact (sourceAngularCoefficient_hasDerivAt hf a b h t).deriv.symm
  · exact ha 0
  · exact ha 1

end ScalarConductivity

end
end

end OAI
