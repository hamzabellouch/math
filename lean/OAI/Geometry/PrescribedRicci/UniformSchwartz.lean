import Mathlib
import OAI.Geometry.PrescribedPotential.ChartParametrix
import OAI.Geometry.PrescribedRicci.JetSobolev
import OAI.Geometry.PrescribedRicci.UniformLocalH2

namespace OAI

/-! Uniform Schwartz. -/

section

 

noncomputable section
open Set Finset MeasureTheory LineDeriv TemperedDistribution
open scoped ContDiff Classical BigOperators ENNReal SchwartzMap BoundedContinuousFunction Real
open scoped ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace SobolevChart
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {Z : Type*}

def UniformSobolev (s : ℝ) (F : Z → 𝓢(E,ℂ)) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖schwartzCoord s (F z)‖ ≤ C

lemma UniformSobolev.of_coreBound {s t : ℝ} {F : Z → 𝓢(E,ℂ)}
    (hF : UniformSobolev s F) {T : 𝓢(E,ℂ) → 𝓢(E,ℂ)} (hT : CoreBound s t T) :
    UniformSobolev t (fun z => T (F z)) := by
  obtain ⟨C,hC,hc⟩ := hF
  obtain ⟨B,hB,hb⟩ := hT
  exact ⟨B*C,mul_nonneg hB hC,fun z => (hb _).trans (mul_le_mul_of_nonneg_left (hc z) hB)⟩

lemma UniformSobolev.mono {s t : ℝ} {F : Z → 𝓢(E,ℂ)}
    (hF : UniformSobolev s F) (hst : t ≤ s) : UniformSobolev t F :=
  hF.of_coreBound (T:=id) (CoreBound.id hst)

lemma UniformSobolev.add {s : ℝ} {F G : Z → 𝓢(E,ℂ)}
    (hF : UniformSobolev s F) (hG : UniformSobolev s G) : UniformSobolev s (fun z => F z+G z) := by
  obtain ⟨C,hC,hc⟩ := hF
  obtain ⟨B,hB,hb⟩ := hG
  refine ⟨C+B,add_nonneg hC hB,fun z => ?_⟩
  rw [schwartzCoord_add]
  exact (norm_add_le _ _).trans (add_le_add (hc z) (hb z))

lemma UniformSobolev.const (s : ℝ) (f : 𝓢(E,ℂ)) : UniformSobolev s (fun _ : Z => f) :=
  ⟨‖schwartzCoord s f‖,norm_nonneg _,fun _ => le_rfl⟩

lemma UniformSobolev.sum {s : ℝ} {κ : Type*} (I : Finset κ)
    (F : κ → Z → 𝓢(E,ℂ)) (hF : ∀ i ∈ I, UniformSobolev s (F i)) :
    UniformSobolev s (fun z => ∑ i ∈ I, F i z) := by
  induction I using Finset.induction_on with
  | empty => simpa using UniformSobolev.const (Z:=Z) s (0 : 𝓢(E,ℂ))
  | @insert i I hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hF i (Finset.mem_insert_self i I)).add (ih (fun j hj => hF j (Finset.mem_insert_of_mem hj)))

lemma UniformSobolev.deriv {s t : ℝ} {F : Z → 𝓢(E,ℂ)}
    (hF : UniformSobolev s F) (v : E) (hst : t ≤ s-1) :
    UniformSobolev t (fun z => ∂_{v} (F z)) := hF.of_coreBound (coreBound_deriv v hst)

lemma UniformSobolev.word {s t : ℝ} {F : Z → 𝓢(E,ℂ)}
    (hF : UniformSobolev s F) (ws : List E) (hst : t ≤ s-ws.length) :
    UniformSobolev t (fun z => schwartzWord ws (F z)) := hF.of_coreBound (coreBound_word ws hst)

lemma uniformSobolev_zero_iff (F : Z → 𝓢(E,ℂ)) : UniformSobolev 0 F ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z, lpNorm (F z : E → ℂ) 2 volume ≤ C := by
  simp only [UniformSobolev,TameInterpolation.lpNorm_schwartz_zero]

lemma uniformSobolev_raise_two {s : ℝ} {F : Z → 𝓢(E,ℂ)}
    (hF : UniformSobolev s F)
    (hD : ∀ j, UniformSobolev s (fun z =>
      ∂_{stdOrthonormalBasis ℝ E j} (∂_{stdOrthonormalBasis ℝ E j} (F z)))) :
    UniformSobolev (s+2) F := by
  obtain ⟨C,hC,hc⟩ := hF
  choose B hB hb using hD
  refine ⟨C+‖(((2*Real.pi)^2:ℝ):ℂ)⁻¹‖*∑ j, B j,add_nonneg hC (mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun j _ => hB j)),fun z => ?_⟩
  apply (schwartzCoord_raise_two_norm s (F z)).trans
  exact add_le_add (hc z) (mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun j _ => hb j z)) (norm_nonneg _))
end SobolevChart

namespace FrozenPoisson
open SobolevChart EllipticKernel MetricLocalization
variable {n : ℕ} {Z : Type*}

theorem uniform_schwartz_H2 {M : ℝ} (hM : 0 ≤ M)
    (H : Z → Matrix (Fin n) (Fin n) ℂ) (hH : ∀ z, (H z).PosDef)
    (hHM : ∀ z, ‖H z‖ ≤ M)
    (a : Z → BasisIndex n → BasisIndex n → EC n →ᵇ ℂ)
    (ha : ∀ z i j, (a z i j : EC n → ℂ).HasTemperateGrowth)
    (hsmall : ∀ z, perturbationBound (stdOrthonormalBasis ℝ (EC n)) (a z) *
      uniformEllipticBound n M ≤ 1/2)
    (F G : Z → 𝓢(EC n,ℂ)) (hG : UniformSobolev 0 G)
    (he : ∀ z, (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume (F z)) -
      chartDifferential (extendedCoefficient (H z) (a z)) (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume (F z)) =
      (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume (G z))) : UniformSobolev 2 F := by
  obtain ⟨C,hC,hc⟩ := hG
  have hU := (uniformEllipticBound_pos (n:=n) hM).le
  refine ⟨2*uniformEllipticBound n M*C,by positivity,fun z => ?_⟩
  have hEq : realize 2 (schwartzCoord 2 (F z)) - frozenDifferential (H z) (realize 2 (schwartzCoord 2 (F z))) -
      (perturbation (stdOrthonormalBasis ℝ (EC n)) (a z) (schwartzCoord 2 (F z)) : 𝓢'(EC n,ℂ)) =
      (schwartzCoord 0 (G z) : 𝓢'(EC n,ℂ)) := by
    rw [sub_sub,← chartDifferential_extension (H z) (a z) (ha z),realize_schwartzCoord]
    have h0 : (schwartzCoord 0 (G z) : 𝓢'(EC n,ℂ)) = (SchwartzMap.toTemperedDistributionCLM (EC n) ℂ volume (G z)) := by
      rw [schwartzCoord_distribution,besselPotential_zero,ContinuousLinearMap.id_apply]
    rw [h0]
    exact he z
  exact (uniform_H2_absorb (H z) (hH z) hM (hHM z) _ _ (hsmall z) _ _ hEq).trans
    (mul_le_mul_of_nonneg_left (hc z) (by positivity))
end FrozenPoisson

end
end

end OAI
