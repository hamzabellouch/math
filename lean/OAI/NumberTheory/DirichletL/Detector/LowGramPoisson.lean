import OAI.NumberTheory.DirichletL.Detector.LowGramProfile

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve RayFourExpansion CenteredMomentGaussEnergy
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma lowGram_pair_prefactor (C : CalibrationData) (W1 : ℝ→ℂ)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v Q : ℝ) (s t : {I : Id // Supported I}) :
    (lowGaussColumn C W1 Y σ v s*star (lowGaussColumn C W1 Y σ v t))*
      ((Q:ℂ)/((Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ)*(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ)))=
      ((Q/Y^3:ℝ):ℂ)*
        ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
          star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y))) := by
  calc
    _ = (Q:ℂ)*(lowGaussColumn C W1 Y σ v s/(Real.sqrt (Ideal.absNorm s.val:ℝ):ℂ))*
        star (lowGaussColumn C W1 Y σ v t/(Real.sqrt (Ideal.absNorm t.val:ℝ):ℂ)) := by
      simp only [Complex.star_def,map_mul,map_inv₀,Complex.conj_ofReal,div_eq_mul_inv,mul_inv_rev]
      ring
    _ = (Q:ℂ)*(lowGramScale Y*star (lowGramScale Y))*
        ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
          star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y))) := by
      rw [lowGaussColumn_unnormalized C W1 Y hY σ v s,lowGaussColumn_unnormalized C W1 Y hY σ v t]
      simp only [star_mul]
      ring
    _ = _ := by rw [lowGramScale_mul_star Y hY];simp only [div_eq_mul_inv,Complex.ofReal_mul,Complex.ofReal_inv]

theorem lowGram_source_poisson (C : CalibrationData) (W1 : ℝ→ℂ)
    (hW1 : HasCompactSupport W1) (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ)
    (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0<Q) :
    gaussEnergy (lowGaussColumns W1 hW1 Y hY) (fun s=>primaryGenerator s.val)
      (fun s=>(supported_span_primaryGenerator_iff s.val).mpr s.property)
      (lowGaussColumn C W1 Y σ v) U Q=
      ((Q/Y^3:ℝ):ℂ)*
        ∑s∈lowGaussColumns W1 hW1 Y hY,∑t∈lowGaussColumns W1 hW1 Y hY,
          ((lowGramCoefficient C σ s*lowGramProfile W1 v ((Ideal.absNorm s.val:ℝ)/Y))*
            star (lowGramCoefficient C σ t*lowGramProfile W1 v ((Ideal.absNorm t.val:ℝ)/Y)))*
          ∑'h : O,actualCorrelation (primaryGenerator s.val) (primaryGenerator t.val)
            ((supported_span_primaryGenerator_iff s.val).mpr s.property)
            ((supported_span_primaryGenerator_iff t.val).mpr t.property) (-h)*
            paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator s.val*primaryGenerator t.val)‖^2) := by
  rw [gaussEnergy_poisson _ _ _ _ U Q hQ]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro t ht
  have hes := congrArg Ideal.absNorm ((primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1)
  have het := congrArg Ideal.absNorm ((primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1)
  rw [hes,het,←mul_assoc,lowGram_pair_prefactor C W1 Y hY σ v Q s t,mul_assoc]

theorem lowGram_kernel_scale (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (s t : {I : Id // Supported I}) (h : O) :
    Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator s.val*primaryGenerator t.val)‖^2=
      ‖eisEmbedding h‖^2/((Y^2/Q)*((Ideal.absNorm s.val:ℝ)/Y)*((Ideal.absNorm t.val:ℝ)/Y)) := by
  simp_rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  rw [←Ideal.span_singleton_mul_span_singleton]
  rw [(primaryGenerator_spec s.val (supported_primaryGenerator_ne_zero s.val s.property)).1,
    (primaryGenerator_spec t.val (supported_primaryGenerator_ne_zero t.val t.property)).1,map_mul,Nat.cast_mul]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
