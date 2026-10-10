import Mathlib
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGeometry
import OAI.Probability.CriticalPercolation.Growth.HomogeneousCover
import OAI.Probability.CriticalPercolation.Growth.HomogeneousGrowth
import OAI.Probability.CriticalPercolation.Growth.HomogeneousPolynomialSpace
import OAI.Probability.CriticalPercolation.Harmonic.GramGrowthScales
import OAI.Probability.CriticalPercolation.Harmonic.HomogeneousGramScales
import OAI.Probability.CriticalPercolation.LinearGroups.MatrixLowGrowthSubspace

namespace OAI

section
noncomputable section
open Set Function Module
open scoped Classical Pointwise BigOperators Matrix

namespace CriticalPercolation.HomogeneousAnalysis.Geometry
open HarmonicAnalysis

variable {A ι : Type*} [Fintype ι] (W : Geometry A)

lemma harmonic_functionCombination (v : ι → A → ℝ) (hv : ∀ i, W.IsHarmonic (v i))
    (a : ι → ℝ) : W.IsHarmonic (functionCombination v a) := by
  rw [functionCombination_eq_linearCombination,Fintype.linearCombination_apply]
  change (∑ i, a i • v i)∈W.harmonicSpace
  exact W.harmonicSpace.sum_mem (fun i _ => W.harmonicSpace.smul_mem (a i) (hv i))

lemma scale_ratio_strict (K s L r R : ℕ) (hr : 1 ≤ r)
    (hscale : 10^(2*L)*r ≤ R) (hL : 8*K^4*s < 10^(4*L)) :
    8*(K:ℝ)^4*(s:ℝ)*(r:ℝ)^2 < (R:ℝ)^2 := by
  have hr' : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hs : (10:ℝ)^(2*L)*(r:ℝ) ≤ R := by exact_mod_cast hscale
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (10:ℝ)^(2*L)*(r:ℝ)) hs 2
  have hLp : 8*(K:ℝ)^4*(s:ℝ) < (10:ℝ)^(4*L) := by exact_mod_cast hL
  have hh := mul_lt_mul_of_pos_right hLp (sq_pos_of_pos hr')
  have he : ((10:ℝ)^(2*L)*(r:ℝ))^2=(10:ℝ)^(4*L)*(r:ℝ)^2 := by
    rw [mul_pow,←pow_mul (10:ℝ)]
    congr 2
    ring
  rw [he] at hp
  exact hh.trans_le hp

theorem harmonic_independent_card_bound (d k : ℕ) (hg : W.HasDegree d)
    (v : ι → A → ℝ) (hharm : ∀ i, W.IsHarmonic (v i))
    (hpol : ∀ i, W.HasPolynomialGrowth k (v i)) (hli : LinearIndependent ℝ v)
    (L : ℕ) (hL : 0 < L)
    (hgap : 8*(10^(4*(2*d+2*k+1)))^4*W.degree < 10^(4*L)) :
    Fintype.card ι ≤ 2*(10^(4*(2*d+2*k+1)))^L := by
  by_cases hm : Fintype.card ι=0
  · simp only [hm]; positivity
  have hm' : 0 < Fintype.card ι := Nat.pos_of_ne_zero hm
  let K : ℕ := 10^(4*(2*d+2*k+1))
  have hK : 1 < (K:ℝ) := by
    have hh : 10 ≤ K := by
      change 10 ≤ 10^(4*(2*d+2*k+1))
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < 10)
        (by omega : 1 ≤ 4*(2*d+2*k+1))
    have hh' : (10:ℝ) ≤ K := by exact_mod_cast hh
    linarith
  obtain ⟨r,R,hr,hR,hrR,hscale,hvol,hdet,hpack,hPD⟩ :=
    W.function_gram_paired_scales d k hg v hpol hli hm' L hL 1
  have hdet' : (functionGram (W.ball (5*R)) v).det ≤
      (K:ℝ)^(Fintype.card ι)*(functionGram (W.ball R) v).det := by
    simpa only [K,Nat.cast_pow,Nat.cast_ofNat] using hdet
  obtain ⟨V,hVdim,hVratio⟩ := exists_low_growth_subspace
    (functionGram (W.ball R) v) (functionGram (W.ball (5*R)) v) hPD
    (functionGram_hermitian _ _) (functionGram_quadratic_mono (W.ball_mono (by omega)) v)
    (K:ℝ) hK hdet'
  obtain ⟨J,hJR,hJ,hJcard,hcover⟩ := W.exists_word_ball_packing R r
  have hJbound : J.card ≤ K^L :=
    le_of_mul_le_mul_right (hJcard.trans hpack) (W.ball_card_pos r)
  have hstrict := scale_ratio_strict K W.degree L r R hr hscale hgap
  let avg : V →ₗ[ℝ] (J → ℝ) :=
    { toFun := fun a c => ∑ x∈W.around c.val (2*r), functionCombination v a.val x
      map_add' := by
        intro a b
        funext c
        simp only [Submodule.coe_add,functionCombination,Pi.add_apply,add_mul,Finset.sum_add_distrib]
      map_smul' := by
        intro a b
        funext c
        simp only [Submodule.coe_smul,functionCombination,Pi.smul_apply,smul_eq_mul,
          mul_assoc,←Finset.mul_sum,RingHom.id_apply] }
  have hInjective : Injective avg := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro a ha
    apply Subtype.ext
    by_contra hane
    have hane' : a.val≠0 := hane
    have hQ : 0 < squareMass (W.ball R) (functionCombination v a.val) := by
      have hh := (Matrix.posDef_iff_dotProduct_mulVec.mp hPD).2 hane'
      simpa only [star_trivial,←functionGram_quadratic,matrixQuadratic] using hh
    have havg : ∀ c∈J, (∑ x∈W.around c (2*r), functionCombination v a.val x)=0 := by
      intro c hc
      exact congrFun ha ⟨c,hc⟩
    have hc := W.harmonic_cover_kernel_bound (W.balanced_suborbits d hg) R r K hR hrR J hJR hJ hcover hvol
      (functionCombination v a.val) (W.harmonic_functionCombination v hharm _) havg
    have hl := hVratio a.val a.property
    rw [functionGram_quadratic,functionGram_quadratic] at hl
    have hm := mul_le_mul_of_nonneg_left hl
      (by positivity : 0 ≤ 8*(K:ℝ)^2*(W.degree:ℝ)*(r:ℝ)^2)
    have hlow := mul_lt_mul_of_pos_right hstrict hQ
    nlinarith
  have hdim : Module.finrank ℝ V ≤ J.card := by
    have hh := LinearMap.finrank_le_finrank_of_injective hInjective
    simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using hh
  exact hVdim.trans (Nat.mul_le_mul_left 2 (hdim.trans hJbound))

omit [Fintype ι] in

theorem polynomialHarmonicSpace_finiteDimensional (d k : ℕ)
    (hg : W.HasDegree d) :
    FiniteDimensional ℝ (W.polynomialHarmonicSpace k) := by
  let K : ℕ := 10^(4*(2*d+2*k+1))
  let L : ℕ := 8*K^4*W.degree+1
  have hL : 0 < L := by dsimp [L]; omega
  have hgap : 8*K^4*W.degree < 10^(4*L) := by
    have hpow : L < 10^L := L.lt_two_pow_self.trans_le (Nat.pow_le_pow_left (by omega) L)
    have hm : 10^L ≤ 10^(4*L) := Nat.pow_le_pow_right (by omega) (by omega)
    exact (by dsimp [L]; omega : 8*K^4*W.degree < L).trans (hpow.trans_le hm)
  let B := 2*K^L
  let H := W.polynomialHarmonicSpace k
  let b := Module.Free.chooseBasis ℝ H
  have hbound {n : ℕ} (w : Fin n → H) (hw : LinearIndependent ℝ w) : n ≤ B := by
    have hj : LinearIndependent ℝ (fun i => (w i:A → ℝ)) :=
      hw.map' H.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have hh := W.harmonic_independent_card_bound d k hg (fun i => (w i:A → ℝ))
      (fun i => (w i).property.1) (fun i => (w i).property.2) hj L hL hgap
    simpa only [Fintype.card_fin] using hh
  have hfinite : Finite (Module.Free.ChooseBasisIndex ℝ H) := by
    by_contra h
    let : Infinite (Module.Free.ChooseBasisIndex ℝ H) := not_finite_iff_infinite.mp h
    let e : Fin (B+1) ↪ Module.Free.ChooseBasisIndex ℝ H :=
      (Fin.valEmbedding).trans (Infinite.natEmbedding _)
    have hh := hbound (fun i => b (e i)) (b.linearIndependent.comp e e.injective)
    omega
  let := hfinite
  exact Module.Finite.of_basis b

end CriticalPercolation.HomogeneousAnalysis.Geometry
end
end

end OAI
