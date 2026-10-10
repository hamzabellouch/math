import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Analytic.TaylorCoefficients

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open Filter

local instance : Finset.HasAntidiagonal Exponent :=
  Finset.HasAntidiagonal.antidiagonalOfLocallyFinite

lemma absolute_add {c d : Exponent → ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hc : AbsolutelyConvergentAt c R) (hd : AbsolutelyConvergentAt d R) :
    AbsolutelyConvergentAt (c + d) R := by
  refine Summable.of_nonneg_of_le (fun p => by positivity) (fun p => ?_) (hc.add hd)
  change ‖c p + d p‖ * R ^ (p.1 + p.2) ≤ _
  calc
    _ ≤ (‖c p‖ + ‖d p‖) * R ^ (p.1 + p.2) :=
      mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hR _)
    _ = _ := by ring

lemma seriesEval_add {c d : Exponent → ℂ} {R : ℝ}
    (hc : AbsolutelyConvergentAt c R) (hd : AbsolutelyConvergentAt d R)
    {x z : ℂ} (hx : ‖x‖ ≤ R) (hz : ‖z‖ ≤ R) :
    seriesEval (c + d) x z = seriesEval c x z + seriesEval d x z := by
  simp only [seriesEval, Pi.add_apply, add_mul]
  exact (absolute_terms_summable hc hx hz).of_norm.tsum_add
    (absolute_terms_summable hd hx hz).of_norm

lemma eventually_polydisk {R : ℝ} (hR : 0 < R) :
    ∀ᶠ q : ℂ × ℂ in 𝓝 0, ‖q.1‖ < R ∧ ‖q.2‖ < R := by
  apply Metric.eventually_nhds_iff.mpr
  refine ⟨R, hR, fun q hq => ?_⟩
  simpa only [dist_zero_right, Prod.norm_def, max_lt_iff] using hq

lemma common_absolute_radius {c d : Exponent → ℂ}
    (hc : ConvergentSeries c) (hd : ConvergentSeries d) :
    ∃ R : ℝ, 0 < R ∧ AbsolutelyConvergentAt c R ∧ AbsolutelyConvergentAt d R := by
  obtain ⟨R, hR, hc⟩ := hc
  obtain ⟨S, hS, hd⟩ := hd
  refine ⟨min R S, lt_min hR hS, ?_, ?_⟩
  · exact absolute_mono hc (le_min hR.le hS.le) (min_le_left _ _)
  · exact absolute_mono hd (le_min hR.le hS.le) (min_le_right _ _)

lemma analyticCoefficients_add (f g : analyticFunctionAlgebra) :
    analyticCoefficients (f + g) = analyticCoefficients f + analyticCoefficients g := by
  obtain ⟨R, hR, hf, hg⟩ := common_absolute_radius
    (analyticCoefficients_spec f).1 (analyticCoefficients_spec g).1
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec (f + g)).1
    ⟨R, hR, absolute_add hR.le hf hg⟩
  filter_upwards [(analyticCoefficients_spec (f + g)).2,
    (analyticCoefficients_spec f).2, (analyticCoefficients_spec g).2,
    eventually_polydisk hR] with q hfg hfe hge hq
  rw [← hfg, seriesEval_add hf hg hq.1.le hq.2.le]
  change f.val q + g.val q = _
  rw [hfe, hge]

lemma analyticCoefficients_mul (f g : analyticFunctionAlgebra) :
    analyticCoefficients (f * g) = coeffConvolution (analyticCoefficients f)
      (analyticCoefficients g) := by
  obtain ⟨R, hR, hf, hg⟩ := common_absolute_radius
    (analyticCoefficients_spec f).1 (analyticCoefficients_spec g).1
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec (f * g)).1
    ⟨R, hR, absolute_convolution hR.le hf hg⟩
  filter_upwards [(analyticCoefficients_spec (f * g)).2,
    (analyticCoefficients_spec f).2, (analyticCoefficients_spec g).2,
    eventually_polydisk hR] with q hfg hfe hge hq
  rw [← hfg, seriesEval_convolution hf hg hq.1.le hq.2.le]
  change f.val q * g.val q = _
  rw [hfe, hge]

lemma analyticCoefficients_const (a : ℂ) :
    analyticCoefficients (algebraMap ℂ analyticFunctionAlgebra a) =
      fun e => if e = (0,0) then a else 0 := by
  let c : Exponent → ℂ := fun e => if e = (0,0) then a else 0
  have hc : ConvergentSeries c := by
    refine ⟨1, zero_lt_one, ?_⟩
    simp only [AbsolutelyConvergentAt, c, apply_ite, norm_zero, one_pow, mul_one]
    exact (hasSum_ite_eq (0,0) ‖a‖).summable
  have he (x z : ℂ) : seriesEval c x z = a := by
    simp [seriesEval, c, ite_mul]
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec _).1 hc
  filter_upwards [(analyticCoefficients_spec (algebraMap ℂ analyticFunctionAlgebra a)).2]
    with q hq
  rw [← hq, he]
  rfl

def analyticCoefficientLinear : analyticFunctionAlgebra →ₗ[ℂ] (Exponent → ℂ) where
  toFun := analyticCoefficients
  map_add' := analyticCoefficients_add
  map_smul' a f := by
    have h := analyticCoefficients_mul (algebraMap ℂ analyticFunctionAlgebra a) f
    rw [Algebra.smul_def, h, analyticCoefficients_const]
    ext e
    simp only [coeffConvolution, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (0,e)]
    · simp [show (0 : Exponent) = (0,0) from rfl]
    · intro ab hab hne
      have ha : ab.1 ≠ 0 := by
        intro hh
        have hx := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
        simp only [hh, zero_add] at hx
        exact hne (Prod.ext hh hx)
      have ha' : ab.1 ≠ (0,0) := ha
      simp [ha']
    · simp

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.AnalyticCoordinates
noncomputable section
open scoped BigOperators Topology
open PowerSeries Filter

local instance : Finset.HasAntidiagonal Exponent :=
  Finset.HasAntidiagonal.antidiagonalOfLocallyFinite

abbrev BiSeries := PowerSeries (PowerSeries ℂ)

def biCoeff (f : BiSeries) (e : Exponent) : ℂ := coeff e.1 (coeff e.2 f)

def biSeries (c : Exponent → ℂ) : BiSeries :=
  PowerSeries.mk (fun b => PowerSeries.mk (fun a => c (a,b)))

@[simp] lemma biCoeff_biSeries (c : Exponent → ℂ) (e : Exponent) :
    biCoeff (biSeries c) e = c e := by simp [biCoeff, biSeries]

lemma biCoeff_injective : Function.Injective biCoeff := by
  intro f g h
  apply PowerSeries.ext
  intro b
  apply PowerSeries.ext
  intro a
  exact congrFun h (a,b)

lemma biCoeff_mul (f g : BiSeries) (e : Exponent) :
    biCoeff (f * g) e = coeffConvolution (biCoeff f) (biCoeff g) e := by
  classical
  simp only [biCoeff, coeff_mul, map_sum]
  rw [← Finset.sum_product _ _
    (fun ij : (ℕ × ℕ) × (ℕ × ℕ) =>
      (coeff ij.2.1 (coeff ij.1.1 f)) * (coeff ij.2.2 (coeff ij.1.2 g)))]
  apply Finset.sum_bij (fun ij _ => ((ij.2.1,ij.1.1),(ij.2.2,ij.1.2)))
  · intro ij hij
    rcases Finset.mem_product.mp hij with ⟨h₁,h₂⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at h₁ h₂ ⊢
    exact Prod.ext h₂ h₁
  · intro i hi j hj he
    have h₁ := congrArg (fun p : Exponent × Exponent => (p.1.2,p.2.2)) he
    have h₂ := congrArg (fun p : Exponent × Exponent => (p.1.1,p.2.1)) he
    exact Prod.ext (by simpa using h₁) (by simpa using h₂)
  · intro p hp
    refine ⟨((p.1.2,p.2.2),(p.1.1,p.2.1)), ?_, rfl⟩
    rw [Finset.mem_product]
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp ⊢
    refine ⟨congrArg Prod.snd hp, ?_⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    exact congrArg Prod.fst hp
  · intro ij hij
    rfl

def analyticFormal : analyticFunctionAlgebra →ₐ[ℂ] BiSeries where
  toFun f := biSeries (analyticCoefficients f)
  map_one' := by
    apply biCoeff_injective
    ext e
    have h := analyticCoefficients_const 1
    simp only [map_one] at h
    simp only [biCoeff_biSeries, h]
    rcases e with ⟨a,b⟩
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [biCoeff, ha, hb]
  map_mul' f g := by
    apply biCoeff_injective
    ext e
    simp only [biCoeff_biSeries, analyticCoefficients_mul, biCoeff_mul]
    congr 1 <;> ext a <;> exact biCoeff_biSeries _ _ |>.symm
  map_zero' := by
    apply biCoeff_injective
    ext e
    have h := analyticCoefficients_const 0
    simp only [map_zero, ite_self] at h
    simp [h, biCoeff, biSeries]
  map_add' f g := by
    apply biCoeff_injective
    ext e
    simp [analyticCoefficients_add, biCoeff, biSeries]
  commutes' a := by
    apply biCoeff_injective
    ext e
    simp only [biCoeff_biSeries, analyticCoefficients_const]
    rw [PowerSeries.algebraMap_apply, PowerSeries.algebraMap_apply]
    simp only [Algebra.algebraMap_self]
    rcases e with ⟨k,b⟩
    by_cases hk : k = 0 <;> by_cases hb : b = 0 <;> simp [biCoeff, coeff_C, hk, hb]

lemma analyticCoefficients_congr (f g : analyticFunctionAlgebra)
    (h : f.val =ᶠ[𝓝 0] g.val) : analyticCoefficients f = analyticCoefficients g := by
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec f).1
    (analyticCoefficients_spec g).1
  exact (analyticCoefficients_spec f).2.symm.trans (h.trans (analyticCoefficients_spec g).2)

lemma analyticFormal_congr (f g : analyticFunctionAlgebra)
    (h : f.val =ᶠ[𝓝 0] g.val) : analyticFormal f = analyticFormal g := by
  exact congrArg biSeries (analyticCoefficients_congr f g h)

lemma analyticFormal_constantCoeff (f : analyticFunctionAlgebra) :
    constantCoeff (constantCoeff (analyticFormal f)) = f.val (0,0) := by
  have h := analyticCoefficients_eq_derivative f 0 0
  simpa [analyticFormal, biSeries, constantCoeff_mk, iteratedDeriv_zero] using h

lemma analyticCoefficients_monomial (f : analyticFunctionAlgebra) (e : Exponent) (c : ℂ)
    (heq : f.val =ᶠ[𝓝 0] (fun q => c * q.1 ^ e.1 * q.2 ^ e.2)) :
    analyticCoefficients f = fun p => if p = e then c else 0 := by
  let d : Exponent → ℂ := fun p => if p = e then c else 0
  have hd : ConvergentSeries d := by
    refine ⟨1, zero_lt_one, ?_⟩
    simp only [AbsolutelyConvergentAt, d, apply_ite, norm_zero, one_pow, mul_one]
    exact (hasSum_ite_eq e ‖c‖).summable
  have hde (x z : ℂ) : seriesEval d x z = c * x ^ e.1 * z ^ e.2 := by
    simp [seriesEval, d, ite_mul]
  apply convergent_expansion_unique _ _ (analyticCoefficients_spec f).1 hd
  filter_upwards [(analyticCoefficients_spec f).2, heq] with q hq hqq
  rw [← hq, hde, hqq]

end
end MaximalSeshadri.AnalyticCoordinates

namespace MaximalSeshadri.FormalCoordinates
noncomputable section
open PowerSeries

variable {F A B : Type*} [CommRing F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

def powerSeriesMapEquiv (e : A ≃ₐ[F] B) : PowerSeries A ≃ₐ[F] PowerSeries B :=
  AlgEquiv.ofAlgHom (PowerSeries.mapAlgHom e.toAlgHom)
    (PowerSeries.mapAlgHom e.symm.toAlgHom)
    (by ext f n; simp [PowerSeries.mapAlgHom_apply])
    (by ext f n; simp [PowerSeries.mapAlgHom_apply])

@[simp] lemma powerSeriesMapEquiv_coeff (e : A ≃ₐ[F] B) (f : PowerSeries A) (n : ℕ) :
    coeff n (powerSeriesMapEquiv e f) = e (coeff n f) := by
  change coeff n (PowerSeries.map e.toRingHom f) = _
  exact coeff_map ..

def binaryEquiv (F : Type*) [CommRing F] :
    MvPowerSeries (Fin 2) F ≃ₐ[F] PowerSeries (PowerSeries F) :=
  (MvPowerSeries.finSuccEquiv F 1).trans (powerSeriesMapEquiv
    ((MvPowerSeries.finSuccEquiv F 0).trans
      (powerSeriesMapEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) F))))

lemma binaryEquiv_coeff (f : MvPowerSeries (Fin 2) F) (a b : ℕ) :
    coeff a (coeff b (binaryEquiv F f)) =
      MvPowerSeries.coeff (Finsupp.cons b (Finsupp.cons a 0)) f := by
  simp only [binaryEquiv, AlgEquiv.trans_apply, powerSeriesMapEquiv_coeff]
  change MvPowerSeries.coeff 0 (coeff a (MvPowerSeries.finSuccEquiv F 0
    (coeff b (MvPowerSeries.finSuccEquiv F 1 f)))) = _
  rw [MvPowerSeries.coeff_coeff_finSuccEquiv, MvPowerSeries.coeff_coeff_finSuccEquiv]

@[simp] lemma binaryEquiv_X_zero :
    binaryEquiv F (MvPowerSeries.X 0) = (PowerSeries.X : PowerSeries (PowerSeries F)) := by
  simp [binaryEquiv, powerSeriesMapEquiv, PowerSeries.mapAlgHom_apply]

@[simp] lemma binaryEquiv_X_one :
    binaryEquiv F (MvPowerSeries.X 1) = PowerSeries.C (PowerSeries.X : PowerSeries F) := by
  unfold binaryEquiv
  rw [AlgEquiv.trans_apply]
  have hx : MvPowerSeries.finSuccEquiv F 1 (MvPowerSeries.X 1) =
      PowerSeries.C (MvPowerSeries.X 0) :=
    MvPowerSeries.finSuccEquiv_X_succ (R := F) (0 : Fin 1)
  rw [hx]
  simp [powerSeriesMapEquiv, PowerSeries.mapAlgHom_apply]

lemma binaryEquiv_constantCoeff (f : MvPowerSeries (Fin 2) F) :
    constantCoeff (constantCoeff (binaryEquiv F f)) = MvPowerSeries.constantCoeff f := by
  have h := binaryEquiv_coeff f 0 0
  simpa using h

end
end MaximalSeshadri.FormalCoordinates


end
end
end

end OAI
