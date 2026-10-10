import Mathlib
import OAI.NumberTheory.CubicGauss.PrimitiveGauss
import OAI.NumberTheory.CubicGauss.ResiduePoisson

namespace OAI

/-! Hecke theta functional equations, rapid decay and completed Mellin series. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment.HeckeTheta

 

def heckeGauss (q : Eisenstein) (hq : q ≠ 0) (χ : MulChar (Residues q) ℂ) : ℂ :=
  ∑' v : Residues q, χ v * residueTraceChar q hq v

lemma residueFourier_primitive (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : FinitePrimitive χ) (b : Eisenstein) :
    residueFourier q χ b =
      χ⁻¹ (Ideal.Quotient.mk (modulus q) b) * heckeGauss q hq χ := by
  let : Finite (Residues q) := finite_residues hq
  let : Fintype (Residues q) := Fintype.ofFinite _
  simp only [residueFourier, heckeGauss, ← residueTraceChar_mul_mk q hq, tsum_fintype]
  simpa only [gaussSum, AddChar.mulShift_apply, mul_comm] using
    primitive_gaussSum_mulShift χ hχ (residueTraceChar q hq)
      (Ideal.Quotient.mk (modulus q) b)

lemma heckeGauss_norm (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : FinitePrimitive χ) :
    ‖heckeGauss q hq χ‖ = Real.sqrt (norm q) := by
  let : Finite (Residues q) := finite_residues hq
  let : Fintype (Residues q) := Fintype.ofFinite _
  have hc : (Fintype.card (Residues q) : ℝ) = norm q := by
    rw [← Nat.card_eq_fintype_card, residues_card hq, normNat_cast]
  simpa only [heckeGauss, tsum_fintype, gaussSum, hc] using
    primitive_gaussSum_norm χ hχ (residueTraceChar q hq) (residueTraceChar_primitive q hq)

 

theorem primitive_theta_reciprocity (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : FinitePrimitive χ)
    (t : ℝ) (ht : 0 < t) :
    residueTheta q χ t =
      (2 * heckeGauss q hq χ / ((Real.sqrt 3 : ℂ) * norm q * t)) *
        residueTheta q (χ⁻¹ : MulChar (Residues q) ℂ) (4/(3*norm q*t)) := by
  rw [residue_theta_poisson q hq χ t ht]
  simp_rw [residueFourier_primitive q hq χ hχ, residueTheta]
  have he (b : Eisenstein) :
      Complex.exp (-(4 * (Real.pi : ℂ)) / (3 * t * norm q) * (norm b : ℂ)) *
          (χ⁻¹ (Ideal.Quotient.mk (modulus q) b) * heckeGauss q hq χ) =
        heckeGauss q hq χ * (χ⁻¹ (Ideal.Quotient.mk (modulus q) b) *
          Complex.exp (-(Real.pi : ℂ) * (4/(3*norm q*t) : ℝ) * (norm b : ℂ))) := by
    have heq : -(4*(Real.pi : ℂ))/(3*t*norm q)*(norm b : ℂ) =
        -(Real.pi : ℂ)*(4/(3*norm q*t) : ℝ)*(norm b : ℂ) := by
      push_cast
      ring
    rw [heq]
    ring
  simp_rw [he, tsum_mul_left]
  ring

 

def heckeRootNumber (q : Eisenstein) (hq : q ≠ 0) (χ : MulChar (Residues q) ℂ) : ℂ :=
  heckeGauss q hq χ / (Real.sqrt (norm q) : ℂ)

lemma heckeRootNumber_norm (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : FinitePrimitive χ) :
    ‖heckeRootNumber q hq χ‖ = 1 := by
  rw [heckeRootNumber, norm_div, heckeGauss_norm q hq χ hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact div_self (Real.sqrt_pos.mpr (norm_pos hq)).ne'

 

def heckeScale (q : Eisenstein) : ℝ := 2/(Real.sqrt 3 * Real.sqrt (norm q))

def heckeTheta (q : Eisenstein) (χ : MulChar (Residues q) ℂ) (t : ℝ) : ℂ :=
  residueTheta q χ (heckeScale q * t)

lemma heckeScale_pos (q : Eisenstein) (hq : q ≠ 0) : 0 < heckeScale q := by
  unfold heckeScale
  positivity [norm_pos hq]

lemma heckeScale_eq (q : Eisenstein) :
    heckeScale q = 2/Real.sqrt (3*norm q) := by
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
  rfl

 

theorem heckeTheta_functional_equation (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : FinitePrimitive χ)
    (t : ℝ) (ht : 0 < t) :
    heckeTheta q χ (1/t) =
      heckeRootNumber q hq χ * t * heckeTheta q χ⁻¹ t := by
  have hs3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3)).ne'
  have hsq : Real.sqrt (norm q) ≠ 0 := (Real.sqrt_pos.mpr (norm_pos hq)).ne'
  have hs3c : (Real.sqrt 3 : ℂ)^2=3 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hsqc : (Real.sqrt (norm q) : ℂ)^2=(norm q : ℂ) := by
    exact_mod_cast Real.sq_sqrt (norm_nonneg q)
  have harg : 4/(3*norm q*(heckeScale q*(1/t)))=heckeScale q*t := by
    unfold heckeScale
    field_simp [hs3, hsq, ht.ne', (norm_pos hq).ne']
    rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤3),Real.sq_sqrt (norm_nonneg q)]
    ring
  unfold heckeTheta
  rw [primitive_theta_reciprocity q hq χ hχ (heckeScale q*(1/t))
    (mul_pos (heckeScale_pos q hq) (one_div_pos.mpr ht)), harg]
  congr 1
  simp only [heckeRootNumber, heckeScale, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_one]
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h3' : (Real.sqrt 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs3
  have hq' : (Real.sqrt (norm q) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq
  have hn' : (norm q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_pos hq).ne'
  rw [← hsqc]
  field_simp


open Filter Asymptotics Set MeasureTheory

lemma gaussian_norm (t : ℝ) (a : Eisenstein) :
    ‖Complex.exp (-(Real.pi : ℂ)*t*(norm a : ℂ))‖ =
      Real.exp (-Real.pi*t*norm a) := by
  rw [Complex.norm_exp]
  congr 1
  simp

lemma norm_one_le {a : Eisenstein} (ha : a ≠ 0) : 1 ≤ norm a := by
  rw [← normNat_cast]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (normNat_ne_zero ha)

lemma weighted_gaussian_continuous (q : Eisenstein) (hq : q ≠ 0)
    (w : Residues q → ℂ) : ContinuousOn (residueTheta q w) (Ioi 0) := by
  intro t ht
  change 0 < t at ht
  have hs := (weighted_lattice_gaussian_summable q hq w (t/2) (half_pos ht)).norm
  have hc : ContinuousOn (residueTheta q w) (Ioi (t/2)) := by
    refine continuousOn_tsum (fun a => ?_) hs ?_
    · fun_prop
    · intro a x hx
      rw [norm_mul, norm_mul, gaussian_norm, gaussian_norm]
      apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
      apply Real.exp_le_exp.mpr
      simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hx.le Real.pi_pos.le) (norm_nonneg a))
  exact (hc.continuousAt (isOpen_Ioi.mem_nhds (by change t/2<t; linarith))).continuousWithinAt

 

lemma weighted_theta_exponential_bound (q : Eisenstein) (hq : q ≠ 0)
    (w : Residues q → ℂ) (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      ‖residueTheta q w (s*t) - w 0‖ ≤ C * Real.exp (-(Real.pi*s/2)*t) := by
  let b (a : Eisenstein) : ℝ := ‖w (Ideal.Quotient.mk (modulus q) a) *
    Complex.exp (-(Real.pi : ℂ)*((s/2 : ℝ) : ℂ)*(norm a : ℂ))‖
  have hb : Summable b :=
    (weighted_lattice_gaussian_summable q hq w (s/2) (half_pos hs)).norm
  refine ⟨∑' a, b a, ?_⟩
  intro t ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have he := (weighted_lattice_gaussian_summable q hq w (s*t) (mul_pos hs ht0)).tsum_eq_add_tsum_ite 0
  have hz : (norm (0 : Eisenstein)) = 0 := by simp [norm]
  simp only [map_zero, hz, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at he
  rw [residueTheta, he, add_sub_cancel_left]
  have hbound (a : Eisenstein) :
      ‖if a=0 then 0 else w (Ideal.Quotient.mk (modulus q) a) *
        Complex.exp (-(Real.pi : ℂ)*((s*t : ℝ) : ℂ)*(norm a : ℂ))‖ ≤
      b a * Real.exp (-(Real.pi*s/2)*t) := by
    split_ifs with ha
    · exact (by rw [_root_.norm_zero]; dsimp [b]; positivity)
    · dsimp [b]
      rw [norm_mul, norm_mul, gaussian_norm, gaussian_norm]
      simp only [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (_root_.norm_nonneg _)
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hn := norm_one_le ha
      have htn : (t+norm a)/2 ≤ t*norm a := by
        nlinarith [mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr hn)]
      have hp : 0 ≤ Real.pi*s := le_of_lt (mul_pos Real.pi_pos hs)
      nlinarith [mul_le_mul_of_nonneg_left htn hp]
  exact tsum_of_norm_bounded (hb.hasSum.mul_right _) hbound

lemma weighted_theta_rapid_decay (q : Eisenstein) (hq : q ≠ 0)
    (w : Residues q → ℂ) (s : ℝ) (hs : 0 < s) (r : ℝ) :
    (fun t => residueTheta q w (s*t)-w 0) =O[atTop] (fun t : ℝ => t^r) := by
  obtain ⟨C,hC⟩ := weighted_theta_exponential_bound q hq w s hs
  have hE : (fun t => residueTheta q w (s*t)-w 0) =O[atTop]
      (fun t : ℝ => Real.exp (-(Real.pi*s/2)*t)) := by
    refine Asymptotics.IsBigO.of_bound C ?_
    apply (eventually_ge_atTop 1).mono
    intro t ht
    simpa only [Real.norm_eq_abs, Real.abs_exp] using hC t ht
  exact hE.trans (isLittleO_exp_neg_mul_rpow_atTop (by positivity [Real.pi_pos]) r).isBigO

lemma heckeTheta_continuous (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) : ContinuousOn (heckeTheta q χ) (Ioi 0) := by
  apply (weighted_gaussian_continuous q hq χ).comp (by fun_prop)
  intro t ht
  exact mul_pos (heckeScale_pos q hq) ht

lemma heckeTheta_rapid_decay (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (r : ℝ) :
    (fun t => heckeTheta q χ t - χ 0) =O[atTop] (fun t : ℝ => t^r) :=
  weighted_theta_rapid_decay q hq χ _ (heckeScale_pos q hq) r

 

def heckeThetaFEPair (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : FinitePrimitive χ) : WeakFEPair ℂ where
  f := heckeTheta q χ
  g := heckeTheta q χ⁻¹
  k := 1
  ε := heckeRootNumber q hq χ
  f₀ := χ 0
  g₀ := χ⁻¹ 0
  hf_int := (heckeTheta_continuous q hq χ).locallyIntegrableOn measurableSet_Ioi
  hg_int := (heckeTheta_continuous q hq χ⁻¹).locallyIntegrableOn measurableSet_Ioi
  hk := zero_lt_one
  hε := by
    intro h
    have hh := heckeRootNumber_norm q hq χ hχ
    rw [h, _root_.norm_zero] at hh
    exact zero_ne_one hh
  h_feq := by
    intro t ht
    simpa only [Real.rpow_one, smul_eq_mul] using heckeTheta_functional_equation q hq χ hχ t ht
  hf_top := heckeTheta_rapid_decay q hq χ
  hg_top := heckeTheta_rapid_decay q hq χ⁻¹

end CubicFirstMoment.HeckeTheta

namespace CubicFirstMoment.HeckeTheta
open Filter Asymptotics Set MeasureTheory

lemma mulChar_zero_of_nonprincipal {R : Type*} [CommRing R]
    (χ : MulChar R ℂ) (hχ : χ ≠ 1) : χ 0=0 := by
  by_cases hR : (0 : R)=1
  · have : Subsingleton R := subsingleton_of_zero_eq_one hR
    apply (hχ ?_).elim
    ext a
    rw [Subsingleton.elim a 1]
    simp
  · have : Nontrivial R := nontrivial_of_ne 0 1 hR
    exact χ.map_zero

lemma heckeThetaFEPair_strong (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : FinitePrimitive χ) (hn : χ ≠ 1) :
    IsStrongFEPair (heckeThetaFEPair q hq χ hχ) := by
  constructor
  · exact mulChar_zero_of_nonprincipal χ hn
  · exact mulChar_zero_of_nonprincipal χ⁻¹ (by simpa using hn)

 

def completedHeckeMellin (q : Eisenstein) (χ : MulChar (Residues q) ℂ) (s : ℂ) : ℂ :=
  (1/6 : ℂ) * mellin (heckeTheta q χ) s

 

theorem completedHeckeMellin_entire (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : FinitePrimitive χ) (hn : χ ≠ 1) :
    Differentiable ℂ (completedHeckeMellin q χ) := by
  have hP := heckeThetaFEPair_strong q hq χ hχ hn
  have hd := hP.differentiable_Λ
  rw [hP.Λ_eq] at hd
  exact hd.const_mul _

 

theorem completedHeckeMellin_functional_equation (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hχ : FinitePrimitive χ) (hn : χ ≠ 1) (s : ℂ) :
    completedHeckeMellin q χ s =
      heckeRootNumber q hq χ * completedHeckeMellin q χ⁻¹ (1-s) := by
  have hP := heckeThetaFEPair_strong q hq χ hχ hn
  have hF := (heckeThetaFEPair q hq χ hχ).functional_equation (1-s)
  rw [hP.Λ_eq, hP.symm_Λ_eq] at hF
  change mellin (heckeTheta q χ) (1-(1-s)) =
    heckeRootNumber q hq χ • mellin (heckeTheta q χ⁻¹) (1-s) at hF
  rw [sub_sub_cancel, smul_eq_mul] at hF
  simp only [completedHeckeMellin, hF]
  ring

lemma shifted_int_rpow_summable (r : ℝ) (hr : 1 < r) :
    Summable (fun n : ℤ => (1+|(n : ℝ)|)^(-r)) := by
  have h := (Real.summable_one_div_int_add_rpow (1/2) r).mpr hr
  apply Summable.of_nonneg_of_le (fun n => Real.rpow_nonneg (by positivity) _) _ h
  intro n
  have hl : 0 < |(n : ℝ)+1/2| := by
    apply abs_pos.mpr
    intro hh
    have hz : (2*n+1 : ℤ)=0 := by exact_mod_cast (show 2*(n : ℝ)+1=0 by linarith)
    omega
  have hb : |(n : ℝ)+1/2| ≤ 1+|(n : ℝ)| := by
    have := abs_add_le (n : ℝ) (1/2)
    norm_num at this
    linarith
  rw [one_div, ← Real.rpow_neg (abs_nonneg _)]
  exact Real.rpow_le_rpow_of_nonpos hl hb (by linarith : -r≤0)

 

lemma norm_coords_product_bound (m n : ℤ) (h : ofCoords m n ≠ 0) :
    (1+|(m : ℝ)|)*(1+|(n : ℝ)|) ≤ 4*norm (ofCoords m n) := by
  have h1 := norm_one_le h
  have hn : norm (ofCoords m n) = (m : ℝ)^2 - (m : ℝ)*(n : ℝ)+(n : ℝ)^2 := by
    simp only [norm,ofCoords_coe,coordinates_norm]
    push_cast
    rfl
  rw [hn] at h1 ⊢
  nlinarith [sq_nonneg (|(m : ℝ)|-1), sq_nonneg (|(n : ℝ)|-1),
    sq_nonneg (|(m : ℝ)|-|(n : ℝ)|), sq_abs (m : ℝ), sq_abs (n : ℝ),
    sq_nonneg ((m : ℝ)-(n : ℝ))]

lemma lattice_norm_rpow_summable (r : ℝ) (hr : 1 < r) :
    Summable (fun a : Eisenstein => (norm a)^(-r)) := by
  have hr0 : 0<r := lt_trans zero_lt_one hr
  let f (n : ℤ) := (1+|(n : ℝ)|)^(-r)
  have hf : Summable f := shifted_int_rpow_summable r hr
  have hprod := (hf.mul_of_nonneg hf (fun _ => Real.rpow_nonneg (by positivity) _)
    (fun _ => Real.rpow_nonneg (by positivity) _)).mul_left ((4 : ℝ)^r)
  apply (latticeEquiv.summable_iff).mp
  apply Summable.of_nonneg_of_le (fun _ => Real.rpow_nonneg (norm_nonneg _) _) _ hprod
  rintro ⟨n,m⟩
  change norm (ofCoords m n)^(-r) ≤ 4^r*(f n*f m)
  by_cases hz : ofCoords m n=0
  · simp [hz,norm,Real.zero_rpow (by linarith : -r ≠ 0),f]
    positivity
  · have hp : 0 < (1+|(m : ℝ)|)*(1+|(n : ℝ)|)/4 := by positivity
    have hb : (1+|(m : ℝ)|)*(1+|(n : ℝ)|)/4 ≤ norm (ofCoords m n) := by
      have := norm_coords_product_bound m n hz
      linarith
    have he := Real.rpow_le_rpow_of_nonpos hp hb (by linarith : -r ≤ 0)
    convert he using 1
    rw [Real.div_rpow (by positivity) (by norm_num : (0:ℝ)≤4),
      Real.mul_rpow (by positivity) (by positivity), Real.rpow_neg (by norm_num : (0:ℝ)≤4)]
    dsimp [f]
    simp only [div_eq_mul_inv, inv_inv]
    ring

instance : Countable Eisenstein := Countable.of_equiv (ℤ × ℤ) latticeEquiv

lemma weighted_norm_rpow_summable (q : Eisenstein) (hq : q ≠ 0)
    (w : Residues q → ℂ) (r : ℝ) (hr : 1 < r) :
    Summable (fun a : Eisenstein => ‖w (Ideal.Quotient.mk (modulus q) a)‖ / norm a ^ r) := by
  let : Finite (Residues q) := finite_residues hq
  let : Fintype (Residues q) := Fintype.ofFinite _
  have hs := (lattice_norm_rpow_summable r hr).mul_left (∑ v : Residues q, ‖w v‖)
  apply Summable.of_nonneg_of_le (fun a => div_nonneg (_root_.norm_nonneg _)
    (Real.rpow_nonneg (norm_nonneg a) _)) _ hs
  intro a
  rw [div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg a)]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (fun v _ => _root_.norm_nonneg (w v))
      (Finset.mem_univ (Ideal.Quotient.mk (modulus q) a)))
    (Real.rpow_nonneg (norm_nonneg a) _)

 

def elementHeckeSeries (q : Eisenstein) (χ : MulChar (Residues q) ℂ) (s : ℂ) : ℂ :=
  (1/6 : ℂ) * ∑' a : Eisenstein, χ (Ideal.Quotient.mk (modulus q) a) / (norm a : ℂ)^s

lemma elementHeckeSeries_summable (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (s : ℂ) (hs : 1 < s.re) :
    Summable (fun a : Eisenstein => χ (Ideal.Quotient.mk (modulus q) a) / (norm a : ℂ)^s) := by
  apply summable_norm_iff.mp
  simpa only [norm_div, Complex.norm_cpow_eq_rpow_re_of_nonneg (norm_nonneg _) (by linarith : s.re ≠ 0)]
    using weighted_norm_rpow_summable q hq χ s.re hs

lemma heckeTheta_mellin_hasSum (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hn : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    HasSum (fun a : Eisenstein => (Real.pi : ℂ)^(-s) * Complex.Gamma s *
      χ (Ideal.Quotient.mk (modulus q) a) / ((heckeScale q * norm a : ℝ) : ℂ)^s)
      (mellin (heckeTheta q χ) s) := by
  have hscale := heckeScale_pos q hq
  refine hasSum_mellin_pi_mul ?_ (by linarith : 0 < s.re) ?_ ?_
  · intro a
    by_cases ha : a=0
    · left
      simp [ha, mulChar_zero_of_nonprincipal χ hn]
    · right
      exact mul_pos hscale (norm_pos ha)
  · intro t ht
    change HasSum _ (residueTheta q χ (heckeScale q*t))
    convert! (weighted_lattice_gaussian_summable q hq χ (heckeScale q*t)
      (mul_pos hscale ht)).hasSum using 1
    ext a
    rw [Complex.ofReal_exp]
    congr 1
    congr 1
    push_cast
    ring
  · have hh := weighted_norm_rpow_summable q hq χ s.re hs
    convert! hh.div_const (heckeScale q ^ s.re) using 1
    ext a
    rw [Real.mul_rpow hscale.le (norm_nonneg _)]
    ring

 
theorem completedHeckeMellin_eq_series (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hn : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    completedHeckeMellin q χ s =
      (Real.pi : ℂ)^(-s) * (heckeScale q : ℂ)^(-s) * Complex.Gamma s *
        elementHeckeSeries q χ s := by
  have hsum := heckeTheta_mellin_hasSum q hq χ hn s hs
  rw [completedHeckeMellin, ← hsum.tsum_eq]
  have he (a : Eisenstein) :
      (Real.pi : ℂ)^(-s) * Complex.Gamma s * χ (Ideal.Quotient.mk (modulus q) a) /
        ((heckeScale q*norm a : ℝ) : ℂ)^s =
      ((Real.pi : ℂ)^(-s) * (heckeScale q : ℂ)^(-s) * Complex.Gamma s) *
        (χ (Ideal.Quotient.mk (modulus q) a) / (norm a : ℂ)^s) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (heckeScale_pos q hq).le
      (norm_nonneg a)]
    simp only [Complex.cpow_neg, div_eq_mul_inv, mul_inv_rev]
    ring
  simp_rw [he]
  rw [tsum_mul_left, elementHeckeSeries]
  ring

 
theorem completedHeckeMellin_eq_exact_completion (q : Eisenstein) (hq : q ≠ 0)
    (χ : MulChar (Residues q) ℂ) (hn : χ ≠ 1) (s : ℂ) (hs : 1 < s.re) :
    completedHeckeMellin q χ s =
      ((Real.sqrt (3*norm q)/(2*Real.pi) : ℝ) : ℂ)^s * Complex.Gamma s *
        elementHeckeSeries q χ s := by
  rw [completedHeckeMellin_eq_series q hq χ hn s hs]
  have he : (Real.pi : ℂ)^(-s) * (heckeScale q : ℂ)^(-s) =
      ((Real.sqrt (3*norm q)/(2*Real.pi) : ℝ) : ℂ)^s := by
    rw [← Complex.mul_cpow_ofReal_nonneg Real.pi_pos.le (heckeScale_pos q hq).le,
      ← Complex.ofReal_mul, Complex.cpow_neg,
      ← Complex.inv_cpow_ofReal_nonneg (mul_pos Real.pi_pos (heckeScale_pos q hq)).le,
      ← Complex.ofReal_inv]
    congr 2
    rw [heckeScale_eq]
    field_simp
  rw [he]

end CubicFirstMoment.HeckeTheta
end

end OAI
