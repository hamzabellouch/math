import Mathlib
import OAI.Combinatorics.StripMass.InverseIntegrability

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace StripPfaffian
noncomputable section
open scoped BigOperators
theorem pfaffian_schur_even (n : ℕ) (hn : Even n) (x : Fin n → ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x) :
    pfaffian n (schurMatrix x) = schurProduct x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [schurProduct]
  | one => exact False.elim (by simp at hn)
  | more n ih _ =>
    have he : Even n := by
      rw [Nat.even_iff] at *
      omega
    revert hd hx
    refine Fin.snocCases (fun y b => ?_) x
    refine Fin.snocCases (fun z a => ?_) y
    intro hd hx
    apply pfaffian_schur_snoc_snoc he z a b
    · apply ih he
      · intro i j
        simpa only [Fin.snoc_castSucc] using hd i.castSucc.castSucc j.castSucc.castSucc
      · intro i j hij
        apply Fin.castSucc_injective
        apply Fin.castSucc_injective
        apply hx
        simpa only [Fin.snoc_castSucc] using hij
    · intro i j
      simpa only [Fin.snoc_castSucc] using hd i.castSucc.castSucc j.castSucc.castSucc
    · intro i
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
        hd i.castSucc.castSucc (Fin.last n).castSucc
    · intro i
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
        hd i.castSucc.castSucc (Fin.last (n + 1))
    · simpa only [Fin.snoc_castSucc, Fin.snoc_last] using
        hd (Fin.last n).castSucc (Fin.last (n + 1))
    · intro hab
      exact Fin.castSucc_ne_last (Fin.last n) (hx (by
        simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hab.symm))

lemma pfaffian_schur_odd_snoc {n : ℕ} (hn : Even n) (x : Fin n → ℂ) (a : ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x)
    (ha : ∀ i, x i + a ≠ 0) :
    pfaffian (n + 2) (border (schurMatrix (Fin.snoc x a)) (fun _ => 1)) =
      schurProduct (Fin.snoc x a) := by
  have hc : schurComplement (schurMatrix x) (fun i => schurEntry (x i) a) (fun _ => 1) 1 =
      fun i j => schurEntry (x i) a * schurMatrix x i j * schurEntry (x j) a := by
    ext i j
    simpa only [schurComplement, schurMatrix, mul_one, one_mul, div_one] using
      schurEntry_border_elimination (hd i j) (ha i) (ha j)
  have h1 : (fun _ : Fin (n + 1) => (1 : ℂ)) = Fin.snoc (fun _ => 1) 1 := by
    ext i
    refine Fin.lastCases ?_ (fun i => ?_) i <;> simp
  rw [schurMatrix_snoc, h1,
    pfaffian_schur_complement hn _ (schurMatrix_skew x) _ _ one_ne_zero,
    one_mul, hc, pfaffian_scale_coordinates hn _ (schurMatrix_skew x),
    pfaffian_schur_even n hn x hd hx, schurProduct_snoc, mul_comm]

 
theorem pfaffian_schur_odd (n : ℕ) (hn : Odd n) (x : Fin n → ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x) :
    pfaffian (n + 1) (border (schurMatrix x) (fun _ => 1)) = schurProduct x := by
  cases n with
  | zero => exact False.elim (by simp at hn)
  | succ n =>
    have he : Even n := by
      rw [Nat.odd_iff] at hn
      rw [Nat.even_iff]
      omega
    revert hd hx
    refine Fin.snocCases (fun y a => ?_) x
    intro hd hx
    apply pfaffian_schur_odd_snoc he y a
    · intro i j
      simpa only [Fin.snoc_castSucc] using hd i.castSucc j.castSucc
    · intro i j hij
      apply Fin.castSucc_injective
      apply hx
      simpa only [Fin.snoc_castSucc] using hij
    · intro i
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using hd i.castSucc (Fin.last n)

end
end StripPfaffian

namespace CriticalStrip
noncomputable section
open MeasureTheory Set
open scoped BigOperators

lemma integral_translate_Ioi (f : ℝ → ℝ) (a b : ℝ) :
    (∫ x in Ioi a, f (x + b)) = ∫ x in Ioi (a + b), f x := by
  have hp : (fun x : ℝ => x + b) ⁻¹' Ioi (a + b) = Ioi a := by
    ext x
    simp
  simpa only [hp] using (measurePreserving_add_right volume b).setIntegral_preimage_emb
    (Homeomorph.addRight b).measurableEmbedding f (Ioi (a + b))

lemma integral_shifted_rpow {p : ℝ} (hp : 0 < p) :
    (∫ t in Ioi (0 : ℝ), (1 + t) ^ (-(p + 1))) = 1 / p := by
  calc
    _ = ∫ x in Ioi (1 : ℝ), x ^ (-(p+1)) := by
      simpa only [zero_add, add_comm] using
        integral_translate_Ioi (fun x : ℝ => x ^ (-(p+1))) 0 1
    _ = 1 / p := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -(p+1)< -1) (by norm_num : (0:ℝ)<1),
        Real.one_rpow]
      rw [show -(p+1)+1 = -p by ring, neg_div_neg_eq]

local notation "μ₊" => (volume.restrict (Ioi (0 : ℝ)))

lemma ae_pos_pair : ∀ᵐ rs : ℝ × ℝ ∂μ₊.prod μ₊, 0 < rs.1 ∧ 0 < rs.2 := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  exact (ae_restrict_mem measurableSet_Ioi).mono fun r hr =>
    (ae_restrict_mem measurableSet_Ioi).mono fun s hs => ⟨hr, hs⟩

def gammaLaplace (p q : ℝ) (z : (ℝ × ℝ) × ℝ) : ℝ :=
  laguerreWeight p z.1.1 * laguerreWeight q z.1.2 * z.1.1 *
    Real.exp (-(z.1.1 + z.1.2) * z.2)

lemma measurable_gammaLaplace (p q : ℝ) : Measurable (gammaLaplace p q) := by
  unfold gammaLaplace laguerreWeight
  fun_prop

lemma integrable_gammaLaplace_section (p q : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    Integrable (fun t => gammaLaplace p q ((r,s),t)) μ₊ := by
  exact (integrableOn_exp_mul_Ioi (show -(r+s) < 0 by linarith) 0).const_mul
    (laguerreWeight p r * laguerreWeight q s * r)

lemma integral_gammaLaplace_section (p q : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (∫ t, gammaLaplace p q ((r,s),t) ∂μ₊) =
      laguerreWeight p r * laguerreWeight q s * (r / (r+s)) := by
  simp only [gammaLaplace, integral_const_mul,
    integral_exp_mul_Ioi (show -(r+s) < 0 by linarith) 0, mul_zero, Real.exp_zero, neg_div_neg_eq]
  ring

lemma integrable_gammaFraction {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Integrable (fun rs : ℝ × ℝ => laguerreWeight p rs.1 * laguerreWeight q rs.2 *
      (rs.1 / (rs.1 + rs.2))) (μ₊.prod μ₊) := by
  have hi := (integrableOn_laguerreWeight hp).mul_prod (integrableOn_laguerreWeight hq)
  apply hi.mono' (by unfold laguerreWeight; fun_prop)
  filter_upwards [ae_pos_pair] with rs hrs
  obtain ⟨hr,hs⟩ := hrs
  have hw : 0 ≤ laguerreWeight p rs.1 * laguerreWeight q rs.2 :=
    mul_nonneg (laguerreWeight_pos p hr).le (laguerreWeight_pos q hs).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (div_nonneg hr.le (add_pos hr hs).le))]
  exact mul_le_of_le_one_right hw ((div_le_one (add_pos hr hs)).2 (by linarith))

lemma integrable_gammaLaplace {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Integrable (gammaLaplace p q) ((μ₊.prod μ₊).prod μ₊) := by
  apply (integrable_prod_iff (measurable_gammaLaplace p q).aestronglyMeasurable).2
  constructor
  · exact ae_pos_pair.mono fun rs hrs => integrable_gammaLaplace_section p q hrs.1 hrs.2
  · apply (integrable_gammaFraction hp hq).congr
    filter_upwards [ae_pos_pair] with rs hrs
    rw [← integral_gammaLaplace_section p q hrs.1 hrs.2]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (Real.norm_of_nonneg (by
      unfold gammaLaplace
      exact mul_nonneg (mul_nonneg (mul_nonneg
        (laguerreWeight_pos p hrs.1).le (laguerreWeight_pos q hrs.2).le) hrs.1.le)
        (Real.exp_pos _).le)).symm

lemma gammaLaplace_factor (p q : ℝ) {r s : ℝ} (hr : 0 < r) (_hs : 0 < s) (t : ℝ) :
    gammaLaplace p q ((r,s),t) =
      (r ^ p * Real.exp (-((1+t)*r))) *
        (s ^ (q-1) * Real.exp (-((1+t)*s))) := by
  unfold gammaLaplace laguerreWeight
  have hrp : r^p = r^(p-1)*r := by
    calc
      _ = r ^ ((p-1)+1) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hr, Real.rpow_one]
  rw [hrp]
  have he : Real.exp (-r) * Real.exp (-s) * Real.exp (-(r+s)*t) =
      Real.exp (-((1+t)*r)) * Real.exp (-((1+t)*s)) := by
    simp only [← Real.exp_add]
    congr 1
    ring
  calc
    _ = (r^(p-1) * r * s^(q-1)) *
        (Real.exp (-r) * Real.exp (-s) * Real.exp (-(r+s)*t)) := by ring
    _ = _ := by rw [he]; ring

lemma integral_gammaLaplace_pair {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {t : ℝ} (ht : 0 < t) :
    (∫ rs : ℝ × ℝ, gammaLaplace p q (rs,t) ∂μ₊.prod μ₊) =
      (Real.Gamma (p+1) * Real.Gamma q) * (1+t)^(-(p+q+1)) := by
  calc
    _ = ∫ rs : ℝ × ℝ, (rs.1^p * Real.exp (-((1+t)*rs.1))) *
        (rs.2^(q-1) * Real.exp (-((1+t)*rs.2))) ∂μ₊.prod μ₊ := by
      apply integral_congr_ae
      exact ae_pos_pair.mono fun rs hrs => gammaLaplace_factor p q hrs.1 hrs.2 t
    _ = (∫ r in Ioi 0, r^p * Real.exp (-((1+t)*r))) *
        (∫ s in Ioi 0, s^(q-1) * Real.exp (-((1+t)*s))) := integral_prod_mul (μ := μ₊) (ν := μ₊)
      (fun r : ℝ => r^p * Real.exp (-((1+t)*r)))
      (fun s : ℝ => s^(q-1) * Real.exp (-((1+t)*s)))
    _ = ((1/(1+t))^(p+1) * Real.Gamma (p+1)) *
        ((1/(1+t))^q * Real.Gamma q) := by
      rw [show p = (p+1)-1 by ring, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0<p+1)
        (by linarith : 0<1+t), Real.integral_rpow_mul_exp_neg_mul_Ioi hq (by linarith : 0<1+t)]
      ring_nf
    _ = _ := by
      rw [show p+q+1 = (p+1)+q by ring, neg_add, Real.rpow_add (by linarith : 0<1+t)]
      simp only [one_div, Real.inv_rpow (by linarith : 0≤1+t), Real.rpow_neg (by linarith : 0≤1+t)]
      ring

lemma integral_gammaFraction {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ rs : ℝ × ℝ, laguerreWeight p rs.1 * laguerreWeight q rs.2 *
      (rs.1 / (rs.1+rs.2)) ∂μ₊.prod μ₊) =
      Real.Gamma p * Real.Gamma q * (p / (p+q)) := by
  calc
    _ = ∫ rs : ℝ × ℝ, ∫ t, gammaLaplace p q (rs,t) ∂μ₊ ∂μ₊.prod μ₊ := by
      apply integral_congr_ae
      exact ae_pos_pair.mono fun rs hrs => (integral_gammaLaplace_section p q hrs.1 hrs.2).symm
    _ = ∫ t, ∫ rs : ℝ × ℝ, gammaLaplace p q (rs,t) ∂μ₊.prod μ₊ ∂μ₊ :=
      integral_integral_swap (integrable_gammaLaplace hp hq)
    _ = ∫ t, (Real.Gamma (p+1) * Real.Gamma q) * (1+t)^(-(p+q+1)) ∂μ₊ := by
      apply integral_congr_ae
      exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht => integral_gammaLaplace_pair hp hq ht
    _ = _ := by
      rw [integral_const_mul, integral_shifted_rpow (add_pos hp hq), Real.Gamma_add_one hp.ne']
      ring

 

def gammaSkewIntegrand (p q : ℝ) (rs : ℝ × ℝ) : ℝ :=
  laguerreWeight p rs.1 * laguerreWeight q rs.2 * ((rs.2-rs.1)/(rs.2+rs.1))

lemma gammaSkewIntegrand_eq (p q : ℝ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    gammaSkewIntegrand p q (r,s) =
      laguerreWeight p r * laguerreWeight q s -
        2 * (laguerreWeight p r * laguerreWeight q s * (r/(r+s))) := by
  unfold gammaSkewIntegrand
  field_simp [(add_pos hr hs).ne', (add_pos hs hr).ne']
  ring

lemma integrable_gammaSkewIntegrand {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    Integrable (gammaSkewIntegrand p q) (μ₊.prod μ₊) := by
  have h := ((integrableOn_laguerreWeight hp).mul_prod (integrableOn_laguerreWeight hq)).sub
    ((integrable_gammaFraction hp hq).const_mul 2)
  exact h.congr (ae_pos_pair.mono fun rs hrs => (gammaSkewIntegrand_eq p q hrs.1 hrs.2).symm)

lemma integral_gammaSkewIntegrand {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (∫ rs : ℝ × ℝ, gammaSkewIntegrand p q rs ∂μ₊.prod μ₊) =
      Real.Gamma p * Real.Gamma q * ((q-p)/(p+q)) := by
  calc
    _ = (∫ rs : ℝ × ℝ, laguerreWeight p rs.1 * laguerreWeight q rs.2 ∂μ₊.prod μ₊) -
        2 * (∫ rs : ℝ × ℝ, laguerreWeight p rs.1 * laguerreWeight q rs.2 *
          (rs.1/(rs.1 + rs.2)) ∂μ₊.prod μ₊) := by
      rw [← integral_const_mul, ← integral_sub
        ((integrableOn_laguerreWeight hp).mul_prod (integrableOn_laguerreWeight hq))
        ((integrable_gammaFraction hp hq).const_mul 2)]
      exact integral_congr_ae (ae_pos_pair.mono fun rs hrs => gammaSkewIntegrand_eq p q hrs.1 hrs.2)
    _ = _ := by
      rw [integral_prod_mul (μ := μ₊) (ν := μ₊) (laguerreWeight p) (laguerreWeight q),
        integral_laguerreWeight hp, integral_laguerreWeight hq, integral_gammaFraction hp hq]
      field_simp [(add_pos hp hq).ne']
      ring

 
theorem laguerre_double_moment {a : ℝ} (ha : 0 < a) (i j : ℕ) :
    Integrable (gammaSkewIntegrand (a+i) (a+j)) (μ₊.prod μ₊) ∧
    (∫ rs : ℝ × ℝ, gammaSkewIntegrand (a+i) (a+j) rs ∂μ₊.prod μ₊) =
      Real.Gamma (a+i) * Real.Gamma (a+j) * (((j:ℝ)-i)/(2*a+i+j)) := by
  have hi : 0 < a+(i:ℝ) := by positivity
  have hj : 0 < a+(j:ℝ) := by positivity
  refine ⟨integrable_gammaSkewIntegrand hi hj, ?_⟩
  rw [integral_gammaSkewIntegrand hi hj]
  congr 2 <;> ring

end
end CriticalStrip

namespace StripPfaffian
noncomputable section
open scoped BigOperators

lemma border_scale_coordinates {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u s : Vec n) :
    border (fun i j => s i * A i j * s j) (fun i => s i * u i) =
      fun i j => (Fin.snoc s (1:ℂ) : Vec (n+1)) i * border A u i j *
        (Fin.snoc s (1:ℂ) : Vec (n+1)) j := by
  funext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  all_goals refine Fin.lastCases ?_ (fun j => ?_) j
  all_goals simp [border]
  ring

lemma pfaffian_border_scale_coordinates {n : ℕ} (hn : Odd n)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : ∀ i j, A j i = -A i j) (u s : Vec n) :
    pfaffian (n+1) (border (fun i j => s i * A i j * s j) (fun i => s i * u i)) =
      (∏ i, s i) * pfaffian (n+1) (border A u) := by
  rw [border_scale_coordinates, pfaffian_scale_coordinates hn.add_one _ (border_skew A hA u),
    Fin.prod_univ_castSucc]
  simp

 

theorem pfaffian_weighted_schur_even (n : ℕ) (hn : Even n) (x s : Fin n → ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x) :
    pfaffian n (fun i j => s i * schurEntry (x i) (x j) * s j) =
      (∏ i, s i) * schurProduct x := by
  have h := pfaffian_scale_coordinates hn (schurMatrix x) (schurMatrix_skew x) s
  rw [pfaffian_schur_even n hn x hd hx] at h
  exact h

theorem pfaffian_weighted_schur_odd (n : ℕ) (hn : Odd n) (x s : Fin n → ℂ)
    (hd : ∀ i j, x i + x j ≠ 0) (hx : Function.Injective x) :
    pfaffian (n+1) (border (fun i j => s i * schurEntry (x i) (x j) * s j) s) =
      (∏ i, s i) * schurProduct x := by
  have h := pfaffian_border_scale_coordinates hn (schurMatrix x) (schurMatrix_skew x)
    (fun _ => 1) s
  rw [pfaffian_schur_odd n hn x hd hx] at h
  simpa only [mul_one, schurMatrix] using h

end
end StripPfaffian

namespace CriticalStrip
noncomputable section
open scoped BigOperators
open MeasureTheory Set StripPfaffian

local notation "μ₊" => volume.restrict (Ioi (0 : ℝ))

def laguerreMomentMatrix (n : ℕ) (a : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ((∫ rs, gammaSkewIntegrand (a+i.val) (a+j.val) rs ∂μ₊.prod μ₊) : ℝ)

def laguerreMomentColumn (n : ℕ) (a : ℝ) : Fin n → ℂ :=
  fun i => ((∫ x in Ioi 0, laguerreWeight (a+i.val) x) : ℝ)

 

def laguerreNormalizerProduct (n : ℕ) (a : ℝ) : ℝ :=
  (∏ i : Fin n, Real.Gamma (a+i.val)) *
    ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, ((j.val:ℝ)-i.val)/(2*a+i.val+j.val)

lemma laguerreMomentMatrix_eq {a : ℝ} (ha : 0 < a) (n : ℕ) :
    laguerreMomentMatrix n a = fun i j =>
      (Real.Gamma (a+i.val) : ℂ) *
        schurEntry ((a+i.val : ℝ) : ℂ) ((a+j.val : ℝ) : ℂ) *
          (Real.Gamma (a+j.val) : ℂ) := by
  ext i j
  rw [laguerreMomentMatrix, (laguerre_double_moment ha i.val j.val).2]
  simp only [StripPfaffian.schurEntry, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  have hn : ((a:ℂ)+j.val) - ((a:ℂ)+i.val) = (j.val:ℂ)-i.val := by ring
  have hd : ((a:ℂ)+i.val) + ((a:ℂ)+j.val) = 2*(a:ℂ)+i.val+j.val := by ring
  rw [hn,hd]
  ring

lemma laguerreMomentColumn_eq {a : ℝ} (ha : 0 < a) (n : ℕ) :
    laguerreMomentColumn n a = fun i => (Real.Gamma (a+i.val) : ℂ) := by
  ext i
  exact congrArg Complex.ofReal (integral_laguerreWeight (by positivity))

lemma laguerre_schur_denominators {a : ℝ} (ha : 0 < a) (n : ℕ) (i j : Fin n) :
    ((a+i.val : ℝ) : ℂ) + ((a+j.val : ℝ) : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_add, Complex.ofReal_ne_zero]
  positivity

lemma laguerre_schur_injective (a : ℝ) (n : ℕ) :
    Function.Injective (fun i : Fin n => ((a+i.val : ℝ) : ℂ)) := by
  intro i j hij
  have h := Complex.ofReal_injective hij
  have he : (i.val:ℝ) = j.val := add_left_cancel h
  exact Fin.ext (Nat.cast_injective he)

lemma laguerreNormalizerProduct_eq (n : ℕ) (a : ℝ) :
    (laguerreNormalizerProduct n a : ℂ) =
      (∏ i : Fin n, (Real.Gamma (a+i.val) : ℂ)) *
        StripPfaffian.schurProduct (fun i : Fin n => ((a+i.val : ℝ) : ℂ)) := by
  simp only [laguerreNormalizerProduct, Complex.ofReal_mul, Complex.ofReal_prod,
    StripPfaffian.schurProduct]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  simp only [StripPfaffian.schurEntry, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  congr 1 <;> ring

 

theorem laguerreMomentMatrix_pfaffian_even {a : ℝ} (ha : 0 < a) (n : ℕ) (hn : Even n) :
    StripPfaffian.pfaffian n (laguerreMomentMatrix n a) = laguerreNormalizerProduct n a := by
  rw [laguerreMomentMatrix_eq ha, laguerreNormalizerProduct_eq]
  exact pfaffian_weighted_schur_even n hn _ _ (laguerre_schur_denominators ha n)
    (laguerre_schur_injective a n)

theorem laguerreMomentMatrix_pfaffian_odd {a : ℝ} (ha : 0 < a) (n : ℕ) (hn : Odd n) :
    StripPfaffian.pfaffian (n+1) (StripPfaffian.border (laguerreMomentMatrix n a)
      (laguerreMomentColumn n a)) = laguerreNormalizerProduct n a := by
  rw [laguerreMomentMatrix_eq ha, laguerreMomentColumn_eq ha, laguerreNormalizerProduct_eq]
  exact pfaffian_weighted_schur_odd n hn _ _ (laguerre_schur_denominators ha n)
    (laguerre_schur_injective a n)

end
end CriticalStrip

 

namespace StripPfaffian
noncomputable section
open scoped BigOperators

lemma sum_pow_list {ι E : Type*} [Fintype ι] [Semiring E] (f : ι → E) (m : ℕ) :
    (∑ i, f i) ^ m = ∑ v : Fin m → ι, (List.ofFn (fun j => f (v j))).prod := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ih, Finset.mul_sum]
    conv_lhs => simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [← Fintype.sum_prod_type (f := fun p : ι × (Fin m → ι) =>
      f p.1 * (List.ofFn (fun j => f (p.2 j))).prod)]
    apply Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => ι))
    intro p
    simp [List.ofFn_succ, Fin.consEquiv]

lemma ofFn_smul_prod {n m : ℕ} (s : Fin m → ℂ) (v : Fin m → Grassmann n) :
    (List.ofFn (fun i => s i • v i)).prod =
      (∏ i, s i) • (List.ofFn v).prod := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    rw [ih, smul_mul_smul_comm]

end
end StripPfaffian

end OAI
