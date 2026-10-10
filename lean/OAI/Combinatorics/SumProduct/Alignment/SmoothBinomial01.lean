import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.MalcevTail01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open scoped commutatorElement BigOperators
noncomputable section
end
end
 

 
section
open scoped BigOperators
noncomputable section
namespace MalcevTailSection
open RationalLattice RationalPolynomialMap
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n l : ℕ}
variable (c : RealCoordinates G n) (k : Fin n → ℤ) (r : Fin l → ℕ)

def flowWord (t : Fin l → ℝ) : G := (List.ofFn (fun i => tailSection c k (r i) (t i))).prod

omit [IsTopologicalGroup G] in
lemma polynomialMap_section {σ : Type*} (q : ℕ) {f : (σ → ℝ) → ℝ}
    (hf : IsPolynomial f) : IsPolynomialMap c (fun x => tailSection c k q (f x)) := by
  classical
  unfold tailSection
  split_ifs with h
  · intro i
    simp only [MalcevCharacters.coord_axis,Pi.single_apply]
    split_ifs
    · have he := RationalPolynomialMap.mul hf (RationalPolynomialMap.const (σ:=σ) ((k h.choose:ℚ)⁻¹))
      simpa only [Rat.cast_inv,Rat.cast_intCast,div_eq_mul_inv] using he
    · exact RationalPolynomialMap.zero
  · exact polynomialMap_one c

omit [IsTopologicalGroup G] in
lemma polynomialMap_flowWord : IsPolynomialMap c (flowWord c k r) := by
  change IsPolynomialMap c (fun x => (List.ofFn (fun i => tailSection c k (r i) (x i))).prod)
  simp only [List.ofFn_eq_map]
  generalize List.finRange l = v
  induction v with
  | nil => exact polynomialMap_one c
  | cons i v ih =>
    simp only [List.map_cons,List.prod_cons]
    exact polynomialMap_mul c (polynomialMap_section c k (r i) (RationalPolynomialMap.coordinate i)) ih

omit [IsTopologicalGroup G] in
lemma flowWord_contDiff : ContDiff ℝ (⊤ : ℕ∞) (fun x => c.coord (flowWord c k r x)) := by
  apply contDiff_pi.mpr
  intro i
  exact RationalPolynomialMap.contDiff (polynomialMap_flowWord c k r i)

 

omit [IsTopologicalGroup G] in
lemma flowWord_bounds (R : ℝ) :
    ∃ M > 0,
      (∀ x, ‖x‖ ≤ R → ‖c.coord (flowWord c k r x)‖ ≤ M) ∧
      (∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
        ‖c.coord (flowWord c k r x)-c.coord (flowWord c k r y)‖ ≤ M*‖x-y‖) := by
  have hd := flowWord_contDiff c k r
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : Fin l → ℝ) R).exists_bound_of_continuousOn hd.continuous.continuousOn
  obtain ⟨D,hD⟩ := (isCompact_closedBall (0 : Fin l → ℝ) R).exists_bound_of_continuousOn
    (hd.continuous_fderiv (by simp)).continuousOn
  refine ⟨max (max M D) 0 + 1,by positivity,?_,?_⟩
  · intro x hx
    exact (hM x (by simpa using hx)).trans (by grind)
  · intro x y hx hy
    have he := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun x (_ : x ∈ Metric.closedBall (0 : Fin l → ℝ) R) => hd.differentiable (by simp) x)
      hD (convex_closedBall (0 : Fin l → ℝ) R) (by simpa using hy) (by simpa using hx)
    exact he.trans (mul_le_mul_of_nonneg_right (by grind) (norm_nonneg _))

omit [IsTopologicalGroup G] in
lemma flowWord_integer (hsk : MalcevCharacters.SecondKind c)
    (lam : Fin l → ℝ) (j : Fin l → ℕ) (z : ℤ) :
    flowWord c k r (fun i => lam i * Ring.choose (z:ℝ) (j i)) =
      RationalFactorPeriods.orderedWord (fun i => tailSection c k (r i) (lam i)) j z := by
  unfold flowWord RationalFactorPeriods.orderedWord
  apply congrArg List.prod
  rw [← List.ofFn_eq_map]
  apply congrArg List.ofFn
  funext i
  have he := Ring.map_choose (Int.castRingHom ℝ) z (j i)
  change ((Ring.choose z (j i) : ℤ) : ℝ) = Ring.choose (z:ℝ) (j i) at he
  dsimp only
  rw [← he,mul_comm,section_zpow c hsk]

end MalcevTailSection
end
end
 

 
section

 

namespace SmoothBinomial
open Filter Set _root_.Polynomial _root_.OAI.Polynomial
open scoped Topology BigOperators
noncomputable section

 

def universal (j : ℕ) : Polynomial (Polynomial ℝ) :=
  C (C (j.factorial : ℝ)⁻¹) *
    ∏ i ∈ Finset.range j, (X - C (C (i : ℝ) * X))

def family (p : Polynomial (Polynomial ℝ)) (t : ℝ) : Polynomial ℝ :=
  p.map (evalRingHom t)

lemma continuous_eval_family (p : Polynomial (Polynomial ℝ)) :
    Continuous (fun z : ℝ × ℝ => (family p z.1).eval z.2) := by
  simp only [family, eval_map, eval₂_eq_sum_range]
  apply continuous_finsetSum
  intro i _
  exact ((p.coeff i).continuous.comp continuous_fst).mul (continuous_snd.pow i)

lemma iteratedDeriv_eval (p : Polynomial ℝ) (k : ℕ) :
    iteratedDeriv k (fun x => p.eval x) = fun x => (derivative^[k] p).eval x := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ', show deriv (fun x => p.eval x) =
      (fun x => p.derivative.eval x) from funext (fun x => p.deriv)]
    simpa only [Function.iterate_succ_apply] using ih p.derivative

lemma iterate_derivative_family (p : Polynomial (Polynomial ℝ)) (t : ℝ) (k : ℕ) :
    derivative^[k] (family p t) = family (derivative^[k] p) t := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    rw [show derivative (family p t) = family p.derivative t from derivative_map p _]
    exact ih p.derivative

 

theorem compact_derivative_limit {ι : Type*} {l : Filter ι}
    (p : Polynomial (Polynomial ℝ)) (k : ℕ)
    {a t : ι → ℝ} {a₀ t₀ : ℝ}
    (ha : Tendsto a l (𝓝 a₀)) (ht : Tendsto t l (𝓝 t₀))
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun n => iteratedDeriv k (fun x => a n * (family p (t n)).eval x))
      (iteratedDeriv k (fun x => a₀ * (family p t₀).eval x)) l K := by
  have hder (a t : ℝ) :
      iteratedDeriv k (fun x => a * (family p t).eval x) =
      fun x => a * (family (derivative^[k] p) t).eval x := by
    have heq : (fun x => a * (family p t).eval x) =
        (fun x => (C a * family p t).eval x) := by ext x; simp
    rw [heq, iteratedDeriv_eval]
    have hd : derivative^[k] (C a * family p t) =
        C a * derivative^[k] (family p t) := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
          derivative_C_mul]
    rw [hd, iterate_derivative_family]
    simp
  simp_rw [hder]
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : (ℝ × ℝ) → K → ℝ := fun z x =>
    z.1 * (family (derivative^[k] p) z.2).eval (x : ℝ)
  have hF : Continuous (Function.uncurry F) := by
    apply Continuous.mul (continuous_fst.fst)
    exact (continuous_eval_family (derivative^[k] p)).comp
      (continuous_fst.snd.prodMk (continuous_subtype_val.comp continuous_snd))
  have hu := hF.tendstoUniformly F (a₀,t₀)
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  intro u hu'
  exact (ha.prodMk_nhds ht).eventually (hu u hu')

lemma universal_eval (j : ℕ) (t x : ℝ) :
    (family (universal j) t).eval x =
      (j.factorial : ℝ)⁻¹ * ∏ i ∈ Finset.range j, (x - (i : ℝ) * t) := by
  simp only [family,universal,Polynomial.map_mul,Polynomial.map_C,
    Polynomial.map_prod,Polynomial.map_sub,Polynomial.map_X,eval_mul,eval_C,
    eval_prod,eval_sub,eval_X]
  change (C (j.factorial : ℝ)⁻¹).eval t *
    (∏ i ∈ Finset.range j, (x - (C (i:ℝ) * X).eval t)) = _
  simp

lemma universal_eval_zero (j : ℕ) (x : ℝ) :
    (family (universal j) 0).eval x = (j.factorial : ℝ)⁻¹ * x^j := by
  simp [universal_eval]

lemma choose_eq_product (x : ℝ) (j : ℕ) :
    Ring.choose x j = (j.factorial : ℝ)⁻¹ *
      ∏ i ∈ Finset.range j, (x - (i : ℝ)) := by
  rw [Ring.choose_eq_smul, smul_eq_mul, ← aeval_eq_smeval,
    aeval_def, ← eval_map, descPochhammer_map, descPochhammer_eval_eq_prod_range]

lemma scale_identity (j : ℕ) (L x : ℝ) (hL : L ≠ 0) :
    L^j * (family (universal j) L⁻¹).eval x = Ring.choose (L*x) j := by
  rw [universal_eval, choose_eq_product]
  have hp : (L^j) * (∏ i ∈ Finset.range j, (x-(i:ℝ)*L⁻¹)) =
      ∏ i ∈ Finset.range j, (L*x-(i:ℝ)) := by
    rw [Finset.pow_eq_prod_const L j, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    field_simp [hL]
  calc
    _ = (j.factorial : ℝ)⁻¹ * (L^j * ∏ i ∈ Finset.range j, (x-(i:ℝ)*L⁻¹)) := by ring
    _ = _ := by rw [hp]

 
lemma amplitude_identity (j : ℕ) (L lam x : ℝ) (hL : L ≠ 0) :
    lam * Ring.choose (L*x) j =
      (L^j * lam) * (family (universal j) L⁻¹).eval x := by
  rw [← scale_identity j L x hL]
  ring

 

theorem smooth_binomial_limit {ι : Type*} {l : Filter ι}
    (j k : ℕ) {L lam : ι → ℝ} {c : ℝ}
    (hL : Tendsto L l atTop) (hlam : Tendsto (fun n => (L n)^j * lam n) l (𝓝 c))
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun n => iteratedDeriv k (fun x => lam n * Ring.choose (L n*x) j))
      (iteratedDeriv k (fun x => c * (j.factorial : ℝ)⁻¹ * x^j)) l K := by
  have hz : ∀ᶠ n in l, L n ≠ 0 := (hL.eventually_gt_atTop 0).mono (fun _ h => ne_of_gt h)
  have ht : Tendsto (fun n => (L n)⁻¹) l (𝓝 0) := tendsto_inv_atTop_zero.comp hL
  have hc := compact_derivative_limit (universal j) k hlam ht K hK
  have heq : (fun x => c * (family (universal j) 0).eval x) =
      (fun x => c * (j.factorial : ℝ)⁻¹ * x^j) := by
    ext x; rw [universal_eval_zero]; ring
  rw [heq] at hc
  apply hc.congr ?_
  filter_upwards [hz] with n hn
  intro x _
  have he : (fun x => lam n * Ring.choose (L n*x) j) =
      (fun x => ((L n)^j*lam n)*(family (universal j) (L n)⁻¹).eval x) := by
    ext y; exact amplitude_identity j _ _ _ hn
  rw [he]

 

theorem smooth_binomial_bounds (j k : ℕ) (A C₀ : ℝ) (hC : 0 ≤ C₀) :
    ∃ B > 0, ∀ L lam : ℝ, 1 ≤ L → |L^j*lam| ≤ C₀ →
      ∀ b : ℝ, |b| ≤ A*L →
        |iteratedDeriv k (fun x => lam * Ring.choose x j) b| ≤ B / L^k := by
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_Icc : IsCompact (Icc (-A) A))).exists_bound_of_continuousOn
    (continuous_eval_family (derivative^[k] (universal j))).continuousOn
      (s := Icc (0:ℝ) 1 ×ˢ Icc (-A) A)
  refine ⟨C₀ * max M 0 + 1,by positivity,?_⟩
  intro L lam hL hlam b hb
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLn : L ≠ 0 := ne_of_gt hLp
  have hinv : L⁻¹ ∈ Icc (0:ℝ) 1 := by
    exact ⟨inv_nonneg.mpr hLp.le,inv_le_one₀ hLp |>.mpr hL⟩
  have hx : |L⁻¹*b| ≤ A := by
    calc
      _ = |b|/L := by rw [abs_mul,abs_inv,abs_of_pos hLp]; ring
      _ ≤ A := (div_le_iff₀ hLp).mpr hb
  have hval := hM (L⁻¹,L⁻¹*b) ⟨hinv,abs_le.mp hx⟩
  simp only [Real.norm_eq_abs] at hval
  have he : (fun x => lam*Ring.choose x j) =
      fun x => (L^j*lam)*(family (universal j) L⁻¹).eval (L⁻¹*x) := by
    ext x
    have hh := amplitude_identity j L lam (L⁻¹*x) hLn
    simpa only [← mul_assoc,mul_inv_cancel₀ hLn,one_mul] using hh
  rw [he]
  rw [iteratedDeriv_const_mul_field]
  have hpoly : ContDiff ℝ k (fun x => (family (universal j) L⁻¹).eval x) := by
    simp only [Polynomial.eval_eq_sum_range]
    fun_prop
  rw [iteratedDeriv_comp_const_mul hpoly,iteratedDeriv_eval,
      iterate_derivative_family]
  rw [abs_mul]
  change |L^j*lam| * |L⁻¹^k *
    (family (derivative^[k] (universal j)) L⁻¹).eval (L⁻¹*b)| ≤ _
  rw [abs_mul (L⁻¹^k),abs_pow L⁻¹,abs_inv,abs_of_pos hLp]
  have hv0 : |(family (derivative^[k] (universal j)) L⁻¹).eval (L⁻¹*b)| ≤ max M 0 :=
    hval.trans (le_max_left _ _)
  calc
    _ ≤ C₀ * ((L⁻¹)^k * max M 0) :=
      mul_le_mul hlam (mul_le_mul_of_nonneg_left hv0 (by positivity))
        (by positivity) hC
    _ = (C₀ * max M 0) / L^k := by simp [div_eq_mul_inv]; ring
    _ ≤ (C₀ * max M 0 + 1) / L^k :=
      div_le_div_of_nonneg_right (by linarith) (pow_nonneg hLp.le _)

end
end SmoothBinomial

end
end
end
end

end OAI
