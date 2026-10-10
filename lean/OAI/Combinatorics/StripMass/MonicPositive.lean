import Mathlib
import OAI.Combinatorics.StripMass.ScalarBridge
import OAI.Combinatorics.StripMass.RightStieltjes

namespace OAI

/-! Critical honeycomb strip paths, polynomial identities and crossing mass. -/


namespace CriticalStrip
noncomputable section
open Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators Classical

lemma projectionF_high_scaled_limit {n : ℕ} (hn : 1 ≤ n) {g P J E : Polynomial ℝ}
    (hP : P.natDegree ≤ n) (hJ : J.natDegree ≤ n) (hE : E.degree < (n : WithBot ℕ))
    (hQ : homogeneousQ n g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) :
    Tendsto (fun z : ℝ => z^(n+1) *
        projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) z) atTop
      (𝓝 (((1/8) / ((2*C)*(1-2*C^2)))^(2*n+1) * ((C-c)^n * g.eval C))) := by
  have hz : ∀ᶠ z : ℝ in atTop, z ≠ 0 := eventually_ne_atTop 0
  have hi : Tendsto (fun z : ℝ => 1/z) atTop (𝓝 0) := by simpa only [one_div] using tendsto_inv_atTop_zero
  have hb : Tendsto (fun z : ℝ => highBranch (1/z)) atTop (𝓝 C) := by
    simpa only [highBranch_zero, Function.comp_def] using highBranch_continuous.continuousAt.tendsto.comp hi
  have hscale := ((highBranch_rescaled hz hi).pow (2*n+1)).mul
    (((hb.sub_const c).pow n).mul (g.continuous.continuousAt.tendsto.comp hb))
  apply hscale.congr'
  filter_upwards [hz,hi.eventually (Ioo_mem_nhds (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1))] with z hz hs
  have he := tilde_projection_eval n P J E hP hJ
    (degree_lt_implies_natDegree_lt (by omega) hE).le hz (branches_harmonic hs).1
  rw [←hQ] at he
  change _ = z^(n+1) * ((tildePoly n P).eval z + highBranch (1/z) * (tildePoly n J).eval z +
    highBranch (1/z)^2 * (tildePoly n E).eval z)
  rw [he]
  simp only [homogeneousQ, eval_mul, eval_pow, eval_sub, eval_C, eval_X, mul_pow, Function.comp_def]
  ring

lemma projectionF_cauchy_scaled_limit {n : ℕ} (hn : 1 ≤ n) {g P J E : Polynomial ℝ}
    (hg : g.Monic) (hd : g.natDegree = n)
    (hP : P.natDegree ≤ n) (hJ : J.natDegree ≤ n) (hE : E.degree < (n : WithBot ℕ))
    (hQ : homogeneousQ n g = P.comp harmonicCoordinate + X * J.comp harmonicCoordinate +
      X^2 * E.comp harmonicCoordinate) :
    Tendsto (fun z : ℝ => z^(n+1) *
        projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) z) atTop
      (𝓝 (-(∫ y, density (n+1) y ∂unitCubeMeasure (n+1)) /
        (Real.pi * (8:ℝ)^n * ((n:ℝ)+1) * ∫ y, density n y ∂unitCubeMeasure n))) := by
  apply ((cauchyDensity_limit (n+1)).neg.div_const _).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with z hz
  rw [projectionF_positive_cauchy hn hg hd hP hJ hE hQ hz]
  ring

 

theorem MonicProblem.eval_C_pos {n : ℕ} (hn : 1 ≤ n) {g : Polynomial ℝ}
    (hg : MonicProblem n g) : 0 < g.eval C := by
  obtain ⟨hgm,hgd,P,J,E,hP,hJ,hE,hQ⟩ := hg
  have he := tendsto_nhds_unique
    (projectionF_high_scaled_limit hn hP hJ hE hQ)
    (projectionF_cauchy_scaled_limit hn hgm hgd hP hJ hE hQ)
  have hpos : 0 < Real.pi * (8:ℝ)^n * ((n:ℝ)+1) * ∫ y, density n y ∂unitCubeMeasure n := by
    have hi := integral_density_unitCube_positive n
    have hp := Real.pi_pos
    positivity
  have hneg := div_neg_of_neg_of_pos
    (neg_neg_of_pos (integral_density_unitCube_positive (n+1))) hpos
  rw [←he] at hneg
  have hC := C_c_facts
  have hCp : 0<C := hC.1.trans hC.2.1
  have hk : (1/8:ℝ)/((2*C)*(1-2*C^2))<0 :=
    div_neg_of_pos_of_neg (by norm_num) (mul_neg_of_pos_of_neg (by linarith) (by
      nlinarith [sq_nonneg (C-c)]))
  have hp : ((1/8:ℝ)/((2*C)*(1-2*C^2)))^(2*n+1)<0 := (odd_two_mul_add_one n).pow_neg hk
  have hd : 0<(C-c)^n := pow_pos (sub_pos.mpr hC.2.1) n
  have hm : 0 < (C-c)^n * g.eval C := ((mul_neg_iff.mp hneg).resolve_left (by rintro ⟨hn,_⟩; linarith)).2
  exact (mul_pos_iff.mp hm).resolve_right (by rintro ⟨hf,_⟩; linarith) |>.2

end
end CriticalStrip

 

 

namespace CriticalStrip.Diagram
noncomputable section
open Filter Polynomial
open scoped Topology BigOperators Classical

lemma scalarValue_continuous (n : ℕ) :
    Continuous (fun a : Fin n → ℂ => scalarValue (RingHom.id ℂ) a) := by
  simpa only [scalarValue, MvPolynomial.eval₂Hom, MvPolynomial.eval] using
    (MvPolynomial.continuous_eval (scalarPolynomial n (d:ℂ) rho (by exact_mod_cast d_ne_zero)))

lemma homogeneous_discriminant_ne_zero : StripPfaffian.D (C:ℂ) (C:ℂ) ≠ 0 := by
  have hc := C_c_facts
  have hCp : 0<C := hc.1.trans hc.2.1
  have hd : 0<d := by have he:=eta_pos; change 0<2*d-1 at he; linarith
  have hsum : C^2+CriticalStrip.c^2=1 := C_c_facts.2.2.1
  have hcp : 0<CriticalStrip.c := C_c_facts.1
  have hclt : CriticalStrip.c<C := C_c_facts.2.1
  have hp : 0<C^2+C^2+2*d*C*C-d^2 := by
    nlinarith [d_sq, mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) hd) hCp) hCp,
      mul_pos (sub_pos.mpr hclt) (add_pos hCp hcp)]
  change (C:ℂ)^2+(C:ℂ)^2+2*(d:ℂ)*(C:ℂ)*(C:ℂ)-(d:ℂ)^2≠0
  exact_mod_cast hp.ne'

 
def separatedHomogeneous (n m : ℕ) (i : Fin n) : ℂ :=
  (C:ℂ)+(i.val:ℂ)*(1/((m:ℂ)+1))

lemma separatedHomogeneous_injective (n m : ℕ) : Function.Injective (separatedHomogeneous n m) := by
  intro i j he
  have hn : (m:ℂ)+1≠0 := by exact_mod_cast (by positivity : (m:ℝ)+1≠0)
  have ht : (1/((m:ℂ)+1))≠0 := one_div_ne_zero hn
  apply Fin.ext
  apply Nat.cast_injective (R:=ℂ)
  exact mul_right_cancel₀ ht (add_left_cancel he)

lemma separatedHomogeneous_tendsto (n : ℕ) :
    Tendsto (separatedHomogeneous n) atTop (𝓝 (fun _ => (C:ℂ))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  simpa only [mul_zero,add_zero,separatedHomogeneous] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℂ)).const_mul (i.val:ℂ) |>.const_add (C:ℂ)

lemma separatedHomogeneous_discriminants (n : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ i j : Fin n,
      StripPfaffian.D (separatedHomogeneous n m i) (separatedHomogeneous n m j) ≠ 0 := by
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  have ht := separatedHomogeneous_tendsto n
  have hD : Continuous (fun a : Fin n → ℂ => StripPfaffian.D (a i) (a j)) := by
    unfold StripPfaffian.D; fun_prop
  exact (hD.continuousAt.tendsto.comp ht).eventually_ne homogeneous_discriminant_ne_zero

lemma polynomial_eval_limit_of_coeff {α : Type*} {l : Filter α} {P : α → Polynomial ℂ}
    {g : Polynomial ℂ} {n : ℕ} (hdeg : ∀ᶠ x in l, (P x).natDegree≤n) (hg : g.natDegree≤n)
    (ht : ∀ i, Tendsto (fun x => (P x).coeff i) l (𝓝 (g.coeff i))) (z : ℂ) :
    Tendsto (fun x => (P x).eval z) l (𝓝 (g.eval z)) := by
  rw [Polynomial.eval_eq_sum_range' (show g.natDegree<n+1 by omega)]
  apply (tendsto_finsetSum (Finset.range (n+1)) (fun i _ => (ht i).mul_const (z^i))).congr'
  filter_upwards [hdeg] with x hx
  exact (Polynomial.eval_eq_sum_range' (show (P x).natDegree<n+1 by omega) z).symm

 

theorem archPolynomialAt_homogeneous_of_ne {n : ℕ} (hn : 1≤n)
    (hp : scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))≠0) :
    ∃ g : Polynomial ℝ, MonicProblem n g ∧
      archPolynomialAt (fun _ : Fin n => (C:ℂ))=g.map Complex.ofRealHom := by
  obtain ⟨g₀,hg₀,hu,g,hg,hgc,hgreg⟩ := archPolynomialAt_confluent n hn
  refine ⟨g₀,hg₀,?_⟩
  apply Polynomial.funext
  intro z
  have ht := separatedHomogeneous_tendsto n
  have hreg := ht.eventually hgreg
  have hpn : ∀ᶠ m in atTop, scalarValue (RingHom.id ℂ) (separatedHomogeneous n m)≠0 :=
    ((scalarValue_continuous n).continuousAt.tendsto.comp ht).eventually_ne hp
  have hgg : Tendsto (fun m => (g (separatedHomogeneous n m)).eval z) atTop
      (𝓝 ((g₀.map Complex.ofRealHom).eval z)) := by
    apply polynomial_eval_limit_of_coeff (n:=n)
      (hreg.mono fun _ h => h.2.1.le)
      ((Polynomial.natDegree_map_le).trans hg₀.2.1.le)
    intro i
    have hh := (hgc i).tendsto.comp ht
    simpa only [hg,Function.comp_def] using hh
  have hal : ∀ a : Fin n → ℂ, (archPolynomialAt a).eval z =
      scalarValue (RingHom.id ℂ) (Fin.snoc a z) / scalarValue (RingHom.id ℂ) a := by
    intro a
    simp only [archPolynomialAt,Polynomial.eval_mul,Polynomial.eval_C,nextScalar_eval]
    ring
  have hcont : Continuous (fun a : Fin n → ℂ => scalarValue (RingHom.id ℂ) (Fin.snoc a z)) := by
    apply (scalarValue_continuous (n+1)).comp
    apply continuous_pi
    intro i
    induction i using Fin.lastCases <;> simp only [Fin.snoc_last,Fin.snoc_castSucc] <;> fun_prop
  have hfrac := ((hcont.continuousAt.tendsto.comp ht).div
    ((scalarValue_continuous n).continuousAt.tendsto.comp ht) hp)
  have hh : Tendsto (fun m => (g (separatedHomogeneous n m)).eval z) atTop
      (𝓝 ((archPolynomialAt (fun _ : Fin n => (C:ℂ))).eval z)) := by
    rw [hal]
    apply hfrac.congr'
    filter_upwards [hreg,hpn,separatedHomogeneous_discriminants n] with m hm hpm hDm
    change scalarValue (RingHom.id ℂ) (Fin.snoc (separatedHomogeneous n m) z) /
      scalarValue (RingHom.id ℂ) (separatedHomogeneous n m)=_
    rw [←hal,hm.2.2 (separatedHomogeneous_injective n m) (fun i j _ => hDm i j) hpm]
  exact tendsto_nhds_unique hh hgg

lemma nextScalar_homogeneous_of_ne {n : ℕ} (hn : 1≤n)
    (hp : scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))≠0) :
    ∃ g : Polynomial ℝ, MonicProblem n g ∧
      nextScalar (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))=
        Polynomial.C (scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))) * g.map Complex.ofRealHom := by
  obtain ⟨g,hg,he⟩:=archPolynomialAt_homogeneous_of_ne hn hp
  refine ⟨g,hg,?_⟩
  rw [←he,archPolynomialAt,←mul_assoc,←Polynomial.C_mul,mul_inv_cancel₀ hp,Polynomial.C_1,one_mul]

 

theorem scalarValue_homogeneous_positive (n : ℕ) :
    ∃ x : ℝ, 0<x ∧ scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))=(x:ℂ) := by
  induction n with
  | zero => exact ⟨1,by norm_num,by simp only [scalarValue_zero,Complex.ofReal_one]⟩
  | succ n ih =>
    by_cases hn : n=0
    · subst n
      exact ⟨1,by norm_num,by simp only [scalarValue_one,Complex.ofReal_one]⟩
    obtain ⟨x,hx,he⟩:=ih
    have hp : scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))≠0 := by
      rw [he]; exact_mod_cast hx.ne'
    obtain ⟨g,hg,hnext⟩:=nextScalar_homogeneous_of_ne (by omega) hp
    refine ⟨x*g.eval C,mul_pos hx (hg.eval_C_pos (by omega)),?_⟩
    have hh:=congrArg (Polynomial.eval (C:ℂ)) hnext
    rw [nextScalar_eval,Polynomial.eval_mul,Polynomial.eval_C,he] at hh
    have hs : (Fin.snoc (fun _ : Fin n => (C:ℂ)) (C:ℂ) : Fin (n+1) → ℂ)=(fun _ => (C:ℂ)) := by
      funext i
      induction i using Fin.lastCases <;> simp
    have hm : Polynomial.eval₂ Complex.ofRealHom (C:ℂ) g=(↑(g.eval (CriticalStrip.C:ℝ)):ℂ) :=
      Polynomial.eval₂_at_apply Complex.ofRealHom C
    rw [hs,Polynomial.eval_map,hm] at hh
    exact hh.trans (Complex.ofReal_mul _ _).symm

end
end CriticalStrip.Diagram

 

 

namespace CriticalStrip
noncomputable section
open Set MeasureTheory Filter Polynomial
open scoped Topology BigOperators Classical

lemma projectionD_nonneg_right {n : ℕ} (hn : 1≤n) {g P J E : Polynomial ℝ}
    (hg : g.Monic) (hd : g.natDegree=n)
    (hP : P.natDegree≤n) (hJ : J.natDegree≤n) (hE : E.degree<(n:WithBot ℕ))
    (hQ : homogeneousQ n g=P.comp harmonicCoordinate+X*J.comp harmonicCoordinate+
      X^2*E.comp harmonicCoordinate) {z : ℝ} (hz : 1≤z) :
    0≤projectionD (tildePoly n J) (tildePoly n E) z := by
  rw [projectionD_expectation n hn g P J E hP hJ hE hQ z (by linarith),
    projection_initial_monic hn hg hd hP hJ hE hQ,←expectation_const_mul]
  apply expectation_nonneg
  intro y hy
  have he : ((-8:ℝ)^n)⁻¹*reflectionProduct n z y=
      ∏ i,((-8:ℝ)⁻¹*((y i-z)/(y i+z))) := by
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,inv_pow,reflectionProduct]
  rw [he]
  apply Finset.prod_nonneg
  intro i _
  apply mul_nonneg_of_nonpos_of_nonpos (by norm_num)
  exact div_nonpos_of_nonpos_of_nonneg (by linarith [(hy.2 i).2]) (by linarith [(hy.2 i).1])

lemma integral_cauchyDensity_lower (n : ℕ) {z : ℝ} (hz : 1<z) (hz₂ : z≤2) :
    (∫ y, density n y ∂unitCubeMeasure n)/(2:ℝ)^n ≤
      ∫ y, cauchyDensity n z y ∂unitCubeMeasure n := by
  rw [←integral_div]
  apply integral_mono_ae ((integrable_density_unitCube n).div_const _) (integrable_cauchyDensity n hz)
  filter_upwards [ae_unitCube n] with y hy
  apply div_le_div₀ (density_nonneg_of_nonneg fun i => (hy i).1.le) le_rfl
    (Finset.prod_pos fun i _ => by linarith [(hy i).2])
  calc
    (∏ i, (z-y i)) ≤ ∏ _ : Fin n, (2:ℝ) := Finset.prod_le_prod₀
      (fun i _ => by linarith [(hy i).2]) (fun i _ => by linarith [(hy i).1])
    _ = _ := by simp

lemma projectionF_continuousAt (P J E : Polynomial ℝ) {z : ℝ} (hz : z≠0) :
    ContinuousAt (projectionF P J E) z := by
  change ContinuousAt (fun z : ℝ => P.eval z + Real.sqrt ((1+Real.sqrt ((1-1/z)/2))/2)*J.eval z +
    Real.sqrt ((1+Real.sqrt ((1-1/z)/2))/2)^2*E.eval z) z
  fun_prop (disch := assumption)

 
lemma projectionF_one_neg {n : ℕ} (hn : 1≤n) {g P J E : Polynomial ℝ}
    (hg : g.Monic) (hd : g.natDegree=n)
    (hP : P.natDegree≤n) (hJ : J.natDegree≤n) (hE : E.degree<(n:WithBot ℕ))
    (hQ : homogeneousQ n g=P.comp harmonicCoordinate+X*J.comp harmonicCoordinate+
      X^2*E.comp harmonicCoordinate) :
    projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) 1<0 := by
  let b : ℝ := (∫ y, density (n+1) y ∂unitCubeMeasure (n+1)) /
    ((2:ℝ)^(n+1)*(Real.pi*8^n*((n:ℝ)+1)*∫ y, density n y ∂unitCubeMeasure n))
  have hb : 0<b := by
    dsimp [b]
    exact div_pos (integral_density_unitCube_positive (n+1)) (by
      have hp:=Real.pi_pos; have hi:=integral_density_unitCube_positive n; positivity)
  have hden : 0<Real.pi*(8:ℝ)^n*((n:ℝ)+1)*∫ y, density n y ∂unitCubeMeasure n := by
    have hp:=Real.pi_pos; have hi:=integral_density_unitCube_positive n; positivity
  have ht := (projectionF_continuousAt (tildePoly n P) (tildePoly n J) (tildePoly n E)
    (by norm_num : (1:ℝ)≠0)).tendsto.mono_left (nhdsWithin_le_nhds (s:=Ioi (1:ℝ)))
  have hbnd : ∀ᶠ z in 𝓝[>] (1:ℝ),
      projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) z≤ -b := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (1:ℝ)<2))] with z hz hz₂
    rw [projectionF_positive_cauchy hn hg hd hP hJ hE hQ hz]
    have hi:=div_le_div_of_nonneg_right (integral_cauchyDensity_lower (n+1) hz hz₂.le) hden.le
    dsimp [b]
    calc
      _ ≤ -( (∫ y, density (n+1) y ∂unitCubeMeasure (n+1))/(2:ℝ)^(n+1) /
        (Real.pi*8^n*((n:ℝ)+1)*∫ y, density n y ∂unitCubeMeasure n)) := by simpa only [neg_div] using neg_le_neg hi
      _ = _ := by rw [div_div]
  exact (le_of_tendsto ht hbnd).trans_lt (neg_neg_of_pos hb)

lemma branches_inverse {x : ℝ} (hx : x∈Ioo c C) :
    let u:=8*x^2*(1-x^2)-1
    0<u ∧ u≤1 ∧ (x=highBranch u ∨ x=lowBranch u) := by
  dsimp only
  have hp : 0<x := C_c_facts.1.trans hx.1
  have hCp : 0<C := C_c_facts.1.trans C_c_facts.2.1
  have hcq : c^2<x^2 := by nlinarith [mul_pos (sub_pos.mpr hx.1) (add_pos hp C_c_facts.1)]
  have hCq : x^2<C^2 := by nlinarith [mul_pos (sub_pos.mpr hx.2) (add_pos hCp hp)]
  have hsum := C_c_facts.2.2.1
  have hprod : C^2*c^2=1/8 := by nlinarith [C_c_facts.2.2.2.1]
  have hfact : 8*x^2*(1-x^2)-1=8*(x^2-c^2)*(C^2-x^2) := by
    nlinarith [hsum,hprod]
  refine ⟨by rw [hfact]; positivity, by nlinarith [sq_nonneg (2*x^2-1)],?_⟩
  have hs : Real.sqrt ((1-(8*x^2*(1-x^2)-1))/2)=|2*x^2-1| := by
    rw [show (1-(8*x^2*(1-x^2)-1))/2=(2*x^2-1)^2 by ring,Real.sqrt_sq_eq_abs]
  by_cases hm : 0≤2*x^2-1
  · left
    rw [highBranch,hs,abs_of_nonneg hm,
      show (1+(2*x^2-1))/2=x^2 by ring,Real.sqrt_sq hp.le]
  · right
    rw [lowBranch,hs,abs_of_neg (lt_of_not_ge hm),
      show (1- -(2*x^2-1))/2=x^2 by ring,Real.sqrt_sq hp.le]

lemma branches_order (u : ℝ) : lowBranch u≤highBranch u := by
  apply Real.sqrt_le_sqrt
  linarith [Real.sqrt_nonneg ((1-u)/2)]

lemma projection_low_difference {n : ℕ} {P J E : Polynomial ℝ}
    (hP : P.natDegree≤n) (hJ : J.natDegree≤n) (hE : E.natDegree≤n)
    {z : ℝ} (hz : 1<z) :
    z^n*(P.comp harmonicCoordinate+X*J.comp harmonicCoordinate+X^2*E.comp harmonicCoordinate).eval (lowBranch (1/z))=
      projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) z -
      (highBranch (1/z)-lowBranch (1/z))*projectionD (tildePoly n J) (tildePoly n E) z := by
  have hs : 1/z∈Ioo (-1:ℝ) 1 := ⟨lt_trans (by norm_num) (one_div_pos.mpr (by linarith)), (div_lt_one (by linarith)).mpr hz⟩
  rw [←tilde_projection_eval n P J E hP hJ hE (by linarith : z≠0) (branches_harmonic hs).2]
  have hsum := branches_sum hs
  change highBranch (1/z)+lowBranch (1/z)=lBranch z at hsum
  dsimp only [projectionF,projectionD]
  change _ = (tildePoly n P).eval z+highBranch (1/z)*(tildePoly n J).eval z+
    highBranch (1/z)^2*(tildePoly n E).eval z -
    (highBranch (1/z)-lowBranch (1/z))*((tildePoly n J).eval z+lBranch z*(tildePoly n E).eval z)
  rw [←hsum]
  ring

 

theorem MonicProblem.eval_pos_between {n : ℕ} (hn : 1≤n) {g : Polynomial ℝ}
    (hg : MonicProblem n g) {x : ℝ} (hx : x∈Ioo c C) : 0<g.eval x := by
  obtain ⟨hgm,hgd,P,J,E,hP,hJ,hE,hQ⟩:=hg
  obtain ⟨hu,hu₁,he⟩:=branches_inverse hx
  let u:=8*x^2*(1-x^2)-1
  have hEn : E.natDegree≤n := (degree_lt_implies_natDegree_lt (by omega) hE).le
  have hQneg : (homogeneousQ n g).eval x<0 := by
    by_cases huc : u=1
    · have heh : highBranch 1=lowBranch 1 := by norm_num [highBranch,lowBranch]
      have hex : x=highBranch 1 := by
        rcases he with he | he
        · simpa only [show 8*x^2*(1-x^2)-1=1 from huc] using he
        · simpa only [show 8*x^2*(1-x^2)-1=1 from huc,←heh] using he
      have hh:=tilde_projection_eval n P J E hP hJ hEn (by norm_num : (1:ℝ)≠0)
        (b:=highBranch 1) (by
          norm_num [harmonicCoordinate,highBranch])
      rw [←hQ,one_pow,one_mul] at hh
      rw [hex]
      have hh' : projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) 1=
          (homogeneousQ n g).eval (highBranch 1) := by simpa only [projectionF,fBranch,highBranch,div_one] using hh
      rw [←hh']
      exact projectionF_one_neg hn hgm hgd hP hJ hE hQ
    · have hu' : u<1 := lt_of_le_of_ne hu₁ huc
      have hz : 1<1/u := (lt_div_iff₀ hu).mpr (by linarith)
      have hs : u∈Ioo (-1:ℝ) 1 := ⟨by linarith,hu'⟩
      have hzn : 0<(1/u)^n := pow_pos (by positivity) n
      rcases he with he | he
      · have hh:=tilde_projection_eval n P J E hP hJ hEn (by positivity : 1/u≠0)
          (b:=highBranch u) (by simpa only [one_div_one_div] using (branches_harmonic hs).1)
        rw [←hQ] at hh
        have hh' : projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) (1/u)=
            (1/u)^n*(homogeneousQ n g).eval (highBranch u) := by
          simpa only [projectionF,fBranch,highBranch,one_div_one_div] using hh
        have ht:=projectionF_neg hn hgm hgd hP hJ hE hQ hz
        rw [hh',←he] at ht
        exact ((mul_neg_iff.mp ht).resolve_right (by rintro ⟨h,_⟩; linarith)).2
      · have hh:=projection_low_difference hP hJ hEn hz
        rw [←hQ,one_div_one_div,←he] at hh
        have hfn:=projectionF_neg hn hgm hgd hP hJ hE hQ hz
        have hdpos:=mul_nonneg (sub_nonneg.mpr (branches_order u))
          (projectionD_nonneg_right hn hgm hgd hP hJ hE hQ hz.le)
        have hhneg : projectionF (tildePoly n P) (tildePoly n J) (tildePoly n E) (1/u) -
            (highBranch u-lowBranch u)*projectionD (tildePoly n J) (tildePoly n E) (1/u)<0 := by
          linarith
        rw [←he] at hhneg
        rw [←hh] at hhneg
        exact ((mul_neg_iff.mp hhneg).resolve_right (by rintro ⟨h,_⟩; linarith)).2
  simp only [homogeneousQ,eval_mul,eval_pow,eval_sub,eval_X,eval_C] at hQneg
  have hp : (x-C)^(2*n+1)*(x-c)^n<0 := mul_neg_of_neg_of_pos
    ((odd_two_mul_add_one n).pow_neg (sub_neg.mpr hx.2)) (pow_pos (sub_pos.mpr hx.1) n)
  exact ((mul_neg_iff.mp hQneg).resolve_left (by rintro ⟨h,_⟩; linarith)).2

end
end CriticalStrip

 

 

namespace CriticalStrip.Diagram
noncomputable section
open Set Polynomial
open scoped BigOperators Classical

lemma c_eq_critical : c=CriticalStrip.c := by
  unfold c lambda CriticalStrip.c
  congr 1
  ring

lemma scalarValue_homogeneous_ne_zero (n : ℕ) :
    scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))≠0 := by
  obtain ⟨x,hx,he⟩:=scalarValue_homogeneous_positive n
  rw [he]
  exact_mod_cast hx.ne'

 

theorem archPolynomialAt_homogeneous {n : ℕ} (hn : 1≤n) :
    ∃ g : Polynomial ℝ, MonicProblem n g ∧
      archPolynomialAt (fun _ : Fin n => (C:ℂ))=g.map Complex.ofRealHom :=
  archPolynomialAt_homogeneous_of_ne hn (scalarValue_homogeneous_ne_zero n)

lemma nextScalar_homogeneous {n : ℕ} (hn : 1≤n) :
    ∃ g : Polynomial ℝ, MonicProblem n g ∧
      nextScalar (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))=
        Polynomial.C (scalarValue (RingHom.id ℂ) (fun _ : Fin n => (C:ℂ))) * g.map Complex.ofRealHom :=
  nextScalar_homogeneous_of_ne hn (scalarValue_homogeneous_ne_zero n)

end
end CriticalStrip.Diagram

namespace CriticalStrip
noncomputable section
open Set Polynomial
open scoped BigOperators Classical

lemma MonicProblem.eval_c {n : ℕ} (hn : 1≤n) {g : Polynomial ℝ}
    (hg : MonicProblem n g) : g.eval c=(2*C)^n := by
  obtain ⟨g₀,hg₀,hnext⟩:=Diagram.nextScalar_homogeneous hn
  have heq : g=g₀ := (homogeneous_monic_unique n hn).unique hg hg₀
  subst g₀
  apply Complex.ofReal_injective
  have hh:=congrArg (Polynomial.eval (c:ℂ)) hnext
  rw [Diagram.nextScalar_eval,Diagram.scalarValue_snoc,←Diagram.c_eq_critical] at hh
  have hflat:=Diagram.scalarValue_flat (RingHom.id ℂ) (fun _ : Fin n => (Diagram.C:ℂ))
  simp only [RingHom.id_apply] at hflat
  rw [hflat] at hh
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_map] at hh
  have hm : Polynomial.eval₂ Complex.ofRealHom (Diagram.c:ℂ) g = (↑(g.eval (c:ℝ)):ℂ) := by
    rw [Diagram.c_eq_critical]
    exact Polynomial.eval₂_at_apply Complex.ofRealHom c
  rw [hm] at hh
  have hv := mul_left_cancel₀ (Diagram.scalarValue_homogeneous_ne_zero n)
    (hh.symm.trans (mul_comm _ _))
  simpa only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,two_mul,Diagram.C,Diagram.lambda,C,lambda,Complex.ofReal_add] using hv

 
theorem MonicProblem.eval_pos_Icc {n : ℕ} (hn : 1≤n) {g : Polynomial ℝ}
    (hg : MonicProblem n g) {x : ℝ} (hx : x∈Icc c C) : 0<g.eval x := by
  rcases hx with ⟨hcx,hxC⟩
  rcases eq_or_lt_of_le hcx with rfl | hc
  · rw [hg.eval_c hn]
    exact pow_pos (mul_pos (by norm_num) (C_c_facts.1.trans C_c_facts.2.1)) n
  rcases eq_or_lt_of_le hxC with rfl | hC
  · exact hg.eval_C_pos hn
  · exact hg.eval_pos_between hn ⟨hc,hC⟩

end
end CriticalStrip

namespace CriticalStrip.Diagram
noncomputable section
open Set Polynomial
open scoped BigOperators Classical

 

theorem scalarValue_deformation_positive (n : ℕ) {x : ℝ}
    (hx : x∈Icc c C) :
    ∃ y : ℝ, 0<y ∧
      scalarValue (RingHom.id ℂ) (Fin.snoc (fun _ : Fin n => (C:ℂ)) (x:ℂ))=(y:ℂ) := by
  by_cases hn : n=0
  · subst n
    refine ⟨1,by norm_num,?_⟩
    have he : (Fin.snoc (fun _ : Fin 0 => (C:ℂ)) (x:ℂ) : Fin 1 → ℂ)=fun _ => (x:ℂ) := by
      funext i; fin_cases i; rfl
    rw [he,scalarValue_one,Complex.ofReal_one]
  obtain ⟨p,hp,he⟩:=scalarValue_homogeneous_positive n
  obtain ⟨g,hg,hnext⟩:=nextScalar_homogeneous (by omega : 1≤n)
  refine ⟨p*g.eval x,mul_pos hp (hg.eval_pos_Icc (by omega) (by simpa only [c_eq_critical,C,lambda,CriticalStrip.C,CriticalStrip.lambda] using hx)),?_⟩
  have hh:=congrArg (Polynomial.eval (x:ℂ)) hnext
  have hm : Polynomial.eval₂ Complex.ofRealHom (x:ℂ) g = (↑(g.eval x):ℂ) :=
    Polynomial.eval₂_at_apply Complex.ofRealHom x
  rw [nextScalar_eval,Polynomial.eval_mul,Polynomial.eval_C,he,Polynomial.eval_map,hm] at hh
  exact hh.trans (Complex.ofReal_mul _ _).symm

lemma scalarValue_deformation_ne_zero (n : ℕ) {x : ℝ} (hx : x∈Icc c C) :
    scalarValue (RingHom.id ℂ) (Fin.snoc (fun _ : Fin n => (C:ℂ)) (x:ℂ))≠0 := by
  obtain ⟨y,hy,he⟩:=scalarValue_deformation_positive n hx
  rw [he]
  exact_mod_cast hy.ne'

lemma cosine_deformation {u : ℝ} (hu : u∈Icc 0 lambda) :
    Real.cos (2*u-3*lambda)∈Icc c C := by
  have hl : 0<lambda := by unfold lambda; positivity
  have hπ : 3*lambda<Real.pi := by unfold lambda; linarith [Real.pi_pos]
  have harg : lambda≤3*lambda-2*u ∧ 3*lambda-2*u≤3*lambda := by constructor <;> linarith [hu.1,hu.2]
  rw [show 2*u-3*lambda= -(3*lambda-2*u) by ring,Real.cos_neg]
  exact ⟨Real.cos_le_cos_of_nonneg_of_le_pi (by linarith) hπ.le harg.2,
    Real.cos_le_cos_of_nonneg_of_le_pi hl.le (harg.2.trans hπ.le) harg.1⟩

end
end CriticalStrip.Diagram

end OAI
