import OAI.NumberTheory.Jacobsthal.Paths.RawBoxRationalWitness
import OAI.NumberTheory.Jacobsthal.Probability.FullBoxVarianceGeometry
import OAI.NumberTheory.Jacobsthal.Sieve.EndpointCofactorSplit

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosVarianceEffective
open ErdosInverseCells

noncomputable def effectiveSize (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (R : ℝ) : ℝ :=
  max (effectiveModulus a r qf : ℝ) (|(effectiveIntercept a r qf : ℝ)|/R)

theorem effective_ratio_identity (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) (R : ℝ) :
    |(effectiveIntercept a r qf : ℝ)|/(R*(effectiveModulus a r qf : ℝ)) =
      |(hitNumerator a r qf : ℝ)|/(R*(r.den : ℝ)*(qf : ℝ)) := by
  let qa := alignedCofactor (fun t => (a t : ℤ)) r qf
  have hqa : (0 : ℝ) < qa := by exact_mod_cast alignedCofactor_pos _ r qf hq
  have he : (qa : ℝ)*(effectiveIntercept a r qf : ℝ) = (hitNumerator a r qf : ℝ) := by
    exact_mod_cast effectiveIntercept_identity a r qf hq
  have hnum : |(hitNumerator a r qf : ℝ)| = (qa : ℝ)*|(effectiveIntercept a r qf : ℝ)| := by
    rw [← he,abs_mul,abs_of_pos hqa]
  have hden : R*(r.den : ℝ)*(qf : ℝ) = (qa : ℝ)*(R*(effectiveModulus a r qf : ℝ)) := by
    have hh : (r.den : ℝ)*(qf : ℝ) = (qa : ℝ)*(effectiveModulus a r qf : ℝ) := by
      exact_mod_cast denominator_full_cofactor a r qf hq
    linear_combination R*hh
  rw [hnum,hden]
  exact (mul_div_mul_left _ _ hqa.ne').symm

theorem effective_ratio_upper (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) (R : ℝ)
    (hR : 0 < R) :
    |(effectiveIntercept a r qf : ℝ)|/(R*(effectiveModulus a r qf : ℝ)) ≤
      1/R+|(r.num : ℝ)|/(R*(r.den : ℝ)*(qf : ℝ)) := by
  rw [effective_ratio_identity a r qf hq R]
  have hD : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hqR : (0 : ℝ) < qf := by exact_mod_cast Nat.pos_of_ne_zero hq.ne_zero
  have hb : (cofactorHit qf a : ℝ) ≤ qf := by exact_mod_cast (cofactorHit_spec qf hq a).2.1
  have hn : |(hitNumerator a r qf : ℝ)| ≤ (r.den : ℝ)*(qf : ℝ)+|(r.num : ℝ)| := by
    have hh := abs_sub ((r.den : ℝ)*(cofactorHit qf a : ℝ)) (r.num : ℝ)
    have hpos : 0 ≤ (r.den : ℝ)*(cofactorHit qf a : ℝ) := by positivity
    simp only [abs_of_nonneg hpos] at hh
    have hb' := mul_le_mul_of_nonneg_left hb hD.le
    simpa only [hitNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast] using
      hh.trans (add_le_add hb' le_rfl)
  calc
    _ ≤ ((r.den : ℝ)*(qf : ℝ)+|(r.num : ℝ)|)/(R*(r.den : ℝ)*(qf : ℝ)) :=
      div_le_div_of_nonneg_right hn (by positivity)
    _ = _ := by field_simp

theorem effective_size_ratio_le (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hqf : Squarefree qf)
    (q : ℕ) (hq : 0 < q) (hqqf : q ≤ qf) (Sq R Z : ℝ)
    (_hSq : 0 ≤ Sq) (hR : 1 ≤ R) (hZ : 2 ≤ Z)
    (hSqratio : Sq/(q : ℝ) ≤ Z) (hA : |(r.num : ℝ)| ≤ Sq*R*Z^10) :
    effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ Z^12 := by
  have hRp : 0 < R := by linarith
  have hqp : (0 : ℝ) < q := by exact_mod_cast hq
  have hH : (0 : ℝ) < effectiveModulus a r qf := by exact_mod_cast effectiveModulus_pos a r qf
  have hD : (1 : ℝ) ≤ r.den := by exact_mod_cast r.pos
  have hqqfR : (q : ℝ) ≤ qf := by exact_mod_cast hqqf
  have hqD : (q : ℝ) ≤ (r.den : ℝ)*(qf : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg qf : (0 : ℝ) ≤ qf)
    nlinarith
  have hnum : |(r.num : ℝ)|/(R*(r.den : ℝ)*(qf : ℝ)) ≤ (Sq/(q : ℝ))*Z^10 := by
    calc
      _ ≤ |(r.num : ℝ)|/(R*(q : ℝ)) := div_le_div_of_nonneg_left (abs_nonneg _)
        (by positivity) (by nlinarith [mul_le_mul_of_nonneg_left hqD hRp.le])
      _ ≤ (Sq*R*Z^10)/(R*(q : ℝ)) := div_le_div_of_nonneg_right hA (by positivity)
      _ = _ := by field_simp
  have hpow : 1 ≤ Z^11 := one_le_pow₀ (by linarith)
  have hZ12 : 1+Z^11 ≤ Z^12 := by
    calc
      _ ≤ 2*Z^11 := by linarith
      _ ≤ Z*Z^11 := mul_le_mul_of_nonneg_right hZ (by positivity)
      _ = _ := by ring
  have hratio : |(effectiveIntercept a r qf : ℝ)|/(R*(effectiveModulus a r qf : ℝ)) ≤ Z^12 := by
    calc
      _ ≤ 1/R+|(r.num : ℝ)|/(R*(r.den : ℝ)*(qf : ℝ)) := effective_ratio_upper a r qf hqf R hRp
      _ ≤ 1+(Sq/(q : ℝ))*Z^10 := add_le_add (div_le_self (by norm_num) hR) hnum
      _ ≤ 1+Z*Z^10 := add_le_add le_rfl (mul_le_mul_of_nonneg_right hSqratio (show 0 ≤ Z^10 by positivity))
      _ = 1+Z^11 := by ring
      _ ≤ _ := hZ12
  apply (div_le_iff₀ hH).mpr
  apply max_le
  · have h1 : 1 ≤ Z^12 := by linarith [hZ12,pow_nonneg (by linarith : (0 : ℝ) ≤ Z) 11]
    nlinarith
  · have hh := (div_le_iff₀ hH).mp (show (|(effectiveIntercept a r qf : ℝ)|/R)/(effectiveModulus a r qf : ℝ) ≤ Z^12 by
        simpa only [div_div] using hratio)
    exact hh

end ErdosVarianceEffective



namespace ErdosVarianceEffective
open ErdosInverseAlignment ErdosPrimitiveIntercept ErdosInverseCells

theorem denominator_le_effectiveModulus (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) :
    r.den ≤ effectiveModulus a r qf := by
  have hE := badPrimeProduct_pos (fun t => (a t : ℤ)) r qf
  dsimp [effectiveModulus]
  nlinarith

theorem nonaligned_le_effectiveModulus (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) :
    badPrimeProduct (fun t => (a t : ℤ)) r qf ≤ effectiveModulus a r qf := by
  have hD := r.pos
  dsimp [effectiveModulus]
  nlinarith

theorem alignedCofactor_le_full (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    alignedCofactor (fun t => (a t : ℤ)) r qf ≤ qf := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero hq.ne_zero)
  exact ⟨badPrimeProduct (fun t => (a t : ℤ)) r qf,(alignedCofactor_mul_bad _ r qf hq).symm⟩

theorem soft_effective_bounds (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (R B : ℝ) (hR : 0 < R)
    (hsoft : effectiveSize a r qf R ≤ B) :
    (r.den : ℝ) ≤ B ∧ (badPrimeProduct (fun t => (a t : ℤ)) r qf : ℝ) ≤ B ∧
      |(effectiveIntercept a r qf : ℝ)| ≤ R*B := by
  have hH : (effectiveModulus a r qf : ℝ) ≤ B := (le_max_left _ _).trans hsoft
  have hC : |(effectiveIntercept a r qf : ℝ)|/R ≤ B := (le_max_right _ _).trans hsoft
  refine ⟨?_,?_,?_⟩
  · have hh : (r.den : ℝ) ≤ effectiveModulus a r qf := by exact_mod_cast denominator_le_effectiveModulus a r qf
    exact hh.trans hH
  · have hh : (badPrimeProduct (fun t => (a t : ℤ)) r qf : ℝ) ≤ effectiveModulus a r qf := by
      exact_mod_cast nonaligned_le_effectiveModulus a r qf
    exact hh.trans hH
  · have hh := (div_le_iff₀ hR).mp hC
    nlinarith

theorem large_factor_aligns_of_soft (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (R B : ℝ) (hR : 0 < R)
    (hsoft : effectiveSize a r qf R ≤ B) (t : ℕ) (ht : t ∈ qf.primeFactors) (hlarge : B < (t : ℝ)) :
    aligns (fun u => (a u : ℤ)) r t := by
  classical
  by_contra hn
  have hmem : t ∈ badPrimeFactors (fun u => (a u : ℤ)) r qf := Finset.mem_filter.mpr ⟨ht,hn⟩
  have hd : t ∣ badPrimeProduct (fun u => (a u : ℤ)) r qf := Finset.dvd_prod_of_mem _ hmem
  have hle := Nat.le_of_dvd (badPrimeProduct_pos _ r qf) hd
  have hleR : (t : ℝ) ≤ badPrimeProduct (fun u => (a u : ℤ)) r qf := by exact_mod_cast hle
  have hbound := (soft_effective_bounds a r qf R B hR hsoft).2.1
  linarith

end ErdosVarianceEffective


section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceSmallModel
open ErdosInversePrimeBin ErdosInverseBoxHeight ErdosVarianceEffective

theorem source_effective_point_domination (alpha : ℝ) (ha : 0 < alpha) :
    ∃ C : ℝ,0 < C ∧ ∀ xi : ℝ,0 < xi → xi ≤ 1 →
      ∀ᶠ z : ℝ in atTop,
      ∀ (R theta : ℝ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ),Squarefree qf →
        z^alpha ≤ R → xi/4 ≤ theta → theta ≤ xi →
        (effectiveModulus a r qf : ℝ) ≤ R^((4 : ℝ)/5) →
        effectiveSize a r qf R/(effectiveModulus a r qf : ℝ) ≤ (sourceZ z)^12 →
        ∃ (hw : 0 ≤ sourceW z) (hP : ∀ p ∈ primeBin R theta,p.Prime)
          (hlarge : ∀ p ∈ primeBin R theta,sourceW z < (p : ℝ)),
        ∀ E : ModelPoint (sourceW z) (effectiveModulus a r qf) → Prop,
          ((actualPrimeEvent (primeBin R theta) (sourceW z) (effectiveModulus a r qf)
            (effectiveIntercept a r qf) hw hP hlarge E).card : ℝ)/((primeBin R theta).card : ℝ) ≤
            C*modelMass R xi (sourceW z) (effectiveModulus a r qf) (effectiveIntercept a r qf) E := by
  obtain ⟨C,hC,hdom⟩ := source_prime_model_domination alpha ha
  refine ⟨C,hC,?_⟩
  intro xi hxi hxi1
  filter_upwards [hdom xi hxi hxi1] with z hz
  intro R theta a r qf hq hRlo htl htu hHsmall hRatio
  exact hz R theta (effectiveModulus a r qf) (effectiveIntercept a r qf)
    hRlo htl htu (effectiveModulus_pos a r qf) (effective_coordinates_gcd a r qf hq) hHsmall hRatio

end ErdosVarianceSmallModel

end


namespace ErdosVarianceEffective
open ErdosInverseCells

theorem actual_numerator_triangle (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf) :
    |(r.num : ℝ)| ≤ (r.den : ℝ)*(qf : ℝ)+(qf : ℝ)*|(effectiveIntercept a r qf : ℝ)| := by
  have hEq : (alignedCofactor (fun t => (a t : ℤ)) r qf : ℝ)*(effectiveIntercept a r qf : ℝ) =
      (r.den : ℝ)*(cofactorHit qf a : ℝ)-(r.num : ℝ) := by
    simpa only [hitNumerator,Int.cast_sub,Int.cast_mul,Int.cast_natCast] using
      congrArg (fun x : ℤ => (x : ℝ)) (effectiveIntercept_identity a r qf hq)
  have hA : (r.num : ℝ) = (r.den : ℝ)*(cofactorHit qf a : ℝ)-
      (alignedCofactor (fun t => (a t : ℤ)) r qf : ℝ)*(effectiveIntercept a r qf : ℝ) := by linarith
  have hb : (cofactorHit qf a : ℝ) ≤ qf := by exact_mod_cast (cofactorHit_spec qf hq a).2.1
  have hqa : (alignedCofactor (fun t => (a t : ℤ)) r qf : ℝ) ≤ qf := by
    exact_mod_cast alignedCofactor_le_full a r qf hq
  rw [hA]
  calc
    _ ≤ |(r.den : ℝ)*(cofactorHit qf a : ℝ)|+
        |(alignedCofactor (fun t => (a t : ℤ)) r qf : ℝ)*(effectiveIntercept a r qf : ℝ)| := abs_sub _ _
    _ = (r.den : ℝ)*(cofactorHit qf a : ℝ)+
        (alignedCofactor (fun t => (a t : ℤ)) r qf : ℝ)*|(effectiveIntercept a r qf : ℝ)| := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (r.den : ℝ)*(cofactorHit qf a : ℝ)),abs_mul,
        abs_of_nonneg (Nat.cast_nonneg _)]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_right hqa (abs_nonneg _))

theorem soft_global_heights (Y : ℕ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) (hp : 0 < p) (R w Cs : ℝ) (hR : 0 < R) (hRp : R ≤ (p : ℝ))
    (hw : 2 ≤ w) (hY : p*qf ≤ Y) (hsoft : effectiveSize a r qf R ≤ w^Cs) :
    (r.den : ℝ) ≤ w^Cs ∧ (r.num.natAbs : ℝ) ≤ (Y : ℝ)*w^(Cs+2) := by
  have hb := soft_effective_bounds a r qf R (w^Cs) hR hsoft
  have hw0 : 0 < w := by linarith
  have hB : 0 ≤ w^Cs := Real.rpow_nonneg hw0.le _
  have hqY : (qf : ℝ) ≤ Y := by
    have hh : qf ≤ Y := (by nlinarith : qf ≤ p*qf).trans hY
    exact_mod_cast hh
  have hRqY : R*(qf : ℝ) ≤ Y := by
    have hh := mul_le_mul_of_nonneg_right hRp (Nat.cast_nonneg qf : (0 : ℝ) ≤ qf)
    have hi : (p : ℝ)*(qf : ℝ) ≤ Y := by exact_mod_cast hY
    exact hh.trans hi
  refine ⟨hb.1,?_⟩
  have hA : |(r.num : ℝ)| ≤ 2*(Y : ℝ)*w^Cs := by
    have htri := actual_numerator_triangle a r qf hq
    have hDq := mul_le_mul_of_nonneg_right hb.1 (Nat.cast_nonneg qf : (0 : ℝ) ≤ qf)
    have hCq := mul_le_mul_of_nonneg_left hb.2.2 (Nat.cast_nonneg qf : (0 : ℝ) ≤ qf)
    have hqY' := mul_le_mul_of_nonneg_left hqY hB
    have hRqY' := mul_le_mul_of_nonneg_left hRqY hB
    nlinarith
  have hw2 : 2 ≤ w^2 := by nlinarith
  have hscale : 2*(Y : ℝ)*w^Cs ≤ (Y : ℝ)*w^(Cs+2) := by
    rw [Real.rpow_add hw0,Real.rpow_two]
    have hh := mul_le_mul_of_nonneg_left hw2 (mul_nonneg (Nat.cast_nonneg Y : (0 : ℝ) ≤ Y) hB)
    nlinarith
  simpa only [Nat.cast_natAbs,Int.cast_abs] using hA.trans hscale

end ErdosVarianceEffective


section

open _root_.Filter
open scoped Topology
namespace ErdosVarianceEffective
open ErdosInverseBoxHeight ErdosInverseEuler ErdosInverseCells ErdosCofactorChoices ErdosPrimitiveIntercept
open NumberTheoryLean.LogarithmicBinScale

theorem source_effective_heights (Clen Cparent : ℝ) (hClen : 0 ≤ Clen) (hCparent : 0 ≤ Cparent) :
    ∀ᶠ z : ℝ in atTop,∀ xi : ℝ,0 < xi → xi ≤ 1 →
      ∀ m : Fin (binCount (sourceW z) z xi) → ℕ,
      ((∑ i,m i : ℕ) : ℝ) ≤ Clen*Real.log (sourceB z) →
      ∀ (a : ℕ → ℕ) (r : ℚ) (q e p : ℕ) (R : ℝ),
      q ∈ cofactorChoices (actualBins z xi) m → 0 < e → 0 < p → Squarefree (q*e) → 1 ≤ R →
      p*(q*e) ≤ sourceY z →
      Real.logb (sourceW z) ((sourceY z : ℝ)/((p : ℝ)*q)) ≤ Cparent →
      ((r.den*badPrimeProduct (fun t => (a t : ℤ)) r q : ℕ) : ℝ) ≤ R*(sourceZ z)^10 →
      (r.num.natAbs : ℝ) ≤ cofactorScale z xi m*R*(sourceZ z)^10 →
      (effectiveModulus a r (q*e) : ℝ) ≤ R*(sourceZ z)^11 ∧
        effectiveSize a r (q*e) R/(effectiveModulus a r (q*e) : ℝ) ≤ (sourceZ z)^12 := by
  filter_upwards [source_span_geometry,source_extension_le_Z Cparent hCparent,
    source_bin_factor_subpower Clen 1 hClen zero_lt_one,sourceZ_tendsto_atTop.eventually_ge_atTop 2]
    with z hspan hext hfactor hZ
  intro xi hxi hxi1 m hm a r q e p R hq he hp hqf hR hFinal hParent hStructure hRaw
  have hqpos := actual_cofactor_positive hspan.1 hspan.2.1 hxi m q hq
  have hqR : (0 : ℝ) < q := by exact_mod_cast hqpos
  have heZ := hext p q e hp hqpos he hFinal hParent
  refine ⟨effectiveModulus_height_of_extension a r q e hqpos he R (sourceZ z) (by linarith)
    (by linarith) hStructure heZ,?_⟩
  have hrange := actual_cofactor_range hspan.1 hspan.2.1 hxi m q hq
  have hratio : cofactorScale z xi m/(q : ℝ) ≤ sourceZ z := by
    calc
      _ ≤ (1+xi)^(∑ i,m i) := by
        apply (div_le_iff₀ hqR).mpr
        have hh := (div_le_iff₀ (pow_pos (by linarith : 0 < 1+xi) _)).mp hrange.1
        nlinarith
      _ ≤ _ := by simpa only [Real.rpow_one] using hfactor xi (∑ i,m i) hxi hxi1 hm
  have hqle : q ≤ q*e := by nlinarith
  have hA : |(r.num : ℝ)| ≤ cofactorScale z xi m*R*(sourceZ z)^10 := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using hRaw
  exact effective_size_ratio_le a r (q*e) hqf q hqpos hqle (cofactorScale z xi m) R (sourceZ z)
    (actual_cofactorScale_pos hspan.1 hspan.2.1 hxi m).le hR hZ hratio hA

end ErdosVarianceEffective

end


namespace ErdosVarianceEffective
open ErdosInverseAlignment

theorem soft_full_factor_alignment (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) (hp : p.Prime) (halign : aligns (fun t => (a t : ℤ)) r p)
    (R B : ℝ) (hR : 0 < R) (hsoft : effectiveSize a r qf R ≤ B) :
    ∀ t ∈ (p*qf).primeFactors,B < (t : ℝ) → aligns (fun u => (a u : ℤ)) r t := by
  intro t ht hlarge
  rw [Nat.primeFactors_mul hp.ne_zero hq.ne_zero,hp.primeFactors] at ht
  rcases Finset.mem_union.mp ht with ht | ht
  · have he : t = p := Finset.mem_singleton.mp ht
    exact he.symm ▸ halign
  · exact large_factor_aligns_of_soft a r qf R B hR hsoft t ht hlarge

theorem soft_endpoint_eligible (Y : ℕ) (a : ℕ → ℕ) (r : ℚ) (qf : ℕ) (hq : Squarefree qf)
    (p : ℕ) (hp : p.Prime) (halign : aligns (fun t => (a t : ℤ)) r p)
    (R w Cs : ℝ) (hR : 0 < R) (hRp : R ≤ (p : ℝ)) (hw : 2 ≤ w)
    (hY : p*qf ≤ Y) (hsoft : effectiveSize a r qf R ≤ w^Cs) :
    (r.den : ℝ) ≤ w^Cs ∧ (r.num.natAbs : ℝ) ≤ (Y : ℝ)*w^(Cs+2) ∧
      ∀ t ∈ (p*qf).primeFactors,Cs < Real.logb w (t : ℝ) → aligns (fun u => (a u : ℤ)) r t := by
  have hheight := soft_global_heights Y a r qf hq p hp.pos R w Cs hR hRp hw hY hsoft
  refine ⟨hheight.1,hheight.2,?_⟩
  intro t ht hlog
  have htpos : (0 : ℝ) < t := by exact_mod_cast Nat.pos_of_mem_primeFactors ht
  have hpow : w^Cs < (t : ℝ) := (Real.lt_logb_iff_rpow_lt (by linarith : 1 < w) htpos).mp hlog
  exact soft_full_factor_alignment a r qf hq p hp halign R (w^Cs) hR hsoft t ht hpow

end ErdosVarianceEffective


section

open _root_.Filter
namespace ErdosVarianceEligible
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
  SafeSubsetBoxGeometry BoundedEdgeBins CofactorAllChoiceBounds ParentCofactorChoices ParentTailPartition BinCutSelections
  StructuredWitnessOutside EndpointCofactorSplit FullIsolatedCofactor SingletonBinSelection TwoPrimeObservableSum
  ErdosCofactorChoices ErdosSubsetWord ErdosVarianceWeighted ErdosVarianceEffective ErdosInverseBoxHeight
  ErdosInverseCells ErdosInverseAlignment ErdosPrimitiveIntercept
  LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinPartition
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

theorem structured_endpoint_heights (C M : ℝ) (hC : 0 ≤ C) (hM : 0 ≤ M) :
    ∀ᶠ top : ℝ in atTop,
      ∀ xi : ℝ,∀ hxi : 0 < xi,xi ≤ 1 → 2*C*xi ≤ 1 →
      ∀ (hw : 1 < sourceW top) (htop : sourceW top < top) (K aStar X : ℝ),0 ≤ aStar →
      ∀ (z : Node),0 < sourceY top →
        z.gap = Real.log (sourceY top : ℝ)/Real.log (sourceW top)-aStar+2 →
        Valid z.side z.ratio → Consistent z → StrongState z → z.closed = true → (sourceW top)^z.cutoff = top →
      ∀ (m : Fin (binCount (sourceW top) top xi) → ℕ),SafeAnchor hw htop hxi C (sourceB top) K z m →
      ∀ f ∈ selections (globalBins (sourceW top) top xi) m,
      ∀ (i j : Fin (binCount (sourceW top) top xi)),j < i → m i = 1 →
        boundedEdgeBin (sourceW top) top xi (sourceY top) m M X j →
      ∀ (residue : ℕ → ℕ) (r : ℚ) (cp : ℝ),
        r ∈ sourceRationalList (globalBins (sourceW top) top xi i) (fun t => (residue t : ℤ))
          (cofactorScale top xi (parentCofactorMultiplicity m i j)) (lower (sourceW top) top xi i) (sourceZ top) cp →
        ((r.den*badPrimeProduct (fun t => (residue t : ℤ)) r (selectionProduct (parentCofactorSelection f i j)) : ℕ) : ℝ) ≤
          lower (sourceW top) top xi i*(sourceZ top)^10 →
        (effectiveModulus residue r (selectionProduct (eraseSelection f i)) : ℝ) ≤
          lower (sourceW top) top xi i*(sourceZ top)^11 ∧
        effectiveSize residue r (selectionProduct (eraseSelection f i)) (lower (sourceW top) top xi i)/
          (effectiveModulus residue r (selectionProduct (eraseSelection f i)) : ℝ) ≤ (sourceZ top)^12 := by
  filter_upwards [source_effective_heights C (M+1) hC (by linarith),
    Real.tendsto_log_atTop.eventually JacobsthalSourceScale.source_scale_eventually] with top hheights hscale
  intro xi hxi hxi1 hDelta hw htop K aStar X ha z hY hroot hs hz hg hclosed hcap m hanchor
    f hf i j hji hi hj residue r cp hraw hstructure
  let P := globalBins (sourceW top) top xi
  let cm := parentCofactorMultiplicity m i j
  let p := pickedPrime f i
  let q := selectionProduct (parentCofactorSelection f i j)
  let e := pickedPrime f j*selectionProduct (belowSelection f j)
  let qf := selectionProduct (eraseSelection f i)
  let R := lower (sourceW top) top xi i
  have hcomp : Real.log (sourceB top) ≤ 2*Real.log (sourceW top) := hscale.2.2.2.2
  have hmj := bounded_edge_singleton m j hj
  have hcoords := full_selection_coordinates P m f hf i j hi hmj
  have hp : p ∈ P i := hcoords.1
  have hq : q ∈ cofactorChoices (actualBins top xi) cm := hcoords.2.2
  have hppos : 0 < p := (bin_prime_in_source (zero_lt_one.trans hw) htop hxi i hp).1.pos
  have he : 0 < e := endpoint_extra_factor_pos hw htop hxi m f hf j hmj
  have hsplit : qf = q*e := endpoint_cofactor_split hw htop hxi m f hf i j hji hmj
  have hfErase := erase_selection_mem P m f hf i
  have hQf := (erased_cofactor_arithmetic hw htop hxi m i (eraseSelection f i) hfErase).1
  have hQsplit : Squarefree (q*e) := hsplit ▸ hQf
  have hprod : selectionProduct f = p*qf := isolated_product P m f hf i hi
  have hprodPos : 0 < selectionProduct f := by
    rw [hprod]
    exact Nat.mul_pos hppos (Nat.pos_of_ne_zero hQf.ne_zero)
  have htotal := full_box_total_length_lower hw htop hxi hC hcomp (sourceY top) hY z hroot
    hs hz hg hclosed hcap m hanchor f hf
  have hFinal := product_le_Y_of_length (sourceW top) aStar hw ha (sourceY top) (selectionProduct f) hY hprodPos htotal
  rw [hprod,hsplit] at hFinal
  have hRlow : sourceW top ≤ R := (bin_source_bounds (zero_lt_one.trans hw) htop hxi i).1
  have hR1 : 1 ≤ R := hw.le.trans hRlow
  have hparent := (cofactor_all_choice_lengths hw htop hxi hC hcomp (sourceY top) hY z hroot
    hs hz hg hclosed hcap m hanchor i j hji hi hj).1 q hq p hp
  have hparentBound : Real.logb (sourceW top) ((sourceY top : ℝ)/((p : ℝ)*q)) ≤ M+1 :=
    hparent.trans (by linarith)
  have hlen := anchor_total_length hw htop hxi z m hanchor
  have hcm : ((∑ k,cm k : ℕ) : ℝ) ≤ C*Real.log (sourceB top) :=
    (Nat.cast_le.mpr (cofactor_total_le m i j)).trans hlen
  have hSq := actual_cofactorScale_pos (zero_lt_one.trans hw) htop hxi cm
  have hnum := ((mem_sourceRationalList (P i) (fun t => (residue t : ℤ)) hSq.le
    (show 0 ≤ R by linarith) r).mp hraw).1
  have hh := hheights xi hxi hxi1 cm hcm residue r q e p R hq he hppos hQsplit hR1 hFinal
    hparentBound hstructure hnum
  simpa only [← hsplit] using hh

end ErdosVarianceEligible

end


namespace ErdosVarianceEligible
open NumberTheoryLean FinitePathGeometry PrimeHistories PrimeBinMembership StrongReferenceTransport
  SafeSubsetBoxGeometry ErdosCofactorChoices ErdosSubsetWord SingletonBinSelection TwoPrimeObservableSum
  FullIsolatedCofactor ErdosVarianceWeighted
  LogarithmicBinScale LogarithmicBinEndpoints LogarithmicBinPartition
attribute [local instance] Classical.propDecidable

theorem full_endpoint_data {w top xi B C K aStar : ℝ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hC : 0 ≤ C) (ha : 0 ≤ aStar)
    (hcomp : Real.log B ≤ 2*Real.log w) (Y : ℕ) (hY : 0 < Y) (z : Node)
    (hroot : z.gap = Real.log (Y : ℝ)/Real.log w-aStar+2)
    (hs : Valid z.side z.ratio) (hz : Consistent z) (hg : StrongState z)
    (hclosed : z.closed = true) (hcap : w^z.cutoff = top)
    (m : Fin (binCount w top xi) → ℕ) (hanchor : SafeAnchor hw htop hxi C B K z m)
    (f : Fin (binCount w top xi) → Finset ℕ) (hf : f ∈ selections (globalBins w top xi) m)
    (i : Fin (binCount w top xi)) (hi : m i = 1) :
    Squarefree (selectionProduct (eraseSelection f i)) ∧ (pickedPrime f i).Prime ∧
      pickedPrime f i ∈ globalBins w top xi i ∧
      pickedPrime f i*selectionProduct (eraseSelection f i) ≤ Y := by
  obtain ⟨p,hp,hfi,_hfill⟩ := singleton_selection_recovery _ m i hi f hf
  have hpmem : pickedPrime f i ∈ globalBins w top xi i := by simpa [pickedPrime,hfi] using hp
  have hprime := (bin_prime_in_source (zero_lt_one.trans hw) htop hxi i hpmem).1
  have hsq := (erased_cofactor_arithmetic hw htop hxi m i (eraseSelection f i)
    (erase_selection_mem _ m f hf i)).1
  have hlen := full_box_total_length_lower hw htop hxi hC hcomp Y hY z hroot hs hz hg hclosed hcap m hanchor f hf
  rw [isolated_product _ m f hf i hi] at hlen
  refine ⟨hsq,hprime,hpmem,?_⟩
  exact product_le_Y_of_length w aStar hw ha Y _ hY
    (Nat.mul_pos hprime.pos (Nat.pos_of_ne_zero hsq.ne_zero)) hlen

end ErdosVarianceEligible


end Erdos970

end OAI
