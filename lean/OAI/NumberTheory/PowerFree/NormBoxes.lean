import OAI.NumberTheory.PowerFree.NormComponents

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators Classical

theorem norm_box_prime_count {n d D : ℕ} (hd : 5 ≤ d) (hd' : d ≤ 8) (hD : 0 < D)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (hωW : ∀ i, ω i ≤ 2/5)
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0) (hscale : ∀ i, (w i:ℝ) = 15*ω i)
    (M : NormBoxSystem n d D ω w) (Cbox : ℝ) (hCbox : 1 ≤ Cbox) (F e₀ : ℕ) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin n → ℤ),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = t)).card ≤ F) →
      (∀ c : Fin d → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
      (∀ z ∈ S, ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime → M.ideal ≤ I →
        affineDimension I ≤ d+1 → affineDegree I ≤ e₀ → (∀ z ∈ S, PointOn I z) →
      (S.card:ℝ) ≤ C*X^(997/1000:ℝ) := by
  classical
  choose K H hK hH halt using fun (e : ℕ) (i : Fin (d+1)) =>
    norm_component_alternatives (h := d+1-i.val) hd hd' (by omega) (by omega) hD
      ω hω hωW w hw hscale M Cbox (by linarith) F e (1/4000) (by norm_num)
  let c := fun e => ∑ i : Fin (d+1), H e i
  let Ke := fun e => 1+∑ i : Fin (d+1), K e i
  have hc : ∀ e, 0 ≤ c e := fun e => Finset.sum_nonneg (fun i _ => hH e i)
  have hKe : ∀ e, 1 ≤ Ke e := by
    intro e
    dsimp [Ke]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => zero_le_one.trans (hK e i)))
  have hci (e) (i : Fin (d+1)) : H e i ≤ c e := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => hH e j) (Finset.mem_univ i)
  have hKi (e) (i : Fin (d+1)) : K e i ≤ Ke e := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => zero_le_one.trans (hK e j)) (Finset.mem_univ i)
    dsimp [Ke]
    linarith
  let W : ℝ := 1+∑ j, ω j
  have hsum : 0 ≤ ∑ j, ω j := Finset.sum_nonneg (fun j _ => (hω j).le)
  have hW : 0 ≤ W := by dsimp [W]; linarith
  obtain ⟨C,Xcut,hC,hcount⟩ := physical_affine_count n (d+1) 0 e₀ (by omega)
    ω hω Cbox W hCbox hW (normBoxIncrement d) (normBoxStage d)
    (normBox_increment_nonneg d hd hd') (fun i => normBoxEnvelope_pos _ _)
    (normBox_prefix d hd hd') (1/1000) (by norm_num) c Ke hc hKe
  refine ⟨C,max (max 2 Cbox) Xcut,hC,fun X hX S hbox hnF haF hnonzero I hI hMI hdim hdeg hon => ?_⟩
  have hX2 : 2 < X := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hX
  have hCX : Cbox ≤ X := le_of_lt (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hX)
  have hXcut : Xcut < X := lt_of_le_of_lt (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hmax (j : Fin n) : ω j ≤ ∑ l, ω l := Finset.single_le_sum
    (fun l _ => (hω l).le) (Finset.mem_univ j)
  have hbound (z) (hz : z ∈ S) (j) : |(z j:ℝ)| ≤ X^W := by
    calc
      _ ≤ Cbox*X^(ω j) := hbox z hz j
      _ ≤ X*X^(∑ l, ω l) := mul_le_mul hCX
        (Real.rpow_le_rpow_of_exponent_le hX1 (hmax j)) (Real.rpow_nonneg hXp.le _) hXp.le
      _ = X^W := by dsimp [W]; rw [Real.rpow_add hXp,Real.rpow_one]
  let G : KernelGeometry n := ⟨S,X^W,Real.one_le_rpow hX1 hW,hbound⟩
  have hb := hcount X hXcut G le_rfl hbox I hI hdim hdeg hon
  have hcS := hb (by
    intro i e J hJ hIJ _ hJe hJdim hp
    let : J.IsPrime := hJ
    obtain ⟨z,hz,hzJ⟩ := hp
    have ha := M.quotient_left_nonzero J z hzJ (hnonzero z hz)
    have hh := halt e i X hX2.le S hbox hnF haF J hJ (hMI.trans hIJ) hJdim hJe ha
    rcases hh with hs | hHilb
    · left
      have hm := mul_le_mul_of_nonneg_right (hKi e i) (Real.rpow_nonneg hXp.le (1/4000))
      norm_num only [show (1/1000:ℝ)/4=1/4000 by norm_num]
      exact hs.trans hm
    · right
      intro T hT
      have hh := hHilb T hT
      have hm := mul_le_mul_of_nonneg_right (hci e i) (pow_nonneg (by linarith : 0 ≤ T) (d+1-i.val-1))
      change T^(d+1-i.val)/(((d+1-i.val).factorial:ℝ)*(normBoxEnvelope d (d+1-i.val))^(d+1-i.val))-
        c e*T^(d+1-i.val-1) ≤ _
      linarith only [hh,hm])
  exact hcS.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX1 (normBox_sum d hd hd')) hC.le)

theorem norm_box_prime_count_unrestricted {n d D : ℕ} (hd : 5 ≤ d) (hd' : d ≤ 8) (hD : 0 < D)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (hωW : ∀ i, ω i ≤ 2/5)
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0) (hscale : ∀ i, (w i:ℝ) = 15*ω i)
    (M : NormBoxSystem n d D ω w) (Cbox : ℝ) (hCbox : 1 ≤ Cbox) (F e₀ : ℕ) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin n → ℤ),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = t)).card ≤ F) →
      (∀ c : Fin d → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
      (∀ z ∈ S, ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) →
      ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)), I.IsPrime → M.ideal ≤ I →
        affineDegree I ≤ e₀ → (∀ z ∈ S, PointOn I z) →
      (S.card:ℝ) ≤ C*X^(997/1000:ℝ) := by
  obtain ⟨C,X₀,hC,hb⟩ := norm_box_prime_count hd hd' hD ω hω hωW w hw hscale M Cbox hCbox F e₀
  refine ⟨C+F+1,max 2 X₀,by positivity,fun X hX S hbox hqF haF hn I hI hMI hdeg hon => ?_⟩
  let : I.IsPrime := hI
  have hX1 : 1 ≤ X := by have := (le_max_left 2 X₀).trans_lt hX; linarith
  have hp : 1 ≤ X^(997/1000:ℝ) := Real.one_le_rpow hX1 (by norm_num)
  have hfilter : S.filter (PointOn I) = S := Finset.filter_true_of_mem hon
  by_cases hq : IsAlgebraic ℂ (Ideal.Quotient.mk I M.q)
  · have hcard := algebraic_polynomial_fibre_count S F M.q hqF I hq
    rw [hfilter] at hcard
    calc
      (S.card:ℝ) ≤ F := by exact_mod_cast hcard
      _ ≤ (C+F+1)*X^(997/1000:ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) F]
  · by_cases hs : S.Nonempty
    · obtain ⟨z,hz⟩ := hs
      have ha := M.quotient_left_nonzero I z (hon z hz) (hn z hz)
      have hdim := norm_dimension_le I (d-2) M.a M.b M.q M.θ ha (M.quotient_equations I hMI) M.generates hq
      have hh := hb X (lt_of_le_of_lt (le_max_right _ _) hX) S hbox hqF haF hn I hI hMI hdim hdeg hon
      exact hh.trans (mul_le_mul_of_nonneg_right (by have := Nat.cast_nonneg (α := ℝ) F; linarith : C ≤ C+F+1) (by positivity))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs,Finset.card_empty,Nat.cast_zero]
      positivity

theorem norm_box_count {n d D : ℕ} (hd : 5 ≤ d) (hd' : d ≤ 8) (hD : 0 < D)
    (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i) (hωW : ∀ i, ω i ≤ 2/5)
    (w : Fin n → ℕ) (hw : ∀ i, w i ≠ 0) (hscale : ∀ i, (w i:ℝ) = 15*ω i)
    (M : NormBoxSystem n d D ω w) (Cbox : ℝ) (hCbox : 1 ≤ Cbox) (F : ℕ) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin n → ℤ),
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ t : ℂ, (S.filter (fun z => MvPolynomial.aeval (fun j => (z j:ℂ)) M.q = t)).card ≤ F) →
      (∀ c : Fin d → ℤ, (S.filter (fun z => ∀ i, z (M.x i) = c i)).card ≤ F) →
      (∀ z ∈ S, ∀ i, MvPolynomial.aeval (fun j => (z j:ℂ)) (M.a i) ≠ 0) →
      (∀ z ∈ S, PointOn M.ideal z) →
      (S.card:ℝ) ≤ C*X^(997/1000:ℝ) := by
  classical
  let Q := (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) ℂ) M.ideal).toFinset
  let E : ℕ := ∑ I ∈ Q, ⌈affineDegree I⌉₊
  have hQ (I) (hI : I ∈ Q) : I ∈ M.ideal.minimalPrimes := (Set.Finite.mem_toFinset _).mp hI
  have hE (I) (hI : I ∈ Q) : affineDegree I ≤ E := by
    have hsum : ⌈affineDegree I⌉₊ ≤ E := Finset.single_le_sum (f := fun J => ⌈affineDegree J⌉₊) (fun _ _ => Nat.zero_le _) hI
    exact (Nat.le_ceil _).trans (by exact_mod_cast hsum)
  obtain ⟨C,X₀,hC,hb⟩ := norm_box_prime_count_unrestricted hd hd' hD ω hω hωW w hw hscale M Cbox hCbox F E
  refine ⟨(Q.card+1)*C,max 2 X₀,by positivity,fun X hX S hbox hqF haF hn hon => ?_⟩
  have hXpos : 0 ≤ X := by have := (le_max_left 2 X₀).trans_lt hX; linarith
  have hX₀ : X₀ < X := (le_max_right _ _).trans_lt hX
  have cover : S ⊆ Q.biUnion (fun I => S.filter (PointOn I)) := by
    intro z hz
    obtain ⟨I,hI,hzI⟩ := point_on_minimal_component M.ideal (fun j => (z j:ℂ)) (hon z hz)
    exact Finset.mem_biUnion.mpr ⟨I,(Set.Finite.mem_toFinset _).mpr hI,Finset.mem_filter.mpr ⟨hz,hzI⟩⟩
  have hbound (I) (hI : I ∈ Q) : ((S.filter (PointOn I)).card:ℝ) ≤ C*X^(997/1000:ℝ) := by
    apply hb X hX₀ (S.filter (PointOn I))
    · intro z hz; exact hbox z (Finset.mem_filter.mp hz).1
    · intro t
      apply (Finset.card_le_card ?_).trans (hqF t)
      exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    · intro c
      apply (Finset.card_le_card ?_).trans (haF c)
      exact Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    · intro z hz; exact hn z (Finset.mem_filter.mp hz).1
    · exact (hQ I hI).isPrime
    · exact (hQ I hI).1.2
    · exact hE I hI
    · intro z hz; exact (Finset.mem_filter.mp hz).2
  calc
    (S.card:ℝ) ≤ (∑ I ∈ Q, (S.filter (PointOn I)).card : ℕ) := by
      exact_mod_cast (Finset.card_le_card cover).trans (Finset.card_biUnion_le)
    _ = ∑ I ∈ Q, ((S.filter (PointOn I)).card:ℝ) := by simp
    _ ≤ ∑ I ∈ Q, C*X^(997/1000:ℝ) := Finset.sum_le_sum hbound
    _ = Q.card*(C*X^(997/1000:ℝ)) := by simp
    _ ≤ ((Q.card+1)*C)*X^(997/1000:ℝ) := by nlinarith [Real.rpow_nonneg (x := X) hXpos (997/1000:ℝ)]

end

section
open Polynomial NumberField

theorem scaleRoots_irreducible {K : Type*} [Field K] (f : Polynomial K)
    (hf : Irreducible f) (r : K) (hr : r ≠ 0) :
    Irreducible (f.scaleRoots r) := by
  have hu (g : Polynomial K) : IsUnit (g.scaleRoots r) ↔ IsUnit g := by
    rw [Polynomial.isUnit_iff_degree_eq_zero,Polynomial.isUnit_iff_degree_eq_zero,
      Polynomial.degree_scaleRoots]
  refine ⟨fun h => hf.not_isUnit (hu f |>.mp h),?_⟩
  intro a b he
  have hback : f = a.scaleRoots r⁻¹ * b.scaleRoots r⁻¹ := by
    rw [← mul_scaleRoots_of_noZeroDivisors,← he,← scaleRoots_mul, mul_inv_cancel₀ hr,
      scaleRoots_one]
  rcases hf.isUnit_or_isUnit hback with ha | hb
  · left
    simpa only [Polynomial.isUnit_iff_degree_eq_zero,degree_scaleRoots] using ha
  · right
    simpa only [Polynomial.isUnit_iff_degree_eq_zero,degree_scaleRoots] using hb

theorem integralNormalization_irreducible (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    Irreducible (f.integralNormalization.map (Int.castRingHom ℚ)) := by
  have hf0 : f ≠ 0 := fun h => hf.ne_zero (by simp [h])
  have hc : (f.leadingCoeff : ℚ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hf0
  have hs := scaleRoots_irreducible (f.map (Int.castRingHom ℚ)) hf (f.leadingCoeff : ℚ) hc
  have he := congrArg (Polynomial.map (Int.castRingHom ℚ))
    (integralNormalization_mul_C_leadingCoeff f)
  rw [Polynomial.map_mul,Polynomial.map_C,map_scaleRoots f f.leadingCoeff _ hc] at he
  change f.integralNormalization.map (Int.castRingHom ℚ) * C (f.leadingCoeff : ℚ) =
    (f.map (Int.castRingHom ℚ)).scaleRoots (f.leadingCoeff : ℚ) at he
  rw [← he] at hs
  exact (irreducible_mul_isUnit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))).mp hs

theorem minpoly_integral_normalization {K : Type*} [Field K] [NumberField K]
    (f : Polynomial ℤ) (hf : Irreducible (f.map (Int.castRingHom ℚ)))
    (hd : 1 ≤ f.natDegree) (θ : K) (hθ : f.aeval θ = 0)
    (t : 𝓞 K) (ht : (t : K) = (f.leadingCoeff : K) * θ) :
    minpoly ℤ t = f.integralNormalization := by
  have hf0 : f ≠ 0 := fun h => hf.ne_zero (by simp [h])
  have he : (f.integralNormalization.map (Int.castRingHom ℚ)).aeval (t : K) = 0 := by
    rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, aeval_map_algebraMap,
      aeval_def, ht]
    change f.integralNormalization.eval₂ (algebraMap ℤ K)
      ((algebraMap ℤ K) f.leadingCoeff * θ) = 0
    rw [integralNormalization_eval₂_leadingCoeff_mul hd]
    change (f.leadingCoeff : K) ^ (f.natDegree - 1) * f.aeval θ = 0
    rw [hθ, mul_zero]
  have hm := minpoly.eq_of_irreducible_of_monic (integralNormalization_irreducible f hf)
    he ((monic_integralNormalization hf0).map (Int.castRingHom ℚ))
  have htint : IsIntegral ℤ t := t.isIntegral
  have hm' := minpoly.isIntegrallyClosed_eq_field_fractions ℚ K htint
  apply map_injective (Int.castRingHom ℚ) (Int.cast_injective)
  change (minpoly ℤ t).map (algebraMap ℤ ℚ) = _
  rw [← hm']
  change minpoly ℚ (t : K) = _
  exact hm.symm

open Polynomial NumberField
open scoped nonZeroDivisors

theorem exponent_ne_zero_of_powerBasis {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (pb : PowerBasis ℚ K) (hgen : pb.gen = (θ : K)) :
    RingOfIntegers.exponent θ ≠ 0 := by
  classical
  let b := RingOfIntegers.basis K
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 K)
  let A := Algebra.adjoin ℤ {θ}
  obtain ⟨m, hm⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ)
    (fun ij : ι × Fin pb.dim => pb.basis.repr ((b ij.1 : 𝓞 K) : K) ij.2)
  choose a ha using hm
  have hmb (i : ι) : (m : ℤ) • b i ∈ A := by
    have he : (m : ℤ) • ((b i : 𝓞 K) : K) =
        ∑ j : Fin pb.dim, (a (i,j) : ℚ) • pb.basis j := by
      conv_lhs => rw [← pb.basis.sum_repr ((b i : 𝓞 K) : K)]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← smul_assoc, ← ha (i,j)]
      rfl
    have he' : (m : ℤ) • b i = ∑ j : Fin pb.dim, a (i,j) • θ ^ (j : ℕ) := by
      apply RingOfIntegers.ext
      simpa [pb.basis_eq_pow,hgen, Algebra.smul_def] using he
    rw [he']
    apply A.sum_mem
    intro j _
    exact A.smul_mem (A.pow_mem (Algebra.subset_adjoin (Set.mem_singleton θ)) _) _
  have hz (z : 𝓞 K) : (m : ℤ) • z ∈ A := by
    rw [← b.sum_repr z]
    rw [Finset.smul_sum]
    apply A.sum_mem
    intro i _
    rw [smul_comm]
    exact A.smul_mem (hmb i) _
  have hmc : (m : ℤ) ∈ Ideal.under ℤ (conductor ℤ θ) := by
    change ((m : ℤ) : 𝓞 K) ∈ conductor ℤ θ
    rw [mem_conductor_iff]
    intro z
    simpa [Algebra.smul_def] using hz z
  intro hzero
  have he := Int.ideal_span_absNorm_eq_self (Ideal.under ℤ (conductor ℤ θ))
  change Ideal.span {((RingOfIntegers.exponent θ : ℕ) : ℤ)} = _ at he
  rw [hzero, Nat.cast_zero, Ideal.span_singleton_zero] at he
  rw [← he, Ideal.mem_bot] at hmc
  exact nonZeroDivisors.coe_ne_zero m hmc

end

open Polynomial NumberField

theorem simple_root_ideal_power {R : Type*} [CommRing R] [IsDedekindDomain R]
    (P : Ideal R) [P.IsPrime] (hP : P ≠ ⊥) (f : Polynomial R)
    (a θ : R) (k : ℕ) (hθ : f.eval θ = 0) (haθ : a - θ ∈ P)
    (hd : f.derivative.eval a ∉ P) (hf : f.eval a ∈ P ^ k) : a - θ ∈ P ^ k := by
  let g := f /ₘ (X - C θ)
  have hfac : f.eval a = (a - θ) * g.eval a := by
    have h := congrArg (Polynomial.eval a)
      (Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic f θ)
    simpa only [eval_mul, eval_sub, eval_X, eval_C, modByMonic_X_sub_C_eq_C_eval,
      hθ, sub_zero] using h.symm
  have hdiag : g.eval θ = f.derivative.eval θ := by
    have h := congrArg (Polynomial.eval θ)
      (Polynomial.divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative f θ)
    simpa only [eval_add, eval_mul, eval_sub, eval_X, eval_C,
      sub_self, zero_mul, add_zero] using h
  have hsub (q : Polynomial R) : q.eval a - q.eval θ ∈ P := by
    obtain ⟨t, ht⟩ := Polynomial.sub_dvd_eval_sub a θ q
    rw [ht]
    exact P.mul_mem_right t haθ
  have hg : g.eval a ∉ P := by
    intro hga
    have hgθ := P.sub_mem hga (hsub g)
    have hh : f.derivative.eval θ ∈ P := by simpa [hdiag] using hgθ
    apply hd
    convert P.add_mem (hsub f.derivative) hh using 1
    ring
  cases k with
  | zero => simp
  | succ k =>
    by_contra hx
    apply hg
    exact Ideal.mem_prime_of_mul_mem_pow hP hx (by rwa [← hfac])

theorem root_prime_ideal {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (a : ℤ) (p k : ℕ) (hp : p.Prime) (hk : 0 < k)
    (hc : ¬ p ∣ RingOfIntegers.exponent θ)
    (hd : ¬ (p : ℤ) ∣ (minpoly ℤ θ).derivative.eval a)
    (hf : (p : ℤ) ^ k ∣ (minpoly ℤ θ).eval a) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ P.absNorm = p ∧
      (a : 𝓞 K) - θ ∈ P ^ k := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let Q : Polynomial ℤ := X - C a
  have hf1 : (p : ℤ) ∣ (minpoly ℤ θ).eval a :=
    dvd_trans (dvd_pow_self (p : ℤ) hk.ne') hf
  have hQ : Q.map (Int.castRingHom (ZMod p)) ∈ RingOfIntegers.monicFactorsMod θ p := by
    change Q.map _ ∈ (UniqueFactorizationMonoid.normalizedFactors _).toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
      (Polynomial.map_monic_ne_zero (minpoly.monic θ.isIntegral))]
    simp only [Q, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    refine ⟨irreducible_X_sub_C _, monic_X_sub_C _, ?_⟩
    rw [Polynomial.dvd_iff_isRoot, IsRoot.def, eval_map, eval₂_at_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hf1
  let P' := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hc).symm ⟨_, hQ⟩
  let P : Ideal (𝓞 K) := P'
  let : P.IsPrime := P'.property.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := P'.property.2
  let : P.IsMaximal := Ideal.primesOver.isMaximal P'
  have hspan : P = Ideal.span {(p : 𝓞 K), θ - (a : 𝓞 K)} := by
    dsimp [P, P']
    rw [NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hc hQ]
    simp [Q]
  have hpP : (p : 𝓞 K) ∈ P := by rw [hspan]; exact Ideal.subset_span (Set.mem_insert _ _)
  have hP0 : P ≠ ⊥ := by
    intro h
    have : (p : 𝓞 K) = 0 := by simpa [h] using hpP
    exact (Nat.cast_ne_zero.mpr hp.ne_zero) this
  have hab : (a : 𝓞 K) - θ ∈ P := by
    have h : θ - (a : 𝓞 K) ∈ P := by rw [hspan]; exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    simpa only [neg_sub] using P.neg_mem h
  have hn : P.absNorm = p := by
    have hdeg := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply hc hQ
    have hdeg' : P.inertiaDeg ℤ = 1 := by
      simpa only [P, P', Q, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, natDegree_X_sub_C] using hdeg
    simpa only [hdeg', pow_one, Int.natAbs_natCast] using
      (Ideal.natAbs_pow_inertiaDeg (p : ℤ) P).symm
  refine ⟨P, inferInstance, hP0, hn, ?_⟩
  let f := (minpoly ℤ θ).map (Int.castRingHom (𝓞 K))
  apply simple_root_ideal_power P hP0 f (a : 𝓞 K) θ k
  · rw [show f = (minpoly ℤ θ).map (algebraMap ℤ (𝓞 K)) from rfl, eval_map]
    exact minpoly.aeval ℤ θ
  · exact hab
  · intro h
    have h' : (minpoly ℤ θ).derivative.eval a ∈ Ideal.span {(p : ℤ)} := by
      apply (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) _).mpr
      simpa [f, derivative_map, eval_map, eval₂_at_apply] using h
    exact hd (Ideal.mem_span_singleton.mp h')
  · obtain ⟨t, ht⟩ := hf
    have he : f.eval (a : 𝓞 K) = (p : 𝓞 K) ^ k * (t : 𝓞 K) := by
      dsimp [f]
      rw [eval_map]
      change (minpoly ℤ θ).eval₂ (Int.castRingHom (𝓞 K)) ((Int.castRingHom (𝓞 K)) a) = _
      rw [eval₂_at_apply]
      change (((minpoly ℤ θ).eval a : ℤ) : 𝓞 K) = _
      rw [ht, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
    rw [he]
    exact (P ^ k).mul_mem_right _ (Ideal.pow_mem_pow hpP k)

end QuarticPowerFree

end OAI
