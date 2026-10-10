import OAI.RepresentationTheory.KazhdanLusztig.OrdinaryR

namespace OAI

/-!
Canonical low-part construction, strict halfdegree, reciprocity and uniqueness; certification of the selected polynomials and interval ranks.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}

noncomputable local instance : DecidableEq W := Classical.decEq W

namespace CanonicalP

/-- The strict lower half of a polynomial, used in the KL recursion. -/
noncomputable def lowPart (d : ℕ) (p : ℤ[X]) : ℤ[X] :=
  ∑ n ∈ Finset.range ((d + 1) / 2), Polynomial.monomial n (p.coeff n)

@[simp] theorem coeff_lowPart (d : ℕ) (p : ℤ[X]) (n : ℕ) :
    (lowPart d p).coeff n = if 2 * n < d then p.coeff n else 0 := by
  classical
  simp only [lowPart, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  have he : n < (d + 1) / 2 ↔ 2 * n < d := by omega
  simp only [Finset.mem_range, he]

theorem lowPart_degree (d : ℕ) (p : ℤ[X]) (hd : 0 < d) :
    2 * (lowPart d p).natDegree < d := by
  have h : (lowPart d p).natDegree ≤ (d - 1) / 2 := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [coeff_lowPart, ite_eq_right (by omega)]
  omega

/-- Solve the anti-reciprocal defect with the required strict degree bound. -/
theorem lowPart_solution (d : ℕ) (p : ℤ[X]) (hanti : reflect d p = -p) :
    reflect d (-lowPart d p) = -lowPart d p + p := by
  apply Polynomial.ext
  intro n
  have hc := congrArg (fun f : ℤ[X] => f.coeff n) hanti
  simp only [Polynomial.coeff_reflect, Polynomial.coeff_neg] at hc
  simp only [Polynomial.coeff_reflect, Polynomial.coeff_neg, Polynomial.coeff_add,
    coeff_lowPart]
  by_cases hn : n ≤ d
  · rw [Polynomial.revAt_le hn] at hc ⊢
    by_cases hlow : 2 * n < d
    · rw [ite_eq_left hlow, ite_eq_right (by omega)]
      ring
    · rw [ite_eq_right hlow]
      by_cases hmid : 2 * n = d
      · have hm : d - n = n := by omega
        rw [hm, ite_eq_right hlow]
        rw [hm] at hc
        linarith
      · rw [ite_eq_left (by omega)]
        linarith
  · rw [Polynomial.revAt_eq_self_of_lt (by omega)] at hc ⊢
    rw [ite_eq_right (by omega)]
    linarith

/-- The standard lower-half KL recursion, on the actual Bruhat interval.
Its reciprocity will be proved from the genuine R-kernel, not stipulated. -/
noncomputable def polynomial (cs : CoxeterSystem M W) (x y : W) : ℤ[X] := by
  classical
  exact if BruhatLE cs x y then
    if x = y then 1 else
      -lowPart (rankDifference cs x y)
        (∑ z ∈ (properIntervalFinset cs x y).attach,
          OrdinaryR.polynomial cs x z.val * polynomial cs z.val y)
    else 0
termination_by rankDifference cs x y
decreasing_by
  have hz := (mem_properIntervalFinset cs x y z.val).mp z.property
  have hlt := length_lt_of_bruhat_ne cs hz.2.1 hz.2.2
  have hle := length_le_of_bruhat cs hz.1
  dsimp [rankDifference]
  omega

@[simp] theorem polynomial_diagonal (cs : CoxeterSystem M W) (x : W) :
    polynomial cs x x = 1 := by
  rw [polynomial]
  simp [bruhat_refl]

theorem polynomial_zero (cs : CoxeterSystem M W) (x y : W)
    (hxy : ¬BruhatLE cs x y) : polynomial cs x y = 0 := by
  rw [polynomial, ite_eq_right hxy]

noncomputable def defect (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  ∑ z ∈ properIntervalFinset cs x y, OrdinaryR.polynomial cs x z * polynomial cs z y

theorem polynomial_recursion (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) (hne : x ≠ y) :
    polynomial cs x y = -lowPart (rankDifference cs x y) (defect cs x y) := by
  rw [polynomial, ite_eq_left hxy, ite_eq_right hne]
  rw [Finset.sum_attach _ (fun z => OrdinaryR.polynomial cs x z * polynomial cs z y), defect]

theorem polynomial_strict_degree (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) (hne : x ≠ y) :
    2 * (polynomial cs x y).natDegree < rankDifference cs x y := by
  rw [polynomial_recursion cs x y hxy hne, Polynomial.natDegree_neg]
  apply lowPart_degree
  have := length_lt_of_bruhat_ne cs hxy hne
  dsimp [rankDifference]
  omega

theorem polynomial_degree (cs : CoxeterSystem M W) (x y : W) :
    (polynomial cs x y).natDegree ≤ rankDifference cs x y := by
  by_cases hxy : BruhatLE cs x y
  · by_cases hne : x = y
    · subst y
      simp
    · have := polynomial_strict_degree cs x y hxy hne
      omega
  · rw [polynomial_zero cs x y hxy]
    simp

theorem defect_full_sum (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) :
    defect cs x y = (∑ z ∈ lowerFinset cs y,
      OrdinaryR.polynomial cs x z * polynomial cs z y) - polynomial cs x y := by
  rw [defect, sum_proper_eq_sub cs x y hxy]
  · simp
  · intro z hz
    rw [OrdinaryR.polynomial_zero cs x z hz, zero_mul]

theorem reversed_kernel_on_lower (cs : CoxeterSystem M W) (x y t : W)
    (hty : BruhatLE cs t y) :
    ∑ z ∈ lowerFinset cs y,
      reflect (rankDifference cs x z) (OrdinaryR.polynomial cs x z) *
        OrdinaryR.polynomial cs z t = if x = t then 1 else 0 := by
  classical
  rw [← OrdinaryR.polynomial_kernel_reverse cs x t]
  symm
  apply Finset.sum_subset
  · intro z hz
    exact (mem_lowerFinset cs y z).mpr
      (bruhat_trans cs ((mem_lowerFinset cs t z).mp hz) hty)
  · intro z hz hnt
    have hzt : ¬BruhatLE cs z t := fun h => hnt ((mem_lowerFinset cs t z).mpr h)
    rw [OrdinaryR.polynomial_zero cs z t hzt, mul_zero]

theorem reversed_kernel_on_proper (cs : CoxeterSystem M W) (x y t : W)
    (hxy : BruhatLE cs x y) (hty : BruhatLE cs t y) :
    ∑ z ∈ properIntervalFinset cs x y,
      reflect (rankDifference cs x z) (OrdinaryR.polynomial cs x z) *
        OrdinaryR.polynomial cs z t =
      (if x = t then 1 else 0) - OrdinaryR.polynomial cs x t := by
  rw [sum_proper_eq_sub cs x y hxy]
  · rw [reversed_kernel_on_lower cs x y t hty]
    simp [rankDifference]
  · intro z hz
    rw [OrdinaryR.polynomial_zero cs x z hz, reflect_zero, zero_mul]

/-- The reciprocity equation is a theorem of the lower-half construction. -/
theorem polynomial_reciprocity (cs : CoxeterSystem M W) (x y : W)
    (hxy : BruhatLE cs x y) :
    reflect (rankDifference cs x y) (polynomial cs x y) =
      ∑ z ∈ lowerFinset cs y, OrdinaryR.polynomial cs x z * polynomial cs z y := by
  classical
  suffices ∀ n : ℕ, ∀ x y : W, rankDifference cs x y = n → BruhatLE cs x y →
      reflect (rankDifference cs x y) (polynomial cs x y) =
        ∑ z ∈ lowerFinset cs y, OrdinaryR.polynomial cs x z * polynomial cs z y by
    exact this _ x y rfl hxy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hn hxy
    by_cases hne : x = y
    · subst y
      rw [polynomial_diagonal]
      simp only [rankDifference, Nat.sub_self, Polynomial.reflect_one, pow_zero]
      symm
      rw [Finset.sum_eq_single x]
      · simp
      · intro z hz hzx
        have hnxz : ¬BruhatLE cs x z := fun hxz =>
          hzx (bruhat_antisymm cs ((mem_lowerFinset cs x z).mp hz) hxz)
        rw [OrdinaryR.polynomial_zero cs x z hnxz, zero_mul]
      · intro hmiss
        exact (hmiss ((mem_lowerFinset cs x x).mpr (bruhat_refl cs x))).elim
    · have hanti : reflect (rankDifference cs x y) (defect cs x y) = -defect cs x y := by
        rw [defect, reflect_finset_sum]
        have heq : ∀ z ∈ properIntervalFinset cs x y,
            reflect (rankDifference cs x y)
              (OrdinaryR.polynomial cs x z * polynomial cs z y) =
            reflect (rankDifference cs x z) (OrdinaryR.polynomial cs x z) *
              (∑ t ∈ lowerFinset cs y, OrdinaryR.polynomial cs z t * polynomial cs t y) := by
          intro z hz
          have hz := (mem_properIntervalFinset cs x y z).mp hz
          have hlt : rankDifference cs z y < n := by
            have := length_lt_of_bruhat_ne cs hz.2.1 hz.2.2
            have := length_le_of_bruhat cs hz.1
            dsimp [rankDifference] at hn ⊢
            omega
          rw [rankDifference_add cs hz.2.1 hz.1,
            reflect_mul _ _ (OrdinaryR.polynomial_degree cs x z) (polynomial_degree cs z y),
            ih _ hlt z y rfl hz.1]
        rw [Finset.sum_congr rfl heq]
        simp_rw [Finset.mul_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul]
        have hkernel : ∀ t ∈ lowerFinset cs y,
            (∑ z ∈ properIntervalFinset cs x y,
              reflect (rankDifference cs x z) (OrdinaryR.polynomial cs x z) *
                OrdinaryR.polynomial cs z t) * polynomial cs t y =
            ((if x = t then 1 else 0) - OrdinaryR.polynomial cs x t) * polynomial cs t y := by
          intro t ht
          rw [reversed_kernel_on_proper cs x y t hxy ((mem_lowerFinset cs y t).mp ht)]
        rw [Finset.sum_congr rfl hkernel]
        simp_rw [sub_mul, Finset.sum_sub_distrib]
        have hdelta : (∑ t ∈ lowerFinset cs y,
            (if x = t then (1 : ℤ[X]) else 0) * polynomial cs t y) = polynomial cs x y := by
          rw [Finset.sum_eq_single x]
          · simp
          · intro t ht htx
            simp [Ne.symm htx]
          · intro hmiss
            exact (hmiss ((mem_lowerFinset cs y x).mpr hxy)).elim
        rw [hdelta]
        change polynomial cs x y - (∑ z ∈ lowerFinset cs y,
          OrdinaryR.polynomial cs x z * polynomial cs z y) = -defect cs x y
        rw [defect_full_sum cs x y hxy]
        ring
      rw [polynomial_recursion cs x y hxy hne, lowPart_solution _ _ hanti]
      rw [← polynomial_recursion cs x y hxy hne, defect_full_sum cs x y hxy]
      ring

end CanonicalP

/-- Finitely supported interval sums agree with the lower-ideal sums used in
our construction; all incomparable summands are literally zero. -/
theorem normalized_interval_sum (cs : CoxeterSystem M W) (x y : W) :
    (∑ᶠ z : Interval cs x y,
      OrdinaryR.polynomial cs x z.val * CanonicalP.polynomial cs z.val y) =
    ∑ z ∈ lowerFinset cs y,
      OrdinaryR.polynomial cs x z * CanonicalP.polynomial cs z y := by
  classical
  let := interval_finite cs x y
  let : Fintype (Interval cs x y) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have hsum := Finset.sum_subtype (F := (inferInstance : Fintype (Interval cs x y)))
    ((lowerFinset cs y).filter (fun z => BruhatLE cs x z))
    (fun z => by simp only [Finset.mem_filter, mem_lowerFinset]; exact and_comm)
    (fun z => OrdinaryR.polynomial cs x z * CanonicalP.polynomial cs z y)
  refine hsum.symm.trans ?_
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro z hz hnot
  have hnxz : ¬BruhatLE cs x z := fun hxz => hnot (Finset.mem_filter.mpr ⟨hz, hxz⟩)
  rw [OrdinaryR.polynomial_zero cs x z hnxz, zero_mul]

/-- The selected polynomials really exist with the classical equal-parameter
normalization. This is a construction, not an extra hypothesis. -/
theorem constructed_normalizedKL (cs : CoxeterSystem M W) :
    NormalizedKL cs (OrdinaryR.polynomial cs, CanonicalP.polynomial cs) where
  R_diagonal := OrdinaryR.polynomial_diagonal cs
  R_zero := OrdinaryR.polynomial_zero cs
  R_recursion := OrdinaryR.polynomial_recursion cs
  P_diagonal := CanonicalP.polynomial_diagonal cs
  P_zero := CanonicalP.polynomial_zero cs
  P_degree := CanonicalP.polynomial_strict_degree cs
  reciprocity := by
    intro x y hxy
    rw [normalized_interval_sum]
    exact CanonicalP.polynomial_reciprocity cs x y hxy

theorem normalizedKL_existsUnique (cs : CoxeterSystem M W) :
    ∃! RP : PolynomialFamilies W, NormalizedKL cs RP := by
  refine ⟨(OrdinaryR.polynomial cs, CanonicalP.polynomial cs), constructed_normalizedKL cs, ?_⟩
  intro RP hRP
  exact normalizedKL_unique cs hRP (constructed_normalizedKL cs)

theorem klFamilies_spec (cs : CoxeterSystem M W) : NormalizedKL cs (klFamilies cs) := by
  exact Classical.epsilon_spec (normalizedKL_existsUnique cs).exists

theorem klFamilies_eq_constructed (cs : CoxeterSystem M W) :
    klFamilies cs = (OrdinaryR.polynomial cs, CanonicalP.polynomial cs) :=
  normalizedKL_unique cs (klFamilies_spec cs) (constructed_normalizedKL cs)

theorem klPolynomial_eq_constructed (cs : CoxeterSystem M W) (x y : W) :
    klPolynomial cs x y = CanonicalP.polynomial cs x y := by
  simp only [klPolynomial, klFamilies_eq_constructed]

theorem rPolynomial_eq_constructed (cs : CoxeterSystem M W) (x y : W) :
    rPolynomial cs x y = OrdinaryR.polynomial cs x y := by
  simp only [rPolynomial, klFamilies_eq_constructed]


/-- Every nontrivial Bruhat interval contains a first step of length one.
This is the grading fact needed to transport rank differences without labels. -/
theorem exists_bruhat_successor (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatLE cs x y) (hne : x ≠ y) :
    ∃ z, BruhatLE cs x z ∧ BruhatLE cs z y ∧ cs.length z = cs.length x + 1 := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x : W,
      BruhatLE cs x y → x ≠ y →
      ∃ z, BruhatLE cs x z ∧ BruhatLE cs z y ∧ cs.length z = cs.length x + 1 by
    exact this _ y rfl x hxy hne
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hyn x hxy hne
    have hy1 : y ≠ 1 := by
      intro hy
      subst y
      have hlen := length_le_of_bruhat cs hxy
      have hx : cs.length x = 0 := by simpa using hlen
      exact hne (cs.length_eq_zero_iff.mp hx)
    obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hy1
    change cs.length (cs.simple i * y) < cs.length y at hi
    have hylen : cs.length y = cs.length (cs.simple i * y) + 1 := by
      have := cs.length_simple_mul y i
      omega
    have hsyn : cs.length (cs.simple i * y) < n := by omega
    have hsyy : BruhatLE cs (cs.simple i * y) y := by
      simpa only [lowerSimple, ite_eq_left hi] using lowerSimple_le cs i y
    by_cases hxsy : BruhatLE cs x (cs.simple i * y)
    · by_cases hxeq : x = cs.simple i * y
      · exact ⟨y, hxy, bruhat_refl cs y, by simpa [hxeq] using hylen⟩
      · obtain ⟨z, hxz, hzsy, hzlen⟩ := ih _ hsyn _ rfl x hxsy hxeq
        exact ⟨z, hxz, bruhat_trans cs hzsy hsyy, hzlen⟩
    · have hxi : cs.length (cs.simple i * x) < cs.length x := by
        by_contra hnxi
        have hxim : cs.length x < cs.length (cs.simple i * x) := by
          have := cs.length_simple_mul x i
          omega
        exact hxsy (bruhat_lifting cs hxy i hxim hi).1
      have hxlen : cs.length x = cs.length (cs.simple i * x) + 1 := by
        have := cs.length_simple_mul x i
        omega
      have hsxsy : BruhatLE cs (cs.simple i * x) (cs.simple i * y) := by
        simpa only [lowerSimple, ite_eq_left hxi, ite_eq_left hi] using lowerSimple_mono cs i hxy
      have hne' : cs.simple i * x ≠ cs.simple i * y := fun he => hne (mul_left_cancel he)
      obtain ⟨w, hsxw, hwsy, hwlen⟩ := ih _ hsyn _ rfl _ hsxsy hne'
      have hux : upperSimple cs i (cs.simple i * x) = x := by
        rw [upperSimple_mul]
        simp only [upperSimple, ite_eq_left hxi]
      have huy : upperSimple cs i (cs.simple i * y) = y := by
        rw [upperSimple_mul]
        simp only [upperSimple, ite_eq_left hi]
      have hxz := upperSimple_mono cs i hsxw
      have hzy := upperSimple_mono cs i hwsy
      rw [hux] at hxz
      rw [huy] at hzy
      have hwlen' : cs.length w = cs.length x := by omega
      have hwi : ¬cs.length (cs.simple i * w) < cs.length w := by
        intro hwi
        simp only [upperSimple, ite_eq_left hwi] at hxz
        have hxw : x = w := by
          by_contra hnxw
          have := length_lt_of_bruhat_ne cs hxz hnxw
          omega
        exact hxsy (hxw ▸ hwsy)
      refine ⟨upperSimple cs i w, hxz, hzy, ?_⟩
      simp only [upperSimple, ite_eq_right hwi]
      have := cs.length_simple_mul w i
      omega


/-- An order embedding between Bruhat intervals cannot shorten rank. -/
theorem rankDifference_le_of_strictMono
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'}
    (f : Interval cs u b → Interval cs' u' b') (hf : StrictMono f)
    {x y : Interval cs u b} (hxy : x ≤ y) :
    rankDifference cs x.val y.val ≤ rankDifference cs' (f x).val (f y).val := by
  suffices ∀ n : ℕ, ∀ x y : Interval cs u b,
      rankDifference cs x.val y.val = n → x ≤ y →
      rankDifference cs x.val y.val ≤ rankDifference cs' (f x).val (f y).val by
    exact this _ x y rfl hxy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hn hxy
    by_cases heq : x = y
    · subst y
      simp [rankDifference]
    · have hne : x.val ≠ y.val := fun hv => heq (Subtype.ext hv)
      obtain ⟨z, hxz, hzy, hzlen⟩ := exists_bruhat_successor cs hxy hne
      let zI : Interval cs u b := ⟨z, bruhat_trans cs x.property.1 hxz,
        bruhat_trans cs hzy y.property.2⟩
      have hxylen := length_le_of_bruhat cs hxy
      have hzylen := length_le_of_bruhat cs hzy
      have hsmall : rankDifference cs zI.val y.val < n := by
        dsimp [zI, rankDifference] at hn ⊢
        omega
      have hsub := ih _ hsmall zI y rfl hzy
      have hxz' : x < zI := by
        refine (lt_iff_le_and_ne).mpr ⟨hxz, ?_⟩
        intro hx
        have hv : x.val = z := congrArg Subtype.val hx
        have := congrArg cs.length hv
        omega
      have hfxz := hf hxz'
      have hfxzlen : cs'.length (f x).val < cs'.length (f zI).val := by
        apply length_lt_of_bruhat_ne cs' hfxz.le
        intro hv
        exact hfxz.ne (Subtype.ext hv)
      have hfzyle := length_le_of_bruhat cs' (hf.monotone (show zI ≤ y from hzy))
      change cs.length y.val - cs.length z ≤
        cs'.length (f y).val - cs'.length (f zI).val at hsub
      change cs.length y.val - cs.length x.val ≤
        cs'.length (f y).val - cs'.length (f x).val
      omega

/-- Rank is intrinsic to the abstract interval poset, with neither root
labels nor simple generators preserved by the isomorphism. -/
theorem intervalIso_rankDifference
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'}
    (ι : Interval cs u b ≃o Interval cs' u' b')
    {x y : Interval cs u b} (hxy : x ≤ y) :
    rankDifference cs x.val y.val = rankDifference cs' (ι x).val (ι y).val := by
  apply Nat.le_antisymm
  · exact rankDifference_le_of_strictMono cs cs' ι ι.strictMono hxy
  · have h := rankDifference_le_of_strictMono cs' cs ι.symm ι.symm.strictMono (ι.monotone hxy)
    simpa only [OrderIso.symm_apply_apply] using h

/-- Named endpoints for an actual nonempty interval. -/
def intervalBottom (cs : CoxeterSystem M W) {u b : W} (hub : BruhatLE cs u b) :
    Interval cs u b := ⟨u, bruhat_refl cs u, hub⟩

def intervalTop (cs : CoxeterSystem M W) {u b : W} (hub : BruhatLE cs u b) :
    Interval cs u b := ⟨b, hub, bruhat_refl cs b⟩

theorem intervalIso_bottom
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
    (ι : Interval cs u b ≃o Interval cs' u' b') :
    ι (intervalBottom cs hub) = intervalBottom cs' hub' := by
  apply le_antisymm
  · have h : intervalBottom cs hub ≤ ι.symm (intervalBottom cs' hub') :=
      (ι.symm (intervalBottom cs' hub')).property.1
    simpa only [OrderIso.apply_symm_apply] using ι.monotone h
  · exact (ι (intervalBottom cs hub)).property.1

theorem intervalIso_top
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
    (ι : Interval cs u b ≃o Interval cs' u' b') :
    ι (intervalTop cs hub) = intervalTop cs' hub' := by
  apply le_antisymm
  · exact (ι (intervalTop cs hub)).property.2
  · have h : ι.symm (intervalTop cs' hub') ≤ intervalTop cs hub :=
      (ι.symm (intervalTop cs' hub')).property.2
    simpa only [OrderIso.apply_symm_apply] using ι.monotone h

theorem intervalIso_full_rankDifference
    {B' : Type u'} {W' : Type v'} [Group W'] {M' : CoxeterMatrix B'}
    (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (hub : BruhatLE cs u b) (hub' : BruhatLE cs' u' b')
    (ι : Interval cs u b ≃o Interval cs' u' b') :
    rankDifference cs u b = rankDifference cs' u' b' := by
  have h := intervalIso_rankDifference cs cs' ι
    (show intervalBottom cs hub ≤ intervalTop cs hub from hub)
  rw [intervalIso_bottom cs cs' hub hub' ι, intervalIso_top cs cs' hub hub' ι] at h
  exact h

end KLInvariance

end

end OAI
