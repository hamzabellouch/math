import OAI.Algebra.Determinantal.RegularSections

namespace OAI

namespace PermanentBorder.SliceParameters

open MvPolynomial

lemma homogeneous_aeval_scale {K L σ : Type*} [CommSemiring K] [CommSemiring L]
    [Algebra K L] {f : MvPolynomial σ K} {r : ℕ} (hf : f.IsHomogeneous r)
    (a : L) (x : σ → L) :
    aeval (fun i => a * x i) f = a^r * aeval x f := by
  classical
  conv_lhs => rw [← f.support_sum_monomial_coeff]
  conv_rhs => rw [← f.support_sum_monomial_coeff]
  simp only [map_sum, aeval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [hf.degree_eq_sum_deg_support hs]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

end PermanentBorder.SliceParameters

namespace PermanentBorder.CI
open MvPolynomial Topology
open scoped Topology Classical
variable {ι : Type*} [Fintype ι]

lemma normalized_eval_zero_iff (H : ι → MvPolynomial (Option ι) ℂ) (l y : Option ι → ℂ) :
    (fun i => eval y (normalized H l i)) = 0 ↔
      (∀ i, eval y (H i) = 0) ∧ eval y (linear l) = 1 := by
  constructor
  · intro h
    constructor
    · intro i; exact congrFun h (some i)
    · have hh := congrFun h none
      simpa [normalized, sub_eq_zero] using hh
  · rintro ⟨hH,hl⟩
    funext i
    cases i <;> simp [normalized, hH, hl]

lemma good_derivative_invertible (H : ι → MvPolynomial (Option ι) ℂ)
    (l y : Option ι → ℂ) (h : Good H l)
    (hy : (fun i => eval y (normalized H l i)) = 0) :
    (fderiv ℂ (fun y i => eval y (normalized H l i)) y).IsInvertible := by
  have hh := (normalized_eval_zero_iff H l y).mp hy
  have hn : y ≠ 0 := by
    intro hz
    have := hh.2
    rw [eval_linear] at this
    simp [hz] at this
  have hd := (h y hn hh.1).2
  have hj : jacobian (normalized H l) y = (square H l).map (eval y) := by
    ext i j
    exact congrArg (eval y) (pderiv_normalized H l i j)
  apply system_fderiv_invertible
  rwa [hj]

lemma fderiv_parameter_slice {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {F : ℂ × V → V} (hF : ContDiff ℂ 1 F) (t : ℂ) (x : V) :
    fderiv ℂ (fun x => F (t,x)) x =
      fderiv ℂ F (t,x) ∘L ContinuousLinearMap.inr ℂ ℂ V := by
  have hi : HasFDerivAt (fun x : V => (t,x)) (ContinuousLinearMap.inr ℂ ℂ V) x := by
    simpa [ContinuousLinearMap.inr] using
      (hasFDerivAt_const (𝕜 := ℂ) t x).prodMk (hasFDerivAt_id (𝕜 := ℂ) x)
  exact ((hF.differentiable (by decide) (t,x)).hasFDerivAt.comp x hi).fderiv

noncomputable def linearEval (l : Option ι → ℂ) : (Option ι → ℂ) →ₗ[ℂ] ℂ :=
  { toFun := fun y => eval y (linear l)
    map_add' := by intro x y; simp [eval_linear, mul_add, Finset.sum_add_distrib]
    map_smul' := by intro c y; simp [eval_linear, Finset.mul_sum, mul_left_comm, mul_add] }

@[simp] lemma linearEval_apply (l y : Option ι → ℂ) :
    linearEval l y = eval y (linear l) := by
  rfl

abbrev FamilyRoots (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (s : Set ℂ) :=
  {z : s × (Option ι → ℂ) // (∀ i, eval z.2 (H z.1.val i) = 0) ∧
    eval z.2 (linear (l z.1.val)) = 1}

def familyProjection (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (s : Set ℂ) : FamilyRoots H l s → s := fun z => z.val.1

lemma normalized_family_proper (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (e : ι → ℕ)
    (hh : ∀ t i, (H t i).IsHomogeneous (e i))
    (hcH : ∀ i, Continuous (fun z : ℂ × (Option ι → ℂ) => eval z.2 (H z.1 i)))
    (hcL : Continuous (fun z : ℂ × (Option ι → ℂ) => eval z.2 (linear (l z.1))))
    (s : Set ℂ) (hg : ∀ t ∈ s, Good (H t) (l t)) :
    IsProperMap (familyProjection H l s) := by
  let V := Option ι → ℂ
  have hval : Continuous (fun z : s × V => (z.1.val,z.2) : s × V → ℂ × V) := by fun_prop
  have hc (i : ι) : Continuous (fun z : s × V => eval z.2 (H z.1.val i)) :=
    Continuous.comp (f := fun z : s × V => (z.1.val,z.2)) (hcH i) hval
  have hci (i : ι) : IsClosed {z : s × V | eval z.2 (H z.1.val i) = 0} :=
    isClosed_eq (hc i) continuous_const
  have hclosed : IsClosed {z : s × V | ∀ i, eval z.2 (H z.1.val i) = 0} := by
    simpa only [Set.ofPred_forall] using isClosed_iInter hci
  have hL : Continuous (fun z : s × V => linearEval (l z.1.val) z.2) := by
    simp only [linearEval_apply]
    exact Continuous.comp (f := fun z : s × V => (z.1.val,z.2)) hcL hval
  apply PermanentBorder.Polar.homogeneous_normalized_proper
    (T := s) (V := V) (fun t y => ∀ i, eval y (H t.val i) = 0) hclosed
    (L := fun t => linearEval (l t.val)) (hL := hL)
  · intro t y c hy i
    have hs := PermanentBorder.SliceParameters.homogeneous_aeval_scale (hh t.val i) c y
    have he : eval (c • y) (H t.val i) = c ^ e i * eval y (H t.val i) := by
      change eval (fun j => c * y j) (H t.val i) = _
      simpa [aeval_def] using hs
    rw [he, hy i, mul_zero]
  · intro t y hy hz
    by_contra hn
    exact (hg t.val t.property y hn hy).1 hz

lemma normalized_family_local (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ)
    (hc : ContDiff ℂ 1 (fun z : ℂ × (Option ι → ℂ) =>
      fun i => eval z.2 (normalized (H z.1) (l z.1) i)))
    (s : Set ℂ) (hg : ∀ t ∈ s, Good (H t) (l t)) :
    IsLocalHomeomorph (familyProjection H l s) := by
  let V := Option ι → ℂ
  let S : ℂ × V → V := fun z i => eval z.2 (normalized (H z.1) (l z.1) i)
  let q : {z : ℂ × V // S z = 0} → ℂ := fun z => z.val.1
  let W := q ⁻¹' s
  let E : FamilyRoots H l s ≃ₜ W :=
    { toFun := fun z => ⟨⟨(z.val.1.val,z.val.2),
        (normalized_eval_zero_iff _ _ _).mpr z.property⟩,z.val.1.property⟩
      invFun := fun z => ⟨(⟨z.val.val.1,z.property⟩,z.val.val.2),
        (normalized_eval_zero_iff _ _ _).mp z.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hq : IsLocalHomeomorph (s.restrictPreimage q) := by
    apply PermanentBorder.Polar.implicit_zero_projection_on (𝕜 := ℂ) S s
    intro z hz
    refine ⟨fderiv ℂ S z.val, hc.hasStrictFDerivAt (by decide), ?_⟩
    rw [← fderiv_parameter_slice hc z.val.1 z.val.2]
    exact good_derivative_invertible (H z.val.1) (l z.val.1) z.val.2
      (hg z.val.1 hz) z.property
  exact hq.comp E.isLocalHomeomorph

noncomputable def familyFiberEquiv (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (s : Set ℂ) (t : s) :
    (familyProjection H l s ⁻¹' {t}) ≃ Roots (H t.val) (l t.val) where
  toFun z := ⟨z.val.val.2, by
    have ht : z.val.val.1 = t := z.property
    simpa only [← ht] using z.val.property⟩
  invFun y := ⟨⟨(t,y.val),y.property⟩,rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext z.property.symm rfl
  right_inv _ := rfl

theorem normalized_count_constant (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (e : ι → ℕ)
    (hh : ∀ t i, (H t i).IsHomogeneous (e i))
    (hc : ContDiff ℂ 1 (fun z : ℂ × (Option ι → ℂ) =>
      fun i => eval z.2 (normalized (H z.1) (l z.1) i)))
    (s : Set ℂ) [PreconnectedSpace s] (hg : ∀ t ∈ s, Good (H t) (l t))
    (a b : s) :
    Nat.card (Roots (H a.val) (l a.val)) = Nat.card (Roots (H b.val) (l b.val)) := by
  have hcH (i : ι) : Continuous (fun z : ℂ × (Option ι → ℂ) => eval z.2 (H z.1 i)) :=
    (continuous_apply (some i)).comp hc.continuous
  have hcL : Continuous (fun z : ℂ × (Option ι → ℂ) => eval z.2 (linear (l z.1))) := by
    have hcont : Continuous (fun z : ℂ × (Option ι → ℂ) =>
        eval z.2 (normalized (H z.1) (l z.1) none) + (1 : ℂ)) :=
      ((continuous_apply none).comp hc.continuous).add continuous_const
    convert! hcont using 1
    funext z
    simp [normalized]
  rw [← Nat.card_congr (familyFiberEquiv H l s a), ← Nat.card_congr (familyFiberEquiv H l s b)]
  exact PermanentBorder.Polar.proper_localHomeomorph_card
    (normalized_family_proper H l e hh hcH hcL s hg) (normalized_family_local H l hc s hg) a b

end PermanentBorder.CI

namespace PermanentBorder.SliceParameters
open MvPolynomial

lemma variable_power_certificate {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Finite σ] (I : Ideal (MvPolynomial σ K))
    (hz : ∀ y ∈ zeroLocus L I, y = 0) (j : σ) :
    ∃ n : ℕ, (X j : MvPolynomial σ K)^n ∈ I := by
  have hx : (X j : MvPolynomial σ K) ∈ vanishingIdeal K (zeroLocus L I) := by
    intro y hy
    rw [hz y hy]
    simp
  rw [vanishingIdeal_zeroLocus_eq_radical] at hx
  exact hx

lemma monomial_mem_of_variable_powers {K σ : Type*} [CommSemiring K] [Fintype σ]
    (I : Ideal (MvPolynomial σ K)) (N : σ → ℕ)
    (hN : ∀ j, (X j : MvPolynomial σ K)^(N j) ∈ I)
    (s : σ →₀ ℕ) (c : K) (hs : (∑ j, N j) < s.degree) : monomial s c ∈ I := by
  classical
  obtain ⟨j,hj⟩ : ∃ j, N j ≤ s j := by
    by_contra h
    have hle (j : σ) : s j ≤ N j := le_of_lt (not_le.mp (not_exists.mp h j))
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hle j)
    have hd : s.degree = ∑ j, s j := by
      exact Finsupp.sum_fintype s (fun _ n => n) (fun _ => rfl)
    rw [hd] at hs
    exact (not_le_of_gt hs) hh
  have he : Finsupp.single j (N j) + (s - Finsupp.single j (N j)) = s :=
    add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr hj)
  rw [← he, monomial_single_add]
  exact I.mul_mem_right _ (hN j)

theorem homogeneous_piece_certificate {K L σ : Type*} [Field K] [Field L] [Algebra K L]
    [IsAlgClosed L] [Fintype σ] (I : Ideal (MvPolynomial σ K))
    (hz : ∀ y ∈ zeroLocus L I, y = 0) :
    ∃ D : ℕ, ∀ f : MvPolynomial σ K, f.IsHomogeneous D → f ∈ I := by
  classical
  choose N hN using variable_power_certificate I hz
  refine ⟨(∑ j, N j)+1, ?_⟩
  intro f hf
  rw [← f.support_sum_monomial_coeff]
  apply I.sum_mem
  intro s hs
  apply monomial_mem_of_variable_powers I N hN
  have hd : s.degree = (∑ j, N j)+1 := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf (mem_support_iff.mp hs)
  omega

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

abbrev DegreeIndex (σ : Type*) (d : ℤ) := {s : σ →₀ ℕ // (s.degree : ℤ) = d}

instance degreeIndex_finite {σ : Type*} [Finite σ] (d : ℤ) : Finite (DegreeIndex σ d) := by
  apply Set.Finite.to_subtype
  apply (Finsupp.finite_of_degree_le d.toNat).subset
  intro s hs
  change s.degree ≤ d.toNat
  rw [← hs]
  simp

noncomputable instance degreeIndex_fintype {σ : Type*} [Finite σ] (d : ℤ) :
    Fintype (DegreeIndex σ d) := Fintype.ofFinite _

lemma intWeight_degree {σ : Type*} (s : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) s = (s.degree : ℤ) := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum]

lemma homogeneous_intWeight {K σ : Type*} [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ} (hf : f.IsHomogeneous d) :
    f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d := by
  intro s hs
  rw [intWeight_degree]
  have h : s.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hf hs
  rw [h]

lemma intWeight_homogeneous {K σ : Type*} [CommSemiring K]
    {f : MvPolynomial σ K} {d : ℕ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d) :
    f.IsHomogeneous d := by
  intro s hs
  change Finsupp.weight (fun _ : σ => (1 : ℕ)) s = d
  rw [← Finsupp.degree_eq_weight_one]
  exact_mod_cast (intWeight_degree s ▸ hf hs)

lemma homogeneous_sum_degree {K σ : Type*} [CommSemiring K] [Finite σ]
    {f : MvPolynomial σ K} {d : ℤ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d) :
    f = ∑ s : DegreeIndex σ d, monomial s.val (f.coeff s.val) := by
  classical
  ext t
  rw [coeff_sum]
  by_cases ht : (t.degree : ℤ) = d
  · rw [Finset.sum_eq_single (⟨t,ht⟩ : DegreeIndex σ d)]
    · simp
    · intro s _ hs
      have he : s.val ≠ t := fun h => hs (Subtype.ext h)
      simp [coeff_monomial, he]
    · simp
  · have hz : f.coeff t = 0 := by
      by_contra hn
      exact ht (intWeight_degree t ▸ hf hn)
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro s _
    have he : s.val ≠ t := fun h => ht (h ▸ s.property)
    simp [coeff_monomial, he]

lemma coeff_sum_degree {K σ : Type*} [CommSemiring K] [Finite σ]
    (d : ℤ) (b : DegreeIndex σ d → K) (s : DegreeIndex σ d) :
    (∑ t : DegreeIndex σ d, monomial t.val (b t)).coeff s.val = b s := by
  classical
  rw [coeff_sum, Finset.sum_eq_single s]
  · simp
  · intro t _ ht
    have he : t.val ≠ s.val := fun h => ht (Subtype.ext h)
    simp [coeff_monomial, he]
  · simp

lemma sum_degree_homogeneous {K σ : Type*} [CommSemiring K] [Finite σ]
    (d : ℤ) (b : DegreeIndex σ d → K) :
    (∑ t : DegreeIndex σ d, monomial t.val (b t)).IsWeightedHomogeneous
      (fun _ : σ => (1 : ℤ)) d := by
  apply IsWeightedHomogeneous.sum
  intro t _
  exact isWeightedHomogeneous_monomial _ _ _ ((intWeight_degree t.val).trans t.property)

lemma homogeneous_ext_degree {K σ : Type*} [CommSemiring K] [Finite σ]
    {f g : MvPolynomial σ K} {d : ℤ}
    (hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d)
    (hg : g.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) d)
    (h : ∀ s : DegreeIndex σ d, f.coeff s.val = g.coeff s.val) : f = g := by
  rw [homogeneous_sum_degree hf, homogeneous_sum_degree hg]
  exact Finset.sum_congr rfl (fun s _ => congrArg (monomial s.val) (h s))

end PermanentBorder.SliceParameters

namespace PermanentBorder.SliceParameters
open MvPolynomial

section Matrix
variable {K σ ι : Type*} [CommRing K] [Finite σ] [Fintype ι]

noncomputable def macaulayMatrix (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ) :
    Matrix (DegreeIndex σ D) (Σ i : ι, DegreeIndex σ (D-e i)) K :=
  fun s t => (F t.1 * monomial t.2.val 1).coeff s.val

noncomputable def macaulayCombination (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) : MvPolynomial σ K :=
  ∑ t, b t • (F t.1 * monomial t.2.val 1)

lemma coeff_macaulayCombination (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) (s : DegreeIndex σ D) :
    (macaulayCombination e F D b).coeff s.val = (macaulayMatrix e F D).mulVec b s := by
  classical
  simp only [macaulayCombination, coeff_sum, coeff_smul, smul_eq_mul,
    macaulayMatrix, Matrix.mulVec, dotProduct, mul_comm]

lemma macaulayCombination_mem (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) :
    macaulayCombination e F D b ∈ Ideal.span (Set.range F) := by
  apply Ideal.sum_mem
  intro t _
  exact Submodule.smul_mem ((Ideal.span (Set.range F)).restrictScalars K) _
    (Ideal.mul_mem_right _ _ Ideal.mem_span_range_self)

lemma macaulayCombination_homogeneous (e : ι → ℤ) (F : ι → MvPolynomial σ K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (e i)) (D : ℤ)
    (b : (Σ i : ι, DegreeIndex σ (D-e i)) → K) :
    (macaulayCombination e F D b).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) D := by
  apply IsWeightedHomogeneous.sum
  intro t _
  apply (weightedHomogeneousSubmodule K (fun _ : σ => (1 : ℤ)) D).smul_mem
  have hm : (monomial t.2.val (1 : K)).IsWeightedHomogeneous
      (fun _ : σ => (1 : ℤ)) (D-e t.1) :=
    isWeightedHomogeneous_monomial _ _ _ ((intWeight_degree t.2.val).trans t.2.property)
  rw [mem_weightedHomogeneousSubmodule]
  simpa only [add_sub_cancel] using (hF t.1).mul hm

omit [Finite σ] [Fintype ι] in
lemma macaulayMatrix_map {L : Type*} [CommRing L] (φ : K →+* L)
    (e : ι → ℤ) (F : ι → MvPolynomial σ K) (D : ℤ) :
    macaulayMatrix e (fun i => map φ (F i)) D = (macaulayMatrix e F D).map φ := by
  classical
  ext s t
  change (map φ (F t.1) * monomial t.2.val 1).coeff s.val =
    φ ((F t.1 * monomial t.2.val 1).coeff s.val)
  rw [← coeff_map, map_mul, map_monomial, φ.map_one]

end Matrix

section Surjectivity
variable {K σ ι : Type*} [Field K] [Finite σ] [Fintype ι]

theorem macaulay_surjective_iff (e : ι → ℤ) (F : ι → MvPolynomial σ K)
    (hF : ∀ i, (F i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (e i)) (D : ℤ) :
    Function.Surjective (macaulayMatrix e F D).mulVec ↔
      ∀ f : MvPolynomial σ K,
        f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) D →
          f ∈ Ideal.span (Set.range F) := by
  classical
  constructor
  · intro hs f hf
    obtain ⟨b,hb⟩ := hs (fun s => f.coeff s.val)
    have he : macaulayCombination e F D b = f := by
      apply homogeneous_ext_degree (macaulayCombination_homogeneous e F hF D b) hf
      intro s
      rw [coeff_macaulayCombination, hb]
    rw [← he]
    exact macaulayCombination_mem e F D b
  · intro hs b
    let f := ∑ t : DegreeIndex σ D, monomial t.val (b t)
    have hf : f.IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) D :=
      sum_degree_homogeneous D b
    obtain ⟨g,hg⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hs f hf)
    let g' := fun i => weightedHomogeneousComponent (fun _ : σ => (1 : ℤ)) (D-e i) (g i)
    have hg'h (i : ι) : (g' i).IsWeightedHomogeneous (fun _ : σ => (1 : ℤ)) (D-e i) :=
      weightedHomogeneousComponent_mem _ _ _
    have he : ∑ i, F i * g' i = f := by
      simp_rw [g', ← PermanentBorder.Multigraded.project_mul _ (hF _)]
      rw [← map_sum]
      simp_rw [mul_comm (F _) _]
      rw [hg, weightedHomogeneousComponent_eq_self hf]
    let c : (Σ i : ι, DegreeIndex σ (D-e i)) → K := fun t => (g' t.1).coeff t.2.val
    have hc : macaulayCombination e F D c = f := by
      rw [macaulayCombination, Fintype.sum_sigma]
      rw [← he]
      apply Finset.sum_congr rfl
      intro i _
      rw [homogeneous_sum_degree (hg'h i), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      change (g' i).coeff s.val • (F i * monomial s.val 1) =
        F i * monomial s.val ((g' i).coeff s.val)
      rw [← mul_smul_comm, smul_monomial, smul_eq_mul, mul_one]
    refine ⟨c, ?_⟩
    ext s
    rw [← coeff_macaulayCombination, hc]
    exact coeff_sum_degree D b s

end Surjectivity
end PermanentBorder.SliceParameters

end OAI
