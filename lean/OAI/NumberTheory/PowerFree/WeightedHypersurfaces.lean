import OAI.NumberTheory.PowerFree.WeightedSlabs

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

@[simp] theorem firstSlab_apply (i : ℕ) (x : ℕ × ℕ) : firstSlab i x = (i,x) := rfl
@[simp] theorem secondSlab_apply (u j : ℕ) (x : ℕ × ℕ) : secondSlab u j x = (u+x.1,j,x.2) := rfl
@[simp] theorem thirdSlab_apply (u v k : ℕ) (x : ℕ × ℕ) : thirdSlab u v k x = (u+x.1,v+x.2,k) := rfl

theorem mem_firstSlabs {a b c u T : ℕ} (_ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hT : a*u ≤ T) (x : NatTriple) :
    x ∈ firstSlabs a b c u T ↔ x.1 < u ∧ tripleWeight a b c x ≤ T := by
  simp only [firstSlabs, Finset.mem_biUnion, Finset.mem_range, Finset.mem_map]
  constructor
  · rintro ⟨i, hi, y, hy, rfl⟩
    have hs : a*i ≤ T := (Nat.mul_le_mul_left a (Nat.le_of_lt hi)).trans hT
    have hy' := (mem_weightedPairs hb hc y (T-a*i)).mp hy
    simp only [firstSlab_apply, tripleWeight]
    exact ⟨hi, by omega⟩
  · rintro ⟨hx, hw⟩
    refine ⟨x.1, hx, (x.2.1,x.2.2), ?_, by simp⟩
    apply (mem_weightedPairs hb hc _ _).mpr
    dsimp [tripleWeight] at hw
    dsimp
    omega

theorem mem_secondSlabs {a b c u v T : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hT : a*u+b*v ≤ T) (x : NatTriple) :
    x ∈ secondSlabs a b c u v T ↔ u ≤ x.1 ∧ x.2.1 < v ∧ tripleWeight a b c x ≤ T := by
  simp only [secondSlabs, Finset.mem_biUnion, Finset.mem_range, Finset.mem_map]
  constructor
  · rintro ⟨j, hj, y, hy, rfl⟩
    have hs : a*u+b*j ≤ T := by nlinarith [Nat.mul_le_mul_left b (Nat.le_of_lt hj)]
    have hy' := (mem_weightedPairs ha hc y _).mp hy
    simp only [secondSlab_apply, tripleWeight]
    refine ⟨by omega, hj, ?_⟩
    nlinarith [Nat.sub_add_cancel hs]
  · rintro ⟨hu, hx, hw⟩
    refine ⟨x.2.1, hx, (x.1-u,x.2.2), ?_, ?_⟩
    · apply (mem_weightedPairs ha hc _ _).mpr
      dsimp [tripleWeight] at hw
      dsimp
      have he := Nat.sub_add_cancel hu
      have hs : a*u+b*x.2.1 ≤ T := by nlinarith [Nat.mul_le_mul_left a hu]
      nlinarith [Nat.sub_add_cancel hs]
    · simp [Nat.add_sub_cancel' hu]

theorem mem_thirdSlabs {a b c u v w T : ℕ} (ha : 0 < a) (hb : 0 < b) (_hc : 0 < c)
    (hT : a*u+b*v+c*w ≤ T) (x : NatTriple) :
    x ∈ thirdSlabs a b c u v w T ↔
      u ≤ x.1 ∧ v ≤ x.2.1 ∧ x.2.2 < w ∧ tripleWeight a b c x ≤ T := by
  simp only [thirdSlabs, Finset.mem_biUnion, Finset.mem_range, Finset.mem_map]
  constructor
  · rintro ⟨k, hk, y, hy, rfl⟩
    have hs : a*u+b*v+c*k ≤ T := by nlinarith [Nat.mul_le_mul_left c (Nat.le_of_lt hk)]
    have hy' := (mem_weightedPairs ha hb y _).mp hy
    simp only [thirdSlab_apply, tripleWeight]
    refine ⟨by omega, by omega, hk, ?_⟩
    nlinarith [Nat.sub_add_cancel hs]
  · rintro ⟨hu, hv, hx, hw⟩
    refine ⟨x.2.2, hx, (x.1-u,x.2.1-v), ?_, ?_⟩
    · apply (mem_weightedPairs ha hb _ _).mpr
      dsimp [tripleWeight] at hw
      dsimp
      have he := Nat.sub_add_cancel hu
      have he' := Nat.sub_add_cancel hv
      have hs : a*u+b*v+c*x.2.2 ≤ T := by
        nlinarith [Nat.mul_le_mul_left a hu, Nat.mul_le_mul_left b hv]
      nlinarith [Nat.sub_add_cancel hs]
    · simp [Nat.add_sub_cancel' hu, Nat.add_sub_cancel' hv]

private theorem card_indexedSlabs {α β : Type*} [DecidableEq β]
    (q : ℕ → Finset α) (e : ℕ → α ↪ β) (f : β → ℕ)
    (hf : ∀ i x, f (e i x) = i) (n : ℕ) :
    ((Finset.range n).biUnion fun i => (q i).map (e i)).card = ∑ i ∈ Finset.range n, (q i).card := by
  rw [Finset.card_biUnion]
  · simp
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨x, _, hx⟩ := Finset.mem_map.mp hz
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hz'
    exact hij ((hf i x).symm.trans ((congrArg f (hx.trans hy.symm)).trans (hf j y)))

theorem weightedNormal_card_slabs {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (m : NatTriple) (T : ℕ) (hT : tripleWeight a b c m ≤ T) :
    (weightedNormal a b c m T).card =
      (∑ i ∈ Finset.range m.1, (weightedPairs b c (T-a*i)).card) +
      (∑ j ∈ Finset.range m.2.1, (weightedPairs a c (T-(a*m.1+b*j))).card) +
      (∑ k ∈ Finset.range m.2.2, (weightedPairs a b (T-(a*m.1+b*m.2.1+c*k))).card) := by
  have h1 : a*m.1 ≤ T := by dsimp [tripleWeight] at hT; omega
  have h2 : a*m.1+b*m.2.1 ≤ T := by dsimp [tripleWeight] at hT; omega
  have he : weightedNormal a b c m T =
      (firstSlabs a b c m.1 T ∪ secondSlabs a b c m.1 m.2.1 T) ∪
        thirdSlabs a b c m.1 m.2.1 m.2.2 T := by
    ext x
    rw [weightedNormal, Finset.mem_filter]
    simp only [mem_weightedTriples ha hb hc,
      Finset.mem_union, mem_firstSlabs ha hb hc h1, mem_secondSlabs ha hb hc h2,
      mem_thirdSlabs ha hb hc hT, tripleDivides]
    omega
  have hd12 : Disjoint (firstSlabs a b c m.1 T) (secondSlabs a b c m.1 m.2.1 T) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hx' := (mem_firstSlabs ha hb hc h1 x).mp hx
    have hy' := (mem_secondSlabs ha hb hc h2 x).mp hy
    omega
  have hd3 : Disjoint (firstSlabs a b c m.1 T ∪ secondSlabs a b c m.1 m.2.1 T)
      (thirdSlabs a b c m.1 m.2.1 m.2.2 T) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have hy' := (mem_thirdSlabs ha hb hc hT x).mp hy
    rcases Finset.mem_union.mp hx with hx | hx
    · have hx' := (mem_firstSlabs ha hb hc h1 x).mp hx; omega
    · have hx' := (mem_secondSlabs ha hb hc h2 x).mp hx; omega
  rw [he, Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd12]
  congr 2
  · exact card_indexedSlabs _ firstSlab Prod.fst (fun _ _ => rfl) _
  · exact card_indexedSlabs _ (secondSlab m.1) (fun x => x.2.1) (fun _ _ => rfl) _
  · exact card_indexedSlabs _ (thirdSlab m.1 m.2.1) (fun x => x.2.2) (fun _ _ => rfl) _

theorem weightedPairs_shift_volume_error {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (s T : ℕ) (hs : s ≤ T) :
    |((weightedPairs a b (T-s)).card : ℝ) - (T:ℝ)^2/(2*(a*b : ℕ))| ≤
      ((s:ℝ)+2)*T + 4*(a*b : ℕ) := by
  have hL : (1:ℝ) ≤ (a*b : ℕ) := by exact_mod_cast Nat.mul_pos ha hb
  have hd : (0:ℝ) < 2*(a*b : ℕ) := by positivity
  have ht : (T-s : ℕ) + s = T := Nat.sub_add_cancel hs
  have ht' : (T-s : ℕ) + (s:ℝ) = T := by exact_mod_cast ht
  have hp := weightedPairs_volume_error ha hb (T-s)
  have hdiff : |((T-s : ℕ):ℝ)^2/(2*(a*b : ℕ))-(T:ℝ)^2/(2*(a*b : ℕ))| ≤
      (s:ℝ)*T := by
    have hn : ((T-s : ℕ):ℝ)^2-(T:ℝ)^2 ≤ 0 := by nlinarith
    rw [← sub_div, abs_div, abs_of_nonpos hn, abs_of_pos hd]
    apply (div_le_iff₀ hd).mpr
    have hx := mul_le_mul_of_nonneg_right hL (show (0:ℝ) ≤ (s:ℝ)*T by positivity)
    nlinarith
  calc
    _ ≤ |((weightedPairs a b (T-s)).card : ℝ) - ((T-s : ℕ):ℝ)^2/(2*(a*b : ℕ))| +
        |((T-s : ℕ):ℝ)^2/(2*(a*b : ℕ))-(T:ℝ)^2/(2*(a*b : ℕ))| := abs_sub_le ..
    _ ≤ _ := by nlinarith

theorem weightedPairs_shift_sum_error {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (n E T : ℕ) (hT : E ≤ T) (q : ℕ → ℕ) (hq : ∀ i < n, q i ≤ E) :
    |((∑ i ∈ Finset.range n, (weightedPairs a b (T-q i)).card : ℕ) : ℝ) -
      (n:ℝ)*(T:ℝ)^2/(2*(a*b : ℕ))| ≤
      (n:ℝ)*((E:ℝ)+2+4*(a*b : ℕ))*((T:ℝ)+1) := by
  have he : (∑ i ∈ Finset.range n,
      (((weightedPairs a b (T-q i)).card : ℝ) - (T:ℝ)^2/(2*(a*b : ℕ)))) =
      ((∑ i ∈ Finset.range n, (weightedPairs a b (T-q i)).card : ℕ) : ℝ) -
      (n:ℝ)*(T:ℝ)^2/(2*(a*b : ℕ)) := by
    simp [Finset.sum_sub_distrib, mul_div_assoc]
  rw [← he]
  calc
    _ ≤ ∑ i ∈ Finset.range n,
        |((weightedPairs a b (T-q i)).card : ℝ) - (T:ℝ)^2/(2*(a*b : ℕ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range n, (((E:ℝ)+2+4*(a*b : ℕ))*((T:ℝ)+1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hqi := hq i (Finset.mem_range.mp hi)
      have hqi' : (q i:ℝ) ≤ E := by exact_mod_cast hqi
      have hb' := weightedPairs_shift_volume_error ha hb (q i) T (hqi.trans hT)
      have hx := mul_le_mul_of_nonneg_right hqi' (show (0:ℝ) ≤ T by positivity)
      nlinarith
    _ = _ := by simp; ring

noncomputable def normalErrorConst (a b c : ℕ) (m : NatTriple) : ℝ :=
  (m.1:ℝ)*((tripleWeight a b c m:ℝ)+2+4*(b*c : ℕ)) +
  (m.2.1:ℝ)*((tripleWeight a b c m:ℝ)+2+4*(a*c : ℕ)) +
  (m.2.2:ℝ)*((tripleWeight a b c m:ℝ)+2+4*(a*b : ℕ))

theorem weightedNormal_volume_error {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (m : NatTriple) (T : ℕ) (hT : tripleWeight a b c m ≤ T) :
    |((weightedNormal a b c m T).card : ℝ) -
      (tripleWeight a b c m : ℝ)*(T:ℝ)^2/(2*(a*b*c : ℕ))| ≤
      normalErrorConst a b c m * ((T:ℝ)+1) := by
  have h1 := weightedPairs_shift_sum_error hb hc m.1 (tripleWeight a b c m) T hT
    (fun i => a*i) (by intro i hi; dsimp [tripleWeight]; nlinarith [Nat.mul_le_mul_left a (Nat.le_of_lt hi)])
  have h2 := weightedPairs_shift_sum_error ha hc m.2.1 (tripleWeight a b c m) T hT
    (fun j => a*m.1+b*j) (by intro j hj; dsimp [tripleWeight]; nlinarith [Nat.mul_le_mul_left b (Nat.le_of_lt hj)])
  have h3 := weightedPairs_shift_sum_error ha hb m.2.2 (tripleWeight a b c m) T hT
    (fun k => a*m.1+b*m.2.1+c*k)
    (by intro k hk; dsimp [tripleWeight]; nlinarith [Nat.mul_le_mul_left c (Nat.le_of_lt hk)])
  have he := weightedNormal_card_slabs ha hb hc m T hT
  have ha' : (a:ℝ) ≠ 0 := by positivity
  have hb' : (b:ℝ) ≠ 0 := by positivity
  have hc' : (c:ℝ) ≠ 0 := by positivity
  have hcoeff : (tripleWeight a b c m : ℝ)*(T:ℝ)^2/(2*(a*b*c : ℕ)) =
      (m.1:ℝ)*(T:ℝ)^2/(2*(b*c : ℕ)) + (m.2.1:ℝ)*(T:ℝ)^2/(2*(a*c : ℕ)) +
      (m.2.2:ℝ)*(T:ℝ)^2/(2*(a*b : ℕ)) := by
    simp only [tripleWeight, Nat.cast_add, Nat.cast_mul]
    field_simp
  rw [he, Nat.cast_add, Nat.cast_add, hcoeff]
  have habs (x y z u v w : ℝ) : |x+y+z-(u+v+w)| ≤ |x-u|+|y-v|+|z-w| := by
    calc
      _ = |(x-u)+(y-v)+(z-w)| := by congr 1; ring
      _ ≤ |(x-u)+(y-v)|+|z-w| := abs_add_le _ _
      _ ≤ _ := by linarith [abs_add_le (x-u) (y-v)]
  have hh := habs
    (((∑ i ∈ Finset.range m.1, (weightedPairs b c (T-a*i)).card : ℕ) : ℝ))
    (((∑ j ∈ Finset.range m.2.1, (weightedPairs a c (T-(a*m.1+b*j))).card : ℕ) : ℝ))
    (((∑ k ∈ Finset.range m.2.2, (weightedPairs a b (T-(a*m.1+b*m.2.1+c*k))).card : ℕ) : ℝ))
    ((m.1:ℝ)*(T:ℝ)^2/(2*(b*c : ℕ)))
    ((m.2.1:ℝ)*(T:ℝ)^2/(2*(a*c : ℕ)))
    ((m.2.2:ℝ)*(T:ℝ)^2/(2*(a*b : ℕ)))
  dsimp [normalErrorConst]
  linarith

end

open MvPolynomial
open scoped BigOperators

noncomputable def weightedLift {σ R : Type*} [CommSemiring R] (w : σ → ℕ) :
    MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  eval₂Hom (Polynomial.C.comp C)
    (fun i => Polynomial.C (X i) * Polynomial.X ^ w i)

theorem weightedLift_monomial {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (m : σ →₀ ℕ) (r : R) :
    weightedLift w (monomial m r) =
      Polynomial.C (monomial m r) * Polynomial.X ^ (Finsupp.weight w m) := by
  classical
  simp only [weightedLift, eval₂Hom_monomial, RingHom.comp_apply]
  simp only [Finsupp.prod, mul_pow, ← map_pow, Finset.prod_mul_distrib,
    ← map_prod]
  rw [← mul_assoc, ← Polynomial.C_mul]
  congr 1
  · rw [monomial_eq, Finsupp.prod]
  · simp only [← pow_mul, Finset.prod_pow_eq_pow_sum]
    congr 1
    simp [Finsupp.weight, Finsupp.linearCombination_apply, Finsupp.sum, mul_comm]

theorem weightedLift_coeff {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) (t : ℕ) :
    (weightedLift w p).coeff t = weightedHomogeneousComponent w t p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial m r =>
    rw [weightedLift_monomial, Polynomial.coeff_C_mul_X_pow]
    ext s
    by_cases hs : m = s
    · subst s
      split_ifs <;> simp_all [coeff_weightedHomogeneousComponent, coeff_monomial, eq_comm]
    · split_ifs <;> simp_all [coeff_weightedHomogeneousComponent, coeff_monomial]
  | add p q hp hq => simp [map_add, Polynomial.coeff_add, hp, hq]

theorem weightedLift_eval_one {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) : (weightedLift w p).eval 1 = p := by
  induction p using MvPolynomial.induction_on' with
  | monomial m r => simp [weightedLift_monomial]
  | add p q hp hq => simp [map_add, hp, hq]

theorem weightedLift_injective {σ R : Type*} [CommSemiring R] (w : σ → ℕ) :
    Function.Injective (weightedLift (R := R) w) := by
  intro p q h
  simpa only [weightedLift_eval_one] using congrArg (Polynomial.eval 1) h

theorem weightedLift_natDegree {σ R : Type*} [CommSemiring R] (w : σ → ℕ)
    (p : MvPolynomial σ R) :
    (weightedLift w p).natDegree = weightedTotalDegree w p := by
  classical
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro t ht
    rw [weightedLift_coeff]
    exact weightedHomogeneousComponent_eq_zero t p ht
  · unfold weightedTotalDegree
    apply Finset.sup_le
    intro m hm
    have hc : (weightedLift w p).coeff (Finsupp.weight w m) ≠ 0 := by
      rw [weightedLift_coeff]
      intro he
      have h := congrArg (fun polynomial => polynomial.coeff m) he
      simp [coeff_weightedHomogeneousComponent, mem_support_iff.mp hm] at h
    exact Polynomial.le_natDegree_of_ne_zero hc

theorem weightedTotalDegree_mul_exact {σ R : Type*} [CommSemiring R] [IsDomain R]
    (w : σ → ℕ) (p q : MvPolynomial σ R) (hp : p ≠ 0) (hq : q ≠ 0) :
    weightedTotalDegree w (p * q) = weightedTotalDegree w p + weightedTotalDegree w q := by
  rw [← weightedLift_natDegree, map_mul, Polynomial.natDegree_mul]
  · rw [weightedLift_natDegree, weightedLift_natDegree]
  · intro h
    apply hp
    apply weightedLift_injective w
    simpa using h
  · intro h
    apply hq
    apply weightedLift_injective w
    simpa using h

theorem finrank_of_exact {K L M N : Type*} [Field K]
    [AddCommGroup L] [Module K L] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module.Finite K M]
    (g : L →ₗ[K] M) (f : M →ₗ[K] N) (hg : Function.Injective g)
    (he : LinearMap.range g = LinearMap.ker f) :
    Module.finrank K (LinearMap.range f) + Module.finrank K L = Module.finrank K M := by
  rw [← LinearMap.finrank_range_of_inj hg, he]
  exact f.finrank_range_add_finrank_ker

theorem filtered_principal_finrank {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (F G : Submodule K R)
    [Module.Finite K F] (c : R) (hc : c ≠ 0)
    (hdegree : ∀ x : R, c * x ∈ F ↔ x ∈ G) :
    Module.finrank K (F.map (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap) +
      Module.finrank K G = Module.finrank K F := by
  let f := (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap.domRestrict F
  let g : G →ₗ[K] F :=
    { toFun := fun x => ⟨c * x.val, (hdegree x.val).mpr x.property⟩
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp }
  have hg : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    exact mul_left_cancel₀ hc (congrArg Subtype.val h)
  have he : LinearMap.range g = LinearMap.ker f := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change (Ideal.Quotient.mk (Ideal.span {c})) (c * y.val) = 0
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_span_singleton.mpr ⟨y.val, rfl⟩
    · intro hx
      have hmem : x.val ∈ Ideal.span {c} := Ideal.Quotient.eq_zero_iff_mem.mp hx
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hmem
      refine ⟨⟨y, (hdegree y).mp (hy ▸ x.property)⟩, ?_⟩
      apply Subtype.ext
      exact hy.symm
  have hr : LinearMap.range f = F.map (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← hr]
  exact finrank_of_exact g f hg he

noncomputable def weightedSpace {σ K : Type*} [CommSemiring K] (w : σ → ℕ) (T : ℕ) :
    Submodule K (MvPolynomial σ K) :=
  restrictSupport K {m | Finsupp.weight w m ≤ T}

theorem mem_weightedSpace {σ K : Type*} [CommSemiring K] (w : σ → ℕ)
    (T : ℕ) (p : MvPolynomial σ K) :
    p ∈ weightedSpace w T ↔ weightedTotalDegree w p ≤ T := by
  classical
  simp only [weightedSpace, mem_restrictSupport_iff, weightedTotalDegree,
    Finset.sup_le_iff, Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq]

theorem weightedSpace_finite {σ K : Type*} [Finite σ] [CommSemiring K]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (T : ℕ) :
    Module.Finite K (weightedSpace (K := K) w T) := by
  have := (Finsupp.finite_of_nat_weight_le w hw T).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport K _)

theorem weightedSpace_finrank {σ K : Type*} [Finite σ] [Field K]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (T : ℕ) :
    Module.finrank K (weightedSpace (K := K) w T) =
      Nat.card {m : σ →₀ ℕ // Finsupp.weight w m ≤ T} := by
  have := (Finsupp.finite_of_nat_weight_le w hw T).to_subtype
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)

theorem weighted_hypersurface_finrank {σ K : Type*} [Finite σ] [Field K]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (F : MvPolynomial σ K) (hF : F ≠ 0)
    (T : ℕ) (hT : weightedTotalDegree w F ≤ T) :
    Module.finrank K ((weightedSpace w T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {F})).toLinearMap) +
      Nat.card {m : σ →₀ ℕ // Finsupp.weight w m ≤ T - weightedTotalDegree w F} =
      Nat.card {m : σ →₀ ℕ // Finsupp.weight w m ≤ T} := by
  have := weightedSpace_finite (K := K) w hw T
  have hd (p : MvPolynomial σ K) : F * p ∈ weightedSpace w T ↔
      p ∈ weightedSpace w (T - weightedTotalDegree w F) := by
    rw [mem_weightedSpace, mem_weightedSpace]
    by_cases hp : p = 0
    · subst p
      simp [weightedTotalDegree]
    · rw [weightedTotalDegree_mul_exact w F p hF hp]
      omega
  have h := filtered_principal_finrank (weightedSpace w T)
    (weightedSpace w (T - weightedTotalDegree w F)) F hF hd
  rwa [weightedSpace_finrank w hw, weightedSpace_finrank w hw] at h

end QuarticPowerFree

end OAI
