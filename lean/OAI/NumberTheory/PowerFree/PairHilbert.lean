import OAI.NumberTheory.PowerFree.PairAlgebras

namespace OAI

namespace QuarticPowerFree

theorem normPair_finrank_of_exact {K L M N : Type*} [Field K]
    [AddCommGroup L] [Module K L] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Module.Finite K M]
    (g : L →ₗ[K] M) (f : M →ₗ[K] N) (hg : Function.Injective g)
    (he : LinearMap.range g = LinearMap.ker f) :
    Module.finrank K (LinearMap.range f) + Module.finrank K L = Module.finrank K M := by
  rw [← LinearMap.finrank_range_of_inj hg, he]
  exact f.finrank_range_add_finrank_ker

theorem normPair_filtered_principal_finrank {K R : Type*} [Field K] [CommRing R]
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
  exact normPair_finrank_of_exact g f hg he

noncomputable def homogeneousSpace {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (T : ℕ) : Submodule K R where
  carrier := {x | L x = Polynomial.monomial T x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change L (x+y) = Polynomial.monomial T (x+y)
    change L x = Polynomial.monomial T x at hx
    change L y = Polynomial.monomial T y at hy
    rw [map_add, hx, hy, map_add]
  smul_mem' := by
    intro c x hx
    change L (c • x) = Polynomial.monomial T (c • x)
    change L x = Polynomial.monomial T x at hx
    rw [map_smul, hx, Polynomial.smul_monomial]

theorem mem_homogeneousSpace {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (T : ℕ) (x : R) :
    x ∈ homogeneousSpace L T ↔ L x = Polynomial.monomial T x := Iff.rfl

theorem homogeneous_principal_finrank {K R : Type*} [Field K] [CommRing R]
    [IsDomain R] [Algebra K R] (L : R →ₐ[K] Polynomial R) (E T : ℕ)
    [Module.Finite K (homogeneousSpace L (E+T))]
    (c : R) (hc : c ≠ 0) (hC : L c = Polynomial.monomial E c) :
    Module.finrank K ((homogeneousSpace L (E+T)).map
      (Ideal.Quotient.mkₐ K (Ideal.span {c})).toLinearMap) +
      Module.finrank K (homogeneousSpace L T) =
      Module.finrank K (homogeneousSpace L (E+T)) := by
  apply normPair_filtered_principal_finrank _ _ c hc
  intro x
  simp only [mem_homogeneousSpace, map_mul, hC]
  rw [← Polynomial.monomial_mul_monomial]
  have hp : Polynomial.monomial E c ≠ 0 := by simpa using hc
  exact ⟨fun h => mul_left_cancel₀ hp h, fun h => congrArg _ h⟩

open scoped BigOperators

theorem homogeneous_coord {ι K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i))
    (x : R) (t : ℕ) (i : ι) :
    b.repr ((L x).coeff t) i = if w i = t then b.repr x i else 0 := by
  classical
  let f := (b.coord i).comp (((Polynomial.lcoeff R t).restrictScalars K).comp L.toLinearMap)
  have hf : f = if w i = t then b.coord i else 0 := by
    apply b.ext
    intro j
    simp only [f, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      AlgHom.toLinearMap_apply, Polynomial.lcoeff_apply, hb, Polynomial.coeff_monomial]
    by_cases hij : i = j
    · subst j
      split_ifs <;> simp_all [Module.Basis.coord_apply]
    · have hji : j ≠ i := Ne.symm hij
      split_ifs <;> simp_all [Module.Basis.coord_apply]
  have hh := LinearMap.congr_fun hf x
  by_cases hi : w i = t
  · simpa [f, hi, Module.Basis.coord_apply] using hh
  · simpa [f, hi, Module.Basis.coord_apply] using hh

theorem homogeneousSpace_eq_basis_span {ι K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i)) (T : ℕ) :
    homogeneousSpace L T = Submodule.span K (b '' {i | w i = T}) := by
  classical
  apply le_antisymm
  · intro x hx
    rw [b.mem_span_image]
    intro i hi
    have hc := homogeneous_coord L b w hb x (w i) i
    rw [(mem_homogeneousSpace L T x).mp hx, Polynomial.coeff_monomial] at hc
    simp only [ite_true] at hc
    by_contra hn
    have hn' : w i ≠ T := hn
    rw [ite_eq_right (Ne.symm hn')] at hc
    simp only [map_zero, Finsupp.zero_apply] at hc
    exact (Finsupp.mem_support_iff.mp hi) hc.symm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,hi,rfl⟩
    exact (hb i).trans (by rw [hi])

theorem homogeneousSpace_finrank {ι K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i)) (T : ℕ)
    [Fintype {i // w i = T}] :
    Module.finrank K (homogeneousSpace L T) = Fintype.card {i // w i = T} := by
  rw [homogeneousSpace_eq_basis_span L b w hb T]
  have hs : b '' {i | w i = T} = Set.range (fun i : {i // w i = T} => b i.val) := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
  rw [hs]
  exact finrank_span_eq_card (b.linearIndependent.comp
    (fun i : {i // w i = T} => i.val) Subtype.val_injective)

theorem homogeneousSpace_finite {ι K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (b : Module.Basis ι K R) (w : ι → ℕ)
    (hb : ∀ i, L (b i) = Polynomial.monomial (w i) (b i)) (T : ℕ)
    [Finite {i // w i = T}] : Module.Finite K (homogeneousSpace L T) := by
  classical
  rw [homogeneousSpace_eq_basis_span L b w hb T]
  have hs : b '' {i | w i = T} = Set.range (fun i : {i // w i = T} => b i.val) := by
    ext x
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
  rw [hs]
  exact Module.Finite.span_of_finite K (Set.finite_range _)

open scoped BigOperators

noncomputable def normPair_simplexTuple (h N : ℕ) : Finset (Fin h → ℕ) :=
  (Finset.range (N+1)).biUnion (Finset.Nat.antidiagonalTuple h)

@[simp] theorem normPair_mem_simplexTuple {h N : ℕ} (x : Fin h → ℕ) :
    x ∈ normPair_simplexTuple h N ↔ ∑ i, x i ≤ N := by
  classical
  simp only [normPair_simplexTuple, Finset.mem_biUnion, Finset.mem_range,
    Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨n, hn, he⟩; omega
  · intro hx; exact ⟨_, by omega, rfl⟩

private theorem normPair_card_antidiagonalTuple (h N : ℕ) :
    (Finset.Nat.antidiagonalTuple h N).card = h.multichoose N := by
  classical
  have hc := Finset.card_finsuppAntidiag_nat_eq_multichoose
    (s := (Finset.univ : Finset (Fin h))) N
  rw [Finset.card_univ, Fintype.card_fin] at hc
  rw [← hc]
  apply Finset.card_bij (fun x _ => Finsupp.equivFunOnFinite.symm x)
  · intro x hx
    rw [Finset.mem_finsuppAntidiag']
    exact ⟨by simpa [Finsupp.sum_fintype] using Finset.Nat.mem_antidiagonalTuple.mp hx,
      Finset.subset_univ _⟩
  · intro x _ y _ he
    exact Finsupp.equivFunOnFinite.symm.injective he
  · intro x hx
    refine ⟨Finsupp.equivFunOnFinite x, ?_, by simp⟩
    rw [Finset.Nat.mem_antidiagonalTuple]
    simpa [Finsupp.sum_fintype] using (Finset.mem_finsuppAntidiag'.mp hx).1

theorem normPair_card_simplexTuple (h N : ℕ) :
    (normPair_simplexTuple h N).card = (N+h).choose h := by
  classical
  rw [normPair_simplexTuple, Finset.card_biUnion]
  · simp_rw [normPair_card_antidiagonalTuple]
    exact Nat.sum_range_multichoose N h
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    exact hij ((Finset.Nat.mem_antidiagonalTuple.mp hi).symm.trans
      (Finset.Nat.mem_antidiagonalTuple.mp hj))

def weightedTuple {h : ℕ} (w : Fin h → ℕ) (T : ℕ) : Finset (Fin h → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (T+1))).filter
    (fun x => ∑ i, w i*x i ≤ T)

theorem mem_weightedTuple {h : ℕ} (w : Fin h → ℕ) (hw : ∀ i, 0 < w i)
    (T : ℕ) (x : Fin h → ℕ) :
    x ∈ weightedTuple w T ↔ ∑ i, w i*x i ≤ T := by
  classical
  simp only [weightedTuple, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro hx
    refine ⟨fun i => ?_, hx⟩
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (w j*x j))
      (Finset.mem_univ i)
    have hixi : x i ≤ w i*x i := by nlinarith [hw i]
    omega

def tupleQuot {h : ℕ} (m : Fin h → ℕ) (x : Fin h → ℕ) : Fin h → ℕ := fun i => x i / m i

def tupleRem {h : ℕ} (m : Fin h → ℕ) (x : Fin h → ℕ) : Fin h → ℕ := fun i => x i % m i

private theorem tuple_divmod_injective {h : ℕ} (m : Fin h → ℕ) :
    Function.Injective (fun x => (tupleQuot m x, tupleRem m x)) := by
  intro x y he
  have hq := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  funext i
  have hqi := congrFun hq i
  have hri := congrFun hr i
  dsimp [tupleQuot, tupleRem] at hqi hri
  have hx := Nat.mod_add_div (x i) (m i)
  have hy := Nat.mod_add_div (y i) (m i)
  rw [hqi, hri] at hx
  omega

theorem weightedTuple_upper {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hw : ∀ i, 0 < w i) (hm : ∀ i, 0 < m i) (hL : 0 < L)
    (hprod : ∀ i, w i*m i = L) (T : ℕ) :
    (weightedTuple w T).card ≤ (normPair_simplexTuple h (T/L)).card * ∏ i, m i := by
  classical
  let R := Fintype.piFinset (fun i => Finset.range (m i))
  let f := fun x => (tupleQuot m x, tupleRem m x)
  have hin (x : Fin h → ℕ) (hx : x ∈ weightedTuple w T) :
      f x ∈ (normPair_simplexTuple h (T/L)) ×ˢ R := by
    apply Finset.mem_product.mpr
    refine ⟨(normPair_mem_simplexTuple _).mpr ?_, ?_⟩
    · apply (Nat.le_div_iff_mul_le hL).mpr
      calc
        (∑ i, tupleQuot m x i)*L = ∑ i, w i*(m i*(x i/m i)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          dsimp [tupleQuot]
          rw [← hprod i]
          ring
        _ ≤ ∑ i, w i*x i := Finset.sum_le_sum (fun i _ =>
          Nat.mul_le_mul_left (w i) (Nat.mul_div_le (x i) (m i)))
        _ ≤ T := (mem_weightedTuple w hw T x).mp hx
    · simp [R, f, tupleRem, Nat.mod_lt _ (hm _)]
  have hc := Finset.card_le_card_of_injOn f hin
    (fun _ _ _ _ he => tuple_divmod_injective m he)
  simpa [R, Finset.card_product, Fintype.card_piFinset] using hc

theorem weightedTuple_lower {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hw : ∀ i, 0 < w i) (hm : ∀ i, 0 < m i)
    (hprod : ∀ i, w i*m i = L) (T : ℕ) (hT : h ≤ T/L) :
    (normPair_simplexTuple h (T/L-h)).card * ∏ i, m i ≤ (weightedTuple w T).card := by
  classical
  let R := Fintype.piFinset (fun i => Finset.range (m i))
  let f : (Fin h → ℕ) × (Fin h → ℕ) → (Fin h → ℕ) :=
    fun x i => m i*x.1 i+x.2 i
  have hh (x : (Fin h → ℕ) × (Fin h → ℕ))
      (hx : x ∈ (normPair_simplexTuple h (T/L-h)) ×ˢ R) :
      (∑ i, x.1 i ≤ T/L-h) ∧ ∀ i, x.2 i < m i := by
    rcases Finset.mem_product.mp hx with ⟨hq, hr⟩
    exact ⟨(normPair_mem_simplexTuple _).mp hq, by simpa [R] using hr⟩
  have hin (x : (Fin h → ℕ) × (Fin h → ℕ))
      (hx : x ∈ (normPair_simplexTuple h (T/L-h)) ×ˢ R) : f x ∈ weightedTuple w T := by
    apply (mem_weightedTuple w hw T _).mpr
    obtain ⟨hxq, hxr⟩ := hh x hx
    calc
      (∑ i, w i*(f x i)) = L*(∑ i, x.1 i) + ∑ i, w i*x.2 i := by
        simp only [f, mul_add, ← mul_assoc, hprod, Finset.sum_add_distrib,
          Finset.mul_sum]
      _ ≤ L*(T/L-h) + h*L := by
        apply Nat.add_le_add (Nat.mul_le_mul_left L hxq)
        calc
          ∑ i, w i*x.2 i ≤ ∑ _i : Fin h, L := Finset.sum_le_sum (fun i _ => by
            rw [← hprod i]; exact Nat.mul_le_mul_left _ (hxr i).le)
          _ = h*L := by simp
      _ = L*(T/L) := by rw [Nat.mul_sub_left_distrib, Nat.mul_comm h L,
        Nat.sub_add_cancel (Nat.mul_le_mul_left L hT)]
      _ ≤ T := Nat.mul_div_le T L
  have hi : Set.InjOn f ↑((normPair_simplexTuple h (T/L-h)) ×ˢ R) := by
    intro x hx y hy he
    obtain ⟨_, hxr⟩ := hh x hx
    obtain ⟨_, hyr⟩ := hh y hy
    have hq : x.1 = y.1 := by
      funext i
      have hd := congrArg (fun v => v i / m i) he
      simpa [f, Nat.mul_add_div (hm i), Nat.div_eq_of_lt (hxr i),
        Nat.div_eq_of_lt (hyr i)] using hd
    apply Prod.ext hq
    funext i
    have hd := congrFun he i
    dsimp [f] at hd
    rw [hq] at hd
    omega
  have hc := Finset.card_le_card_of_injOn f hin hi
  simpa [R, Finset.card_product, Fintype.card_piFinset] using hc

theorem simplexTuple_power_bounds (h N : ℕ) :
    N^h ≤ h.factorial*(normPair_simplexTuple h N).card ∧
    h.factorial*(normPair_simplexTuple h N).card ≤ (N+h)^h := by
  rw [normPair_card_simplexTuple, ← Nat.descFactorial_eq_factorial_mul_choose]
  refine ⟨?_, Nat.descFactorial_le_pow _ _⟩
  have he : N+h+1-h = N+1 := by omega
  exact (Nat.pow_le_pow_left (by omega : N ≤ N+1) h).trans
    (he ▸ Nat.pow_sub_le_descFactorial (N+h) h)

theorem prod_weight_comultiples {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hprod : ∀ i, w i*m i = L) :
    (∏ i, w i)*(∏ i, m i) = L^h := by
  rw [← Finset.prod_mul_distrib]
  simp_rw [hprod]
  simp

theorem weightedTuple_power_bounds {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hw : ∀ i, 0 < w i) (hm : ∀ i, 0 < m i) (hL : 0 < L)
    (hprod : ∀ i, w i*m i = L) (T : ℕ) (hT : h ≤ T/L) :
    (L*(T/L-h))^h ≤ h.factorial*(∏ i, w i)*(weightedTuple w T).card ∧
    h.factorial*(∏ i, w i)*(weightedTuple w T).card ≤ (L*(T/L+h))^h := by
  have hu := weightedTuple_upper w m L hw hm hL hprod T
  have hl := weightedTuple_lower w m L hw hm hprod T hT
  have hpu := (simplexTuple_power_bounds h (T/L)).2
  have hpl := (simplexTuple_power_bounds h (T/L-h)).1
  have hp := prod_weight_comultiples w m L hprod
  constructor
  · calc
      (L*(T/L-h))^h = (∏ i, w i)*(∏ i, m i)*(T/L-h)^h := by rw [mul_pow, hp]
      _ ≤ (∏ i, w i)*(∏ i, m i)*(h.factorial*(normPair_simplexTuple h (T/L-h)).card) :=
        Nat.mul_le_mul_left _ hpl
      _ = (h.factorial*(∏ i, w i))*
          ((normPair_simplexTuple h (T/L-h)).card*(∏ i, m i)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hl
  · calc
      h.factorial*(∏ i, w i)*(weightedTuple w T).card ≤
          h.factorial*(∏ i, w i)*((normPair_simplexTuple h (T/L)).card*(∏ i, m i)) :=
        Nat.mul_le_mul_left _ hu
      _ = (∏ i, w i)*(∏ i, m i)*(h.factorial*(normPair_simplexTuple h (T/L)).card) := by ring
      _ ≤ (∏ i, w i)*(∏ i, m i)*(T/L+h)^h := Nat.mul_le_mul_left _ hpu
      _ = (L*(T/L+h))^h := by rw [mul_pow, hp]

private theorem nearby_power_error (h : ℕ) {x y c : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c) (hd : |y-x| ≤ c) :
    |y^h-x^h| ≤ c*h*(c+1)^(h-1)*(x+1)^(h-1) := by
  have hmax : max |y| |x| ≤ (c+1)*(x+1) := by
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    apply max_le
    · have hi := (abs_le.mp hd).2
      nlinarith
    · nlinarith
  calc
    |y^h-x^h| ≤ |y-x| * h * max |y| |x| ^ (h-1) := abs_pow_sub_pow_le y x h
    _ ≤ c*h*((c+1)*(x+1))^(h-1) := by gcongr
    _ = c*h*(c+1)^(h-1)*(x+1)^(h-1) := by rw [mul_pow]; ring

theorem weightedTuple_volume_error_with_scale {h : ℕ} (w m : Fin h → ℕ) (L : ℕ)
    (hw : ∀ i, 0 < w i) (hm : ∀ i, 0 < m i) (hL : 0 < L)
    (hprod : ∀ i, w i*m i = L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, h*L ≤ T →
      |((weightedTuple w T).card : ℝ) -
        (T:ℝ)^h/((h.factorial*(∏ i, w i) : ℕ):ℝ)| ≤ C*((T:ℝ)+1)^(h-1) := by
  let c : ℝ := (h+1:ℕ)*L
  let s : ℝ := (h.factorial*(∏ i, w i) : ℕ)
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos h) (Finset.prod_pos (fun i _ => hw i))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨c*h*(c+1)^(h-1)/s, by positivity, fun T hT => ?_⟩
  have hq : h ≤ T/L := (Nat.le_div_iff_mul_le hL).mpr hT
  obtain ⟨hl, hu⟩ := weightedTuple_power_bounds w m L hw hm hL hprod T hq
  have hl' : ((L*(T/L-h):ℕ):ℝ)^h ≤ s*(weightedTuple w T).card := by dsimp [s]; exact_mod_cast hl
  have hu' : s*(weightedTuple w T).card ≤ ((L*(T/L+h):ℕ):ℝ)^h := by dsimp [s]; exact_mod_cast hu
  have hnl : L*(T/L-h) ≤ T := by
    calc L*(T/L-h) ≤ L*(T/L) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
         _ ≤ T := Nat.mul_div_le T L
  have hnr : T < L*(T/L-h)+(h+1)*L := by
    have he : L*(T/L-h)+h*L = L*(T/L) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_comm h L,
        Nat.sub_add_cancel (Nat.mul_le_mul_left L hq)]
    have hr := Nat.mod_lt T hL
    have ht := Nat.mod_add_div T L
    nlinarith
  have hup : L*(T/L+h) ≤ T+(h+1)*L := by
    have ht := Nat.mul_div_le T L
    nlinarith
  have hdown : T ≤ L*(T/L+h)+(h+1)*L := by
    have ht := Nat.mod_add_div T L
    have hr := Nat.mod_lt T hL
    nlinarith
  have hnl' : ((L*(T/L-h):ℕ):ℝ) ≤ (T:ℝ) := by exact_mod_cast hnl
  have hnr' : (T:ℝ) < ((L*(T/L-h):ℕ):ℝ)+c := by dsimp [c]; exact_mod_cast hnr
  have hup' : ((L*(T/L+h):ℕ):ℝ) ≤ (T:ℝ)+c := by dsimp [c]; exact_mod_cast hup
  have hdown' : (T:ℝ) ≤ ((L*(T/L+h):ℕ):ℝ)+c := by dsimp [c]; exact_mod_cast hdown
  have hdl : |((L*(T/L-h):ℕ):ℝ)-(T:ℝ)| ≤ c := by
    apply abs_le.mpr
    constructor <;> linarith
  have hdu : |((L*(T/L+h):ℕ):ℝ)-(T:ℝ)| ≤ c := by
    apply abs_le.mpr
    constructor <;> linarith
  have el := nearby_power_error h (Nat.cast_nonneg T) (Nat.cast_nonneg _) hc hdl
  have eu := nearby_power_error h (Nat.cast_nonneg T) (Nat.cast_nonneg _) hc hdu
  have he : |s*(weightedTuple w T).card-(T:ℝ)^h| ≤
      c*h*(c+1)^(h-1)*((T:ℝ)+1)^(h-1) := by
    apply abs_le.mpr
    have hel := (abs_le.mp el).1
    have heu := (abs_le.mp eu).2
    constructor <;> linarith
  change |(weightedTuple w T).card-(T:ℝ)^h/s| ≤ _
  calc
    |(weightedTuple w T).card-(T:ℝ)^h/s| =
        |s*(weightedTuple w T).card-(T:ℝ)^h|/s := by
      rw [← abs_of_pos hs, ← abs_div]
      congr 1
      rw [abs_of_pos hs]
      field_simp
    _ ≤ (c*h*(c+1)^(h-1)*((T:ℝ)+1)^(h-1))/s :=
      div_le_div_of_nonneg_right he hs.le
    _ = _ := by ring

theorem weightedTuple_volume_error {h : ℕ} (w : Fin h → ℕ) (hw : ∀ i, 0 < w i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |((weightedTuple w T).card : ℝ) -
        (T:ℝ)^h/((h.factorial*(∏ i, w i) : ℕ):ℝ)| ≤ C*((T:ℝ)+1)^(h-1) := by
  classical
  let L := ∏ i, w i
  let m := fun i => ∏ j ∈ Finset.univ.erase i, w j
  have hL : 0 < L := Finset.prod_pos (fun i _ => hw i)
  have hm : ∀ i, 0 < m i := fun _ => Finset.prod_pos (fun i _ => hw i)
  have hprod : ∀ i, w i*m i = L := fun i =>
    Finset.mul_prod_erase _ _ (Finset.mem_univ i)
  obtain ⟨C, hC, herror⟩ := weightedTuple_volume_error_with_scale w m L hw hm hL hprod
  let e := fun T : ℕ => |((weightedTuple w T).card : ℝ) -
    (T:ℝ)^h/((h.factorial*(∏ i, w i) : ℕ):ℝ)|
  let S := ∑ T ∈ Finset.range (h*L), e T
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C+S, by linarith, fun T => ?_⟩
  by_cases ht : h*L ≤ T
  · exact (herror T ht).trans (mul_le_mul_of_nonneg_right (by linarith)
      (by positivity))
  · have he : e T ≤ S := Finset.single_le_sum (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega))
    have hfactor : 1 ≤ ((T:ℝ)+1)^(h-1) := one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) T; linarith)
    change e T ≤ _
    calc e T ≤ C+S := by linarith
         _ ≤ (C+S)*((T:ℝ)+1)^(h-1) := le_mul_of_one_le_right (by linarith) hfactor

noncomputable def shiftedTupleCount {h : ℕ} (w : Fin h → ℕ) (e T : ℕ) : ℕ :=
  if e ≤ T then (weightedTuple w (T-e)).card else 0

theorem shiftedTuple_volume_error {h : ℕ} (w : Fin h → ℕ) (hw : ∀ i, 0 < w i)
    (e : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |(shiftedTupleCount w e T : ℝ) -
        (T:ℝ)^h/((h.factorial*(∏ i, w i) : ℕ):ℝ)| ≤ C*((T:ℝ)+1)^(h-1) := by
  obtain ⟨C, hC, herror⟩ := weightedTuple_volume_error w hw
  let s : ℝ := (h.factorial*(∏ i, w i) : ℕ)
  let B : ℝ := (e:ℝ)*h*((e:ℝ)+1)^(h-1)/s
  have hs : 0 < s := by
    dsimp [s]
    exact_mod_cast Nat.mul_pos (Nat.factorial_pos h) (Finset.prod_pos (fun i _ => hw i))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨C+B+(e:ℝ)^h/s, by positivity, fun T => ?_⟩
  have ht0 : (0:ℝ) ≤ T := Nat.cast_nonneg _
  have hf : 1 ≤ ((T:ℝ)+1)^(h-1) := one_le_pow₀ (by linarith)
  by_cases heT : e ≤ T
  · rw [shiftedTupleCount, ite_eq_left heT]
    have hnat : ((T-e:ℕ):ℝ) ≤ (T:ℝ) := by exact_mod_cast Nat.sub_le T e
    have hdiff : |((T-e:ℕ):ℝ)-(T:ℝ)| ≤ (e:ℝ) := by
      rw [Nat.cast_sub heT]
      have : (T:ℝ)-(e:ℝ)-(T:ℝ) = -(e:ℝ) := by ring
      rw [this, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
    have he := nearby_power_error h (Nat.cast_nonneg T) (Nat.cast_nonneg _)
      (Nat.cast_nonneg e) hdiff
    have he' : |((T-e:ℕ):ℝ)^h/s-(T:ℝ)^h/s| ≤ B*((T:ℝ)+1)^(h-1) := by
      rw [← sub_div, abs_div, abs_of_pos hs]
      calc
        |((T-e:ℕ):ℝ)^h-(T:ℝ)^h|/s ≤
            ((e:ℝ)*h*((e:ℝ)+1)^(h-1)*((T:ℝ)+1)^(h-1))/s :=
          div_le_div_of_nonneg_right he hs.le
        _ = _ := by dsimp [B]; ring
    have hbase : |((weightedTuple w (T-e)).card : ℝ)-((T-e:ℕ):ℝ)^h/s| ≤
        C*((T:ℝ)+1)^(h-1) := by
      exact (herror (T-e)).trans (by gcongr)
    change |((weightedTuple w (T-e)).card : ℝ)-(T:ℝ)^h/s| ≤ _
    calc
      _ ≤ |((weightedTuple w (T-e)).card : ℝ)-((T-e:ℕ):ℝ)^h/s| +
          |((T-e:ℕ):ℝ)^h/s-(T:ℝ)^h/s| := abs_sub_le _ _ _
      _ ≤ (C+B)*((T:ℝ)+1)^(h-1) := by nlinarith [hbase, he']
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  · rw [shiftedTupleCount, ite_eq_right heT, Nat.cast_zero, zero_sub, abs_neg,
      abs_of_nonneg (by positivity)]
    change (T:ℝ)^h/s ≤ _
    have he : (T:ℝ) ≤ (e:ℝ) := by exact_mod_cast (by omega : T ≤ e)
    calc
      (T:ℝ)^h/s ≤ (e:ℝ)^h/s := by gcongr
      _ ≤ C+B+(e:ℝ)^h/s := by linarith
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hf

def PairSector (u v : ℕ) := Fin u ⊕ Fin v

instance (u v : ℕ) : Fintype (PairSector u v) := inferInstanceAs (Fintype (Fin u ⊕ Fin v))
instance (u v : ℕ) : DecidableEq (PairSector u v) := inferInstanceAs (DecidableEq (Fin u ⊕ Fin v))

def sectorPoint {u v : ℕ} (c : PairSector u v) (x : ℕ) : ℕ × ℕ :=
  match c with
  | Sum.inl r => (r, x)
  | Sum.inr r => (u+x, r)

theorem sectorPoint_normal {u v : ℕ} (c : PairSector u v) (x : ℕ) :
    (sectorPoint c x).1 < u ∨ (sectorPoint c x).2 < v := by
  cases c with
  | inl r => exact Or.inl r.isLt
  | inr r => exact Or.inr r.isLt

theorem sectorPoint_injective {u v : ℕ} :
    Function.Injective (fun p : PairSector u v × ℕ => sectorPoint p.1 p.2) := by
  rintro ⟨c,x⟩ ⟨d,y⟩ he
  cases c with
  | inl r =>
    cases d with
    | inl s =>
      simp only [sectorPoint, Prod.mk.injEq] at he
      exact Prod.ext (congrArg Sum.inl (Fin.ext he.1)) he.2
    | inr s =>
      have he' := congrArg Prod.fst he
      dsimp [sectorPoint] at he'
      have := r.isLt
      omega
  | inr r =>
    cases d with
    | inl s =>
      have he' := congrArg Prod.fst he
      dsimp [sectorPoint] at he'
      have := s.isLt
      omega
    | inr s =>
      simp only [sectorPoint, Prod.mk.injEq] at he
      exact Prod.ext (congrArg Sum.inr (Fin.ext he.2)) (Nat.add_left_cancel he.1)

theorem sectorPoint_surjective {u v : ℕ} (p : ℕ × ℕ)
    (hp : p.1 < u ∨ p.2 < v) :
    ∃ c : PairSector u v, ∃ x : ℕ, sectorPoint c x = p := by
  by_cases h : p.1 < u
  · exact ⟨Sum.inl ⟨p.1,h⟩, p.2, rfl⟩
  · have h' : p.2 < v := hp.resolve_left h
    refine ⟨Sum.inr ⟨p.2,h'⟩, p.1-u, ?_⟩
    exact Prod.ext (by dsimp [sectorPoint]; omega) rfl

def sectorWeight (A B : ℕ) {u v : ℕ} (c : PairSector u v) : ℕ :=
  match c with
  | Sum.inl _ => B
  | Sum.inr _ => A

def sectorShift (A B : ℕ) {u v : ℕ} (c : PairSector u v) : ℕ :=
  match c with
  | Sum.inl r => A*r
  | Sum.inr r => A*u+B*r

theorem sector_weight_identity (A B : ℕ) {u v : ℕ} (c : PairSector u v) (x : ℕ) :
    A*(sectorPoint c x).1+B*(sectorPoint c x).2 =
      sectorShift A B c + sectorWeight A B c*x := by
  cases c with
  | inl r => rfl
  | inr r => simp only [sectorPoint, sectorShift, sectorWeight]; ring

theorem sectorWeight_pos {A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    {u v : ℕ} (c : PairSector u v) : 0 < sectorWeight A B c := by
  cases c <;> assumption

def normalPairTuples {h : ℕ} (A B : ℕ) (u v : Fin h → ℕ) (T : ℕ) :
    Finset (Fin h → ℕ × ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (T+1) ×ˢ Finset.range (T+1))).filter
    (fun p => (∀ i, (p i).1 < u i ∨ (p i).2 < v i) ∧
      ∑ i, (A*(p i).1+B*(p i).2) ≤ T)

theorem mem_normalPairTuples {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) (T : ℕ) (p : Fin h → ℕ × ℕ) :
    p ∈ normalPairTuples A B u v T ↔
      (∀ i, (p i).1 < u i ∨ (p i).2 < v i) ∧
        ∑ i, (A*(p i).1+B*(p i).2) ≤ T := by
  classical
  simp only [normalPairTuples, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro hp
    refine ⟨fun i => ?_, hp⟩
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      Nat.zero_le (A*(p j).1+B*(p j).2)) (Finset.mem_univ i)
    have ha : (p i).1 ≤ A*(p i).1 := by nlinarith
    have hb : (p i).2 ≤ B*(p i).2 := by nlinarith
    constructor <;> omega

noncomputable def sectorTuples {h : ℕ} (A B : ℕ) (u v : Fin h → ℕ) (T : ℕ) :
    Finset (Σ _c : (i : Fin h) → PairSector (u i) (v i), Fin h → ℕ) :=
  Finset.univ.sigma (fun c =>
    if ∑ i, sectorShift A B (c i) ≤ T then
      weightedTuple (fun i => sectorWeight A B (c i)) (T-∑ i, sectorShift A B (c i))
    else ∅)

theorem mem_sectorTuples {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) (T : ℕ)
    (p : Σ _c : (i : Fin h) → PairSector (u i) (v i), Fin h → ℕ) :
    p ∈ sectorTuples A B u v T ↔
      (∑ i, sectorShift A B (p.1 i)) +
        (∑ i, sectorWeight A B (p.1 i)*p.2 i) ≤ T := by
  classical
  simp only [sectorTuples, Finset.mem_sigma, Finset.mem_univ, true_and]
  split_ifs with ht
  · rw [mem_weightedTuple _ (fun _ => sectorWeight_pos hA hB _)]; omega
  · simp only [Finset.notMem_empty, false_iff]; omega

theorem card_normalPairTuples {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) (T : ℕ) :
    (normalPairTuples A B u v T).card =
      ∑ c : (i : Fin h) → PairSector (u i) (v i),
        shiftedTupleCount (fun i => sectorWeight A B (c i))
          (∑ i, sectorShift A B (c i)) T := by
  classical
  have hc : (sectorTuples A B u v T).card = (normalPairTuples A B u v T).card := by
    apply Finset.card_bij (fun p _ => fun i => sectorPoint (p.1 i) (p.2 i))
    · intro p hp
      apply (mem_normalPairTuples hA hB u v T _).mpr
      refine ⟨fun i => sectorPoint_normal _ _, ?_⟩
      simp_rw [sector_weight_identity, Finset.sum_add_distrib]
      exact (mem_sectorTuples hA hB u v T p).mp hp
    · intro p _ q _ hpq
      have he (i : Fin h) : (p.1 i, p.2 i) = (q.1 i, q.2 i) :=
        sectorPoint_injective (congrFun hpq i)
      have hc : p.1 = q.1 := funext (fun i => congrArg Prod.fst (he i))
      have hx : p.2 = q.2 := funext (fun i => congrArg Prod.snd (he i))
      cases p; cases q; dsimp at hc hx; cases hc; cases hx; rfl
    · intro p hp
      obtain ⟨hn, ht⟩ := (mem_normalPairTuples hA hB u v T p).mp hp
      choose c x hx using (fun i => sectorPoint_surjective (p i) (hn i))
      refine ⟨⟨c,x⟩, (mem_sectorTuples hA hB u v T _).mpr ?_, funext hx⟩
      simpa only [← Finset.sum_add_distrib, ← sector_weight_identity, hx] using ht
  rw [← hc]
  simp only [sectorTuples, Finset.card_sigma, shiftedTupleCount]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp

theorem normalPairTuples_volume_error {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |((normalPairTuples A B u v T).card : ℝ) -
        (T:ℝ)^h * (∑ c : (i : Fin h) → PairSector (u i) (v i),
          1 / ((h.factorial * ∏ i, sectorWeight A B (c i) : ℕ):ℝ))| ≤
        C*((T:ℝ)+1)^(h-1) := by
  classical
  have he (c : (i : Fin h) → PairSector (u i) (v i)) :=
    shiftedTuple_volume_error (fun i => sectorWeight A B (c i))
      (fun _ => sectorWeight_pos hA hB _) (∑ i, sectorShift A B (c i))
  choose C hC herr using he
  refine ⟨∑ c, C c, Finset.sum_nonneg (fun c _ => hC c), fun T => ?_⟩
  rw [card_normalPairTuples hA hB, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c, |(shiftedTupleCount (fun i => sectorWeight A B (c i))
        (∑ i, sectorShift A B (c i)) T : ℝ) -
        (T:ℝ)^h*(1 / ((h.factorial * ∏ i, sectorWeight A B (c i) : ℕ):ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c, C c*((T:ℝ)+1)^(h-1) := Finset.sum_le_sum (fun c _ => by
      simpa only [mul_one_div] using herr c T)
    _ = _ := by rw [Finset.sum_mul]

private theorem sector_reciprocal_sum (A B u v : ℕ) :
    (∑ c : PairSector u v, 1/(sectorWeight A B c : ℝ)) = (u:ℝ)/B+(v:ℝ)/A := by
  change (∑ c : Fin u ⊕ Fin v, 1/(sectorWeight A B c : ℝ)) = _
  rw [Fintype.sum_sum_type]
  simp [sectorWeight, nsmul_eq_mul, div_eq_mul_inv]

private theorem sector_coefficient {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) :
    (∑ c : (i : Fin h) → PairSector (u i) (v i),
      1 / ((h.factorial * ∏ i, sectorWeight A B (c i) : ℕ):ℝ)) =
      (∏ i, ((u i:ℝ)*A+(v i:ℝ)*B)) /
        ((h.factorial:ℝ)*(A:ℝ)^h*(B:ℝ)^h) := by
  classical
  have ha : (A:ℝ) ≠ 0 := by positivity
  have hb : (B:ℝ) ≠ 0 := by positivity
  calc
    _ = (∑ c : (i : Fin h) → PairSector (u i) (v i),
        ∏ i, 1/(sectorWeight A B (c i) : ℝ))/(h.factorial:ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro c _
      simp [Nat.cast_mul, Nat.cast_prod, div_eq_mul_inv, Finset.prod_inv_distrib, mul_comm]
    _ = (∏ i, ∑ c : PairSector (u i) (v i),
        1/(sectorWeight A B c : ℝ))/(h.factorial:ℝ) := by
      rw [Fintype.prod_sum]
    _ = (∏ i, ((u i:ℝ)*A+(v i:ℝ)*B)/((A:ℝ)*B))/(h.factorial:ℝ) := by
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      rw [sector_reciprocal_sum]
      field_simp
    _ = _ := by
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
      rw [div_div]
      congr 1
      ring

theorem normalPairTuples_hilbert_error {h A B : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : Fin h → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |((normalPairTuples A B u v T).card : ℝ) -
        (∏ i, ((u i:ℝ)*A+(v i:ℝ)*B)) /
          ((h.factorial:ℝ)*(A:ℝ)^h*(B:ℝ)^h)*(T:ℝ)^h| ≤
        C*((T:ℝ)+1)^(h-1) := by
  obtain ⟨C,hC,herror⟩ := normalPairTuples_volume_error hA hB u v
  refine ⟨C,hC,fun T => ?_⟩
  simpa only [sector_coefficient hA hB, mul_comm] using herror T

def ambientPairTuples (h A B k T : ℕ) : Finset (Fin (h+1) → ℕ × ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (T+1) ×ˢ Finset.range (T+1))).filter
    (fun p => (∀ i : Fin h, (p i.succ).1 < k ∨ (p i.succ).2 = 0) ∧
      ∑ i, (A*(p i).1+B*(p i).2) ≤ T)

theorem mem_ambientPairTuples {h A B k T : ℕ} (hA : 0 < A) (hB : 0 < B)
    (p : Fin (h+1) → ℕ × ℕ) :
    p ∈ ambientPairTuples h A B k T ↔
      (∀ i : Fin h, (p i.succ).1 < k ∨ (p i.succ).2 = 0) ∧
        ∑ i, (A*(p i).1+B*(p i).2) ≤ T := by
  classical
  simp only [ambientPairTuples, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro hp
    refine ⟨fun i => ?_, hp⟩
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      Nat.zero_le (A*(p j).1+B*(p j).2)) (Finset.mem_univ i)
    have ha : (p i).1 ≤ A*(p i).1 := by nlinarith
    have hb : (p i).2 ≤ B*(p i).2 := by nlinarith
    constructor <;> omega

def pairTranslate {h : ℕ} (u v : ℕ) (p : Fin (h+1) → ℕ × ℕ) :
    Fin (h+1) → ℕ × ℕ :=
  Fin.cons ((p 0).1+u, (p 0).2+v) (fun i => p i.succ)

theorem pairTranslate_weight {h : ℕ} (A B u v : ℕ) (p : Fin (h+1) → ℕ × ℕ) :
    ∑ i, (A*(pairTranslate u v p i).1+B*(pairTranslate u v p i).2) =
      (∑ i, (A*(p i).1+B*(p i).2)) + A*u+B*v := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [pairTranslate, Fin.cons_zero, Fin.cons_succ]
  ring

theorem pairTranslate_injective {h : ℕ} (u v : ℕ) :
    Function.Injective (pairTranslate (h := h) u v) := by
  intro p q he
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have h0 := congrFun he 0
    simp only [pairTranslate, Fin.cons_zero, Prod.mk.injEq] at h0
    exact Prod.ext (Nat.add_right_cancel h0.1) (Nat.add_right_cancel h0.2)
  · exact congrFun he j.succ

theorem ambientPairTuples_card_cut {h A B k T : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : ℕ) :
    (ambientPairTuples h A B k T).card =
      (normalPairTuples A B (Fin.cons u (fun _ : Fin h => k))
        (Fin.cons v (fun _ : Fin h => 1)) T).card +
      if A*u+B*v ≤ T then (ambientPairTuples h A B k (T-(A*u+B*v))).card else 0 := by
  classical
  let s := ambientPairTuples h A B k T
  let P := fun p : Fin (h+1) → ℕ × ℕ => u ≤ (p 0).1 ∧ v ≤ (p 0).2
  have hn : s.filter (fun p => ¬ P p) =
      normalPairTuples A B (Fin.cons u (fun _ : Fin h => k))
        (Fin.cons v (fun _ : Fin h => 1)) T := by
    ext p
    rw [Finset.mem_filter, mem_normalPairTuples hA hB]
    change (p ∈ ambientPairTuples h A B k T ∧ _) ↔ _
    rw [mem_ambientPairTuples hA hB]
    simp only [Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Nat.lt_one_iff]
    dsimp [P]
    simp only [not_and_or, not_le]
    tauto
  have hr : (s.filter P).card =
      if A*u+B*v ≤ T then (ambientPairTuples h A B k (T-(A*u+B*v))).card else 0 := by
    by_cases he : A*u+B*v ≤ T
    · rw [ite_eq_left he]
      symm
      apply Finset.card_bij (fun p _ => pairTranslate u v p)
      · intro p hp
        obtain ⟨hpN,hpT⟩ := (mem_ambientPairTuples hA hB p).mp hp
        apply Finset.mem_filter.mpr
        constructor
        · apply (mem_ambientPairTuples hA hB _).mpr
          refine ⟨by simpa only [pairTranslate, Fin.cons_succ] using hpN, ?_⟩
          rw [pairTranslate_weight]
          omega
        · simp only [P, pairTranslate, Fin.cons_zero]
          exact ⟨Nat.le_add_left _ _, Nat.le_add_left _ _⟩
      · intro p _ q _ heq
        exact pairTranslate_injective u v heq
      · intro p hp
        obtain ⟨hpS,hpP⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpN,hpT⟩ := (mem_ambientPairTuples hA hB p).mp hpS
        let q : Fin (h+1) → ℕ × ℕ := Fin.cons ((p 0).1-u,(p 0).2-v) (fun i : Fin h => p i.succ)
        have hqp : pairTranslate u v q = p := by
          funext i
          refine Fin.cases ?_ (fun _ => rfl) i
          exact Prod.ext (Nat.sub_add_cancel hpP.1) (Nat.sub_add_cancel hpP.2)
        refine ⟨q, (mem_ambientPairTuples hA hB q).mpr ⟨?_,?_⟩, hqp⟩
        · simpa only [q, Fin.cons_succ] using hpN
        · have hw := pairTranslate_weight A B u v q
          rw [hqp] at hw
          omega
    · rw [ite_eq_right he, Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hpS,hpP⟩ := Finset.mem_filter.mp hp
      obtain ⟨_,hpT⟩ := (mem_ambientPairTuples hA hB p).mp hpS
      have h0 := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
        Nat.zero_le (A*(p i).1+B*(p i).2)) (Finset.mem_univ (0 : Fin (h+1)))
      have hA' := Nat.mul_le_mul_left A hpP.1
      have hB' := Nat.mul_le_mul_left B hpP.2
      omega
  have hc := Finset.card_filter_add_card_filter_not (s := s) P
  rw [hn, hr] at hc
  exact hc.symm.trans (Nat.add_comm _ _)

theorem pairFilteredDifference_hilbert_error {h A B k : ℕ} (hA : 0 < A) (hB : 0 < B)
    (u v : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |((ambientPairTuples h A B k T).card -
          (if A*u+B*v ≤ T then (ambientPairTuples h A B k (T-(A*u+B*v))).card else 0) : ℝ) -
        ((A*u+B*v : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^h /
          (((h+1).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))*(T:ℝ)^(h+1)| ≤
        C*((T:ℝ)+1)^h := by
  obtain ⟨C,hC,herror⟩ := normalPairTuples_hilbert_error hA hB
    (Fin.cons u (fun _ : Fin h => k)) (Fin.cons v (fun _ : Fin h => 1))
  refine ⟨C,hC,fun T => ?_⟩
  have hc := ambientPairTuples_card_cut (h := h) (k := k) (T := T) hA hB u v
  have hc' : ((ambientPairTuples h A B k T).card:ℝ) -
      (if A*u+B*v ≤ T then ((ambientPairTuples h A B k (T-(A*u+B*v))).card:ℝ) else 0) =
      ((normalPairTuples A B (Fin.cons u (fun _ : Fin h => k))
        (Fin.cons v (fun _ : Fin h => 1)) T).card : ℝ) := by
    have hh := congrArg (Nat.cast : ℕ → ℝ) hc
    push_cast at hh
    linarith
  simp only [Nat.cast_ite, Nat.cast_zero]
  rw [hc']
  have hp : (∏ i : Fin (h+1),
      (((Fin.cons (α := fun _ : Fin (h+1) => ℕ) u (fun _ : Fin h => k) i) : ℝ)*A+
        ((Fin.cons (α := fun _ : Fin (h+1) => ℕ) v (fun _ : Fin h => 1) i) : ℝ)*B)) =
      ((A*u+B*v:ℕ):ℝ)*((k*A+B:ℕ):ℝ)^h := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, Nat.cast_one, one_mul,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_mul]
    ring
  simpa only [hp, Nat.add_sub_cancel] using herror T

end QuarticPowerFree

end OAI
