import OAI.NumberTheory.PowerFree.WeightedHypersurfaces

namespace OAI


namespace QuarticPowerFree
open MvPolynomial

noncomputable def tripleFinsuppEquiv : (Fin 3 →₀ ℕ) ≃ NatTriple :=
  Finsupp.equivFunOnFinite.trans
    { toFun := fun f => (f 0, f 1, f 2)
      invFun := fun x => ![x.1, x.2.1, x.2.2]
      left_inv := by intro f; funext i; fin_cases i <;> rfl
      right_inv := by rintro ⟨x,y,z⟩; rfl }

def tripleWeights (a b c : ℕ) : Fin 3 → ℕ := ![a,b,c]

theorem weight_eq_tripleWeight (a b c : ℕ) (m : Fin 3 →₀ ℕ) :
    Finsupp.weight (tripleWeights a b c) m = tripleWeight a b c (tripleFinsuppEquiv m) := by
  rw [Finsupp.weight_eq_sum]
  simp [Fin.sum_univ_succ, tripleWeights, tripleWeight, tripleFinsuppEquiv, mul_comm, add_assoc]

theorem tripleWeights_ne_zero {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∀ i, tripleWeights a b c i ≠ 0 := by
  intro i
  fin_cases i <;> simp [tripleWeights, ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]

theorem weightedExponents_card {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (T : ℕ) :
    Nat.card {m : Fin 3 →₀ ℕ // Finsupp.weight (tripleWeights a b c) m ≤ T} =
      (weightedTriples a b c T).card := by
  let e : {m : Fin 3 →₀ ℕ // Finsupp.weight (tripleWeights a b c) m ≤ T} ≃
      {x : NatTriple // x ∈ weightedTriples a b c T} :=
    tripleFinsuppEquiv.subtypeEquiv (by intro m; rw [mem_weightedTriples ha hb hc, weight_eq_tripleWeight])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

theorem weighted_hypersurface_normal_card {K : Type*} [Field K]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) (m : NatTriple)
    (hm : tripleWeight a b c m = weightedTotalDegree (tripleWeights a b c) F)
    (T : ℕ) (hT : weightedTotalDegree (tripleWeights a b c) F ≤ T) :
    Module.finrank K ((weightedSpace (tripleWeights a b c) T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {F})).toLinearMap) =
      (weightedNormal a b c m T).card := by
  have hh := weighted_hypersurface_finrank (tripleWeights a b c)
    (tripleWeights_ne_zero ha hb hc) F hF T hT
  rw [weightedExponents_card ha hb hc, weightedExponents_card ha hb hc] at hh
  have hn := weightedNormal_card_add ha hb hc m T (hm ▸ hT)
  rw [hm] at hn
  omega

theorem surface_hilbert_error {K : Type*} [Field K]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, weightedTotalDegree (tripleWeights a b c) F ≤ T →
      |(Module.finrank K ((weightedSpace (tripleWeights a b c) T).map
        (Ideal.Quotient.mkₐ K (Ideal.span {F})).toLinearMap) : ℝ) -
        ((weightedTotalDegree (tripleWeights a b c) F : ℕ) : ℝ)*(T:ℝ)^2/(2*(a*b*c : ℕ))|
          ≤ C*((T:ℝ)+1) := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_mem_eq_sup F.support (support_nonempty.mpr hF)
    (Finsupp.weight (tripleWeights a b c))
  have hm' : tripleWeight a b c (tripleFinsuppEquiv m) =
      weightedTotalDegree (tripleWeights a b c) F := by
    rw [← weight_eq_tripleWeight]
    exact hm.symm
  refine ⟨normalErrorConst a b c (tripleFinsuppEquiv m), by unfold normalErrorConst; positivity,
    fun T hT => ?_⟩
  rw [weighted_hypersurface_normal_card ha hb hc F hF _ hm' T hT]
  rw [← hm']
  exact weightedNormal_volume_error ha hb hc _ T (hm' ▸ hT)

end QuarticPowerFree


open Polynomial Matrix
open scoped BigOperators

namespace QuarticPowerFree.ComplexValues

theorem denominator_value_dvd_resultant (A B : ℤ[X])
    (hB : B.natDegree ≠ 0) {s : ℤ} (hs : B.eval s ∣ A.eval s) :
    B.eval s ∣ A.resultant B := by
  obtain ⟨u, v, _, _, h⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant A B
    le_rfl le_rfl (Or.inr hB)
  have he := congrArg (Polynomial.eval s) h
  simp only [eval_add, eval_mul, eval_C] at he
  rw [← he]
  exact dvd_add (dvd_mul_of_dvd_left hs _) (dvd_mul_right _ _)

theorem card_fibre_eval_le (B : ℤ[X]) (hB : 0 < B.natDegree)
    (S : Finset ℤ) (q : ℤ) :
    (S.filter (fun s => B.eval s = q)).card ≤ B.natDegree := by
  have hnz : B - C q ≠ 0 := by
    intro hz
    have hh := congrArg Polynomial.natDegree hz
    rw [natDegree_sub_C, natDegree_zero] at hh
    omega
  have hh : (S.filter (fun s => B.eval s = q)).val ⊆ (B - C q).roots := by
    intro s hs
    have he := (Finset.mem_filter.mp hs).2
    exact Polynomial.mem_roots hnz |>.mpr (by simp [he])
  simpa only [natDegree_sub_C] using Polynomial.card_le_degree_of_subset_roots hh

def signedDivisors (r : ℤ) : Finset ℤ :=
  (r.natAbs.divisors.image (fun n : ℕ => (n : ℤ))) ∪
    (r.natAbs.divisors.image (fun n : ℕ => -(n : ℤ)))

theorem mem_signedDivisors {r q : ℤ} (hr : r ≠ 0) (hq : q ∣ r) :
    q ∈ signedDivisors r := by
  have hn : q.natAbs ∈ r.natAbs.divisors :=
    Nat.mem_divisors.mpr ⟨Int.natAbs_dvd_natAbs.mpr hq, Int.natAbs_ne_zero.mpr hr⟩
  rcases le_total 0 q with h | h
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨_, hn, by simp [abs_of_nonneg h]⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨_, hn, by simp [abs_of_nonpos h]⟩)

theorem card_signedDivisors_le (r : ℤ) :
    (signedDivisors r).card ≤ 2 * r.natAbs.divisors.card := by
  exact (Finset.card_union_le _ _).trans (by
    have h₁ := Finset.card_image_le (s := r.natAbs.divisors) (f := fun n => (n : ℤ))
    have h₂ := Finset.card_image_le (s := r.natAbs.divisors) (f := fun n => -(n : ℤ))
    omega)

theorem rational_values_card_le_divisors (A B : ℤ[X])
    (hB : 0 < B.natDegree) (hres : A.resultant B ≠ 0) (S : Finset ℤ) :
    (S.filter (fun s => B.eval s ∣ A.eval s)).card ≤
      2 * B.natDegree * (A.resultant B).natAbs.divisors.card := by
  classical
  let T := S.filter (fun s => B.eval s ∣ A.eval s)
  have himage : T.image B.eval ⊆ signedDivisors (A.resultant B) := by
    intro q hq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
    exact mem_signedDivisors hres (denominator_value_dvd_resultant A B
      (Nat.ne_zero_of_lt hB) (Finset.mem_filter.mp hs).2)
  calc
    T.card = ∑ q ∈ T.image B.eval, (T.filter (fun s => B.eval s = q)).card :=
      (Finset.card_eq_sum_card_image B.eval T)
    _ ≤ ∑ q ∈ T.image B.eval, B.natDegree := by
      apply Finset.sum_le_sum
      intro q _
      exact card_fibre_eval_le B hB T q
    _ = (T.image B.eval).card * B.natDegree := by simp
    _ ≤ (signedDivisors (A.resultant B)).card * B.natDegree :=
      Nat.mul_le_mul_right _ (Finset.card_le_card himage)
    _ ≤ (2 * (A.resultant B).natAbs.divisors.card) * B.natDegree :=
      Nat.mul_le_mul_right _ (card_signedDivisors_le _)
    _ = 2 * B.natDegree * (A.resultant B).natAbs.divisors.card := by ring

theorem rational_function_interpolation_cross {F : Type*} [Field F]
    (A B A₁ B₁ : F[X]) (S : Finset F)
    (hA : A₁.natDegree ≤ A.natDegree) (hB : B₁.natDegree ≤ B.natDegree)
    (hcard : A.natDegree + B.natDegree < S.card)
    (heval : ∀ s ∈ S, A₁.eval s * B.eval s = A.eval s * B₁.eval s) :
    A₁ * B = A * B₁ := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S
  · intro s hs
    simpa only [eval_sub, eval_mul, sub_eq_zero] using heval s hs
  · have hd := Polynomial.natDegree_sub_le (A₁ * B) (A * B₁)
    have h₁ := Polynomial.natDegree_mul_le (p := A₁) (q := B)
    have h₂ := Polynomial.natDegree_mul_le (p := A) (q := B₁)
    exact lt_of_le_of_lt (hd.trans (max_le (by omega) (by omega))) hcard

theorem rational_function_interpolation_unique {F : Type*} [Field F]
    (A B A₁ B₁ : F[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (hB : B₁.natDegree ≤ B.natDegree) (heq : A₁ * B = A * B₁) :
    ∃ c : F, A₁ = C c * A ∧ B₁ = C c * B := by
  have hdvd : B ∣ B₁ := hcop.symm.dvd_of_dvd_mul_left (heq ▸ dvd_mul_left B A₁)
  obtain ⟨Q, hQ⟩ := hdvd
  by_cases hQz : Q = 0
  · refine ⟨0, ?_, ?_⟩
    · have hz : A₁ = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_right hBn
        rw [heq, hQ, hQz, mul_zero, mul_zero]
      simpa using hz
    · simp [hQ, hQz]
  · have hdeg : Q.natDegree = 0 := by
      rw [hQ, Polynomial.natDegree_mul hBn hQz] at hB
      omega
    have hQc : Q = C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg
    refine ⟨Q.coeff 0, ?_, ?_⟩
    · apply mul_right_cancel₀ hBn
      conv_lhs => rw [heq, hQ, hQc]
      ring
    · calc B₁ = B * Q := hQ
           _ = B * C (Q.coeff 0) := congrArg (B * ·) hQc
           _ = C (Q.coeff 0) * B := mul_comm _ _

def interpolationRow {R ι : Type*} [CommRing R] {a b : ℕ}
    (s v : ι → R) (i : Option ι) : Fin (a + 1) ⊕ Fin (b + 1) → R :=
  match i with
  | none => Pi.single (Sum.inr ⟨b, Nat.lt_succ_self b⟩) 1
  | some t => Sum.elim (fun j => s t ^ j.val) (fun j => -(v t * s t ^ j.val))

theorem interpolationRow_some_dot {R ι : Type*} [CommRing R] [DecidableEq R] {a b : ℕ}
    (s v : ι → R) (t : ι) (c : Fin (a + 1) ⊕ Fin (b + 1) → R) :
    interpolationRow s v (some t) ⬝ᵥ c =
      (Polynomial.ofFn (a + 1) (fun j => c (Sum.inl j))).eval (s t) -
      v t * (Polynomial.ofFn (b + 1) (fun j => c (Sum.inr j))).eval (s t) := by
  classical
  simp only [interpolationRow, dotProduct, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.mul_sum,
    neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  congr 1
  · exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  · congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)

theorem interpolationRow_none_dot {R ι : Type*} [CommRing R] {a b : ℕ}
    (s v : ι → R) (c : Fin (a + 1) ⊕ Fin (b + 1) → R) :
    interpolationRow s v none ⬝ᵥ c = c (Sum.inr ⟨b, Nat.lt_succ_self b⟩) := by
  rw [interpolationRow, single_dotProduct, one_mul]

def interpolationMatrix {R ι : Type*} [CommRing R] {a b : ℕ}
    (s v : ι → R) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι) :
    Matrix (Fin (a + 1) ⊕ Fin (b + 1)) (Fin (a + 1) ⊕ Fin (b + 1)) R :=
  Matrix.of (fun j => interpolationRow s v (e j))

theorem interpolationMatrix_det_ne_zero {F ι : Type*} [Field F] [Fintype ι]
    (A B : F[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (s v : ι → F) (hs : Function.Injective s)
    (hcard : A.natDegree + B.natDegree < Fintype.card ι)
    (heval : ∀ i, A.eval (s i) = v i * B.eval (s i))
    (e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option ι) :
    (interpolationMatrix s v e).det ≠ 0 := by
  classical
  let M := interpolationMatrix s v e
  have hker : ∀ c, M *ᵥ c = 0 → c = 0 := by
    intro c hc
    let P := Polynomial.ofFn (A.natDegree + 1) (fun j => c (Sum.inl j))
    let Q := Polynomial.ofFn (B.natDegree + 1) (fun j => c (Sum.inr j))
    have hpdeg : P.natDegree ≤ A.natDegree := by
      have h := Polynomial.ofFn_natDegree_lt (R := F) (Nat.succ_pos A.natDegree)
        (fun j => c (Sum.inl j))
      exact Nat.le_of_lt_succ h
    have hqdeg : Q.natDegree ≤ B.natDegree := by
      have h := Polynomial.ofFn_natDegree_lt (R := F) (Nat.succ_pos B.natDegree)
        (fun j => c (Sum.inr j))
      exact Nat.le_of_lt_succ h
    have hpeval (i : ι) : P.eval (s i) = v i * Q.eval (s i) := by
      have hh := congrFun hc (e.symm (some i))
      change interpolationRow s v (e (e.symm (some i))) ⬝ᵥ c = 0 at hh
      rw [e.apply_symm_apply, interpolationRow_some_dot] at hh
      exact sub_eq_zero.mp hh
    have hcross : P * B = A * Q := by
      apply rational_function_interpolation_cross A B P Q (Finset.univ.image s) hpdeg hqdeg
      · simpa only [Finset.card_image_of_injective _ hs, Finset.card_univ] using hcard
      · intro x hx
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
        rw [hpeval, heval]
        ring
    obtain ⟨r, hP, hQ⟩ := rational_function_interpolation_unique A B P Q hcop hBn hqdeg hcross
    have hqzero : Q.coeff B.natDegree = 0 := by
      have hh := congrFun hc (e.symm none)
      change interpolationRow s v (e (e.symm none)) ⬝ᵥ c = 0 at hh
      rw [e.apply_symm_apply, interpolationRow_none_dot] at hh
      simpa only [Q, Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_self _)] using hh
    have hr : r = 0 := by
      rw [hQ, Polynomial.coeff_C_mul] at hqzero
      exact (mul_eq_zero.mp hqzero).resolve_right (Polynomial.leadingCoeff_ne_zero.mpr hBn)
    have hpzero : P = 0 := by simp [hP, hr]
    have hqzero' : Q = 0 := by simp [hQ, hr]
    funext j
    rcases j with j | j
    · have hh := congrArg (fun p : F[X] => p.coeff j.val) hpzero
      simpa only [P, Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt, Polynomial.coeff_zero,
        Pi.zero_apply] using hh
    · have hh := congrArg (fun p : F[X] => p.coeff j.val) hqzero'
      simpa only [Q, Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt, Polynomial.coeff_zero,
        Pi.zero_apply] using hh
  have hi : Function.Injective (Matrix.mulVecLin M) :=
    LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hker)
  exact (M.isUnit_iff_isUnit_det.mp (Matrix.mulVec_injective_iff_isUnit.mp hi)).ne_zero

theorem ofFn_map_hom {R S : Type*} [Semiring R] [Semiring S]
    [DecidableEq R] [DecidableEq S] (f : R →+* S) (n : ℕ) (v : Fin n → R) :
    (Polynomial.ofFn n v).map f = Polynomial.ofFn n (fun j => f (v j)) := by
  ext i
  by_cases hi : i < n
  · simp only [Polynomial.coeff_map, Polynomial.ofFn_coeff_eq_val_of_lt _ hi]
  · simp only [Polynomial.coeff_map,
      Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi), map_zero]

theorem interpolationMatrix_map {R S ι : Type*} [CommRing R] [CommRing S]
    {a b : ℕ} (f : R →+* S) (s v : ι → R)
    (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι) :
    (interpolationMatrix s v e).map f =
      interpolationMatrix (fun i => f (s i)) (fun i => f (v i)) e := by
  classical
  ext i j
  change f (interpolationRow s v (e i) j) = _
  change _ = interpolationRow (fun i => f (s i)) (fun i => f (v i)) (e i) j
  rcases h : e i with _ | t
  · simp only [interpolationRow]
    by_cases hj : j = Sum.inr ⟨b, Nat.lt_succ_self b⟩
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hj]
  · rcases j with j | j <;> simp [interpolationRow]

noncomputable def interpolationCramer {ι : Type*} [Fintype ι] {a b : ℕ}
    (s v : ι → ℤ) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι) :
    Fin (a + 1) ⊕ Fin (b + 1) → ℤ := by
  classical
  exact (interpolationMatrix s v e).cramer (fun j => if e j = none then 1 else 0)

theorem rational_interpolation_integral_pair {ι : Type*} [Fintype ι]
    (A B : ℂ[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (s v : ι → ℤ) (hs : Function.Injective s)
    (hcard : A.natDegree + B.natDegree < Fintype.card ι)
    (heval : ∀ i, A.eval (s i : ℂ) = (v i : ℂ) * B.eval (s i : ℂ))
    (e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option ι) :
    ∃ P Q : ℤ[X], ∃ r : ℂ, r ≠ 0 ∧
      P.map (Int.castRingHom ℂ) = C r * A ∧
      Q.map (Int.castRingHom ℂ) = C r * B ∧
      P.natDegree ≤ A.natDegree ∧ Q.natDegree ≤ B.natDegree ∧
      P = Polynomial.ofFn (A.natDegree + 1)
        (fun j => interpolationCramer s v e (Sum.inl j)) ∧
      Q = Polynomial.ofFn (B.natDegree + 1)
        (fun j => interpolationCramer s v e (Sum.inr j)) := by
  classical
  let M := interpolationMatrix s v e
  let u : Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1) → ℤ :=
    fun j => if e j = none then 1 else 0
  let c := M.cramer u
  let P := Polynomial.ofFn (A.natDegree + 1) (fun j => c (Sum.inl j))
  let Q := Polynomial.ofFn (B.natDegree + 1) (fun j => c (Sum.inr j))
  have hdet : M.det ≠ 0 := by
    have h := interpolationMatrix_det_ne_zero A B hcop hBn
      (fun i => (s i : ℂ)) (fun i => (v i : ℂ))
      (Int.cast_injective.comp hs) hcard heval e
    intro hz
    apply h
    have hm := interpolationMatrix_map (Int.castRingHom ℂ) s v e
    simp only [Int.coe_castRingHom] at hm
    rw [← hm, ← Int.cast_det,
      show (interpolationMatrix s v e).det = 0 from hz, Int.cast_zero]
  have hc : M *ᵥ c = M.det • u := M.mulVec_cramer u
  have hpdeg : P.natDegree ≤ A.natDegree := Nat.le_of_lt_succ
    (Polynomial.ofFn_natDegree_lt (R := ℤ) (Nat.succ_pos _) _)
  have hqdeg : Q.natDegree ≤ B.natDegree := Nat.le_of_lt_succ
    (Polynomial.ofFn_natDegree_lt (R := ℤ) (Nat.succ_pos _) _)
  let f := Int.castRingHom ℂ
  have heval' (i : ι) : (P.map f).eval (s i : ℂ) = (v i : ℂ) * (Q.map f).eval (s i : ℂ) := by
    have hh := congrFun hc (e.symm (some i))
    change interpolationRow s v (e (e.symm (some i))) ⬝ᵥ c = _ at hh
    rw [e.apply_symm_apply, interpolationRow_some_dot] at hh
    have hz : P.eval (s i) - v i * Q.eval (s i) = 0 := by
      simpa [P, Q, u] using hh
    have he := congrArg f (sub_eq_zero.mp hz)
    simpa only [Polynomial.eval_intCast_map, Int.cast_id, map_mul, f, Int.coe_castRingHom] using he
  have hcross : (P.map f) * B = A * (Q.map f) := by
    apply rational_function_interpolation_cross A B _ _
      (Finset.univ.image (fun i => (s i : ℂ)))
    · rwa [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    · rwa [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    · have hsQ : Function.Injective (fun i => (s i : ℂ)) := Int.cast_injective.comp hs
      rw [Finset.card_image_of_injective _ hsQ, Finset.card_univ]
      exact hcard
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      rw [heval', heval]
      ring
  obtain ⟨r, hP, hQ⟩ := rational_function_interpolation_unique A B _ _ hcop hBn
    (by rwa [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]) hcross
  have hr : r ≠ 0 := by
    intro hr
    have hzero : Q.map f = 0 := by simp [hQ, hr]
    have hcoef : Q.coeff B.natDegree = M.det := by
      have hh := congrFun hc (e.symm none)
      change interpolationRow s v (e (e.symm none)) ⬝ᵥ c = _ at hh
      rw [e.apply_symm_apply, interpolationRow_none_dot] at hh
      simpa [Q, u, Polynomial.ofFn_coeff_eq_val_of_lt _ (Nat.lt_succ_self _)] using hh
    have hz := congrArg (fun p : ℂ[X] => p.coeff B.natDegree) hzero
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero, hcoef] at hz
    exact hdet (Int.cast_eq_zero.mp hz)
  exact ⟨P, Q, r, hr, hP, hQ, hpdeg, hqdeg, rfl, rfl⟩

theorem det_abs_le_row_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (B : ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ B i) :
    |A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
  calc
    |A.det| = |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A (σ i) i| := by
      rw [Matrix.det_apply]
    _ ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [show |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| from
        AbsoluteValue.abs.map_units_int_smul _ _, Finset.abs_prod]
    _ ≤ ∑ σ : Equiv.Perm ι, ∏ i, B (σ i) := by
      apply Finset.sum_le_sum
      intro σ _
      exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
    _ = (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
      simp_rw [Equiv.prod_comp]
      simp [Fintype.card_perm]

theorem det_abs_le_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (B : ℝ) (hA : ∀ i j, |(A i j : ℝ)| ≤ B) :
    |(A.det : ℝ)| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι := by
  rw [Int.cast_det]
  simpa only [Finset.prod_const, Finset.card_univ] using
    det_abs_le_row_product (A.map fun x => (x : ℝ)) (fun _ => B) hA

theorem interpolationRow_abs_le {ι : Type*} {a b : ℕ} (s v : ι → ℤ)
    (H : ℝ) (hH : 1 ≤ H) (hs : ∀ i, |(s i : ℝ)| ≤ H)
    (hv : ∀ i, |(v i : ℝ)| ≤ H) (i : Option ι)
    (j : Fin (a + 1) ⊕ Fin (b + 1)) :
    |((interpolationRow s v i j : ℤ) : ℝ)| ≤ H ^ (max a b + 1) := by
  classical
  have h0 : 0 ≤ H := zero_le_one.trans hH
  cases i with
  | none =>
    by_cases hj : j = Sum.inr ⟨b, Nat.lt_succ_self b⟩
    · subst j
      simpa [interpolationRow] using one_le_pow₀ hH (n := max a b + 1)
    · simp [interpolationRow, Pi.single_eq_of_ne hj, pow_nonneg h0]
  | some i =>
    cases j with
    | inl j =>
      simp only [interpolationRow, Sum.elim_inl, Int.cast_pow, abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hs i) _).trans
        (pow_le_pow_right₀ hH (by have := j.isLt; omega))
    | inr j =>
      simp only [interpolationRow, Sum.elim_inr, Int.cast_neg, Int.cast_mul,
        Int.cast_pow, abs_neg, abs_mul, abs_pow]
      calc
        |(v i : ℝ)| * |(s i : ℝ)| ^ j.val ≤ H * H ^ j.val :=
          mul_le_mul (hv i) (pow_le_pow_left₀ (abs_nonneg _) (hs i) _)
            (by positivity) h0
        _ = H ^ (j.val + 1) := by rw [pow_succ]; ring
        _ ≤ H ^ (max a b + 1) := pow_le_pow_right₀ hH (by have := j.isLt; omega)

theorem interpolationCramer_abs_le {ι : Type*} [Fintype ι] {a b : ℕ}
    (s v : ι → ℤ) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι)
    (H : ℝ) (hH : 1 ≤ H) (hs : ∀ i, |(s i : ℝ)| ≤ H)
    (hv : ∀ i, |(v i : ℝ)| ≤ H) (j : Fin (a + 1) ⊕ Fin (b + 1)) :
    |(interpolationCramer s v e j : ℝ)| ≤
      (Nat.factorial (a + b + 2) : ℝ) * H ^ ((max a b + 1) * (a + b + 2)) := by
  classical
  unfold interpolationCramer
  rw [Matrix.cramer_apply]
  have h := det_abs_le_uniform
    ((interpolationMatrix s v e).updateCol j (fun j => if e j = none then 1 else 0))
    (H ^ (max a b + 1)) (fun i j' => ?_)
  · simpa only [Fintype.card_sum, Fintype.card_fin, ← pow_mul,
      show a + 1 + (b + 1) = a + b + 2 by omega] using h
  · by_cases hj : j' = j
    · subst j'
      simp only [Matrix.updateCol_self]
      split_ifs
      · simpa using one_le_pow₀ hH (n := max a b + 1)
      · simp [pow_nonneg (zero_le_one.trans hH)]
    · rw [Matrix.updateCol_ne hj]
      exact interpolationRow_abs_le s v H hH hs hv (e i) j'

def interpolationHeight (D : ℕ) (H : ℝ) : ℝ :=
  (Nat.factorial (2 * D + 2) : ℝ) * H ^ ((D + 1) * (2 * D + 2))

theorem interpolationHeight_one_le (D : ℕ) {H : ℝ} (hH : 1 ≤ H) :
    1 ≤ interpolationHeight D H := by
  exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast Nat.factorial_pos (2 * D + 2))
    (one_le_pow₀ hH)

theorem interpolationCramer_abs_le_degree_bound {ι : Type*} [Fintype ι] {a b : ℕ}
    (s v : ι → ℤ) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι)
    (D : ℕ) (ha : a ≤ D) (hb : b ≤ D)
    (H : ℝ) (hH : 1 ≤ H) (hs : ∀ i, |(s i : ℝ)| ≤ H)
    (hv : ∀ i, |(v i : ℝ)| ≤ H) (j : Fin (a + 1) ⊕ Fin (b + 1)) :
    |(interpolationCramer s v e j : ℝ)| ≤ interpolationHeight D H := by
  apply (interpolationCramer_abs_le s v e H hH hs hv j).trans
  apply mul_le_mul
  · exact_mod_cast Nat.factorial_le (show a + b + 2 ≤ 2 * D + 2 by omega)
  · exact pow_le_pow_right₀ hH (Nat.mul_le_mul (by omega) (by omega))
  · positivity
  · positivity

theorem resultant_abs_le_coeff_bound (P Q : ℤ[X]) (H : ℝ) (hH : 0 ≤ H)
    (hP : ∀ j, |(P.coeff j : ℝ)| ≤ H) (hQ : ∀ j, |(Q.coeff j : ℝ)| ≤ H) :
    |(P.resultant Q : ℝ)| ≤ (Nat.factorial (P.natDegree + Q.natDegree) : ℝ) *
      H ^ (P.natDegree + Q.natDegree) := by
  unfold Polynomial.resultant
  apply (det_abs_le_uniform _ H ?_).trans_eq
  · simp only [Fintype.card_fin]
  · intro i j
    refine Fin.addCases ?_ ?_ j
    · intro j'
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hQ _
      · simpa using hH
    · intro j'
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hP _
      · simpa using hH

theorem resultant_ne_zero_of_scalar_maps (A B : ℂ[X]) (P Q : ℤ[X])
    (hcop : IsCoprime A B) (r : ℂ) (hr : r ≠ 0)
    (hP : P.map (Int.castRingHom ℂ) = C r * A)
    (hQ : Q.map (Int.castRingHom ℂ) = C r * B) : P.resultant Q ≠ 0 := by
  have hcop' : IsCoprime (P.map (Int.castRingHom ℂ)) (Q.map (Int.castRingHom ℂ)) := by
    rw [hP, hQ]
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨C r⁻¹ * u, C r⁻¹ * v, ?_⟩
    calc
      C r⁻¹ * u * (C r * A) + C r⁻¹ * v * (C r * B) =
          C r⁻¹ * C r * (u * A + v * B) := by ring
      _ = 1 := by rw [huv, ← Polynomial.C_mul]; simp [hr]
  have hh := Polynomial.resultant_ne_zero _ _ hcop'
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.natDegree_map_eq_of_injective Int.cast_injective,
    Polynomial.resultant_map_map] at hh
  exact fun hz => hh (by simp only [hz, map_zero])

theorem rational_interpolation_height {ι : Type*} [Fintype ι]
    (A B : ℂ[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (s v : ι → ℤ) (hs : Function.Injective s)
    (hcard : A.natDegree + B.natDegree < Fintype.card ι)
    (heval : ∀ i, A.eval (s i : ℂ) = (v i : ℂ) * B.eval (s i : ℂ))
    (e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option ι)
    (D : ℕ) (hA : A.natDegree ≤ D) (hB : B.natDegree ≤ D)
    (H : ℝ) (hH : 1 ≤ H) (hsH : ∀ i, |(s i : ℝ)| ≤ H)
    (hvH : ∀ i, |(v i : ℝ)| ≤ H) :
    ∃ P Q : ℤ[X], ∃ r : ℂ, r ≠ 0 ∧
      P.map (Int.castRingHom ℂ) = C r * A ∧
      Q.map (Int.castRingHom ℂ) = C r * B ∧
      P.natDegree ≤ D ∧ Q.natDegree = B.natDegree ∧
      P.resultant Q ≠ 0 ∧
      (∀ j, |(P.coeff j : ℝ)| ≤ interpolationHeight D H) ∧
      (∀ j, |(Q.coeff j : ℝ)| ≤ interpolationHeight D H) := by
  obtain ⟨P, Q, r, hr, hP, hQ, hpdeg, _, hPc, hQc⟩ :=
    rational_interpolation_integral_pair A B hcop hBn s v hs hcard heval e
  have hqdeg : Q.natDegree = B.natDegree := by
    rw [← Polynomial.natDegree_map_eq_of_injective (p := Q) (f := Int.castRingHom ℂ) Int.cast_injective,
      hQ, Polynomial.natDegree_C_mul hr]
  refine ⟨P, Q, r, hr, hP, hQ, hpdeg.trans hA, hqdeg,
    resultant_ne_zero_of_scalar_maps A B P Q hcop r hr hP hQ, ?_, ?_⟩
  · intro j
    rw [hPc]
    by_cases hj : j < A.natDegree + 1
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
      exact interpolationCramer_abs_le_degree_bound s v e D hA hB H hH hsH hvH _
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
      exact_mod_cast (zero_le_one.trans (interpolationHeight_one_le D hH))
  · intro j
    rw [hQc]
    by_cases hj : j < B.natDegree + 1
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
      exact interpolationCramer_abs_le_degree_bound s v e D hA hB H hH hsH hvH _
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
      exact_mod_cast (zero_le_one.trans (interpolationHeight_one_le D hH))

theorem eval_eq_mul_of_scalar_maps (A B : ℂ[X]) (P Q : ℤ[X]) (r : ℂ)
    (hP : P.map (Int.castRingHom ℂ) = C r * A)
    (hQ : Q.map (Int.castRingHom ℂ) = C r * B) (s v : ℤ)
    (hv : A.eval (s : ℂ) = (v : ℂ) * B.eval (s : ℂ)) :
    P.eval s = v * Q.eval s := by
  apply Int.cast_injective (α := ℂ)
  have hp := congrArg (Polynomial.eval (s : ℂ)) hP
  have hq := congrArg (Polynomial.eval (s : ℂ)) hQ
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_intCast_map, Int.coe_castRingHom, Int.cast_id] at hp hq
  push_cast
  rw [hp, hq, hv]
  ring

theorem rational_values_height_representative
    (A B : ℂ[X]) (hcop : IsCoprime A B) (hBn : B ≠ 0)
    (S : Finset ℤ) (v : ℤ → ℤ)
    (heval : ∀ s ∈ S, A.eval (s : ℂ) = (v s : ℂ) * B.eval (s : ℂ))
    (hcard : A.natDegree + B.natDegree < S.card)
    (D : ℕ) (hA : A.natDegree ≤ D) (hB : B.natDegree ≤ D)
    (H : ℝ) (hH : 1 ≤ H) (hsH : ∀ s ∈ S, |(s : ℝ)| ≤ H)
    (hvH : ∀ s ∈ S, |(v s : ℝ)| ≤ H) :
    ∃ P Q : ℤ[X], P.natDegree ≤ D ∧ Q.natDegree = B.natDegree ∧
      P.resultant Q ≠ 0 ∧
      (∀ j, |(P.coeff j : ℝ)| ≤ interpolationHeight D H) ∧
      (∀ j, |(Q.coeff j : ℝ)| ≤ interpolationHeight D H) ∧
      ∀ s ∈ S, P.eval s = v s * Q.eval s := by
  classical
  obtain ⟨T, hTS, hTc⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hcard)
  let e : (Fin (A.natDegree + 1) ⊕ Fin (B.natDegree + 1)) ≃ Option T :=
    Fintype.equivOfCardEq (by simp [hTc]; omega)
  obtain ⟨P, Q, r, _, hP, hQ, hpdeg, hqdeg, hres, hpH, hqH⟩ :=
    rational_interpolation_height A B hcop hBn
      (fun s : T => s.val) (fun s : T => v s.val) Subtype.val_injective
      (by simp [hTc])
      (fun s => heval s.val (hTS s.property)) e D hA hB H hH
      (fun s => hsH s.val (hTS s.property)) (fun s => hvH s.val (hTS s.property))
  refine ⟨P, Q, hpdeg, hqdeg, hres, hpH, hqH, ?_⟩
  intro s hs
  exact eval_eq_mul_of_scalar_maps A B P Q r hP hQ s (v s) (heval s hs)

def rationalResultantConstant (D : ℕ) : ℝ :=
  (Nat.factorial (2 * D) : ℝ) * (Nat.factorial (2 * D + 2) : ℝ) ^ (2 * D)

def rationalResultantExponent (D : ℕ) : ℕ := 2 * D * ((D + 1) * (2 * D + 2))

theorem rationalResultantConstant_pos (D : ℕ) : 0 < rationalResultantConstant D := by
  unfold rationalResultantConstant
  positivity

theorem rationalResultantExponent_pos {D : ℕ} (hD : 0 < D) :
    0 < rationalResultantExponent D := by
  unfold rationalResultantExponent
  positivity

theorem resultant_abs_le_interpolation_height (P Q : ℤ[X]) (D : ℕ)
    (hPdeg : P.natDegree ≤ D) (hQdeg : Q.natDegree ≤ D)
    (H : ℝ) (hH : 1 ≤ H)
    (hP : ∀ j, |(P.coeff j : ℝ)| ≤ interpolationHeight D H)
    (hQ : ∀ j, |(Q.coeff j : ℝ)| ≤ interpolationHeight D H) :
    |(P.resultant Q : ℝ)| ≤ rationalResultantConstant D * H ^ rationalResultantExponent D := by
  have hi := interpolationHeight_one_le D hH
  apply (resultant_abs_le_coeff_bound P Q (interpolationHeight D H)
    (zero_le_one.trans hi) hP hQ).trans
  calc
    _ ≤ (Nat.factorial (2 * D) : ℝ) * interpolationHeight D H ^ (2 * D) := by
      apply mul_le_mul
      · exact_mod_cast Nat.factorial_le (show P.natDegree + Q.natDegree ≤ 2 * D by omega)
      · exact pow_le_pow_right₀ hi (by omega)
      · positivity
      · positivity
    _ = rationalResultantConstant D * H ^ rationalResultantExponent D := by
      simp only [interpolationHeight, rationalResultantConstant, rationalResultantExponent,
        mul_pow, ← pow_mul]
      rw [Nat.mul_comm ((D + 1) * (2 * D + 2)) (2 * D)]
      ring

open Filter

theorem succ_le_geometric (r : ℝ) (hr : 1 < r) (a : ℕ) :
    (a : ℝ) + 1 ≤ (1 + (r - 1)⁻¹) * r ^ a := by
  have h₁ := a.cast_le_pow_div_sub hr
  have h₂ : (1 : ℝ) ≤ r ^ a := one_le_pow₀ hr.le
  calc
    (a : ℝ) + 1 ≤ r ^ a / (r - 1) + r ^ a := add_le_add h₁ h₂
    _ = (1 + (r - 1)⁻¹) * r ^ a := by ring

theorem divisors_card_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let c : ℝ := 1 + (r - 1)⁻¹
  have hc : 1 ≤ c := by
    have hh : 0 ≤ (r - 1)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hr.le)
    dsimp [c]
    linarith
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have ht : Tendsto (fun p : ℕ => (p : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨c ^ N, pow_pos hc0 _, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow hε.ne']
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ) + 1 ≤
        (if p < N then c else 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hsmall : p < N
    · rw [ite_eq_left hsmall]
      exact (succ_le_geometric r hr _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2 hε.le) _)
        hc0.le)
    · rw [ite_eq_right hsmall, one_mul]
      have hh : (n.factorization p : ℝ) + 1 ≤ (2 : ℝ) ^ n.factorization p := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n.factorization p))
      exact hh.trans (pow_le_pow_left₀ (by norm_num) (hN p (Nat.le_of_not_gt hsmall)) _)
  have hconstant : (∏ p ∈ n.primeFactors, if p < N then c else 1) ≤ c ^ N := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
    apply pow_le_pow_right₀ hc
    exact (Finset.card_le_card (show n.primeFactors.filter (fun p => p < N) ⊆
      Finset.range N from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)).trans
        (by rw [Finset.card_range])
  have hpowers : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) =
      (n : ℝ) ^ ε := by
    simp_rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _) ε,
      mul_comm ε, Real.rpow_natCast_mul (Nat.cast_nonneg _) _ ε]
    rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn]
      push_cast
      rfl
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < N then c else 1) * ((p : ℝ) ^ ε) ^ n.factorization p :=
      Finset.prod_le_prod₀ (fun p _ => by positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, if p < N then c else 1) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, hpowers]
    _ ≤ c ^ N * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hconstant (by positivity)

theorem rational_values_card_le_rpow (D : ℕ) (hD : 0 < D) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℂ[X]), IsCoprime A B →
      0 < B.natDegree → A.natDegree ≤ D → B.natDegree ≤ D →
      ∀ (S : Finset ℤ) (v : ℤ → ℤ) (H : ℝ), 1 ≤ H →
      (∀ s ∈ S, A.eval (s : ℂ) = (v s : ℂ) * B.eval (s : ℂ)) →
      (∀ s ∈ S, |(s : ℝ)| ≤ H) → (∀ s ∈ S, |(v s : ℝ)| ≤ H) →
      (S.card : ℝ) ≤ C * H ^ ε := by
  let E := rationalResultantExponent D
  have hE : (0 : ℝ) < E := by exact_mod_cast rationalResultantExponent_pos hD
  let δ := ε / (E : ℝ)
  have hδ : 0 < δ := div_pos hε hE
  obtain ⟨c, hc, hdiv⟩ := divisors_card_le_rpow δ hδ
  let K := rationalResultantConstant D
  have hK : 0 < K := rationalResultantConstant_pos D
  let C : ℝ := (2 * D : ℕ) + (2 * D : ℕ) * c * K ^ δ
  have h2D : (0 : ℝ) < (2 * D : ℕ) := by exact_mod_cast (by omega : 0 < 2 * D)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro A B hcop hBpos hAdeg hBdeg S v H hH heval hsH hvH
  have hHε : 1 ≤ H ^ ε := Real.one_le_rpow hH hε.le
  by_cases hcard : A.natDegree + B.natDegree < S.card
  · have hBn : B ≠ 0 := by
      intro hz
      simp only [hz, Polynomial.natDegree_zero, lt_self_iff_false] at hBpos
    obtain ⟨P, Q, hPdeg, hQdeg, hres, hP, hQ, hpq⟩ :=
      rational_values_height_representative A B hcop hBn S v heval hcard D hAdeg hBdeg
        H hH hsH hvH
    have hi : S.filter (fun s => Q.eval s ∣ P.eval s) = S := by
      apply Finset.filter_eq_self.mpr
      intro s hs
      rw [hpq s hs]
      exact dvd_mul_left _ _
    have hτ := rational_values_card_le_divisors P Q (by omega) hres S
    rw [hi] at hτ
    have hR : ((P.resultant Q).natAbs : ℝ) ≤ K * H ^ E := by
      have hab : ((P.resultant Q).natAbs : ℝ) = |(P.resultant Q : ℝ)| := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [hab]
      exact resultant_abs_le_interpolation_height P Q D hPdeg (hQdeg ▸ hBdeg) H hH hP hQ
    have hpowers : (K * H ^ E) ^ δ = K ^ δ * H ^ ε := by
      rw [Real.mul_rpow hK.le (pow_nonneg (zero_le_one.trans hH) _),
        ← Real.rpow_natCast_mul (zero_le_one.trans hH)]
      congr 1
      dsimp [δ]
      rw [mul_div_cancel₀ _ hE.ne']
    calc
      (S.card : ℝ) ≤ ((2 * Q.natDegree : ℕ) : ℝ) *
          ((P.resultant Q).natAbs.divisors.card : ℝ) := by exact_mod_cast hτ
      _ ≤ ((2 * D : ℕ) : ℝ) * (c * (((P.resultant Q).natAbs : ℝ) ^ δ)) := by
        apply mul_le_mul
        · exact_mod_cast Nat.mul_le_mul_left 2 (hQdeg ▸ hBdeg)
        · exact hdiv _
        · positivity
        · positivity
      _ ≤ ((2 * D : ℕ) : ℝ) * (c * ((K * H ^ E) ^ δ)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) hR hδ.le) hc.le) h2D.le
      _ = (((2 * D : ℕ) : ℝ) * c * K ^ δ) * H ^ ε := by rw [hpowers]; ring
      _ ≤ C * H ^ ε := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C]
        linarith
  · have hsmall : (S.card : ℝ) ≤ (2 * D : ℕ) := by exact_mod_cast (by omega : S.card ≤ 2 * D)
    calc
      (S.card : ℝ) ≤ (2 * D : ℕ) := hsmall
      _ ≤ ((2 * D : ℕ) : ℝ) * H ^ ε := le_mul_of_one_le_right h2D.le hHε
      _ ≤ C * H ^ ε := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [C]
        have hnonneg : 0 ≤ ((2 * D : ℕ) : ℝ) * c * K ^ δ := by positivity
        linarith

theorem rational_integer_values_uniform (D : ℕ) (hD : 0 < D)
    (a b C₀ : ℝ) (ha : 0 < a) (_hb : 0 < b) (_hC₀ : 0 < C₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℂ[X]), IsCoprime A B →
      0 < B.natDegree → A.natDegree ≤ D → B.natDegree ≤ D →
      ∀ (S : Finset ℤ) (v : ℤ → ℤ) (X : ℝ), 2 ≤ X →
      (∀ s ∈ S, A.eval (s : ℂ) = (v s : ℂ) * B.eval (s : ℂ)) →
      (∀ s ∈ S, |(s : ℝ)| ≤ C₀ * X ^ a) →
      (∀ s ∈ S, |(v s : ℝ)| ≤ C₀ * X ^ b) →
      (S.card : ℝ) ≤ C * X ^ ε := by
  let M := max a b
  have hM : 0 < M := lt_of_lt_of_le ha (le_max_left _ _)
  let K := max 1 C₀
  have hK : 1 ≤ K := le_max_left _ _
  let δ := ε / M
  have hδ : 0 < δ := div_pos hε hM
  obtain ⟨c, hc, h⟩ := rational_values_card_le_rpow D hD δ hδ
  refine ⟨c * K ^ δ, by positivity, ?_⟩
  intro A B hcop hBpos hAdeg hBdeg S v X hX heval hsX hvX
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 ≤ X := by linarith
  have hXM : 1 ≤ X ^ M := Real.one_le_rpow hX1 hM.le
  have hH : 1 ≤ K * X ^ M := one_le_mul_of_one_le_of_one_le hK hXM
  have hbound (c₁ : ℝ) (hc₁ : c₁ ≤ M) : C₀ * X ^ c₁ ≤ K * X ^ M := by
    exact mul_le_mul (le_max_right _ _) (Real.rpow_le_rpow_of_exponent_le hX1 hc₁)
      (by positivity) (zero_le_one.trans hK)
  have hh := h A B hcop hBpos hAdeg hBdeg S v (K * X ^ M) hH heval
    (fun s hs => (hsX s hs).trans (hbound a (le_max_left _ _)))
    (fun s hs => (hvX s hs).trans (hbound b (le_max_right _ _)))
  have hp : (K * X ^ M) ^ δ = K ^ δ * X ^ ε := by
    rw [Real.mul_rpow (zero_le_one.trans hK) (Real.rpow_nonneg hX0 _),
      ← Real.rpow_mul hX0]
    congr 1
    dsimp [δ]
    rw [mul_div_cancel₀ _ hM.ne']
  simpa only [hp, mul_assoc] using hh

end QuarticPowerFree.ComplexValues

end OAI
