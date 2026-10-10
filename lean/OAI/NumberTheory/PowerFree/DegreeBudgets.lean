import OAI.NumberTheory.PowerFree.PureCuts

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

theorem minimal_prime_separators {R ι : Type*} [CommRing R] [Fintype ι]
    (J : Ideal R) (P : ι → Ideal R) (hP : ∀ i, P i ∈ J.minimalPrimes)
    (hPi : Function.Injective P) :
    ∃ b : ι → R, (∀ i, b i ∉ P i) ∧ (∀ i j, i ≠ j → b i ∈ P j) := by
  classical
  have hex : ∀ i j : ι, i ≠ j → ∃ a : R, a ∈ P j ∧ a ∉ P i := by
    intro i j hij
    by_contra hh
    have hji : P j ≤ P i := by
      intro a ha
      by_contra hn
      exact hh ⟨a,ha,hn⟩
    have he : P i = P j := le_antisymm ((hP i).2 (hP j).1 hji) hji
    exact hij (hPi he)
  choose a ha using hex
  let b : ι → R := fun i => ∏ j : {j : ι // i ≠ j}, a i j j.property
  refine ⟨b,?_,?_⟩
  · intro i
    have : (P i).IsPrime := (hP i).isPrime
    simp only [b, Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and, not_exists]
    intro j
    exact (ha i j j.property).2
  · intro i j hij
    have : (P j).IsPrime := (hP j).isPrime
    exact Ideal.IsPrime.prod_mem_iff.mpr ⟨⟨j,hij⟩,Finset.mem_univ _,(ha i j hij).1⟩

theorem component_hilbert_sum_le_shift {n : ℕ} {K ι : Type*} [Field K] [Fintype ι]
    (J : Ideal (MvPolynomial (Fin n) K))
    (P : ι → Ideal (MvPolynomial (Fin n) K)) (hPr : ∀ i, (P i).IsPrime)
    (hJP : ∀ i, J ≤ P i) (b : ι → MvPolynomial (Fin n) K)
    (hb : ∀ i, b i ∉ P i) (hsep : ∀ i j, i ≠ j → b i ∈ P j)
    (B T : ℕ) (hB : ∀ i, (b i).totalDegree ≤ B) :
    (∑ i, Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K (P i)).toLinearMap)) ≤
      Module.finrank K ((totalSpace (T+B)).map (Ideal.Quotient.mkₐ K J).toLinearMap) := by
  classical
  let V := fun i => (totalSpace T).map (Ideal.Quotient.mkₐ K (P i)).toLinearMap
  let W := (totalSpace (T+B)).map (Ideal.Quotient.mkₐ K J).toLinearMap
  let f : ∀ i, totalSpace (σ := Fin n) (K := K) T →ₗ[K] V i := fun i =>
    { toFun := fun x => ⟨Ideal.Quotient.mk (P i) x.val, ⟨x.val,x.property,rfl⟩⟩
      map_add' := by intros; ext; simp
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact (Ideal.Quotient.mkₐ K (P i)).toLinearMap.map_smul c x.val }
  have hf : ∀ i, LinearMap.range (f i) = ⊤ := by
    intro i
    apply LinearMap.range_eq_top.mpr
    rintro ⟨y,p,hp,hpy⟩
    exact ⟨⟨p,hp⟩,Subtype.ext hpy⟩
  let (i : ι) : Module.Free K (V i) := Module.Free.of_divisionRing K (V i)
  let (i : ι) : Module.Projective K (V i) := Module.Projective.of_free
  choose l hl using fun i => (f i).exists_rightInverse_of_surjective (hf i)
  have hli : ∀ i (x : V i), Ideal.Quotient.mk (P i) (l i x).val = x.val := by
    intro i x
    exact congrArg Subtype.val (LinearMap.congr_fun (hl i) x)
  let L : (∀ i, V i) →ₗ[K] W :=
    { toFun := fun x => ⟨Ideal.Quotient.mk J (∑ i, b i * (l i (x i)).val), by
        refine ⟨∑ i, b i * (l i (x i)).val, ?_, rfl⟩
        apply Submodule.sum_mem
        intro i _
        apply mem_totalSpace.mpr
        exact (totalDegree_mul _ _).trans ((Nat.add_le_add (hB i)
          (mem_totalSpace.mp (l i (x i)).property)).trans_eq (Nat.add_comm B T))⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp only [Pi.add_apply, map_add, AddMemClass.coe_add, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        apply Subtype.ext
        simp only [Pi.smul_apply, map_smul, SetLike.val_smul, mul_smul_comm,
          ← Finset.smul_sum]
        exact (Ideal.Quotient.mkₐ K J).toLinearMap.map_smul c _ }
  have hL : Function.Injective L := by
    intro x y hxy
    funext i
    have : (P i).IsPrime := hPr i
    apply Subtype.ext
    have hh := congrArg (fun z : W => Ideal.Quotient.factor (hJP i) z.val) hxy
    change Ideal.Quotient.mk (P i) (∑ j, b j * (l j (x j)).val) =
      Ideal.Quotient.mk (P i) (∑ j, b j * (l j (y j)).val) at hh
    have hs (z : ∀ j, V j) : Ideal.Quotient.mk (P i) (∑ j, b j * (l j (z j)).val) =
        Ideal.Quotient.mk (P i) (b i) * (z i).val := by
      rw [map_sum, Finset.sum_eq_single i, map_mul, hli]
      · intro j _ hji
        rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hsep j i hji),zero_mul]
      · simp
    rw [hs, hs] at hh
    exact mul_left_cancel₀ (fun hz => hb i (Ideal.Quotient.eq_zero_iff_mem.mp hz)) hh
  let := totalSpace_finite (n := n) (K := K) T
  let := totalSpace_finite (n := n) (K := K) (T+B)
  simpa only [Module.finrank_pi_fintype] using LinearMap.finrank_le_finrank_of_injective hL

theorem component_hilbert_coeff_sum_le {n h : ℕ} {K ι : Type*} [Field K] [Fintype ι]
    (J : Ideal (MvPolynomial (Fin n) K))
    (P : ι → Ideal (MvPolynomial (Fin n) K)) (hPr : ∀ i, P i ∈ J.minimalPrimes)
    (hPi : Function.Injective P) (D : Polynomial ℚ) (S : ι → Polynomial ℚ)
    (hD : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap) : ℚ) = D.eval (T : ℚ))
    (hS : ∀ i, ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K (P i)).toLinearMap) : ℚ) = (S i).eval (T : ℚ))
    (hdD : D.natDegree ≤ h) (hdS : ∀ i, (S i).natDegree ≤ h) :
    ∑ i, (S i).coeff h ≤ D.coeff h := by
  classical
  obtain ⟨b,hb,hsep⟩ := minimal_prime_separators J P hPr hPi
  let B := Finset.univ.sup (fun i => (b i).totalDegree)
  have hB : ∀ i, (b i).totalDegree ≤ B := fun i => Finset.le_sup (f := fun i => (b i).totalDegree) (Finset.mem_univ i)
  have hsum : (∑ i, S i).natDegree ≤ h :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => hdS i)
  have hshift : (Polynomial.taylor (B : ℚ) D).natDegree ≤ h := by simpa using hdD
  have hDT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace (T+B)).map (Ideal.Quotient.mkₐ K J).toLinearMap) : ℚ) =
        D.eval ((T+B : ℕ) : ℚ) := by
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hD
    exact Filter.eventually_atTop.mpr ⟨N,fun T hT => hN (T+B) (by omega)⟩
  have hle : ∀ᶠ T : ℕ in Filter.atTop,
      (∑ i, S i).eval (T : ℚ) ≤ (Polynomial.taylor (B : ℚ) D).eval (T : ℚ) := by
    filter_upwards [Filter.eventually_all.mpr hS,hDT] with T hs hd
    rw [Polynomial.eval_finsetSum,Polynomial.taylor_eval,← Nat.cast_add,← hd]
    simp_rw [← hs]
    exact_mod_cast component_hilbert_sum_le_shift J P (fun i => (hPr i).isPrime)
      (fun i => (hPr i).le) b hb hsep B T hB
  have hc := coeff_le_of_eventually_nat_eval_le (∑ i, S i) (Polynomial.taylor (B : ℚ) D)
    h hsum hshift hle
  rw [coeff_taylor_high D (B : ℚ) h hdD] at hc
  simpa only [Polynomial.finsetSum_coeff] using hc

theorem polynomial_eq_of_eventually_nat_eval_eq (P Q : Polynomial ℚ)
    (he : ∀ᶠ T : ℕ in Filter.atTop, P.eval (T : ℚ) = Q.eval (T : ℚ)) : P = Q := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Ici_infinite N).image (Nat.cast_injective (R := ℚ)).injOn).mono
  rintro _ ⟨T,hT,rfl⟩
  exact hN T hT

noncomputable def coordinateHilbert {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) : Polynomial ℚ :=
  (coordinate_hilbert_eventually_polynomial I).choose

noncomputable def affineDimension {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) : ℕ := (coordinateHilbert I).natDegree

noncomputable def affineDegree {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) : ℚ :=
  ((affineDimension I).factorial : ℚ) * (coordinateHilbert I).coeff (affineDimension I)

theorem coordinateHilbert_eventually {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) : ∀ᶠ T : ℕ in Filter.atTop,
    (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
      (coordinateHilbert I).eval (T : ℚ) := by
  obtain ⟨N,hN⟩ := (coordinate_hilbert_eventually_polynomial I).choose_spec.2
  exact Filter.eventually_atTop.mpr ⟨N,hN⟩

theorem one_le_affineDegree {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : I ≠ ⊤) : 1 ≤ affineDegree I := by
  obtain ⟨P,_,_,_,hc,N,hN⟩ := coordinate_hilbert_degree_independent I hI
  have he : P = coordinateHilbert I := by
    apply polynomial_eq_of_eventually_nat_eval_eq
    filter_upwards [Filter.eventually_atTop.mpr ⟨N,hN⟩,coordinateHilbert_eventually I] with T hp hq
    exact hp.symm.trans hq
  rw [he] at hc
  have hf : (0 : ℚ) < ((affineDimension I).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  calc
    1 = ((affineDimension I).factorial : ℚ) * ((affineDimension I).factorial : ℚ)⁻¹ :=
      (mul_inv_cancel₀ hf.ne').symm
    _ ≤ affineDegree I := mul_le_mul_of_nonneg_left hc hf.le

theorem proper_cut_component_dimension {n h : ℕ} {K : Type u} [Field K]
    (I Q : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [Q.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I)
    (hQ : Q ∈ (I ⊔ Ideal.span {p}).minimalPrimes) (hd : affineDimension I = h+1) :
    affineDimension Q = h :=
  proper_cut_hilbert_purity I Q p hp hQ _ _ _ (coordinateHilbert_eventually I)
    (coordinateHilbert_eventually _) (coordinateHilbert_eventually Q) hd

theorem proper_cut_sum_affineDegree_le {n h : ℕ} {K : Type u} {ι : Type*}
    [Field K] [Fintype ι] (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I) (hd : affineDimension I = h+1)
    (Q : ι → Ideal (MvPolynomial (Fin n) K))
    (hQ : ∀ i, Q i ∈ (I ⊔ Ideal.span {p}).minimalPrimes) (hQi : Function.Injective Q) :
    ∑ i, affineDegree (Q i) ≤ (p.totalDegree : ℚ) * affineDegree I := by
  classical
  let J := I ⊔ Ideal.span {p}
  have hdim : ∀ i, affineDimension (Q i) = h := by
    intro i
    let := (hQ i).isPrime
    exact proper_cut_component_dimension I (Q i) p hp (hQ i) hd
  have hj := proper_cut_hilbert_polynomial I p hp (coordinateHilbert I) (coordinateHilbert J)
    ((coordinateHilbert_eventually I).mono (fun _ ht => ht.symm))
    ((coordinateHilbert_eventually J).mono (fun _ ht => ht.symm)) h hd.le
  have hc := component_hilbert_coeff_sum_le J Q hQ hQi (coordinateHilbert J)
    (fun i => coordinateHilbert (Q i)) (coordinateHilbert_eventually J)
    (fun i => coordinateHilbert_eventually (Q i)) hj.1 (fun i => (hdim i).le)
  have hf : (0 : ℚ) ≤ (h.factorial : ℚ) := Nat.cast_nonneg _
  calc
    ∑ i, affineDegree (Q i) = (h.factorial : ℚ) * ∑ i, (coordinateHilbert (Q i)).coeff h := by
      simp only [affineDegree, hdim, Finset.mul_sum]
    _ ≤ (h.factorial : ℚ) * (coordinateHilbert J).coeff h := mul_le_mul_of_nonneg_left hc hf
    _ ≤ (h.factorial : ℚ) * ((p.totalDegree : ℚ) * (h+1) * (coordinateHilbert I).coeff (h+1)) :=
      mul_le_mul_of_nonneg_left hj.2 hf
    _ = (p.totalDegree : ℚ) * affineDegree I := by
      rw [affineDegree, hd, Nat.factorial_succ]
      push_cast
      ring

theorem proper_cut_component_card_le {n h : ℕ} {K : Type u} {ι : Type*}
    [Field K] [Fintype ι] (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I) (hd : affineDimension I = h+1)
    (Q : ι → Ideal (MvPolynomial (Fin n) K))
    (hQ : ∀ i, Q i ∈ (I ⊔ Ideal.span {p}).minimalPrimes) (hQi : Function.Injective Q) :
    (Fintype.card ι : ℚ) ≤ (p.totalDegree : ℚ) * affineDegree I := by
  have hi : (Fintype.card ι : ℚ) ≤ ∑ i, affineDegree (Q i) := by
    calc
      (Fintype.card ι : ℚ) = ∑ _i : ι, (1 : ℚ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => one_le_affineDegree (Q i) (hQ i).isPrime.ne_top
  exact hi.trans (proper_cut_sum_affineDegree_le I p hp hd Q hQ hQi)

end

open MvPolynomial

def DeterminedInDegree {σ ι K : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (z : ι → σ → ℤ) (D : ℕ) : Prop :=
  ∀ p : MvPolynomial σ K, p.totalDegree ≤ D →
    ((∀ i, eval (fun l => (z i l : K)) p = 0) ↔ p ∈ I)

theorem totalDegree_map_ringEquiv {σ K : Type*} [CommSemiring K]
    (τ : K ≃+* K) (p : MvPolynomial σ K) :
    (MvPolynomial.map τ.toRingHom p).totalDegree = p.totalDegree := by
  classical
  simp only [totalDegree, support_map_of_injective p (f := τ.toRingHom) τ.injective]

theorem eval_integer_point_map {σ K : Type*} [CommRing K]
    (τ : K ≃+* K) (p : MvPolynomial σ K) (z : σ → ℤ) :
    eval (fun i => (z i : K)) (MvPolynomial.map τ.toRingHom p) =
      τ (eval (fun i => (z i : K)) p) := by
  rw [eval_map]
  change eval₂ τ.toRingHom (fun i => (z i : K)) p =
    τ.toRingHom (eval₂ (RingHom.id K) (fun i => (z i : K)) p)
  simpa only [RingHom.comp_id, map_intCast] using
    (hom_eval₂ p (RingHom.id K) τ.toRingHom (fun i => (z i : K))).symm

theorem determined_equations_invariant {σ ι K : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (z : ι → σ → ℤ) (D : ℕ)
    (h : DeterminedInDegree I z D) (τ : K ≃+* K)
    (p : MvPolynomial σ K) (hp : p.totalDegree ≤ D) :
    MvPolynomial.map τ.toRingHom p ∈ I ↔ p ∈ I := by
  rw [← h _ (by simpa only [totalDegree_map_ringEquiv] using hp), ← h p hp]
  simp only [eval_integer_point_map, map_eq_zero_iff τ τ.injective]

theorem bounded_cut_or_determined {σ ι K : Type*}
    [Fintype σ] [Fintype ι] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial σ K)) (z : ι → σ → ℤ)
    (hzI : ∀ p ∈ I, ∀ i, eval (fun l => (z i l : K)) p = 0)
    (D : ℕ) (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H) :
    (∃ G : MvPolynomial σ ℤ,
      G.totalDegree ≤ D ∧
      (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤
        integralKernelHeight ((D + Fintype.card σ).choose (Fintype.card σ)) (H^D)) ∧
      (∀ i, eval (z i) G = 0) ∧ MvPolynomial.map (Int.castRingHom K) G ∉ I) ∨
    DeterminedInDegree I z D := by
  classical
  obtain ⟨G,hdeg,hheight,hvan,hspan⟩ :=
    exists_bounded_degree_vanishing_polynomials (F := K) z H hH hz D
  by_cases hGI : ∀ a, MvPolynomial.map (Int.castRingHom K) (G a) ∈ I
  · right
    intro p hp
    constructor
    · intro hvanp
      exact (Submodule.span_le.mpr (by rintro _ ⟨a,rfl⟩; exact hGI a) :
        Submodule.span K (Set.range (fun a => MvPolynomial.map (Int.castRingHom K) (G a))) ≤
          I.restrictScalars K) (hspan p hp hvanp)
    · exact hzI p
  · left
    obtain ⟨a,ha⟩ := not_forall.mp hGI
    exact ⟨G a,hdeg a,hheight a,hvan a,ha⟩

end QuarticPowerFree

end OAI
