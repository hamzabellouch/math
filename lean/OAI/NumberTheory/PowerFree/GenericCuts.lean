import OAI.NumberTheory.PowerFree.IntegralKernels

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree

section
open MvPolynomial
attribute [local instance] Classical.propDecidable

noncomputable def genericPoint {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    Fin n → FractionRing (MvPolynomial (Fin n) K ⧸ I) :=
  fun i => algebraMap _ _ (Ideal.Quotient.mk I (X i))

theorem aeval_genericPoint {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    aeval (genericPoint I) =
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K ⧸ I)
        (FractionRing (MvPolynomial (Fin n) K ⧸ I))).comp (Ideal.Quotient.mkₐ K I) := by
  ext i
  simp only [aeval_X, AlgHom.comp_apply]
  rfl

theorem aeval_genericPoint_eq_zero_iff {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) :
    aeval (genericPoint I) p = 0 ↔ p ∈ I := by
  rw [aeval_genericPoint]
  change algebraMap (MvPolynomial (Fin n) K ⧸ I)
    (FractionRing (MvPolynomial (Fin n) K ⧸ I)) (Ideal.Quotient.mk I p) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

theorem aeval_jacobian_det {σ β K F : Type*} [Fintype β] [DecidableEq β]
    [CommRing K] [CommRing F] [Algebra K F]
    (z : σ → F) (v : β → σ) (G : β → MvPolynomial σ K) :
    aeval z (Matrix.det (fun i j => pderiv (v j) (G i))) =
      Matrix.det (fun i j => aeval z (pderiv (v j) (G i))) := by
  exact (aeval z).toRingHom.map_det (fun i j => pderiv (v j) (G i))

theorem bounded_patch_or_cut {n h D : ℕ} {ι K : Type*}
    [Fintype ι] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (P : Polynomial ℚ) (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) = P.eval (T : ℚ))
    (hD : (h.factorial : ℚ) * P.coeff h ≤ D)
    (j : Fin h → Fin n)
    (hj : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))))
    (z : ι → Fin n → ℤ) (hzI : ∀ p ∈ I, ∀ i, eval (fun l => (z i l : K)) p = 0)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H) :
    (∃ G : MvPolynomial (Fin n) ℤ,
      G.totalDegree ≤ D ∧
      (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ integralKernelHeight ((D+n).choose n) (H^D)) ∧
      (∀ i, eval (z i) G = 0) ∧ MvPolynomial.map (Int.castRingHom K) G ∉ I) ∨
    (∃ J : Set (Fin n), Nat.card J = h ∧
      ∃ G : ↥(Jᶜ) → MvPolynomial (Fin n) ℤ,
        (∀ i, (G i).totalDegree ≤ D) ∧
        (∀ i m, |(((G i).coeff m : ℤ) : ℝ)| ≤ integralKernelHeight ((D+n).choose n) (H^D)) ∧
        (∀ i, MvPolynomial.map (Int.castRingHom K) (G i) ∈ I) ∧
        Matrix.det (fun i l : ↥(Jᶜ) => pderiv l.val (MvPolynomial.map (Int.castRingHom K) (G i))) ∉ I) := by
  classical
  obtain ⟨G,hGdeg,hGheight,hGvan,hGspan⟩ :=
    exists_bounded_degree_vanishing_polynomials (F := K) z H hH hz D
  simp only [Fintype.card_fin] at hGheight
  by_cases hGI : ∀ a, MvPolynomial.map (Int.castRingHom K) (G a) ∈ I
  · right
    obtain ⟨J,hJ,P₁,hPdeg,hPI,hPdet⟩ := bounded_generic_jacobian I P hP hT hD j hj
    have hspan (i : ↥(Jᶜ)) : P₁ i ∈ Submodule.span K
        (Set.range (fun a => MvPolynomial.map (Int.castRingHom K) (G a))) :=
      hGspan (P₁ i) (hPdeg i) (hzI (P₁ i) (hPI i))
    have hdet : Matrix.det (fun i l : ↥(Jᶜ) =>
        aeval (genericPoint I) (pderiv l.val (P₁ i))) ≠ 0 := by
      rw [← aeval_jacobian_det]
      exact mt (aeval_genericPoint_eq_zero_iff I _).mp hPdet
    obtain ⟨a,_,ha⟩ := exists_nonsingular_jacobian_of_span
      (genericPoint I) (fun l : ↥(Jᶜ) => l.val)
      (fun a => MvPolynomial.map (Int.castRingHom K) (G a)) P₁ hspan hdet
    refine ⟨J,hJ,(fun i => G (a i)),(fun i => hGdeg (a i)),
      (fun i => hGheight (a i)),(fun i => hGI (a i)),?_⟩
    intro hm
    apply ha
    rw [← aeval_jacobian_det]
    exact (aeval_genericPoint_eq_zero_iff I _).mpr hm
  · left
    obtain ⟨a,ha⟩ := not_forall.mp hGI
    exact ⟨G a,hGdeg a,hGheight a,hGvan a,ha⟩

end

open MvPolynomial

lemma monomial_exponent_le_order {σ : Type*} (m : σ →₀ ℕ) (i : σ) :
    m i ≤ monomialOrder m := by
  classical
  by_cases hi : i ∈ m.support
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
  · simp only [Finsupp.notMem_support_iff.mp hi, Nat.zero_le]

theorem eval_abs_le_height_degree {σ : Type*} [Fintype σ]
    (p : MvPolynomial σ ℤ) (D : ℕ) (hp : p.totalDegree ≤ D)
    (C H : ℝ) (hC : 0 ≤ C) (hH : 1 ≤ H)
    (hc : ∀ m, |((p.coeff m : ℤ) : ℝ)| ≤ C)
    (z : σ → ℤ) (hz : ∀ i, |(z i : ℝ)| ≤ H) :
    |((eval z p : ℤ) : ℝ)| ≤
      ((D + Fintype.card σ).choose (Fintype.card σ) : ℝ) * C * H^D := by
  classical
  have hs : p.support ⊆ monomialsUpTo σ D := by
    intro m hm
    exact mem_monomialsUpTo.mpr ((le_totalDegree hm).trans hp)
  have hcard : p.support.card ≤ (D + Fintype.card σ).choose (Fintype.card σ) := by
    rw [← card_monomialsUpTo]
    exact Finset.card_le_card hs
  have hm (m : σ →₀ ℕ) (hm : m ∈ p.support) :
      |((p.coeff m * m.prod (fun i e => z i ^ e) : ℤ) : ℝ)| ≤ C * H^D := by
    rw [Int.cast_mul, abs_mul]
    exact mul_le_mul (hc m)
      (monomial_eval_abs_le z m H hH hz D ((le_totalDegree hm).trans hp))
      (abs_nonneg _) hC
  rw [MvPolynomial.eval_eq, Int.cast_sum]
  calc
    |∑ m ∈ p.support, ((p.coeff m * ∏ i ∈ m.support, z i ^ m i : ℤ) : ℝ)| ≤
        ∑ m ∈ p.support, |((p.coeff m * ∏ i ∈ m.support, z i ^ m i : ℤ) : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ p.support, C * H^D := Finset.sum_le_sum hm
    _ = (p.support.card : ℝ) * C * H^D := by simp [mul_assoc]
    _ ≤ ((D + Fintype.card σ).choose (Fintype.card σ) : ℝ) * C * H^D := by
      gcongr

theorem pderiv_coeff_abs_le {σ : Type*} (p : MvPolynomial σ ℤ)
    (D : ℕ) (hp : p.totalDegree ≤ D) (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ m, |((p.coeff m : ℤ) : ℝ)| ≤ C) (i : σ) (m : σ →₀ ℕ) :
    |(((pderiv i p).coeff m : ℤ) : ℝ)| ≤ (D : ℝ) * C := by
  classical
  rw [coeff_pderiv]
  by_cases hn : p.coeff (m + Finsupp.single i 1) = 0
  · simp only [hn, zero_mul, Int.cast_zero, abs_zero]
    positivity
  · have hd : monomialOrder (m + Finsupp.single i 1) ≤ D :=
      (le_totalDegree (mem_support_iff.mpr hn)).trans hp
    have hex := (monomial_exponent_le_order (m + Finsupp.single i 1) i).trans hd
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hex
    rw [Int.cast_mul, abs_mul, Int.cast_add, Int.cast_natCast, Int.cast_one,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (m i : ℝ) + 1)]
    calc
      _ ≤ C * (D : ℝ) := mul_le_mul (hc _) (by exact_mod_cast hex) (by positivity) hC
      _ = _ := mul_comm _ _

theorem pderiv_degree_le_sub_one {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (D : ℕ) (hp : p.totalDegree ≤ D) (i : σ) :
    (pderiv i p).totalDegree ≤ D-1 := by
  by_cases he : pderiv i p = 0
  · simp [he]
  · have hd := pderiv_totalDegree_lt i p he
    omega

theorem jacobian_minor_degree {σ β R : Type*} [Fintype β] [DecidableEq β]
    [CommRing R] (G : β → MvPolynomial σ R) (v : β → σ)
    (D : ℕ) (hG : ∀ i, (G i).totalDegree ≤ D) :
    (Matrix.det (fun i j => pderiv (v j) (G i))).totalDegree ≤
      Fintype.card β * (D-1) := by
  classical
  let M : Matrix β β (MvPolynomial σ R) := fun i j => pderiv (v j) (G i)
  change M.det.totalDegree ≤ _
  rw [Matrix.det_apply]
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro e _
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    ∑ i : β, (pderiv (v i) (G (e i))).totalDegree ≤ ∑ _i : β, (D-1) :=
      Finset.sum_le_sum (fun i _ => pderiv_degree_le_sub_one _ D (hG _) _)
    _ = Fintype.card β * (D-1) := by simp

theorem eval_jacobian_minor_abs_le {σ β : Type*}
    [Fintype σ] [Fintype β] [DecidableEq β]
    (G : β → MvPolynomial σ ℤ) (v : β → σ)
    (D : ℕ) (hG : ∀ i, (G i).totalDegree ≤ D)
    (C H : ℝ) (hC : 0 ≤ C) (hH : 1 ≤ H)
    (hc : ∀ i m, |(((G i).coeff m : ℤ) : ℝ)| ≤ C)
    (z : σ → ℤ) (hz : ∀ i, |(z i : ℝ)| ≤ H) :
    |((eval z (Matrix.det (fun i j => pderiv (v j) (G i))) : ℤ) : ℝ)| ≤
      (Fintype.card β).factorial *
        (((D + Fintype.card σ).choose (Fintype.card σ) : ℝ) * ((D : ℝ)*C) * H^D)^Fintype.card β := by
  let M : Matrix β β (MvPolynomial σ ℤ) := fun i j => pderiv (v j) (G i)
  change |((eval z M.det : ℤ) : ℝ)| ≤ _
  rw [(eval z).map_det M]
  apply det_abs_le_uniform
  intro i j
  apply eval_abs_le_height_degree _ D
    ((pderiv_degree_le_sub_one _ D (hG i) _).trans (Nat.sub_le _ _))
    ((D : ℝ)*C) H (mul_nonneg (Nat.cast_nonneg _) hC) hH
    (pderiv_coeff_abs_le _ D (hG i) C hC (hc i) (v j)) z hz

theorem coordinate_transcendence_basis {n : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    ∃ m : ℕ, ∃ j : Fin m → Fin n,
      AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))) ∧
      Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) = m := by
  classical
  let A := MvPolynomial (Fin n) K ⧸ I
  let x : Fin n → A := fun i => Ideal.Quotient.mk I (MvPolynomial.X i)
  have hx : MvPolynomial.aeval x = Ideal.Quotient.mkₐ K I := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X]
    rfl
  have hg : Algebra.adjoin K (Set.range x) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, hx]
    exact (AlgHom.range_eq_top _).mpr Ideal.Quotient.mk_surjective
  have : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) A := by
    rw [hg]
    constructor
    intro a
    exact isAlgebraic_algebraMap (R := (⊤ : Subalgebra K A)) ⟨a, trivial⟩
  obtain ⟨t, ht, htb⟩ := exists_isTranscendenceBasis_subset (R := K) (A := A) (Set.range x)
  have htfin : t.Finite := (Set.finite_range x).subset ht
  let : Fintype t := htfin.fintype
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  choose j hj using fun a : Fin (Fintype.card t) => ht (e a).property
  refine ⟨Fintype.card t, j, ?_, ?_⟩
  · have hi := htb.1.comp e e.injective
    simpa only [Function.comp_def, ← hj] using hi
  · rw [← htb.cardinalMk_eq_trdeg, Cardinal.mk_fintype]

theorem hilbert_natDegree_eq_trdeg {n : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (P : Polynomial ℚ)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) : (P.natDegree : Cardinal) = Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) := by
  obtain ⟨Q,j,_,hj,_,T₀,hQ⟩ := coordinate_hilbert_degree_independent I Ideal.IsPrime.ne_top'
  have hQN : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        Q.eval (T : ℚ) := Filter.eventually_atTop.mpr ⟨T₀,hQ⟩
  have hPN : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ P.eval (T : ℚ) := hT.mono (fun T ht => by
    rw [← ht]; positivity)
  have hQNN : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ Q.eval (T : ℚ) := hQN.mono (fun T ht => by
    rw [← ht]; positivity)
  have heval : ∀ᶠ T : ℕ in Filter.atTop, P.eval (T : ℚ) = Q.eval (T : ℚ) := by
    filter_upwards [hT,hQN] with T hp hq
    exact hp.symm.trans hq
  have hPQ : P.natDegree = Q.natDegree := le_antisymm
    (natDegree_le_of_eventually_nat_eval_bounds P Q hPN (heval.mono fun _ ht => ht.le))
    (natDegree_le_of_eventually_nat_eval_bounds Q P hQNN (heval.mono fun _ ht => ht.ge))
  obtain ⟨m, z, hz, hm⟩ := coordinate_transcendence_basis I
  have h1 : (P.natDegree : Cardinal) ≤ Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) := by
    rw [hPQ]
    simpa using hj.lift_cardinalMk_le_trdeg
  have h2 : m ≤ P.natDegree := by
    by_contra hh
    have hm' : P.natDegree+1 ≤ m := by omega
    let v : Fin (P.natDegree+1) → Fin n := fun a => z (Fin.castLE hm' a)
    exact not_independent_over_hilbert_degree I P le_rfl hT v
      (hz.comp (Fin.castLE hm') (Fin.castLE_injective hm'))
  rw [hm] at h1 ⊢
  exact le_antisymm h1 (by exact_mod_cast h2)

theorem proper_cut_hilbert_inequality {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I) (T : ℕ) (hT : p.totalDegree ≤ T) :
    Module.finrank K ((totalSpace T).map
      (Ideal.Quotient.mkₐ K (I ⊔ Ideal.span {p})).toLinearMap) +
      Module.finrank K ((totalSpace (T-p.totalDegree)).map
        (Ideal.Quotient.mkₐ K I).toLinearMap) ≤
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  classical
  let A := MvPolynomial (Fin n) K ⧸ I
  let J := I ⊔ Ideal.span {p}
  let F := (totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap
  let G := (totalSpace (T-p.totalDegree)).map (Ideal.Quotient.mkₐ K I).toLinearMap
  let := totalSpace_finite (n := n) (K := K) T
  let := totalSpace_finite (n := n) (K := K) (T-p.totalDegree)
  let f := (Ideal.Quotient.factorₐ K (show I ≤ J from le_sup_left)).toLinearMap.domRestrict F
  let g : G →ₗ[K] F :=
    { toFun := fun x => ⟨Ideal.Quotient.mk I p * x.val, by
        obtain ⟨q, hq, hqx⟩ := x.property
        refine ⟨p*q, ?_, ?_⟩
        · apply mem_totalSpace.mpr
          exact (totalDegree_mul p q).trans ((Nat.add_le_add_left (mem_totalSpace.mp hq) _).trans
            (by omega))
        · change Ideal.Quotient.mk I (p*q) = _
          rw [map_mul]
          exact congrArg (fun y => Ideal.Quotient.mk I p * y) hqx⟩
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp }
  have hpn : Ideal.Quotient.mk I p ≠ 0 := by
    exact fun h => hp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (mul_left_cancel₀ hpn (congrArg Subtype.val h))
  have hgle : LinearMap.range g ≤ LinearMap.ker f := by
    rintro x ⟨y, rfl⟩
    change (Ideal.Quotient.factorₐ K (show I ≤ J from le_sup_left))
      (Ideal.Quotient.mk I p * y.val) = 0
    rw [map_mul]
    have hpJ : Ideal.Quotient.mk J p = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact (le_sup_right : Ideal.span {p} ≤ J) (Ideal.subset_span (Set.mem_singleton p))
    change Ideal.Quotient.mk J p * _ = 0
    rw [hpJ, zero_mul]
  have hk : Module.finrank K G ≤ Module.finrank K (LinearMap.ker f) := by
    rw [← LinearMap.finrank_range_of_inj hg]
    exact Submodule.finrank_mono hgle
  have hdim := f.finrank_range_add_finrank_ker
  have hr : LinearMap.range f = (totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap := by
    ext z
    constructor
    · rintro ⟨⟨y, q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨Ideal.Quotient.mk I q, ⟨q, hq, rfl⟩⟩, rfl⟩
  rw [hr] at hdim
  exact (Nat.add_le_add_left hk _).trans_eq hdim

theorem coeff_taylor_high (P : Polynomial ℚ) (a : ℚ) (n : ℕ)
    (hn : P.natDegree ≤ n) : (Polynomial.taylor a P).coeff n = P.coeff n := by
  obtain h | rfl := lt_or_eq_of_le hn
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := Polynomial.taylor a P) (by simpa using h),
      Polynomial.coeff_eq_zero_of_natDegree_lt h]
  · rw [Polynomial.coeff_taylor_natDegree, Polynomial.coeff_natDegree]

theorem hilbert_difference_degree (P : Polynomial ℚ) (a : ℚ) (h : ℕ)
    (hP : P.natDegree ≤ h+1) : (P - Polynomial.taylor a P).natDegree ≤ h := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [Polynomial.coeff_sub, coeff_taylor_high P a n (by omega), sub_self]

theorem hilbert_difference_coeff (P : Polynomial ℚ) (a : ℚ) (h : ℕ)
    (hP : P.natDegree ≤ h+1) :
    (P - Polynomial.taylor (-a) P).coeff h = a * (h+1) * P.coeff (h+1) := by
  have hn : (Polynomial.hasseDeriv h P).natDegree ≤ 1 :=
    (Polynomial.natDegree_hasseDeriv_le P h).trans (by omega)
  rw [Polynomial.coeff_sub, Polynomial.taylor_coeff,
    Polynomial.eq_X_add_C_of_natDegree_le_one hn]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.hasseDeriv_coeff, zero_add, Nat.choose_self,
    Nat.cast_one, one_mul]
  rw [Nat.add_comm 1 h, Nat.choose_succ_self_right]
  push_cast
  ring

theorem proper_cut_hilbert_polynomial {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I) (P Q : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in Filter.atTop, P.eval (T : ℚ) =
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap))
    (hQ : ∀ᶠ T : ℕ in Filter.atTop, Q.eval (T : ℚ) =
      Module.finrank K ((totalSpace T).map
        (Ideal.Quotient.mkₐ K (I ⊔ Ideal.span {p})).toLinearMap))
    (h : ℕ) (hdeg : P.natDegree ≤ h+1) :
    Q.natDegree ≤ h ∧ Q.coeff h ≤ (p.totalDegree : ℚ) * (h+1) * P.coeff (h+1) := by
  let D := P - Polynomial.taylor (-(p.totalDegree : ℚ)) P
  have hD : D.natDegree ≤ h := hilbert_difference_degree P _ h hdeg
  have hn : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ Q.eval (T : ℚ) := hQ.mono (fun T hT => by
    rw [hT]; positivity)
  have hl : ∀ᶠ T : ℕ in Filter.atTop, Q.eval (T : ℚ) ≤ D.eval (T : ℚ) := by
    have hs := (Filter.tendsto_sub_atTop_nat p.totalDegree).eventually hP
    filter_upwards [hP, hQ, hs, Filter.eventually_ge_atTop p.totalDegree] with T hPT hQT hPS hT
    have hi := proper_cut_hilbert_inequality I p hp T hT
    have hie : (Module.finrank K ((totalSpace T).map
        (Ideal.Quotient.mkₐ K (I ⊔ Ideal.span {p})).toLinearMap) : ℚ) +
      Module.finrank K ((totalSpace (T-p.totalDegree)).map
        (Ideal.Quotient.mkₐ K I).toLinearMap) ≤
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
      exact_mod_cast hi
    dsimp [D]
    rw [Polynomial.eval_sub, Polynomial.taylor_eval, ← sub_eq_add_neg,
      ← Nat.cast_sub hT, hPT, hQT, hPS]
    exact le_sub_iff_add_le.mpr hie
  have hdQ := (natDegree_le_of_eventually_nat_eval_bounds Q D hn hl).trans hD
  refine ⟨hdQ, ?_⟩
  have hc := coeff_le_of_eventually_nat_eval_le Q D h hdQ hD hl
  exact hc.trans_eq (hilbert_difference_coeff P (p.totalDegree : ℚ) h hdeg)

end QuarticPowerFree

end OAI
