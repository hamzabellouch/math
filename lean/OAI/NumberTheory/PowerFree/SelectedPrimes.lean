import OAI.NumberTheory.PowerFree.CurveAlternatives

namespace OAI

namespace QuarticPowerFree

section
open Polynomial
open scoped BigOperators Classical

theorem primitive_map_zmod_ne_zero (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (p : ℕ) (hp : p.Prime) : f.map (Int.castRingHom (ZMod p)) ≠ 0 := by
  intro hz
  have hd : Polynomial.C (p:ℤ) ∣ f := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    have hh := congrArg (fun g : Polynomial (ZMod p) => g.coeff i) hz
    simpa using hh
  have hu := Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mp hf (p:ℤ) hd
  have he := Int.isUnit_iff_natAbs_eq.mp hu
  exact hp.ne_one (by simpa using he)

theorem selected_constant_prime_count (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (p : ℕ) (hp : p.Prime) (X : ℝ) (hXp : X < p) (S : Finset (Fin 3 → ℤ))
    (hinj : Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set (Fin 3 → ℤ)))
    (hrange : ∀ z ∈ S, X < (z 0:ℝ) ∧ (z 0:ℝ) ≤ 2*X)
    (hroot : ∀ z ∈ S, (p:ℤ) ∣ f.eval (z 0)) : S.card ≤ f.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let F := f.map (Int.castRingHom (ZMod p))
  have hF : F ≠ 0 := primitive_map_zmod_ne_zero f hf p hp
  have hmap : Set.MapsTo (fun z : Fin 3 → ℤ => (z 0 : ZMod p)) (S:Set _) (F.roots.toFinset:Set _) := by
    intro z hz
    rw [Finset.mem_coe,Multiset.mem_toFinset,Polynomial.mem_roots hF]
    change F.eval (z 0 : ZMod p) = 0
    rw [show F = f.map (Int.castRingHom (ZMod p)) from rfl,Polynomial.eval_map]
    change f.eval₂ (Int.castRingHom (ZMod p)) ((Int.castRingHom (ZMod p)) (z 0)) = 0
    rw [Polynomial.eval₂_at_apply]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hroot z hz)
  have hmodinj : Set.InjOn (fun z : Fin 3 → ℤ => (z 0 : ZMod p)) (S:Set _) := by
    intro u hu v hv huv
    apply hinj hu hv
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub (u 0) (v 0) p).mp huv
    obtain ⟨hu1,hu2⟩ := hrange u hu
    obtain ⟨hv1,hv2⟩ := hrange v hv
    have hh : |((v 0-u 0:ℤ):ℝ)| < (p:ℝ) := by
      push_cast
      rw [abs_lt]
      constructor <;> linarith
    have hh' : (v 0-u 0).natAbs < p := by
      exact_mod_cast (show ((v 0-u 0).natAbs:ℝ) < p by simpa only [Nat.cast_natAbs,Int.cast_abs] using hh)
    have he : v 0-u 0 = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd (by simpa using hh')
    exact (sub_eq_zero.mp he).symm
  calc
    S.card ≤ F.roots.toFinset.card := Finset.card_le_card_of_injOn _ hmap hmodinj
    _ ≤ F.roots.card := Multiset.toFinset_card_le _
    _ ≤ F.natDegree := Polynomial.card_roots' _
    _ ≤ f.natDegree := Polynomial.natDegree_map_le

end
open MvPolynomial
open scoped BigOperators Classical

noncomputable def pointEvaluation {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : PointOn I z) :
    (MvPolynomial (Fin n) K ⧸ I) →ₐ[K] K :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval (fun j => (z j : K))) (by
    intro p hp
    exact hz p hp)

@[simp] theorem pointEvaluation_X {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : PointOn I z) (j : Fin n) :
    pointEvaluation I z hz (Ideal.Quotient.mk I (X j)) = (z j:K) := by
  change MvPolynomial.aeval (fun i => (z i:K)) (X j) = _
  simp

theorem coordinate_constant_at_point {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : PointOn I z) (j : Fin n)
    (c : K) (hc : algebraMap K (MvPolynomial (Fin n) K ⧸ I) c = Ideal.Quotient.mk I (X j)) :
    (z j:K) = c := by
  have he := congrArg (pointEvaluation I z hz) hc
  simpa only [AlgHom.commutes,Algebra.algebraMap_self, RingHom.id_apply,pointEvaluation_X] using he.symm

theorem rational_coordinate_at_point {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : PointOn I z) (x j : Fin n)
    (A B : Polynomial K)
    (he : Polynomial.aeval (Ideal.Quotient.mk I (X x)) A =
      Ideal.Quotient.mk I (X j)*Polynomial.aeval (Ideal.Quotient.mk I (X x)) B) :
    A.eval (z x:K) = (z j:K)*B.eval (z x:K) := by
  have hh := congrArg (pointEvaluation I z hz) he
  rw [map_mul,← Polynomial.aeval_algHom_apply,← Polynomial.aeval_algHom_apply] at hh
  simpa only [pointEvaluation_X,Polynomial.aeval_def,
    Algebra.algebraMap_self,Polynomial.eval₂_id] using hh

theorem rational_selected_count (D : ℕ) (hD : 0 < D) (ω : Fin 3 → ℝ)
    (hω : ∀ i, 0 < ω i) (hω0 : ω 0 = 1) (Cbox : ℝ) (hCbox : 0 < Cbox)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (X : ℝ), 2 ≤ X → ∀ (S : Finset (Fin 3 → ℤ)),
      Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set _) →
      (∀ z ∈ S, ∀ i, |(z i:ℝ)| ≤ Cbox*X^(ω i)) →
      ∀ (j : Fin 3) (A B : Polynomial ℂ), (j = 1 ∨ j = 2) → IsCoprime A B →
      0 < B.natDegree → A.natDegree ≤ D → B.natDegree ≤ D →
      (∀ z ∈ S, A.eval (z 0:ℂ) = (z j:ℂ)*B.eval (z 0:ℂ)) →
      (S.card:ℝ) ≤ C*X^ε := by
  classical
  obtain ⟨C,hC,hbound⟩ := ComplexValues.rational_integer_values_uniform D hD 1 (max (ω 1) (ω 2)) Cbox
    (by norm_num) (lt_of_lt_of_le (hω 1) (le_max_left _ _)) hCbox ε hε
  refine ⟨C,hC,?_⟩
  intro X hX S hinj hbox j A B hj hcop hB hAD hBD he
  let v : ℤ → ℤ := fun s => if hs : ∃ z ∈ S, z 0 = s then hs.choose j else 0
  have hv (z) (hz : z ∈ S) : v (z 0) = z j := by
    have hs : ∃ u ∈ S, u 0 = z 0 := ⟨z,hz,rfl⟩
    dsimp only [v]
    rw [dite_eq_left hs]
    have hu := hinj hs.choose_spec.1 hz hs.choose_spec.2
    exact congrArg (fun u => u j) hu
  have hcard : (S.image fun z => z 0).card = S.card := Finset.card_image_of_injOn hinj
  rw [← hcard]
  apply hbound A B hcop hB hAD hBD _ v X hX
  · intro s hs
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    rw [hv z hz]
    exact he z hz
  · intro s hs
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    simpa only [hω0] using hbox z hz 0
  · intro s hs
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hs
    rw [hv z hz]
    apply (hbox z hz j).trans
    gcongr
    · linarith
    · rcases hj with rfl | rfl
      · exact le_max_left _ _
      · exact le_max_right _ _

theorem direct_curve_count_or_hilbert (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hsq : Squarefree (f.map (Int.castRingHom ℂ))) (k : ℕ) (hk : 2 ≤ k)
    (e : ℕ) (ω : Fin 3 → ℝ) (hω : ∀ j, 0 < ω j) (hω0 : ω 0 = 1)
    (Cbox : ℝ) (hCbox : 0 < Cbox) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (X : ℝ), 2 ≤ X → ∀ (S : Finset (Fin 3 → ℤ)),
      Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set _) →
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ z ∈ S, X < (z 0:ℝ) ∧ (z 0:ℝ) ≤ 2*X) →
      (∀ z ∈ S, ∃ p : ℕ, p.Prime ∧ z 2 = p ∧ X < p ∧ (p:ℤ) ∣ f.eval (z 0)) →
      ∀ (I : Ideal (MvPolynomial (Fin 3) ℂ)), I.IsPrime →
      affineDimension I ≤ 1 → affineDegree I ≤ e →
      (∀ z ∈ S, PointOn I z) →
      (Polynomial.aeval (Ideal.Quotient.mk I (MvPolynomial.X 0)) (f.map (Int.castRingHom ℂ)) =
        Ideal.Quotient.mk I (MvPolynomial.X 1)*(Ideal.Quotient.mk I (MvPolynomial.X 2))^k) →
      (S.card:ℝ) ≤ C*X^ε ∨
        (∀ T : ℝ, 1 ≤ T → 2*T-2*(ω 1+ω 2+1) ≤ weightedHilbert I ω T) := by
  classical
  obtain ⟨Cr,hCr,hcount⟩ := rational_selected_count (e+1) (by omega) ω hω hω0 Cbox hCbox ε hε
  let C : ℝ := 1+Cr+f.natDegree
  have hC : 1 ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) f.natDegree]
  refine ⟨C,hC,?_⟩
  intro X hX S hinj hbox hrange hselected I hI hdim hdeg hon he
  let : I.IsPrime := hI
  have hpow : 1 ≤ X^ε := Real.one_le_rpow (by linarith) hε.le
  have hsmall (a : ℕ) (ha : S.card ≤ a) (haC : (a:ℝ) ≤ C) : (S.card:ℝ) ≤ C*X^ε := by
    have ha' : (S.card:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
    exact ha'.trans (haC.trans (le_mul_of_one_le_right (zero_le_one.trans hC) hpow))
  rcases direct_curve_alternative I hdim e hdeg ω hω hω0 (f.map (Int.castRingHom ℂ)) hsq k hk he with
    ⟨c,hc⟩ | ⟨j,A,B,hj,hcop,hB,hAD,hBD,hrel⟩ | ⟨c,hc⟩ | hH
  · left
    apply hsmall 1 _ (by simpa using hC)
    apply Finset.card_le_one.mpr
    intro u hu v hv
    apply hinj hu hv
    apply Int.cast_injective (α := ℂ)
    exact (coordinate_constant_at_point I u (hon u hu) 0 c hc).trans
      (coordinate_constant_at_point I v (hon v hv) 0 c hc).symm
  · left
    have hC' : Cr ≤ C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) f.natDegree]
    exact (hcount X hX S hinj hbox j A B hj hcop hB (by omega) (by omega)
      (fun z hz => rational_coordinate_at_point I z (hon z hz) 0 j A B hrel)).trans
      (mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg (by linarith) _))
  · left
    by_cases hn : S.Nonempty
    · obtain ⟨u,hu⟩ := hn
      obtain ⟨p,hp,hup,hXp,_⟩ := hselected u hu
      have hroot (z) (hz : z ∈ S) : (p:ℤ) ∣ f.eval (z 0) := by
        obtain ⟨q,hq,hzq,_,hroot⟩ := hselected z hz
        have heq : z 2 = u 2 := Int.cast_injective ((coordinate_constant_at_point I z (hon z hz) 2 c hc).trans
          (coordinate_constant_at_point I u (hon u hu) 2 c hc).symm)
        rw [hup,hzq] at heq
        have hqp : q = p := by exact_mod_cast heq
        simpa only [hqp] using hroot
      apply hsmall f.natDegree (selected_constant_prime_count f hf p hp X hXp S hinj hrange hroot)
      dsimp [C]
      linarith
    · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
      subst S
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  · exact Or.inr hH

noncomputable def directSurface {K : Type*} [CommRing K] (f : Polynomial K) (k : ℕ) :
    MvPolynomial (Fin 3) K := Polynomial.eval₂ C (X 0) f - X 1*(X 2)^k

noncomputable def directSurfaceEquiv (K : Type*) [CommRing K] :
    MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
  (renameEquiv K (Equiv.swap 0 1)).trans (finSuccEquiv K 2)

@[simp] theorem directSurfaceEquiv_X0 {K : Type*} [CommRing K] :
    directSurfaceEquiv K (X 0) = Polynomial.C (X 0) := by
  simp [directSurfaceEquiv,finSuccEquiv_apply]
  rfl

@[simp] theorem directSurfaceEquiv_X1 {K : Type*} [CommRing K] :
    directSurfaceEquiv K (X 1) = Polynomial.X := by
  simp [directSurfaceEquiv,finSuccEquiv_apply]

@[simp] theorem directSurfaceEquiv_X2 {K : Type*} [CommRing K] :
    directSurfaceEquiv K (X 2) = Polynomial.C (X 1) := by
  simp [directSurfaceEquiv,Equiv.swap_apply_of_ne_of_ne,finSuccEquiv_apply]
  rfl

@[simp] theorem directSurfaceEquiv_C {K : Type*} [CommRing K] (c : K) :
    directSurfaceEquiv K (C c) = Polynomial.C (C c) := by
  simp [directSurfaceEquiv,finSuccEquiv_apply]

theorem directSurfaceEquiv_apply {K : Type*} [CommRing K] (f : Polynomial K) (k : ℕ) :
    directSurfaceEquiv K (directSurface f k) =
      Polynomial.C (-(X 1)^k) * Polynomial.X + Polynomial.C (Polynomial.eval₂ C (X 0) f) := by
  have he : directSurfaceEquiv K (Polynomial.eval₂ C (X 0) f) =
      Polynomial.C (Polynomial.eval₂ C (X 0) f) := by
    induction f using Polynomial.induction_on' with
    | add p q hp hq => simp only [Polynomial.eval₂_add,map_add,hp,hq]
    | monomial n a => simp [Polynomial.eval₂_monomial,mul_comm]
  simp only [directSurface,map_sub,he,map_mul,map_pow,directSurfaceEquiv_X1,directSurfaceEquiv_X2,
    Polynomial.C_neg]
  ring

theorem directSurface_coeff_relprime {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (k : ℕ) :
    IsRelPrime (-(X (1:Fin 2))^k) (Polynomial.eval₂ C (X 0) f) := by
  have hn : ¬ (X (1:Fin 2) : MvPolynomial (Fin 2) K) ∣ Polynomial.eval₂ C (X 0) f := by
    intro hd
    let ψ : MvPolynomial (Fin 2) K →+* Polynomial K := eval₂Hom Polynomial.C ![Polynomial.X,0]
    have he : ψ (Polynomial.eval₂ C (X 0) f) = f := by
      clear hf hd
      induction f using Polynomial.induction_on' with
      | add p q hp hq => simp only [Polynomial.eval₂_add,map_add,hp,hq]
      | monomial n a => simp [Polynomial.eval₂_monomial,ψ,Polynomial.C_mul_X_pow_eq_monomial]
    have hh := map_dvd ψ hd
    apply hf
    simpa only [ψ,eval₂Hom_X',Matrix.cons_val_one,Matrix.cons_val_zero,zero_dvd_iff,he] using hh
  have hp := (MvPolynomial.X_prime (i := (1:Fin 2)) (R := K)).irreducible
  exact ((hp.isRelPrime_iff_not_dvd.mpr hn).pow_left).neg_left

theorem directSurface_irreducible {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (k : ℕ) : Irreducible (directSurface f k) := by
  apply (MulEquiv.irreducible_iff (directSurfaceEquiv K)).mp
  rw [directSurfaceEquiv_apply]
  exact Polynomial.irreducible_C_mul_X_add_C (neg_ne_zero.mpr (pow_ne_zero _ (X_ne_zero _)))
    (directSurface_coeff_relprime f hf k)

theorem coeff_single_eval₂_C_X {σ K : Type*} [CommSemiring K] (i : σ)
    (f : Polynomial K) (n : ℕ) :
    (Polynomial.eval₂ C (X i) f).coeff (Finsupp.single i n) = f.coeff n := by
  classical
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.eval₂_add,AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply,Polynomial.coeff_add,hp,hq]
  | monomial m a =>
    simp [Polynomial.eval₂_monomial,C_mul_X_pow_eq_monomial,coeff_monomial,
      Polynomial.coeff_monomial,(Finsupp.single_injective i).eq_iff]

theorem directSurface_coeff_single {K : Type*} [CommRing K]
    (f : Polynomial K) (k n : ℕ) :
    (directSurface f k).coeff (Finsupp.single 0 n) = f.coeff n := by
  classical
  have hne : Finsupp.single (1:Fin 3) 1 + Finsupp.single 2 k ≠ Finsupp.single 0 n := by
    intro h
    have hh := congrArg (fun v : Fin 3 →₀ ℕ => v 1) h
    simp at hh
  rw [directSurface,coeff_sub,coeff_single_eval₂_C_X,X_pow_eq_monomial]
  rw [X,monomial_mul_monomial,one_mul,coeff_monomial,ite_eq_right hne,sub_zero]

theorem directSurface_weightedDegree_lower {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (k : ℕ) (w : Fin 3 → ℕ) :
    f.natDegree*w 0 ≤ weightedTotalDegree w (directSurface f k) := by
  have hm : Finsupp.single 0 f.natDegree ∈ (directSurface f k).support := by
    rw [mem_support_iff,directSurface_coeff_single]
    exact Polynomial.leadingCoeff_ne_zero.mpr hf
  have hh := Finset.le_sup (f := Finsupp.weight w) hm
  simpa only [weightedTotalDegree,Finsupp.weight_single,nsmul_eq_mul,Nat.cast_id] using hh

theorem totalDegree_pos_of_irreducible {σ K : Type*} [Field K]
    (F : MvPolynomial σ K) (hF : Irreducible F) : 0 < F.totalDegree := by
  by_contra hn
  have hd : F.totalDegree = 0 := by omega
  have he : F = C (F.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp hd
  have hc : F.coeff 0 ≠ 0 := by intro hh; rw [he,hh,map_zero] at hF; exact hF.ne_zero rfl
  exact hF.not_isUnit (he ▸ (isUnit_iff_ne_zero.mpr hc).map C)

end QuarticPowerFree

end OAI
