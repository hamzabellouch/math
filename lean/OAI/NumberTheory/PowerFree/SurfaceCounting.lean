import OAI.NumberTheory.PowerFree.SelectedPrimes

namespace OAI

namespace QuarticPowerFree
open MvPolynomial
open scoped BigOperators Classical

theorem coordinateHilbert_hypersurface {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin (n+1)) K) (hF : F ≠ 0) :
    coordinateHilbert (Ideal.span {F}) = hypersurfaceHilbertPolynomial n F.totalDegree := by
  apply polynomial_eq_of_eventually_nat_eval_eq
  filter_upwards [coordinateHilbert_eventually (Ideal.span {F}),
    Filter.eventually_ge_atTop F.totalDegree] with T he hT
  exact he.symm.trans (hypersurface_hilbert_polynomial F hF T hT)

theorem affineDimension_hypersurface {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin (n+1)) K) (hF : F ≠ 0) (hdeg : 0 < F.totalDegree) :
    affineDimension (Ideal.span {F}) = n := by
  rw [affineDimension,coordinateHilbert_hypersurface F hF]
  apply le_antisymm (hypersurfaceHilbertPolynomial_degree n F.totalDegree)
  apply Polynomial.le_natDegree_of_ne_zero
  rw [hypersurfaceHilbertPolynomial_coeff]
  exact div_ne_zero (by exact_mod_cast hdeg.ne') (by exact_mod_cast Nat.factorial_ne_zero n)

theorem affineDegree_hypersurface {n : ℕ} {K : Type*} [Field K]
    (F : MvPolynomial (Fin (n+1)) K) (hF : F ≠ 0) (hdeg : 0 < F.totalDegree) :
    affineDegree (Ideal.span {F}) = F.totalDegree := by
  rw [affineDegree,affineDimension_hypersurface F hF hdeg,
    coordinateHilbert_hypersurface F hF,hypersurfaceHilbertPolynomial_coeff]
  field_simp

theorem affineDimension_lt_of_lt {n h : ℕ} {K : Type*} [Field K]
    (I J : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hIJ : I < J) (hd : affineDimension I = h+1) :
    affineDimension J ≤ h := by
  obtain ⟨p,hpJ,hpI⟩ := SetLike.exists_of_lt hIJ
  have hcut : I ⊔ Ideal.span {p} ≤ J := sup_le hIJ.le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpJ))
  have hdeg := (proper_cut_hilbert_polynomial I p hpI (coordinateHilbert I)
    (coordinateHilbert (I ⊔ Ideal.span {p}))
    ((coordinateHilbert_eventually I).mono (fun _ ht => ht.symm))
    ((coordinateHilbert_eventually _).mono (fun _ ht => ht.symm)) h hd.le).1
  have hnon : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ (coordinateHilbert J).eval (T:ℚ) := by
    filter_upwards [coordinateHilbert_eventually J] with T he
    rw [← he]; positivity
  have hle : ∀ᶠ T : ℕ in Filter.atTop,
      (coordinateHilbert J).eval (T:ℚ) ≤ (coordinateHilbert (I ⊔ Ideal.span {p})).eval (T:ℚ) := by
    filter_upwards [coordinateHilbert_eventually J,coordinateHilbert_eventually (I ⊔ Ideal.span {p})]
      with T hJ hI
    rw [← hJ,← hI]
    exact_mod_cast quotient_hilbert_le _ J hcut T
  exact (natDegree_le_of_eventually_nat_eval_bounds _ _ hnon hle).trans hdeg

theorem prime_same_dimension_eq {n h : ℕ} {K : Type*} [Field K]
    (I J : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hIJ : I ≤ J) (hdI : affineDimension I = h+1) (hdJ : affineDimension J = h+1) :
    I = J := by
  by_contra hne
  have h := affineDimension_lt_of_lt I J (lt_of_le_of_ne hIJ hne) hdI
  omega

theorem weightedSpace_map_le_weightedFunctions {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (w : Fin n → ℕ) (ω : Fin n → ℝ)
    (hω : ∀ i, 0 < ω i) (L : ℝ) (hL : 0 < L)
    (hw : ∀ i, (w i : ℝ) = L*ω i) (T : ℝ) (hT : 0 ≤ T) :
    (weightedSpace w ⌊L*T⌋₊).map (Ideal.Quotient.mkₐ K I).toLinearMap ≤
      weightedFunctions I ω T := by
  classical
  rintro y ⟨p,hp,rfl⟩
  have hs : ∀ a ∈ p.support, monomialWeight ω a ≤ T := by
    intro a ha
    have hh : Finsupp.weight w a ≤ ⌊L*T⌋₊ :=
      hp ha
    have he : (Finsupp.weight w a : ℝ) = L*monomialWeight ω a := by
      rw [Finsupp.weight_eq_sum]
      simp only [Nat.cast_sum,monomialWeight,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [nsmul_eq_mul,Nat.cast_mul,hw]
      norm_cast
      ring
    have hhN : (Finsupp.weight w a : ℝ) ≤ (⌊L*T⌋₊:ℕ) := by exact_mod_cast hh
    have hh' : (Finsupp.weight w a : ℝ) ≤ L*T :=
      hhN.trans (Nat.floor_le (mul_nonneg hL.le hT))
    rw [he] at hh'
    exact (mul_le_mul_iff_right₀ hL).mp hh'
  rw [p.as_sum,map_sum]
  apply Submodule.sum_mem
  intro a ha
  have hm : Ideal.Quotient.mk I (monomial a (1:K)) ∈ weightedFunctions I ω T :=
    Submodule.subset_span ⟨a,(mem_weightedMonomials ω hω T a).mpr (hs a ha),rfl⟩
  have he : monomial a (p.coeff a) = (p.coeff a) • monomial a (1:K) := by
    rw [smul_monomial,smul_eq_mul,mul_one]
  rw [he]
  simpa using (weightedFunctions I ω T).smul_mem (p.coeff a) hm

theorem real_surface_hilbert_lower {K : Type*} [Field K]
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (F : MvPolynomial (Fin 3) K) (hF : F ≠ 0)
    (ω : Fin 3 → ℝ) (hω : ∀ i, 0 < ω i)
    (hw : ∀ i, (tripleWeights a b c i : ℝ) = (a:ℝ)*ω i) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      ((weightedTotalDegree (tripleWeights a b c) F : ℕ):ℝ)*(a:ℝ)^2 /
        (2*(a*b*c:ℕ)) * T^2 - C*T ≤ weightedHilbert (Ideal.span {F}) ω T := by
  classical
  obtain ⟨C,hC,hH⟩ := surface_hilbert_error ha hb hc F hF
  let D := weightedTotalDegree (tripleWeights a b c) F
  let A : ℝ := D/(2*(a*b*c:ℕ))
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have habc : (0:ℝ) < (a*b*c:ℕ) := by exact_mod_cast Nat.mul_pos (Nat.mul_pos ha hb) hc
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let E : ℝ := A*(2*a + (D:ℝ)^2) + C*(a+1)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨E,hE,?_⟩
  intro T hT
  let N := ⌊(a:ℝ)*T⌋₊
  have hN : (N:ℝ) ≤ a*T := Nat.floor_le (by positivity)
  have hN' : a*T < (N:ℝ)+1 := Nat.lt_floor_add_one _
  have hrank := Submodule.finrank_mono (weightedSpace_map_le_weightedFunctions
    (Ideal.span {F}) (tripleWeights a b c) ω hω (a:ℝ) ha' hw T (by linarith))
  have htarget : ((weightedTotalDegree (tripleWeights a b c) F : ℕ):ℝ)*(a:ℝ)^2 /
      (2*(a*b*c:ℕ))*T^2 = A*((a:ℝ)*T)^2 := by dsimp [A,D]; ring
  rw [htarget]
  by_cases hDN : D ≤ N
  · have hh := (abs_le.mp (hH N hDN)).1
    have hr : (Module.finrank K ((weightedSpace (tripleWeights a b c) N).map
        (Ideal.Quotient.mkₐ K (Ideal.span {F})).toLinearMap):ℝ) ≤
        weightedHilbert (Ideal.span {F}) ω T := by exact_mod_cast hrank
    have hsq : ((a:ℝ)*T)^2 ≤ (N:ℝ)^2+2*a*T := by
      have hnn : (0:ℝ) ≤ N := Nat.cast_nonneg _
      nlinarith
    have hh' : A*(N:ℝ)^2-C*((N:ℝ)+1) ≤ weightedHilbert (Ideal.span {F}) ω T := by
      have hv : A*(N:ℝ)^2 =
          ((weightedTotalDegree (tripleWeights a b c) F : ℕ):ℝ)*(N:ℝ)^2/(2*(a*b*c:ℕ)) := by
        dsimp [A,D]; ring
      rw [← hv] at hh
      linarith only [hh,hr]
    have hCs : C*((N:ℝ)+1) ≤ C*(a+1)*T := by nlinarith
    have hAs := mul_le_mul_of_nonneg_left hsq hA
    have hDterm : 0 ≤ A*(D:ℝ)^2*T := by positivity
    dsimp [E]
    nlinarith only [hAs,hh',hCs,hDterm]
  · have hND : N+1 ≤ D := by omega
    have hbound : (a:ℝ)*T ≤ D := by
      have hND' : (N:ℝ)+1 ≤ D := by exact_mod_cast hND
      linarith
    have hsq : ((a:ℝ)*T)^2 ≤ (D:ℝ)^2 := sq_le_sq₀ (by positivity) (by positivity) |>.mpr hbound
    have hAs := mul_le_mul_of_nonneg_left hsq hA
    have hDterm : A*(D:ℝ)^2 ≤ A*(D:ℝ)^2*T := le_mul_of_one_le_right (by positivity) hT
    have hr : (0:ℝ) ≤ weightedHilbert (Ideal.span {F}) ω T := Nat.cast_nonneg _
    have hother : 0 ≤ (A*(2*a)+C*(a+1))*T := by positivity
    dsimp [E]
    nlinarith

theorem directSurface_equation {K : Type*} [Field K] (f : Polynomial K) (k : ℕ)
    (J : Ideal (MvPolynomial (Fin 3) K)) (hJ : Ideal.span {directSurface f k} ≤ J) :
    Polynomial.aeval (Ideal.Quotient.mk J (X 0)) f =
      Ideal.Quotient.mk J (X 1)*(Ideal.Quotient.mk J (X 2))^k := by
  have hz : Ideal.Quotient.mk J (directSurface f k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hJ (Ideal.subset_span (Set.mem_singleton _)))
  have he : Ideal.Quotient.mk J (Polynomial.eval₂ C (X 0) f) =
      Polynomial.aeval (Ideal.Quotient.mk J (X 0)) f := by
    change (Ideal.Quotient.mkₐ K J) (Polynomial.aeval (X 0) f) = _
    exact (Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ K J) (X 0) f).symm
  simpa only [directSurface,map_sub,map_mul,map_pow,he,sub_eq_zero] using hz

theorem directSurface_hilbert_threshold {K : Type*} [Field K]
    (f : Polynomial K) (hf : f ≠ 0) (k : ℕ)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ω : Fin 3 → ℝ) (hω : ∀ i, 0 < ω i)
    (hw : ∀ i, (tripleWeights a b c i : ℝ) = (a:ℝ)*ω i)
    (δ : ℝ) (hδ : 0 < δ)
    (hmargin : (b:ℝ)*(c:ℝ) ≤ (f.natDegree:ℝ)*(a:ℝ)^2*δ^2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      T^2/(2*δ^2)-C*T ≤ weightedHilbert (Ideal.span {directSurface f k}) ω T := by
  have hF := (directSurface_irreducible f hf k).ne_zero
  obtain ⟨C,hC,hH⟩ := real_surface_hilbert_lower ha hb hc (directSurface f k) hF ω hω hw
  refine ⟨C,hC,?_⟩
  intro T hT
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have hb' : (0:ℝ) < b := by exact_mod_cast hb
  have hc' : (0:ℝ) < c := by exact_mod_cast hc
  let D := weightedTotalDegree (tripleWeights a b c) (directSurface f k)
  have hD : (f.natDegree:ℝ)*(a:ℝ) ≤ (D:ℝ) := by
    have hh := directSurface_weightedDegree_lower f hf k (tripleWeights a b c)
    simpa only [tripleWeights,Matrix.cons_val_zero,Nat.cast_mul] using (show
      ((f.natDegree*tripleWeights a b c 0:ℕ):ℝ) ≤ D from by exact_mod_cast hh)
  have he : (D:ℝ)*(a:ℝ)^2/(2*(a*b*c:ℕ)) = (D:ℝ)*a/(2*(b:ℝ)*c) := by
    push_cast
    field_simp
  have hcoeff : 1/(2*δ^2) ≤ (D:ℝ)*(a:ℝ)^2/(2*(a*b*c:ℕ)) := by
    rw [he]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_right hD (show 0 ≤ (a:ℝ)*δ^2 by positivity)
    nlinarith only [hmargin,hm]
  have hh := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg T)
  have hH' := hH T hT
  dsimp only [D] at hh
  have heq : 1/(2*δ^2)*T^2 = T^2/(2*δ^2) := by ring
  rw [heq] at hh
  linarith only [hh,hH']

theorem direct_surface_selected_count (f : Polynomial ℤ) (hf : f.IsPrimitive)
    (hsq : Squarefree (f.map (Int.castRingHom ℂ))) (k : ℕ) (hk : 2 ≤ k)
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ω : Fin 3 → ℝ) (hω : ∀ j, 0 < ω j) (hω0 : ω 0 = 1)
    (hw : ∀ i, (tripleWeights a b c i : ℝ) = (a:ℝ)*ω i)
    (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1/2)
    (hmargin : (b:ℝ)*(c:ℝ) ≤ (f.natDegree:ℝ)*(a:ℝ)^2*δ^2)
    (Cbox : ℝ) (hCbox : 1 ≤ Cbox) (ε : ℝ) (hε : 0 < ε) :
    ∃ C X₀ : ℝ, 0 < C ∧ ∀ X : ℝ, X₀ < X → ∀ S : Finset (Fin 3 → ℤ),
      Set.InjOn (fun z : Fin 3 → ℤ => z 0) (S:Set _) →
      (∀ z ∈ S, ∀ j, |(z j:ℝ)| ≤ Cbox*X^(ω j)) →
      (∀ z ∈ S, X < (z 0:ℝ) ∧ (z 0:ℝ) ≤ 2*X) →
      (∀ z ∈ S, ∃ p : ℕ, p.Prime ∧ z 2 = p ∧ X < p ∧ (p:ℤ) ∣ f.eval (z 0)) →
      (∀ z ∈ S, (f.map (Int.castRingHom ℂ)).eval (z 0:ℂ) = (z 1:ℂ)*(z 2:ℂ)^k) →
      (S.card:ℝ) ≤ C*X^(δ+1/2+ε) := by
  classical
  let fc := f.map (Int.castRingHom ℂ)
  have hfc : fc ≠ 0 := (Polynomial.map_ne_zero_iff (Int.cast_injective)).mpr hf.ne_zero
  have hdegfc : fc.natDegree = f.natDegree := Polynomial.natDegree_map_eq_of_injective (Int.cast_injective) f
  let F := directSurface fc k
  have hFir : Irreducible F := directSurface_irreducible fc hfc k
  have hFdeg : 0 < F.totalDegree := totalDegree_pos_of_irreducible F hFir
  let I := Ideal.span {F}
  have hI : I.IsPrime := (Ideal.span_singleton_prime hFir.ne_zero).mpr hFir.prime
  let : I.IsPrime := hI
  have hdI : affineDimension I = 2 := affineDimension_hypersurface F hFir.ne_zero hFdeg
  have heI : affineDegree I = F.totalDegree := affineDegree_hypersurface F hFir.ne_zero hFdeg
  have hmarginc : (b:ℝ)*(c:ℝ) ≤ (fc.natDegree:ℝ)*(a:ℝ)^2*δ^2 := by rwa [hdegfc]
  obtain ⟨Cs,hCs,hHs⟩ := directSurface_hilbert_threshold fc hfc k ha hb hc ω hω hw δ hδ hmarginc
  choose Kex hKex hcurve using fun e => direct_curve_count_or_hilbert f hf hsq k hk e ω hω hω0
    Cbox (by linarith) (ε/4) (by linarith)
  let cc := fun _ : ℕ => Cs+2*(ω 1+ω 2+1)
  have hcc : ∀ e, 0 ≤ cc e := by intro e; dsimp [cc]; linarith [hω 1,hω 2]
  let av : Fin 2 → ℝ := ![δ,1/2-δ]
  let dv : Fin 2 → ℝ := ![δ,1/2]
  have hav : ∀ i, 0 ≤ av i := by intro i; fin_cases i <;> simp [av] <;> linarith
  have hdv : ∀ i, 0 < dv i := by intro i; fin_cases i <;> simp [dv,hδ]
  have hprefix : ∀ i, dv i ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin 2 => j.val ≤ i.val), av j := by
    intro i
    fin_cases i <;> norm_num [av,dv,Fin.sum_univ_two,Finset.sum_filter]
  let w := 1+∑ j, ω j
  have hsum : 0 ≤ ∑ j, ω j := Finset.sum_nonneg (fun j _ => (hω j).le)
  have hwpos : 0 ≤ w := by dsimp [w]; linarith
  obtain ⟨C,Xcut,hC,hcount⟩ := physical_affine_count 3 2 0 F.totalDegree (by norm_num)
    ω hω Cbox w hCbox hwpos av dv hav hdv hprefix ε hε cc Kex hcc hKex
  refine ⟨C,max (max 2 Cbox) Xcut,hC,?_⟩
  intro X hX S hinj hbox hrange hselected heq
  have hX2 : 2 < X := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hX
  have hCX : Cbox ≤ X := le_of_lt (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hX)
  have hXcut : Xcut < X := lt_of_le_of_lt (le_max_right _ _) hX
  have hX1 : 1 ≤ X := by linarith
  have hXp : 0 < X := by linarith
  have hmax (j : Fin 3) : ω j ≤ ∑ l, ω l :=
    Finset.single_le_sum (fun l _ => (hω l).le) (Finset.mem_univ j)
  have hbound (z) (hz : z ∈ S) (j) : |(z j:ℝ)| ≤ X^w := by
    calc
      _ ≤ Cbox*X^(ω j) := hbox z hz j
      _ ≤ X*X^(∑ l, ω l) := mul_le_mul hCX (Real.rpow_le_rpow_of_exponent_le hX1 (hmax j))
        (Real.rpow_nonneg hXp.le _) (by linarith)
      _ = X^w := by dsimp [w]; rw [Real.rpow_add hXp,Real.rpow_one]
  let G : KernelGeometry 3 := ⟨S,X^w,Real.one_le_rpow hX1 hwpos,hbound⟩
  have hpoints : ∀ z ∈ G.points, PointOn I z := by
    intro z hz
    change I ≤ RingHom.ker (MvPolynomial.aeval (fun j => (z j:ℂ))).toRingHom
    apply Ideal.span_le.mpr
    intro p hp
    have hp' : p = F := Set.mem_singleton_iff.mp hp
    subst p
    change MvPolynomial.aeval (fun j => (z j:ℂ)) (directSurface fc k) = 0
    have hev : MvPolynomial.aeval (fun j => (z j:ℂ)) (Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X 0) fc) = fc.eval (z 0:ℂ) := by
      induction fc using Polynomial.induction_on' with
      | add p q hp hq => simp only [Polynomial.eval₂_add,map_add,Polynomial.eval_add,hp,hq]
      | monomial n a => simp [Polynomial.eval₂_monomial,Polynomial.eval_monomial]
    simpa only [directSurface,map_sub,map_mul,map_pow,MvPolynomial.aeval_X,hev,sub_eq_zero] using heq z hz
  have hh := hcount X hXcut G le_rfl hbox I hI hdI.le heI.le hpoints
  have hend := hh (by
    intro i e J hJ hIJ _ hJe hJdim _
    let : J.IsPrime := hJ
    fin_cases i
    · have heJI : I = J := prime_same_dimension_eq I J hIJ hdI hJdim
      subst J
      right
      intro T hT
      have hlo := hHs T hT
      have hn : 0 ≤ 2*(ω 1+ω 2+1)*T := by
        exact mul_nonneg (by linarith [hω 1,hω 2]) (by linarith)
      norm_num [dv,cc]
      linarith only [hlo,hn]
    · have hjdim : affineDimension J ≤ 1 := by simpa using hJdim.le
      have hS' : ∀ z ∈ S.filter (PointOn J), z ∈ S := fun z hz => (Finset.mem_filter.mp hz).1
      have hcur := hcurve e X hX2.le (S.filter (PointOn J)) (hinj.mono (Finset.filter_subset _ _))
        (fun z hz j => hbox z (hS' z hz) j) (fun z hz => hrange z (hS' z hz))
        (fun z hz => hselected z (hS' z hz)) J hJ hjdim hJe
        (fun z hz => (Finset.mem_filter.mp hz).2) (directSurface_equation fc k J hIJ)
      rcases hcur with hsmall | hH
      · exact Or.inl hsmall
      · right
        intro T hT
        have hlo := hH T hT
        have hn : 0 ≤ Cs := hCs
        norm_num [dv,cc]
        linarith only [hlo,hn])
  have hexp : (∑ i : Fin 2, ((2-i.val:ℕ):ℝ)*av i)+ε = δ+1/2+ε := by
    simp [av,Fin.sum_univ_two]
    ring
  simpa only [hexp] using hend

end QuarticPowerFree

end OAI
