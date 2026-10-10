import OAI.Combinatorics.SquareDifference.SievedFourier

namespace OAI

section
open Finset
open scoped ComplexConjugate BigOperators
namespace SquareDifference

lemma prime_power_sieved_zero {p k : ℕ} [Fact p.Prime] [NeZero k]
    (hp : p≠2) (hpk : p∣k) (ψ : AddChar (ZMod (p*k)) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod (p*k), ψ (x^2))-
      (𝔼 x : ZMod (p*k),
        (primeSieveWeight p (ZMod.castHom (dvd_mul_right p k) (ZMod p) x) : ℂ)*ψ (x^2))=0 := by
  classical
  have he (x : ZMod (p*k)) :
      ψ (x^2)-(primeSieveWeight p (ZMod.castHom (dvd_mul_right p k) (ZMod p) x) : ℂ)*ψ (x^2)=
      ((p : ℂ)/(p-1))*
      ((if ZMod.castHom (dvd_mul_right p k) (ZMod p) x≠0 then (1 : ℂ) else 0)*ψ (x^2)) := by
    have hh := congrArg (fun z : ℝ => (z : ℂ))
      (primeSieveWeight_unit_density (ZMod.castHom (dvd_mul_right p k) (ZMod p) x))
    push_cast at hh
    calc
      _ = (1-(primeSieveWeight p (ZMod.castHom (dvd_mul_right p k) (ZMod p) x) : ℂ))*ψ (x^2) := by ring
      _ = _ := by rw [hh]; split_ifs <;> simp only [Complex.ofReal_one,Complex.ofReal_zero] <;> ring
  rw [← expect_sub_distrib]
  simp_rw [he]
  rw [← mul_expect,odd_unit_gauss_zero_char hp hpk ψ hψ,mul_zero]

lemma two_le_rpow_sixth {x : ℝ} (hx : 64≤x) : 2≤x^((1 : ℝ)/6) := by
  have h : (2 : ℝ)≤x^(6 : ℝ)⁻¹ := by
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num) (by linarith : 0≤x) (by norm_num)).mpr
    norm_num
    exact hx
  simpa only [one_div] using h

lemma smallPrime_product_bound (S : Finset ℕ) (a : ℕ → ℕ)
    (ha : ∀p∈S, p≤a p) (hp : ∀p∈S, 1≤p) :
    (2 : ℝ)^S.card≤2^64*((∏p∈S, (a p : ℝ))^((1 : ℝ)/6)) := by
  let K := S.filter (fun p => p<64)
  have hK : K⊆range 64 := by intro p hp; exact mem_range.mpr (mem_filter.mp hp).2
  have hcard : K.card≤64 := le_trans (card_le_card hK) (by simp)
  have hk0 : ∀p∈S, 0≤(a p : ℝ) := fun _ _ => Nat.cast_nonneg _
  have hle (p : ℕ) (hps : p∈S) : (2 : ℝ)≤
      (if p<64 then (2 : ℝ) else 1)*(a p : ℝ)^((1 : ℝ)/6) := by
    split_ifs with h
    · have h1 : (1 : ℝ)≤(a p : ℝ)^((1 : ℝ)/6) :=
        Real.one_le_rpow (by exact_mod_cast (hp p hps).trans (ha p hps)) (by norm_num)
      linarith
    · rw [one_mul]
      apply two_le_rpow_sixth
      exact_mod_cast (le_trans (Nat.le_of_not_gt h) (ha p hps))
  calc
    _ = ∏p∈S, (2 : ℝ) := (prod_const 2).symm
    _ ≤ ∏p∈S, (if p<64 then (2 : ℝ) else 1)*(a p : ℝ)^((1 : ℝ)/6) :=
      Finset.prod_le_prod₀ (by intros; norm_num) hle
    _ = (2 : ℝ)^K.card*(∏p∈S, (a p : ℝ))^((1 : ℝ)/6) := by
      rw [prod_mul_distrib,prod_ite]
      simp only [prod_const,one_pow,mul_one]
      rw [Real.finsetProd_rpow _ _ (fun p hp => hk0 p hp)]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard)
      (Real.rpow_nonneg (prod_nonneg hk0) _)

lemma truncatedSieveMean_decay (S : Finset ℕ) (a : ℕ → ℕ) (H : ℝ) (A B : ℕ → ℂ)
    (ha : ∀p∈S, p≤a p) (hp : ∀p∈S, 1≤p)
    (hA : ∀p∈S, ‖A p‖≤(a p : ℝ)^(-(1 : ℝ)/2))
    (hB : ∀p∈S, ‖B p‖≤(a p : ℝ)^(-(1 : ℝ)/2)) :
    ‖truncatedSieveMean S id H A B‖≤2^64*(∏p∈S, (a p : ℝ))^(-(1 : ℝ)/3) := by
  have hpos (p : ℕ) (hps : p∈S) : (0 : ℝ)<a p := by exact_mod_cast (hp p hps).trans (ha p hps)
  have hprod : 0<∏p∈S, (a p : ℝ) := prod_pos hpos
  apply (truncatedSieveMean_bound S id H A B _ hA hB).trans
  rw [Real.finsetProd_rpow _ _ (fun p hp => (hpos p hp).le)]
  calc
    _ ≤ (2^64*(∏p∈S, (a p : ℝ))^((1 : ℝ)/6))*(∏p∈S, (a p : ℝ))^(-(1 : ℝ)/2) :=
      mul_le_mul_of_nonneg_right (smallPrime_product_bound S a ha hp) (Real.rpow_nonneg hprod.le _)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hprod]; norm_num

lemma truncatedSieveMean_restrict {I : Type*} [DecidableEq I]
    (S U : Finset I) (hUS : U⊆S) (p : I → ℕ) (H : ℝ) (a b : I → ℂ)
    (ha : ∀i∈S, i∉U → a i=1) (hb : ∀i∈S, i∉U → b i=0) :
    truncatedSieveMean S p H a b=truncatedSieveMean U p H a b := by
  unfold truncatedSieveMean
  symm
  calc
    _ = ∑T∈U.powerset, if ((∏i∈T, p i : ℕ) : ℝ)≤H then localSieveTerm S a b T else 0 := by
      apply sum_congr rfl
      intro T hTU
      have hT := mem_powerset.mp hTU
      split_ifs
      · unfold localSieveTerm
        congr 2
        apply prod_subset
        · exact sdiff_subset_sdiff_left T hUS
        · intro i hi hni
          exact ha i (mem_sdiff.mp hi).1 (by intro hiu; exact hni (mem_sdiff.mpr ⟨hiu,(mem_sdiff.mp hi).2⟩))
      · rfl
    _ = _ := by
      apply sum_subset (powerset_mono.mpr hUS)
      intro T hTS hTU
      have hsub := mem_powerset.mp hTS
      have hnsub : ¬T⊆U := fun h => hTU (mem_powerset.mpr h)
      obtain ⟨i,hiT,hiU⟩ := not_subset.mp hnsub
      split_ifs
      · unfold localSieveTerm
        rw [prod_eq_zero hiT (hb i (hsub hiT) hiU),mul_zero]
      · rfl

lemma product_sieve_coefficient {I : Type*} [Fintype I] [DecidableEq I]
    {R : I → Type*} [∀i, CommRing (R i)] [∀i, Fintype (R i)]
    (ψ : AddChar (∀i, R i) ℂ) (root w : ∀i, R i → ℂ)
    (p : I → ℕ) (H : ℝ) :
    (∑T∈(univ : Finset I).powerset, if ((∏i∈T, p i : ℕ) : ℝ)≤H then
      (-1)^T.card*(𝔼 x : ∀i, R i, (∏i, root i (x i))*(∏i∈T, w i (x i))*ψ (x^2)) else 0)=
    truncatedSieveMean univ p H
      (fun i => 𝔼 t : R i, root i t*coordinateChar ψ i (t^2))
      (fun i => 𝔼 t : R i, (root i t*w i t)*coordinateChar ψ i (t^2)) := by
  unfold truncatedSieveMean
  apply sum_congr rfl
  intro T hT
  split_ifs
  · rw [localSieveTerm_product _ _ (subset_univ _)]
    congr 1
    have he (x : ∀i, R i) : (∏i, root i (x i))*(∏i∈T, w i (x i))=
        ∏i, root i (x i)*(if i∈T then w i (x i) else 1) := by
      rw [prod_mul_distrib]
      congr 1
      rw [prod_ite]
      simp
    simp_rw [he]
    rw [product_quadratic_mean ψ (fun i t => root i t*(if i∈T then w i t else 1))]
    apply prod_congr rfl
    intro i _
    by_cases hi : i∈T
    · simp only [ite_eq_left hi]
    · simp only [ite_eq_right hi,mul_one]
  · rfl

lemma localSieveTerm_factor {I : Type*} [DecidableEq I]
    (S U T : Finset I) (hUS : U⊆S) (hTU : T⊆U) (a b : I → ℂ) :
    localSieveTerm S a b T=(∏i∈S\U, a i)*localSieveTerm U a b T := by
  have hd : Disjoint (S\U) (U\T) := by
    rw [disjoint_left]
    intro i hi hj
    exact (mem_sdiff.mp hi).2 (mem_sdiff.mp hj).1
  have he : S\T=(S\U)∪(U\T) := by
    ext i
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨hiS,hiT⟩
      by_cases hiU : i∈U
      · exact Or.inr ⟨hiU,hiT⟩
      · exact Or.inl ⟨hiS,hiU⟩
    · rintro (⟨hiS,hiU⟩|⟨hiU,hiT⟩)
      · exact ⟨hiS,fun hiT => hiU (hTU hiT)⟩
      · exact ⟨hUS hiU,hiT⟩
  unfold localSieveTerm
  rw [he,prod_union hd]
  ring

lemma truncatedSieveMean_factor {I : Type*} [DecidableEq I]
    (S U : Finset I) (hUS : U⊆S) (p : I → ℕ) (H : ℝ) (a b : I → ℂ)
    (hb : ∀i∈S, i∉U → b i=0) :
    truncatedSieveMean S p H a b=(∏i∈S\U, a i)*truncatedSieveMean U p H a b := by
  unfold truncatedSieveMean
  rw [mul_sum]
  symm
  calc
    _ = ∑T∈U.powerset, if ((∏i∈T, p i : ℕ) : ℝ)≤H then localSieveTerm S a b T else 0 := by
      apply sum_congr rfl
      intro T hTU
      split_ifs
      · exact (localSieveTerm_factor S U T hUS (mem_powerset.mp hTU) a b).symm
      · exact mul_zero _
    _ = _ := by
      apply sum_subset (powerset_mono.mpr hUS)
      intro T hTS hTU
      have hsub := mem_powerset.mp hTS
      obtain ⟨i,hiT,hiU⟩ := not_subset.mp (show ¬T⊆U from fun h => hTU (mem_powerset.mpr h))
      split_ifs
      · unfold localSieveTerm
        rw [prod_eq_zero hiT (hb i (hsub hiT) hiU),mul_zero]
      · rfl

lemma truncatedSieveMean_congr_active {I : Type*} [DecidableEq I]
    (S : Finset I) (p : I → ℕ) (H : ℝ) (a b c : I → ℂ)
    (hp : ∀i∈S, 1≤p i) (hbc : ∀i∈S, (p i : ℝ)≤H → b i=c i) :
    truncatedSieveMean S p H a b=truncatedSieveMean S p H a c := by
  unfold truncatedSieveMean
  apply sum_congr rfl
  intro T hT
  split_ifs with hH
  · unfold localSieveTerm
    congr 1
    apply prod_congr rfl
    intro i hiT
    apply hbc i ((mem_powerset.mp hT) hiT)
    apply le_trans _ hH
    exact_mod_cast single_le_prod (fun j hj => hp j ((mem_powerset.mp hT) hj)) hiT
  · rfl

lemma residueDensity_nonneg {m q : ℕ} (hmq : m∣q) (c : ZMod m) (x : ZMod q) :
    0≤residueDensity hmq c x := by unfold residueDensity; split_ifs <;> positivity

lemma residueDensity_quadratic_norm {m q : ℕ} [NeZero m] [NeZero q]
    (hmq : m∣q) (c : ZMod m) (ψ : AddChar (ZMod q) ℂ) :
    ‖𝔼 x : ZMod q, (residueDensity hmq c x : ℂ)*ψ (x^2)‖≤1 := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  have he (x : ZMod q) : ‖(residueDensity hmq c x : ℂ)*ψ (x^2)‖=residueDensity hmq c x := by
    rw [norm_mul,ψ.norm_apply,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (residueDensity_nonneg hmq c x)]
  simp_rw [he]
  have h := residueDensity_mean hmq c
  have hr : (𝔼 x : ZMod q, residueDensity hmq c x)=(1 : ℝ) := by exact_mod_cast h
  exact hr.le

lemma smallPrime_product_bound_inj {I : Type*} [DecidableEq I]
    (S : Finset I) (p a : I → ℕ) (hi : Set.InjOn p S)
    (ha : ∀i∈S, p i≤a i) (hp : ∀i∈S, 1≤p i) :
    (2 : ℝ)^S.card≤2^64*((∏i∈S, (a i : ℝ))^((1 : ℝ)/6)) := by
  let K := S.filter (fun i => p i<64)
  have hK : K.image p⊆range 64 := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    exact mem_range.mpr (mem_filter.mp hi).2
  have hki : Set.InjOn p K := hi.mono (filter_subset _ _)
  have hcard : K.card≤64 := by
    rw [← card_image_of_injOn hki]
    exact le_trans (card_le_card hK) (by simp)
  have hk0 : ∀i∈S, 0≤(a i : ℝ) := fun _ _ => Nat.cast_nonneg _
  have hle (i : I) (his : i∈S) : (2 : ℝ)≤
      (if p i<64 then (2 : ℝ) else 1)*(a i : ℝ)^((1 : ℝ)/6) := by
    split_ifs with h
    · have h1 : (1 : ℝ)≤(a i : ℝ)^((1 : ℝ)/6) :=
        Real.one_le_rpow (by exact_mod_cast (hp i his).trans (ha i his)) (by norm_num)
      linarith
    · rw [one_mul]
      apply two_le_rpow_sixth
      exact_mod_cast (le_trans (Nat.le_of_not_gt h) (ha i his))
  calc
    _ = ∏i∈S, (2 : ℝ) := (prod_const 2).symm
    _ ≤ ∏i∈S, (if p i<64 then (2 : ℝ) else 1)*(a i : ℝ)^((1 : ℝ)/6) :=
      Finset.prod_le_prod₀ (by intros; norm_num) hle
    _ = (2 : ℝ)^K.card*(∏i∈S, (a i : ℝ))^((1 : ℝ)/6) := by
      rw [prod_mul_distrib,prod_ite]
      simp only [prod_const,one_pow,mul_one]
      rw [Real.finsetProd_rpow _ _ hk0]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hcard)
      (Real.rpow_nonneg (prod_nonneg hk0) _)

lemma truncatedSieveMean_decay_inj {I : Type*} [DecidableEq I]
    (S : Finset I) (p a : I → ℕ) (hi : Set.InjOn p S) (H : ℝ) (A B : I → ℂ)
    (ha : ∀i∈S, p i≤a i) (hp : ∀i∈S, 1≤p i)
    (hA : ∀i∈S, ‖A i‖≤(a i : ℝ)^(-(1 : ℝ)/2))
    (hB : ∀i∈S, ‖B i‖≤(a i : ℝ)^(-(1 : ℝ)/2)) :
    ‖truncatedSieveMean S p H A B‖≤2^64*(∏i∈S, (a i : ℝ))^(-(1 : ℝ)/3) := by
  have hpos (i : I) (his : i∈S) : (0 : ℝ)<a i := by exact_mod_cast (hp i his).trans (ha i his)
  have hprod : 0<∏i∈S, (a i : ℝ) := prod_pos hpos
  apply (truncatedSieveMean_bound S p H A B _ hA hB).trans
  rw [Real.finsetProd_rpow _ _ (fun i hi => (hpos i hi).le)]
  calc
    _ ≤ (2^64*(∏i∈S, (a i : ℝ))^((1 : ℝ)/6))*(∏i∈S, (a i : ℝ))^(-(1 : ℝ)/2) :=
      mul_le_mul_of_nonneg_right (smallPrime_product_bound_inj S p a hi ha hp) (Real.rpow_nonneg hprod.le _)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hprod]; norm_num

section RootSieve

variable {I : Type*} [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : ∀i, AddChar (ZMod (m i)) ℂ)

noncomputable def rootSieveA (i : I) : ℂ :=
  if i∈R then 𝔼 x : ZMod (m i), (residueDensity (hm i) (c i) x : ℂ)*ψ i (x^2)
  else 𝔼 x : ZMod (m i), ψ i (x^2)

noncomputable def rootSieveB (i : I) : ℂ :=
  if i∈R then 0 else 𝔼 x : ZMod (m i),
    (primeSieveWeight (p i) (ZMod.castHom (hm i) (ZMod (p i)) x) : ℂ)*ψ i (x^2)

lemma rootSieveA_trivial (i : I) (hi : ψ i=1) : rootSieveA p m hm R c ψ i=1 := by
  unfold rootSieveA
  rw [hi]
  split_ifs
  · simpa only [AddChar.one_apply,mul_one] using residueDensity_mean (hm i) (c i)
  · simp only [AddChar.one_apply,Fintype.expect_const]

lemma rootSieveB_trivial (i : I) (hi : ψ i=1) : rootSieveB p m hm R ψ i=0 := by
  unfold rootSieveB
  rw [hi]
  split_ifs
  · rfl
  · simpa only [AddChar.one_apply,mul_one] using nonprime_sieve_mean_zero (hm i)

lemma rootSieveA_root_bound (i : I) (hi : i∈R) : ‖rootSieveA p m hm R c ψ i‖≤1 := by
  rw [rootSieveA,ite_eq_left hi]
  exact residueDensity_quadratic_norm (hm i) (c i) (ψ i)

lemma rootSieveB_root (i : I) (hi : i∈R) : rootSieveB p m hm R ψ i=0 := by
  rw [rootSieveB,ite_eq_left hi]

lemma rootSieve_factor (S T : Finset I) (hTS : T⊆S) (H : ℝ)
    (hψ : ∀i∈S, i∉T → ψ i=1) :
    truncatedSieveMean S p H (rootSieveA p m hm R c ψ) (rootSieveB p m hm R ψ)=
    (∏i∈T∩R, rootSieveA p m hm R c ψ i)*
      truncatedSieveMean (T\R) p H (rootSieveA p m hm R c ψ) (rootSieveB p m hm R ψ) := by
  rw [truncatedSieveMean_restrict S T hTS p H _ _
    (fun i hi hn => rootSieveA_trivial p m hm R c ψ i (hψ i hi hn))
    (fun i hi hn => rootSieveB_trivial p m hm R ψ i (hψ i hi hn))]
  rw [truncatedSieveMean_factor T (T\R) sdiff_subset p H _ _ (by
    intro i hi hn
    apply rootSieveB_root p m hm R ψ i
    by_contra hir
    exact hn (mem_sdiff.mpr ⟨hi,hir⟩))]
  congr 2
  ext i
  simp

lemma rootSieve_decay (S T : Finset I) (hTS : T⊆S) (H : ℝ)
    (hinj : Set.InjOn p (↑(T\R) : Set I)) (hle : ∀i∈T, p i ≤ m i)
    (hψ0 : ∀i∈S, i∉T → ψ i=1)
    (hψ : ∀i∈T\R, (ψ i).IsPrimitive)
    (hodd : ∀i∈T\R, IsUnit (2 : ZMod (m i))) :
    ‖truncatedSieveMean S p H (rootSieveA p m hm R c ψ) (rootSieveB p m hm R ψ)‖≤
      2^64*(∏i∈T\R, (m i : ℝ))^(-(1 : ℝ)/3) := by
  rw [rootSieve_factor p m hm R c ψ S T hTS H hψ0,norm_mul]
  have hr : ‖∏i∈T∩R, rootSieveA p m hm R c ψ i‖≤1 := by
    rw [norm_prod]
    exact prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i hi => rootSieveA_root_bound p m hm R c ψ i (mem_inter.mp hi).2)
  apply (mul_le_mul_of_nonneg_right hr (norm_nonneg _)).trans
  rw [one_mul]
  apply truncatedSieveMean_decay_inj (T\R) p m hinj H _ _
    (fun i hi => hle i (mem_sdiff.mp hi).1) (fun i _ => (Fact.out : (p i).Prime).one_lt.le)
  · intro i hi
    rw [rootSieveA,ite_eq_right (mem_sdiff.mp hi).2]
    exact (quadratic_sieve_bounds (hm i) (hodd i hi) (ψ i) (hψ i hi)).1
  · intro i hi
    rw [rootSieveB,ite_eq_right (mem_sdiff.mp hi).2]
    exact (quadratic_sieve_bounds (hm i) (hodd i hi) (ψ i) (hψ i hi)).2

end RootSieve

lemma residueDensity_quadratic_zero_dvd {p q : ℕ} [NeZero p] [NeZero q]
    (h : p*p∣q) (c : ZMod p) (hc : (2 : ZMod p)*c≠0)
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod q, (residueDensity ((dvd_mul_right p p).trans h) c x : ℂ)*ψ (x^2))=0 := by
  obtain ⟨k,hk⟩ := h
  have he : q=p*(p*k) := by rw [hk]; ring
  subst he
  have hk0 : k≠0 := by intro hz; subst k; simpa using (NeZero.ne (p*(p*0)))
  let : NeZero k := ⟨hk0⟩
  exact residueDensity_quadratic_zero (dvd_mul_right p k) ψ hψ c hc

lemma odd_prime_power_root_zero {p : ℕ} [Fact p.Prime] (k : ℕ)
    (c : ZMod p) (hc : (2 : ZMod p)*c≠0)
    (ψ : AddChar (ZMod (p^(k+2))) ℂ) (hψ : ψ.IsPrimitive) :
      (𝔼 x : ZMod (p^(k+2)), (residueDensity (dvd_pow_self p (by omega : k+2≠0)) c x : ℂ)*ψ (x^2))=0 := by
  apply residueDensity_quadratic_zero_dvd _ c hc ψ hψ
  exact ⟨p^k,by ring⟩

lemma odd_root_quadratic_large_dvd {q : ℕ} [NeZero q] (h : 16∣q)
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod q, (residueDensity ((by norm_num : 2∣16).trans h) 1 x : ℂ)*ψ (x^2))=0 := by
  obtain ⟨k,hk⟩ := h
  have he : q=4*(4*k) := by omega
  subst he
  have hk0 : k≠0 := by
    have hh := NeZero.ne (4*(4*k))
    intro hz
    rw [hz] at hh
    norm_num at hh
  let : NeZero k := ⟨hk0⟩
  exact odd_root_quadratic_large (dvd_mul_right 4 k) ψ hψ

lemma two_prime_power_root_zero (k : ℕ)
    (ψ : AddChar (ZMod (2^(k+4))) ℂ) (hψ : ψ.IsPrimitive) :
      (𝔼 x : ZMod (2^(k+4)), (residueDensity (dvd_pow_self 2 (by omega : k+4≠0)) 1 x : ℂ)*ψ (x^2))=0 := by
  apply odd_root_quadratic_large_dvd _ ψ hψ
  exact ⟨2^k,by ring⟩

lemma two_prime_power_root_small (e : ℕ) (he1 : 1≤e) (he3 : e≤3)
    (ψ : AddChar (ZMod (2^e)) ℂ) :
    (𝔼 x : ZMod (2^e), (residueDensity (dvd_pow_self 2 (by omega : e≠0)) 1 x : ℂ)*ψ (x^2))=ψ 1 := by
  have hs : 2^e∣8 := by
    change 2^e∣2^3
    exact pow_dvd_pow 2 he3
  exact odd_root_quadratic_small (dvd_pow_self 2 (by omega : e≠0)) hs ψ

lemma prime_power_sieved_zero_dvd {p q : ℕ} [Fact p.Prime] [NeZero q]
    (hp : p≠2) (h : p*p∣q) (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) :
    (𝔼 x : ZMod q, ψ (x^2))-
      (𝔼 x : ZMod q, (primeSieveWeight p (ZMod.castHom ((dvd_mul_right p p).trans h) (ZMod p) x) : ℂ)*ψ (x^2))=0 := by
  obtain ⟨k,hk⟩ := h
  have he : q=p*(p*k) := by rw [hk]; ring
  subst he
  have hk0 : k≠0 := by intro hz; subst k; simpa using (NeZero.ne (p*(p*0)))
  let : NeZero k := ⟨hk0⟩
  exact prime_power_sieved_zero hp (dvd_mul_right p k) ψ hψ

lemma prime_power_sieve_complete_zero {p : ℕ} [Fact p.Prime] (hp : p≠2) (k : ℕ)
    (ψ : AddChar (ZMod (p^(k+2))) ℂ) (hψ : ψ.IsPrimitive) :
      (𝔼 x : ZMod (p^(k+2)), ψ (x^2))-
      (𝔼 x : ZMod (p^(k+2)), (primeSieveWeight p (ZMod.castHom (dvd_pow_self p (by omega : k+2≠0)) (ZMod p) x) : ℂ)*ψ (x^2))=0 := by
  apply prime_power_sieved_zero_dvd hp _ ψ hψ
  exact ⟨p^k,by ring⟩

lemma residueDensity_quadratic_phase {p m : ℕ} [NeZero p] [NeZero m]
    (hpm : p∣m) (c : ZMod p) (r : ZMod m) (ψ : AddChar (ZMod m) ℂ)
    (hsq : ∀x : ZMod m, ZMod.castHom hpm (ZMod p) x=c → x^2=r) :
    (𝔼 x : ZMod m, (residueDensity hpm c x : ℂ)*ψ (x^2))=ψ r := by
  have he (x : ZMod m) : (residueDensity hpm c x : ℂ)*ψ (x^2)=
      (residueDensity hpm c x : ℂ)*ψ r := by
    by_cases hx : ZMod.castHom hpm (ZMod p) x=c
    · rw [hsq x hx]
    · simp only [residueDensity,ite_eq_right hx,Complex.ofReal_zero,zero_mul]
  simp_rw [he]
  rw [← expect_mul,residueDensity_mean,one_mul]

lemma prime_unit_quadratic_of_eq {p m : ℕ} [Fact p.Prime] [NeZero m]
    (hpm : p∣m) (he : m=p) (ψ : AddChar (ZMod m) ℂ) :
    (𝔼 x : ZMod m, ψ (x^2))-
      (𝔼 x : ZMod m, (primeSieveWeight p (ZMod.castHom hpm (ZMod p) x) : ℂ)*ψ (x^2))=
        unitQuadraticMean ψ := by
  subst m
  have hh : ZMod.castHom hpm (ZMod p)=RingHom.id (ZMod p) := Subsingleton.elim _ _
  simp only [hh,RingHom.id_apply]
  exact prime_unit_quadratic ψ

section RootSieveComplete

variable {I : Type*} [DecidableEq I]
    (p m : I → ℕ) [∀i, Fact (p i).Prime] [∀i, NeZero (m i)]
    (hm : ∀i, p i∣m i) (R : Finset I) (c : ∀i, ZMod (p i))
    (ψ : ∀i, AddChar (ZMod (m i)) ℂ)

lemma rootSieve_complete (S T : Finset I) (hTS : T⊆S) (H : ℝ)
    (hψ0 : ∀i∈S, i∉T → ψ i=1) (hH : ((∏i∈T\R, p i : ℕ) : ℝ)≤H) :
    truncatedSieveMean S p H (rootSieveA p m hm R c ψ) (rootSieveB p m hm R ψ)=
    (∏i∈T∩R, rootSieveA p m hm R c ψ i)*
      ∏i∈T\R, (rootSieveA p m hm R c ψ i-rootSieveB p m hm R ψ i) := by
  rw [rootSieve_factor p m hm R c ψ S T hTS H hψ0]
  congr 1
  exact truncatedSieveMean_complete _ _ _ _ _
    (fun i _ => (Fact.out : (p i).Prime).one_lt.le) hH

lemma rootSieve_complete_phase (S T : Finset I) (hTS : T⊆S) (H : ℝ)
    (hψ0 : ∀i∈S, i∉T → ψ i=1) (hH : ((∏i∈T\R, p i : ℕ) : ℝ)≤H)
    (he : ∀i∈T\R, m i=p i) (r : ∀i, ZMod (m i))
    (hsq : ∀i∈T∩R, ∀x : ZMod (m i), ZMod.castHom (hm i) (ZMod (p i)) x=c i → x^2=r i) :
    truncatedSieveMean S p H (rootSieveA p m hm R c ψ) (rootSieveB p m hm R ψ)=
      (∏i∈T∩R, ψ i (r i))*(∏i∈T\R, unitQuadraticMean (ψ i)) := by
  rw [rootSieve_complete p m hm R c ψ S T hTS H hψ0 hH]
  congr 1
  · apply prod_congr rfl
    intro i hi
    rw [rootSieveA,ite_eq_left (mem_inter.mp hi).2]
    exact residueDensity_quadratic_phase (hm i) (c i) (r i) (ψ i) (hsq i hi)
  · apply prod_congr rfl
    intro i hi
    simp only [rootSieveA,rootSieveB,ite_eq_right (mem_sdiff.mp hi).2]
    exact prime_unit_quadratic_of_eq (hm i) (he i hi) (ψ i)

lemma rootSieve_zero_of_root (S T : Finset I) (hTS : T⊆S) (H : ℝ)
    (hψ0 : ∀i∈S, i∉T → ψ i=1) (i : I) (hi : i∈T∩R)
    (hz : (𝔼 x : ZMod (m i), (residueDensity (hm i) (c i) x : ℂ)*ψ i (x^2))=0) :
    truncatedSieveMean S p H (rootSieveA p m hm R c ψ) (rootSieveB p m hm R ψ)=0 := by
  rw [rootSieve_factor p m hm R c ψ S T hTS H hψ0]
  have he : rootSieveA p m hm R c ψ i=0 := by rw [rootSieveA,ite_eq_left (mem_inter.mp hi).2,hz]
  rw [prod_eq_zero hi he,zero_mul]

lemma rootSieve_zero_of_squarefactor (S T : Finset I) (hTS : T⊆S) (H : ℝ)
    (hψ0 : ∀i∈S, i∉T → ψ i=1) (hH : ((∏i∈T\R, p i : ℕ) : ℝ)≤H)
    (i : I) (hi : i∈T\R) (hp : p i≠2) (h2 : p i*p i∣m i) (hψ : (ψ i).IsPrimitive) :
    truncatedSieveMean S p H (rootSieveA p m hm R c ψ) (rootSieveB p m hm R ψ)=0 := by
  rw [rootSieve_complete p m hm R c ψ S T hTS H hψ0 hH]
  have he : rootSieveA p m hm R c ψ i-rootSieveB p m hm R ψ i=0 := by
    simp only [rootSieveA,rootSieveB,ite_eq_right (mem_sdiff.mp hi).2]
    exact prime_power_sieved_zero_dvd hp h2 (ψ i) hψ
  rw [prod_eq_zero hi he,mul_zero]

end RootSieveComplete

lemma zmod_equiv_coordinate {I : Type*} [DecidableEq I] (m : I → ℕ) {L : ℕ}
    (e : ZMod L ≃+* ∀i, ZMod (m i)) (i : I) (hi : m i∣L) (x : ZMod L) :
    e x i=ZMod.castHom hi (ZMod (m i)) x := by
  exact DFunLike.congr_fun (Subsingleton.elim
    ((Pi.evalRingHom (fun i => ZMod (m i)) i).comp e.toRingHom)
    (ZMod.castHom hi (ZMod (m i)))) x

lemma coordinateChar_inflation_primitive {I : Type*} [DecidableEq I]
    (m : I → ℕ) {q L : ℕ} (hqL : q∣L)
    (e : ZMod L ≃+* ∀i, ZMod (m i))
    (ψ : AddChar (ZMod q) ℂ) (hψ : ψ.IsPrimitive) (i : I) (hiq : m i∣q) :
    (coordinateChar ((ψ.compAddMonoidHom (ZMod.castHom hqL (ZMod q)).toAddMonoidHom).compAddMonoidHom
      e.symm.toAddMonoidHom) i).IsPrimitive := by
  intro a ha he
  let xL := e.symm (Pi.single i a)
  let x := ZMod.castHom hqL (ZMod q) xL
  have hx : x≠0 := by
    intro hx
    have hh := congrArg (ZMod.castHom hiq (ZMod (m i))) hx
    have hc : ZMod.castHom hiq (ZMod (m i)) x=a := by
      change ((ZMod.castHom hiq (ZMod (m i))).comp (ZMod.castHom hqL (ZMod q))) xL=a
      rw [zmod_cast_comp]
      rw [← zmod_equiv_coordinate m e i (hiq.trans hqL)]
      simp only [xL,RingEquiv.apply_symm_apply,Pi.single_eq_same]
    rw [hc,map_zero] at hh
    exact ha hh
  apply hψ hx
  ext z
  obtain ⟨y,rfl⟩ := ZMod.ringHom_surjective (ZMod.castHom hqL (ZMod q)) z
  have hh := congrArg (fun φ : AddChar (ZMod (m i)) ℂ => φ (e y i)) he
  change ψ (ZMod.castHom hqL (ZMod q) (e.symm (Pi.single i (a*e y i))))=1 at hh
  have hm : e.symm (Pi.single i (a*e y i))=xL*y := by
    apply e.injective
    simp only [RingEquiv.apply_symm_apply,map_mul,xL]
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Pi.single_eq_of_ne hj]
  change ψ (x*ZMod.castHom hqL (ZMod q) y)=1
  rw [hm,map_mul] at hh
  exact hh

end SquareDifference
end

end OAI
