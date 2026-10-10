import OAI.NumberTheory.PowerFree.NormHilbert

namespace OAI

universe u

namespace QuarticPowerFree

section
open MvPolynomial

theorem norm_real_hilbert_uniform {n d h : ℕ} {K : Type u} [Field K]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (E D : ℕ) (hD : 0 < D) (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
        (a b : Fin d → MvPolynomial (Fin n) K) (x : MvPolynomial (Fin n) K)
        (θ : Fin d → K), Function.Injective θ →
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^k * Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I x - algebraMap K (MvPolynomial (Fin n) K ⧸ I) (θ i)) →
      Algebra.adjoin K (Set.range (fun i => Ideal.Quotient.mk I (a i)) ∪
        Set.range (fun i => Ideal.Quotient.mk I (b i))) = ⊤ →
      Transcendental K (Ideal.Quotient.mk I x) →
      affineDimension I = h+1 → h+1 ≤ d → affineDegree I ≤ E →
      (∀ i, (a i).totalDegree ≤ D) → x.totalDegree ≤ D →
      ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w A) → (∀ i, b i ∈ weightedSpace w B) →
      ∀ (ω : Fin n → ℝ), (∀ i, 0 < ω i) → (∀ i, (w i:ℝ) = L*ω i) →
      ∀ T : ℝ, 1 ≤ T →
        ((min A B : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^h * L^(h+1) /
          (((h+1).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))*T^(h+1) -
          C*T^h ≤ weightedHilbert I ω T := by
  let α : ℝ := ((min A B : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^h /
    (((h+1).factorial:ℝ)*(A:ℝ)^(h+1)*(B:ℝ)^(h+1))
  have hα : 0 ≤ α := by dsimp [α]; positivity
  obtain ⟨C,hC,hh⟩ := norm_ambient_hilbert_uniform (n := n) (d := d) (h := h)
    (K := K) hk A B hA hB E D hD
  obtain ⟨c,hc,hr⟩ := uniform_real_hilbert_floor h ((k*A+B)*(E*D^(h+1))) L α C hL hα hC
  refine ⟨c,hc,fun I _ a b x θ hθ ha hab hgen hx hdim hd hdeg hadeg hxdeg w hw haw hbw ω hω hscale T hT => ?_⟩
  have hb := hr (fun N => (Module.finrank K ((weightedSpace w N).map
        (Ideal.Quotient.mkₐ K I).toLinearMap):ℝ))
    (fun t => (weightedHilbert I ω t:ℝ))
    (fun t => Nat.cast_nonneg _)
    (fun t ht => by
      exact_mod_cast Submodule.finrank_mono
        (weightedSpace_map_le_weightedFunctions I w ω hω L hL hscale t (by linarith)))
    (hh I a b x θ hθ ha hab hgen hx hdim hd hdeg hadeg hxdeg w hw haw hbw) T hT
  dsimp only [α] at hb
  convert hb using 1; ring

end

section

open Polynomial

theorem curve_parameter_injective {F ι : Type*} [Field F]
    (N : F[X]) (θ τ : ι → F) (hθ : Function.Injective θ)
    {k : ℕ} (hk : 0 < k)
    (hdiv : ∀ i, (X - C (τ i)) ^ k ∣ N - C (θ i)) : Function.Injective τ := by
  have heval (i : ι) : N.eval (τ i) = θ i := by
    obtain ⟨q, hq⟩ := hdiv i
    have he := congrArg (Polynomial.eval (τ i)) hq
    have hz : N.eval (τ i) - θ i = 0 := by
      simpa [zero_pow (Nat.ne_zero_of_lt hk)] using he
    exact sub_eq_zero.mp hz
  intro i j hij
  apply hθ
  rw [← heval i, ← heval j, hij]

theorem curve_input_degree_lower_bound {F ι : Type*} [Field F] [CharZero F]
    [Fintype ι] (N : F[X]) (hN : 0 < N.natDegree)
    (θ τ : ι → F) (hθ : Function.Injective θ) {k : ℕ} (hk : 0 < k)
    (hdiv : ∀ i, (X - C (τ i)) ^ k ∣ N - C (θ i)) :
    1 + Fintype.card ι * (k - 1) ≤ N.natDegree := by
  classical
  have hτ := curve_parameter_injective N θ τ hθ hk hdiv
  have hder (i : ι) : (X - C (τ i)) ^ (k - 1) ∣ N.derivative := by
    have hh := Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd (hdiv i)
    simpa only [derivative_sub, derivative_C, sub_zero] using hh
  have hprod : ∏ i, (X - C (τ i)) ^ (k - 1) ∣ N.derivative := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      exact (Polynomial.pairwise_coprime_X_sub_C hτ hij).pow
    · intro i _
      exact hder i
  have hdeg := Polynomial.natDegree_le_of_dvd hprod
    (Polynomial.derivative_ne_zero.mpr (Nat.ne_zero_of_lt hN))
  rw [Polynomial.natDegree_prod] at hdeg
  · simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one,
      Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Polynomial.natDegree_derivative] at hdeg
    omega
  · intro i _
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)

theorem affine_factor_eq {F : Type*} [Field F] (r q : F) (hr : r ≠ 0) :
    C r * X + C q = C r * (X - C (-q / r)) := by
  rw [mul_sub, ← C_mul]
  congr 1
  rw [mul_div_cancel₀ _ hr, C_neg, neg_neg]

theorem curve_polynomial_degrees {F ι : Type*} [Field F] [CharZero F]
    [Fintype ι] [Nonempty ι] (N : F[X]) (hN : 0 < N.natDegree)
    (θ r q : ι → F) (b : ι → F[X]) (hθ : Function.Injective θ)
    (hr : ∀ i, r i ≠ 0) {k : ℕ} (hk : 0 < k)
    (hidentity : ∀ i, (C (r i) * X + C (q i)) ^ k * b i = N - C (θ i)) :
    1 + Fintype.card ι * (k - 1) ≤ N.natDegree ∧
      ∀ i, (b i).natDegree = N.natDegree - k ∧
        (Fintype.card ι - 1) * (k - 1) ≤ (b i).natDegree := by
  classical
  let τ : ι → F := fun i => -q i / r i
  have hdiv (i : ι) : (X - C (τ i)) ^ k ∣ N - C (θ i) := by
    rw [← hidentity i, affine_factor_eq _ _ (hr i), mul_pow]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hdeg := curve_input_degree_lower_bound N hN θ τ hθ hk hdiv
  refine ⟨hdeg, fun i => ?_⟩
  have hnz : N - C (θ i) ≠ 0 := by
    intro hh
    have hz := congrArg Polynomial.natDegree hh
    rw [Polynomial.natDegree_sub_C, Polynomial.natDegree_zero] at hz
    omega
  have hab : (C (r i) * X + C (q i)) ^ k * b i ≠ 0 := by
    rw [hidentity i]
    exact hnz
  have heq := congrArg Polynomial.natDegree (hidentity i)
  rw [Polynomial.natDegree_mul (left_ne_zero_of_mul hab) (right_ne_zero_of_mul hab),
    Polynomial.natDegree_pow, Polynomial.natDegree_sub_C,
    affine_factor_eq _ _ (hr i), Polynomial.natDegree_mul
      (Polynomial.C_ne_zero.mpr (hr i)) (Polynomial.X_sub_C_ne_zero _),
    Polynomial.natDegree_C, Polynomial.natDegree_X_sub_C, zero_add, mul_one] at heq
  constructor
  · omega
  · have hcard : 0 < Fintype.card ι := Fintype.card_pos
    have hkm : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have hcount : Fintype.card ι - 1 + 1 = Fintype.card ι := Nat.sub_add_cancel hcard
    nlinarith

theorem polynomial_linearIndependent_of_degrees {F ι : Type*} [Field F]
    (p : ι → F[X]) (hp : ∀ i, p i ≠ 0)
    (hdeg : Function.Injective (fun i => (p i).natDegree)) : LinearIndependent F p := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  by_contra hci
  let t := s.filter (fun j => c j ≠ 0)
  have ht : t.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  obtain ⟨j, hjt, hjmax⟩ := Finset.exists_max_image t (fun j => (p j).natDegree) ht
  have hj : j ∈ s := (Finset.mem_filter.mp hjt).1
  have hcj : c j ≠ 0 := (Finset.mem_filter.mp hjt).2
  have he := congrArg (fun f : F[X] => f.coeff (p j).natDegree) hsum
  simp only [finsetSum_coeff, coeff_smul, smul_eq_mul, coeff_zero] at he
  rw [Finset.sum_eq_single j] at he
  · exact (mul_ne_zero hcj (Polynomial.leadingCoeff_ne_zero.mpr (hp j))) he
  · intro l hls hlj
    by_cases hcl : c l = 0
    · simp [hcl]
    · have hlt : l ∈ t := Finset.mem_filter.mpr ⟨hls, hcl⟩
      have hle := hjmax l hlt
      have hne : (p l).natDegree ≠ (p j).natDegree := fun hh => hlj (hdeg hh)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne hle hne)]
      exact mul_zero _
  · exact fun hnot => False.elim (hnot hj)

theorem curve_polynomial_families_independent {F : Type*} [Field F]
    (b : F[X]) {g : ℕ} (hg : 0 < g) (hbdeg : g ≤ b.natDegree) :
    LinearIndependent F (fun v : Fin g × ℕ => X ^ v.1.val * b ^ v.2) := by
  have hb : b ≠ 0 := by
    intro hh
    simp only [hh, Polynomial.natDegree_zero] at hbdeg
    omega
  have hp (v : Fin g × ℕ) : (X : F[X]) ^ v.1.val * b ^ v.2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hb)
  apply polynomial_linearIndependent_of_degrees _ hp
  intro v w h
  have hdegree (v : Fin g × ℕ) :
      ((X : F[X]) ^ v.1.val * b ^ v.2).natDegree = v.1.val + v.2 * b.natDegree := by
    rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) (pow_ne_zero _ hb),
      Polynomial.natDegree_X_pow, Polynomial.natDegree_pow]
  change (X ^ v.1.val * b ^ v.2).natDegree = (X ^ w.1.val * b ^ w.2).natDegree at h
  rw [hdegree, hdegree] at h
  have hv : v.1.val < b.natDegree := lt_of_lt_of_le v.1.isLt hbdeg
  have hw : w.1.val < b.natDegree := lt_of_lt_of_le w.1.isLt hbdeg
  have hm := congrArg (fun n => n % b.natDegree) h
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv, Nat.mod_eq_of_lt hw] at hm
  have hfst : v.1 = w.1 := Fin.ext hm
  have hmul : v.2 * b.natDegree = w.2 * b.natDegree := by omega
  have hpos : 0 < b.natDegree := lt_of_lt_of_le hg hbdeg
  exact Prod.ext hfst (Nat.eq_of_mul_eq_mul_right hpos hmul)

end
open MvPolynomial
open scoped Classical BigOperators

theorem projection_strip_hilbert_weighted {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p)
    (M : ℕ) (T : ℝ) (hT : ω x * M + ω y ≤ T) :
    2*(M+1) ≤ weightedHilbert I ω T := by
  classical
  let v := fun i : Fin 2 × Fin (M+1) =>
    Ideal.Quotient.mk I (rename ![y,x] (monomial (binaryStripExponent i) (1:K)))
  have hv (i : Fin 2 × Fin (M+1)) : v i ∈ weightedFunctions I ω T := by
    have he : rename ![y,x] (monomial (binaryStripExponent i) (1:K)) = (X y)^i.1.val*(X x)^i.2.val := by
      rw [binaryStripExponent,← one_mul (1:K),← monomial_mul_monomial,← X_pow_eq_monomial,← X_pow_eq_monomial]
      simp
    dsimp only [v]
    rw [he]
    apply coordinate_power_mem_weighted I ω hω x y _ _ T
    have h1 : (i.1.val:ℝ) ≤ 1 := by exact_mod_cast (show i.1.val ≤ 1 by omega)
    have h2 : (i.2.val:ℝ) ≤ M := by exact_mod_cast (show i.2.val ≤ M by omega)
    nlinarith [mul_le_mul_of_nonneg_left h1 (hω y).le,
      mul_le_mul_of_nonneg_left h2 (hω x).le]
  let u : (Fin 2 × Fin (M+1)) → weightedFunctions I ω T := fun i => ⟨v i,hv i⟩
  have hu : LinearIndependent K u := LinearIndependent.of_comp (weightedFunctions I ω T).subtype
    (projection_strip_independent I x y q hq hker M)
  simpa only [Fintype.card_prod,Fintype.card_fin,weightedHilbert] using hu.fintype_card_le_finrank

theorem projection_curve_hilbert_weighted {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j)
    (x y : Fin n) (q : MvPolynomial (Fin 2) K) (hq : 2 ≤ q.degreeOf 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename ![y,x] p) = 0 ↔ q ∣ p) :
    ∀ T : ℝ, 0 ≤ T → 2*T/(ω x)-2*(ω y/(ω x)+1) ≤ weightedHilbert I ω T := by
  intro T _
  by_cases hT : ω y ≤ T
  · let M := ⌊(T-ω y)/(ω x)⌋₊
    have hf : (M:ℝ) ≤ (T-ω y)/(ω x) := Nat.floor_le (div_nonneg (sub_nonneg.mpr hT) (hω x).le)
    have hb := projection_strip_hilbert_weighted I ω hω x y q hq hker M T (by
      have := (le_div_iff₀ (hω x)).mp hf
      nlinarith)
    have hbr : 2*((M:ℝ)+1) ≤ weightedHilbert I ω T := by exact_mod_cast hb
    have hl : (T-ω y)/(ω x) < (M:ℝ)+1 := Nat.lt_floor_add_one _
    rw [sub_div] at hl
    rw [mul_div_assoc]
    linarith
  · have hh : (0:ℝ) ≤ weightedHilbert I ω T := Nat.cast_nonneg _
    have ht : T/(ω x) < (ω y)/(ω x) := (div_lt_div_iff_of_pos_right (hω x)).mpr (lt_of_not_ge hT)
    rw [mul_div_assoc]
    linarith

theorem curve_coordinate_rationalization {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hI : affineDimension I ≤ 1) (e : ℕ) (hdeg : affineDegree I ≤ e)
    (ω : Fin n → ℝ) (hω : ∀ j, 0 < ω j) (s : Fin n)
    (hs : Transcendental K (Ideal.Quotient.mk I (X s))) :
    (∃ j, ∀ T : ℝ, 0 ≤ T →
      2*T/(ω s)-2*(ω j/(ω s)+1) ≤ weightedHilbert I ω T) ∨
    (∃ A B : Fin n → Polynomial K, ∀ j, IsCoprime (A j) (B j) ∧ B j ≠ 0 ∧
      (A j).natDegree ≤ e ∧ (B j).natDegree ≤ e ∧
      Polynomial.aeval (Ideal.Quotient.mk I (X s)) (A j) =
        Ideal.Quotient.mk I (X j)*Polynomial.aeval (Ideal.Quotient.mk I (X s)) (B j)) := by
  classical
  choose q hq hd hb hker using fun j => curve_coordinate_relation I hI s j hs
  by_cases h2 : ∃ j, 2 ≤ (q j).degreeOf 0
  · obtain ⟨j,hj⟩ := h2
    exact Or.inl ⟨j,projection_curve_hilbert_weighted I ω hω s j (q j) hj (hker j)⟩
  push Not at h2
  have hone (j) : (q j).degreeOf 0 = 1 := by have := hd j; have := h2 j; omega
  choose A B hcop hB hAdeg hBdeg hrel using fun j => linear_projection_rational (q j) (hq j) (hone j)
  refine Or.inr ⟨A,B,fun j => ⟨hcop j,hB j,?_,?_,?_⟩⟩
  · exact (hAdeg j).trans (by exact_mod_cast (hb j).trans hdeg)
  · exact (hBdeg j).trans (by exact_mod_cast (hb j).trans hdeg)
  · exact (hrel j (algebraMap K _) (Ideal.Quotient.mk I (X s)) (Ideal.Quotient.mk I (X j))).mp
      (projection_equation_quotient I s j (q j) ((hker j (q j)).mpr (dvd_refl _)))

theorem rational_graph_denominator_ne_zero {K : Type*} [Field K]
    (A B : Polynomial K) (hcop : IsCoprime A B) (x y : K)
    (he : A.eval x = y*B.eval x) : B.eval x ≠ 0 := by
  intro hz
  obtain ⟨u,v,huv⟩ := hcop
  have hh := congrArg (Polynomial.eval x) huv
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,he,hz,mul_zero,
    add_zero] at hh
  exact zero_ne_one hh

theorem rational_coordinates_injOn {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (s : Fin n) (A B : Fin n → Polynomial ℂ)
    (hcop : ∀ j, IsCoprime (A j) (B j))
    (hrel : ∀ j, Polynomial.aeval (Ideal.Quotient.mk I (X s)) (A j) =
      Ideal.Quotient.mk I (X j)*Polynomial.aeval (Ideal.Quotient.mk I (X s)) (B j)) :
    Set.InjOn (fun z : Fin n → ℤ => z s) {z | PointOn I z} := by
  intro z hz v hv h
  funext j
  have hez := rational_coordinate_at_point I z hz s j (A j) (B j) (hrel j)
  have hev := rational_coordinate_at_point I v hv s j (A j) (B j) (hrel j)
  have hn := rational_graph_denominator_ne_zero (A j) (B j) (hcop j) (z s) (z j) hez
  change z s = v s at h
  rw [←h] at hev
  apply Int.cast_injective (α := ℂ)
  exact mul_right_cancel₀ hn (hez.symm.trans hev)

end QuarticPowerFree

end OAI
