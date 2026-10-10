import OAI.NumberTheory.PowerFree.AffineHilbert

namespace OAI

universe u

namespace QuarticPowerFree

section
open MvPolynomial

theorem norm_real_hilbert_uniform_affine_pair {n d : ℕ} {K : Type u} [Field K]
    {k : ℕ} (hk : 0 < k) (A B : ℕ) (hA : 0 < A) (hB : 0 < B)
    (E D : ℕ) (hD : 0 < D) (L : ℝ) (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
        (a b : Fin d → MvPolynomial (Fin n) K) (x : MvPolynomial (Fin n) K)
        (θ : Fin d → K), Function.Injective θ →
      (∀ i, Ideal.Quotient.mk I (a i) ≠ 0) →
      (∀ i, Ideal.Quotient.mk I (a i)^k * Ideal.Quotient.mk I (b i) =
        Ideal.Quotient.mk I x - algebraMap K (MvPolynomial (Fin n) K ⧸ I) (θ i)) →
      ∀ (j : Fin 2 → Fin d), Function.Injective j →
      AlgebraicIndependent K (Fin.cases (Ideal.Quotient.mk I x)
        (fun _ : Fin 1 => Ideal.Quotient.mk I (a (j 1)))) →
      LinearIndependent K (fun o : Option (Fin 2) => o.elim 1 (fun i => Ideal.Quotient.mk I (a (j i)))) →
      affineDimension I = 2 → affineDegree I ≤ E →
      (∀ i, (a i).totalDegree ≤ D) → x.totalDegree ≤ D →
      ∀ (w : Fin n → ℕ), (∀ i, w i ≠ 0) →
        (∀ i, a i ∈ weightedSpace w A) → (∀ i, b i ∈ weightedSpace w B) →
      ∀ (ω : Fin n → ℝ), (∀ i, 0 < ω i) → (∀ i, (w i:ℝ) = L*ω i) →
      ∀ T : ℝ, 1 ≤ T →
        ((min (2*A) B : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^1 * L^(2) /
          (((2).factorial:ℝ)*(A:ℝ)^(2)*(B:ℝ)^(2))*T^(2) -
          C*T^1 ≤ weightedHilbert I ω T := by
  let α : ℝ := ((min (2*A) B : ℕ):ℝ)*((k*A+B : ℕ):ℝ)^1 /
    (((2).factorial:ℝ)*(A:ℝ)^(2)*(B:ℝ)^(2))
  have hα : 0 ≤ α := by dsimp [α]; positivity
  obtain ⟨C,hC,hh⟩ := norm_ambient_hilbert_uniform_affine_pair (n := n) (d := d)
    (K := K) hk A B hA hB E D hD
  obtain ⟨c,hc,hr⟩ := uniform_real_hilbert_floor 1 ((k*A+B)*(E*D^(2))) L α C hL hα hC
  refine ⟨c,hc,fun I _ a b x θ hθ ha hab j hj hind hlind hdim hdeg hadeg hxdeg w hw haw hbw ω hω hscale T hT => ?_⟩
  have hb := hr (fun N => (Module.finrank K ((weightedSpace w N).map
        (Ideal.Quotient.mkₐ K I).toLinearMap):ℝ))
    (fun t => (weightedHilbert I ω t:ℝ))
    (fun t => Nat.cast_nonneg _)
    (fun t ht => by
      exact_mod_cast Submodule.finrank_mono
        (weightedSpace_map_le_weightedFunctions I w ω hω L hL hscale t (by linarith)))
    (by simpa only [α,pow_one] using hh I a b x θ hθ ha hab j hj hind hlind hdim hdeg hadeg hxdeg w hw haw hbw) T hT
  dsimp only [α] at hb
  convert hb using 1; ring

end

open Polynomial
open scoped BigOperators Classical

noncomputable def rootCoeffLinear {K : Type*} [Field K] (r : K) (n : ℕ) :
    Polynomial K →ₗ[K] K :=
  (Polynomial.lcoeff K n).comp ((Polynomial.aeval (Polynomial.X+Polynomial.C r)).toLinearMap)

lemma rootCoeffLinear_apply {K : Type*} [Field K] (r : K) (n : ℕ) (P : Polynomial K) :
    rootCoeffLinear r n P = (P.comp (X+C r)).coeff n := by
  rfl

lemma rootCoeffLinear_mul_pow {K : Type*} [Field K] (r : K) (m n : ℕ) (P : Polynomial K) :
    rootCoeffLinear r n ((X-C r)^m*P) =
      if m ≤ n then (P.comp (X+C r)).coeff (n-m) else 0 := by
  rw [rootCoeffLinear_apply]
  simp only [Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.sub_comp,Polynomial.X_comp,
    Polynomial.C_comp,add_sub_cancel_right]
  rw [Polynomial.coeff_X_pow_mul']

theorem linearIndependent_of_blocks {K V α ι β : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Fintype α] [Fintype ι]
    (b : α → V) (e : ι → V) (block : ι → β) (ord : ι → ℕ)
    (φ : ι → V →ₗ[K] K) (hb : LinearIndependent K b)
    (hbase : ∀ i a, φ i (b a) = 0)
    (hlead : ∀ i, φ i (e i) ≠ 0)
    (htri : ∀ i j, block i ≠ block j ∨ ord i < ord j → φ i (e j) = 0)
    (hinj : ∀ i j, block i = block j → ord i = ord j → i = j) :
    LinearIndependent K (Sum.elim b e) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hce : ∀ i, c (.inr i) = 0 := by
    have hind : ∀ n, ∀ i, ord i = n → c (.inr i) = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro i hi
        have hh := congrArg (φ i) hc
        simp only [map_add,map_sum,map_smul,map_zero,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr] at hh
        have hterms : ∀ j, j ≠ i → c (.inr j) • φ i (e j) = 0 := by
          intro j hji
          by_cases hblock : block i = block j
          · by_cases hlt : ord j < ord i
            · rw [ih (ord j) (hi ▸ hlt) j rfl,zero_smul]
            · have hne : ord i ≠ ord j := fun heq => hji (hinj i j hblock heq).symm
              rw [htri i j (Or.inr (by omega)),smul_zero]
          · rw [htri i j (Or.inl hblock),smul_zero]
        rw [Finset.sum_eq_single i] at hh
        · simp only [hbase,smul_eq_mul,mul_zero,Finset.sum_const_zero,zero_add] at hh
          exact (mul_eq_zero.mp hh).resolve_right (hlead i)
        · exact fun j _ hji => hterms j hji
        · simp
    exact fun i => hind (ord i) i rfl
  have hcb : ∀ a, c (.inl a) = 0 := by
    apply Fintype.linearIndependent_iff.mp hb
    simpa only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,hce,zero_smul,
      Finset.sum_const_zero,add_zero] using hc
  intro i
  cases i with
  | inl a => exact hcb a
  | inr i => exact hce i

lemma rootCoeffLinear_zero_of_dvd {K : Type*} [Field K] (r : K) (m n : ℕ)
    (hn : n < m) (P : Polynomial K) (hP : (X-C r)^m ∣ P) :
    rootCoeffLinear r n P = 0 := by
  obtain ⟨Q,rfl⟩ := hP
  rw [rootCoeffLinear_mul_pow,ite_eq_right (by omega)]

lemma rootCoeffLinear_lead {K : Type*} [Field K] (r : K) (m : ℕ) (P : Polynomial K) :
    rootCoeffLinear r m ((X-C r)^m*P) = P.eval r := by
  rw [rootCoeffLinear_mul_pow,ite_eq_left le_rfl,Nat.sub_self,Polynomial.coeff_zero_eq_eval_zero]
  simp

lemma polynomial_powers_mul_independent {K : Type*} [Field K] (N : ℕ)
    (D : Polynomial K) (hD : D ≠ 0) :
    LinearIndependent K (fun a : Fin N => X^a.val*D) := by
  have hb := (Polynomial.basisMonomials K).linearIndependent.comp
    (fun a : Fin N => a.val) Fin.val_injective
  rw [Polynomial.coe_basisMonomials] at hb
  simp only [Function.comp_def,Polynomial.monomial_one_right_eq_X_pow] at hb
  exact hb.map' (LinearMap.mulRight K D) (LinearMap.ker_eq_bot.mpr (mul_left_injective₀ hD))

noncomputable def threePoleNumerator {K : Type*} [Field K] (r₀ : K) (r : Fin 2 → K)
    (m : ℕ) (i : Fin 2 × Fin m × Fin 2) : Polynomial K :=
  (X-C (r i.1))^(2*(m-(i.2.1.val+1))+i.2.2.val) *
    ((X-C r₀)^(2*(i.2.1.val+1)) * (X-C (r (1-i.1)))^(2*m))

noncomputable def threePoleBase {K : Type*} [Field K] (r : Fin 2 → K) (m : ℕ) : Polynomial K :=
  (X-C (r 0))^(2*m)*(X-C (r 1))^(2*m)

lemma fin_two_complement {s t : Fin 2} (h : s ≠ t) : s = 1-t := by
  fin_cases s <;> fin_cases t
  all_goals simp_all

lemma threePoleNumerator_other_dvd {K : Type*} [Field K] (r₀ : K) (r : Fin 2 → K)
    (m : ℕ) (s : Fin 2) (i : Fin 2 × Fin m × Fin 2) (h : s ≠ i.1) :
    (X-C (r s))^(2*m) ∣ threePoleNumerator r₀ r m i := by
  rw [fin_two_complement h]
  exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

theorem threePole_leading_independent {K : Type*} [Field K] (r₀ : K) (r : Fin 2 → K)
    (h₀ : ∀ i, r i ≠ r₀) (hr : Function.Injective r) (m N : ℕ) :
    LinearIndependent K (Sum.elim (fun a : Fin N => X^a.val*threePoleBase r m)
      (threePoleNumerator r₀ r m)) := by
  classical
  let v (i : Fin 2 × Fin m × Fin 2) := 2*(m-(i.2.1.val+1))+i.2.2.val
  have hv (i : Fin 2 × Fin m × Fin 2) : v i < 2*m := by
    dsimp [v]
    have := i.2.1.isLt
    have := i.2.2.isLt
    omega
  have hother (i : Fin 2) : r i - r (1-i) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hh := hr h
    fin_cases i <;> norm_num at hh
  have hD : threePoleBase r m ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) (pow_ne_zero _ (X_sub_C_ne_zero _))
  apply linearIndependent_of_blocks _ _ (fun i => i.1) v
    (fun i => rootCoeffLinear (r i.1) (v i)) (polynomial_powers_mul_independent N _ hD)
  · intro i a
    apply rootCoeffLinear_zero_of_dvd _ (2*m) _ (hv i)
    apply dvd_mul_of_dvd_right
    dsimp [threePoleBase]
    rcases i with ⟨s,j,e⟩
    fin_cases s
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  · intro i
    change rootCoeffLinear _ _ ((X-C (r i.1))^(v i)*_) ≠ 0
    rw [rootCoeffLinear_lead]
    simpa only [eval_mul,eval_pow,eval_sub,eval_X,eval_C] using
      mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (h₀ i.1))) (pow_ne_zero _ (hother i.1))
  · intro i j hij
    by_cases hblock : i.1 = j.1
    · have hless : v i < v j := hij.resolve_left (not_not.mpr hblock)
      apply rootCoeffLinear_zero_of_dvd _ (v j) _ hless
      rw [hblock]
      exact dvd_mul_right _ _
    · exact rootCoeffLinear_zero_of_dvd _ (2*m) _ (hv i) _
        (threePoleNumerator_other_dvd r₀ r m i.1 j hblock)
  · intro i j hblock horder
    apply Prod.ext hblock
    apply Prod.ext
    · apply Fin.ext
      dsimp [v] at horder
      have := i.2.1.isLt
      have := j.2.1.isLt
      have := i.2.2.isLt
      have := j.2.2.isLt
      omega
    · apply Fin.ext
      dsimp [v] at horder
      have := i.2.1.isLt
      have := j.2.1.isLt
      have := i.2.2.isLt
      have := j.2.2.isLt
      omega

theorem linearIndependent_of_top_blocks {K V W ι : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Fintype ι]
    (p : ι → V) (d : ι → ℕ) (φ : ℕ → V →ₗ[K] W)
    (hzero : ∀ i n, d i < n → φ n (p i) = 0)
    (hlead : ∀ n, LinearIndependent K (fun i : {i // d i = n} => φ n (p i.val))) :
    LinearIndependent K p := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hci
  let s := Finset.univ.filter (fun j => c j ≠ 0)
  have hs : s.Nonempty := ⟨i,by simp [s,hci]⟩
  obtain ⟨j,hjs,hmax⟩ := Finset.exists_max_image s d hs
  have hcj := (Finset.mem_filter.mp hjs).2
  have hh := congrArg (φ (d j)) hc
  simp only [map_sum,map_smul,map_zero] at hh
  have heq : (∑ l : {l // d l = d j}, c l.val • φ (d j) (p l.val)) = 0 := by
    have hsub : (∑ l : {l // d l = d j}, c l.val • φ (d j) (p l.val)) =
        ∑ l ∈ Finset.univ.filter (fun l => d l = d j), c l • φ (d j) (p l) := by
      simpa using (Finset.sum_subtype_eq_sum_filter (s := Finset.univ)
        (p := fun l => d l = d j) (fun l => c l • φ (d j) (p l)))
    rw [hsub]
    have hfilter : (∑ l ∈ Finset.univ.filter (fun l => d l = d j), c l • φ (d j) (p l)) =
        ∑ l, c l • φ (d j) (p l) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro l _ hl
      have hne : d l ≠ d j := by simpa using hl
      by_cases hcl : c l = 0
      · simp [hcl]
      · have hle := hmax l (by simp [s,hcl])
        rw [hzero l (d j) (lt_of_le_of_ne hle hne),smul_zero]
    exact hfilter.trans hh
  exact hcj (Fintype.linearIndependent_iff.mp (hlead (d j)) _ heq ⟨j,rfl⟩)

noncomputable def twoPoleNumerator {K : Type*} [Field K] (r₀ r₁ : K)
    (m l : ℕ) (i : (Fin m × Fin 2) ⊕ (Fin l × Fin 2)) : Polynomial K :=
  i.elim (fun j => (X-C r₁)^(2*(m-(j.1.val+1))+j.2.val)*
      ((X-C r₀)^(2*l+2*(j.1.val+1))))
    (fun j => (X-C r₀)^(2*(l-(j.1.val+1))+j.2.val)*(X-C r₁)^(2*m))

theorem twoPole_leading_independent {K : Type*} [Field K] (r₀ r₁ : K)
    (hr : r₀ ≠ r₁) (m l N : ℕ) :
    LinearIndependent K (Sum.elim (fun a : Fin N => X^a.val*((X-C r₀)^(2*l)*(X-C r₁)^(2*m)))
      (twoPoleNumerator r₀ r₁ m l)) := by
  classical
  let block : (Fin m × Fin 2) ⊕ (Fin l × Fin 2) → Bool := Sum.elim (fun _ => true) (fun _ => false)
  let v : (Fin m × Fin 2) ⊕ (Fin l × Fin 2) → ℕ :=
    Sum.elim (fun j => 2*(m-(j.1.val+1))+j.2.val) (fun j => 2*(l-(j.1.val+1))+j.2.val)
  let r : Bool → K := fun b => if b then r₁ else r₀
  have hvm (j : Fin m × Fin 2) : v (.inl j) < 2*m := by
    dsimp [v]
    have := j.1.isLt
    have := j.2.isLt
    omega
  have hvl (j : Fin l × Fin 2) : v (.inr j) < 2*l := by
    dsimp [v]
    have := j.1.isLt
    have := j.2.isLt
    omega
  have hD : (X-C r₀)^(2*l)*(X-C r₁)^(2*m) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) (pow_ne_zero _ (X_sub_C_ne_zero _))
  apply linearIndependent_of_blocks _ _ block v (fun i => rootCoeffLinear (r (block i)) (v i))
    (polynomial_powers_mul_independent N _ hD)
  · intro i a
    cases i with
    | inl j =>
      apply rootCoeffLinear_zero_of_dvd _ (2*m) _ (hvm j)
      exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _
    | inr j =>
      apply rootCoeffLinear_zero_of_dvd _ (2*l) _ (hvl j)
      exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _
  · intro i
    cases i with
    | inl j =>
      change rootCoeffLinear r₁ _ ((X-C r₁)^_*_) ≠ 0
      dsimp only [v,Sum.elim_inl,Sum.elim_inr]
      rw [rootCoeffLinear_lead]
      simp only [eval_pow,eval_sub,eval_X,eval_C]
      exact pow_ne_zero _ (sub_ne_zero.mpr hr.symm)
    | inr j =>
      change rootCoeffLinear r₀ _ ((X-C r₀)^_*_) ≠ 0
      dsimp only [v,Sum.elim_inl,Sum.elim_inr]
      rw [rootCoeffLinear_lead]
      simp only [eval_pow,eval_sub,eval_X,eval_C]
      exact pow_ne_zero _ (sub_ne_zero.mpr hr)
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have hless : v (.inl i) < v (.inl j) := hij.resolve_left (by simp [block])
        exact rootCoeffLinear_zero_of_dvd _ _ _ hless _ (dvd_mul_right _ _)
      | inr j =>
        exact rootCoeffLinear_zero_of_dvd _ (2*m) _ (hvm i) _ (dvd_mul_left _ _)
    | inr i =>
      cases j with
      | inl j =>
        apply rootCoeffLinear_zero_of_dvd _ (2*l) _ (hvl i)
        apply dvd_mul_of_dvd_right
        exact pow_dvd_pow _ (Nat.le_add_right _ _)
      | inr j =>
        have hless : v (.inr i) < v (.inr j) := hij.resolve_left (by simp [block])
        exact rootCoeffLinear_zero_of_dvd _ _ _ hless _ (dvd_mul_right _ _)
  · intro i j hb hv
    cases i with
    | inl i =>
      cases j with
      | inr j => simp [block] at hb
      | inl j =>
        apply congrArg Sum.inl
        apply Prod.ext <;> apply Fin.ext
        all_goals
          dsimp [v] at hv
          have := i.1.isLt
          have := j.1.isLt
          have := i.2.isLt
          have := j.2.isLt
          omega
    | inr i =>
      cases j with
      | inl j => simp [block] at hb
      | inr j =>
        apply congrArg Sum.inr
        apply Prod.ext <;> apply Fin.ext
        all_goals
          dsimp [v] at hv
          have := i.1.isLt
          have := j.1.isLt
          have := i.2.isLt
          have := j.2.isLt
          omega

end QuarticPowerFree

end OAI
