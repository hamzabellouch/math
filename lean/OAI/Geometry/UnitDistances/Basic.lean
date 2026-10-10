import Mathlib

namespace OAI

namespace PlanarUnitDistances

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def IsUnitPair : Sym2 Plane → Prop :=
  Sym2.lift ⟨fun x y => dist x y = 1, fun x y => by dsimp; rw [dist_comm]⟩

noncomputable def unitPairCount (X : Finset Plane) : ℕ := by
  classical
  exact (X.sym2.filter IsUnitPair).card

noncomputable def u (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ X : Finset Plane, X.card = n ∧ unitPairCount X = m}

def MainClaim : Prop := ∃ C β : ℝ, 0 < C ∧ 1 ≤ β ∧ β < (4 : ℝ) / 3 ∧
    ∀ n : ℕ, (u n : ℝ) ≤ C * (n : ℝ) ^ β

@[simp] theorem isUnitPair_mk (x y : Plane) :
    IsUnitPair s(x, y) ↔ dist x y = 1 := Iff.rfl

@[simp] theorem not_isUnitPair_diag (x : Plane) :
    ¬ IsUnitPair (Sym2.diag x) := by
  simp [IsUnitPair, Sym2.diag]

theorem unitPairCount_le_card_sq (X : Finset Plane) :
    unitPairCount X ≤ X.card ^ 2 := by
  classical
  calc
    unitPairCount X ≤ X.sym2.card := Finset.card_filter_le _ _
    _ ≤ (X ×ˢ X).card := by
      rw [Finset.sym2_eq_image]
      exact Finset.card_image_le
    _ = X.card ^ 2 := by rw [Finset.card_product, pow_two]

private theorem attainable_nonempty (n : ℕ) :
    {m : ℕ | ∃ X : Finset Plane, X.card = n ∧ unitPairCount X = m}.Nonempty := by
  obtain ⟨X, hX⟩ := Infinite.exists_subset_card_eq Plane n
  exact ⟨unitPairCount X, X, hX, rfl⟩

private theorem attainable_bddAbove (n : ℕ) :
    BddAbove {m : ℕ | ∃ X : Finset Plane, X.card = n ∧ unitPairCount X = m} := by
  refine ⟨n ^ 2, ?_⟩
  rintro m ⟨X, hX, rfl⟩
  simpa [hX] using unitPairCount_le_card_sq X

theorem exists_maximizer (n : ℕ) :
    ∃ X : Finset Plane, X.card = n ∧ unitPairCount X = u n :=
  Nat.sSup_mem (attainable_nonempty n) (attainable_bddAbove n)

theorem unitPairCount_le_u (X : Finset Plane) : unitPairCount X ≤ u X.card := by
  exact le_csSup (attainable_bddAbove X.card) ⟨X, rfl, rfl⟩

theorem u_le_sq (n : ℕ) : u n ≤ n ^ 2 := by
  obtain ⟨X, hX, hmax⟩ := exists_maximizer n
  rw [← hmax, ← hX]
  exact unitPairCount_le_card_sq X

@[simp] theorem u_zero : u 0 = 0 := Nat.eq_zero_of_le_zero (by simpa using u_le_sq 0)

@[simp] theorem unitPairCount_singleton (p : Plane) : unitPairCount {p} = 0 := by
  classical
  simp [unitPairCount]

@[simp] theorem u_one : u 1 = 0 := by
  obtain ⟨X, hX, hmax⟩ := exists_maximizer 1
  obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hX
  simpa using hmax.symm

theorem mainClaim_iff_uniform : MainClaim ↔
    ∃ C β : ℝ, 0 < C ∧ 1 ≤ β ∧ β < (4 : ℝ) / 3 ∧
      ∀ X : Finset Plane, (unitPairCount X : ℝ) ≤ C * (X.card : ℝ) ^ β := by
  constructor
  · rintro ⟨C, β, hC, hβ, hβ', hb⟩
    refine ⟨C, β, hC, hβ, hβ', fun X => ?_⟩
    exact (Nat.cast_le.mpr (unitPairCount_le_u X)).trans (hb X.card)
  · rintro ⟨C, β, hC, hβ, hβ', hb⟩
    refine ⟨C, β, hC, hβ, hβ', fun n => ?_⟩
    obtain ⟨X, hX, hmax⟩ := exists_maximizer n
    simpa [hX, hmax] using hb X

theorem arbitrarily_large_counterexample (hmain : ¬ MainClaim)
    (β : ℝ) (hβ : 1 ≤ β) (hβ' : β < (4 : ℝ) / 3) (N : ℕ) :
    ∃ X : Finset Plane, N ≤ X.card ∧
      (X.card : ℝ) ^ β < (unitPairCount X : ℝ) := by
  classical
  let C : ℝ := (N + 1 : ℝ) ^ 2 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hfail : ¬ ∀ n : ℕ, (u n : ℝ) ≤ C * (n : ℝ) ^ β := by
    intro hb
    exact hmain ⟨C, β, hC, hβ, hβ', hb⟩
  push Not at hfail
  obtain ⟨n, hn⟩ := hfail
  have hn0 : n ≠ 0 := by
    intro heq
    simp only [heq, Nat.cast_zero, u_zero] at hn
    rw [Real.zero_rpow (by linarith : β ≠ 0), mul_zero] at hn
    exact (lt_irrefl 0) hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
  have hrpow : 1 ≤ (n : ℝ) ^ β := Real.one_le_rpow hn1 (by linarith)
  have hnN : N ≤ n := by
    by_contra h
    have hnN' : (n : ℝ) ≤ N + 1 := by exact_mod_cast (by omega : n ≤ N + 1)
    have hnsq : (n : ℝ) ^ 2 ≤ (N + 1 : ℝ) ^ 2 := by
      exact sq_le_sq₀ (by positivity) (by positivity) |>.mpr hnN'
    have hu : (u n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast u_le_sq n
    have hmul : C ≤ C * (n : ℝ) ^ β := by nlinarith [hC]
    dsimp [C] at hmul hn
    nlinarith
  have hC1 : 1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg (N + 1 : ℝ)]
  have hsmall : (n : ℝ) ^ β ≤ C * (n : ℝ) ^ β := by
    exact le_mul_of_one_le_left (by positivity) hC1
  obtain ⟨X, hX, hmax⟩ := exists_maximizer n
  exact ⟨X, hX ▸ hnN, by simpa [hX, hmax] using hsmall.trans_lt hn⟩

theorem counterexample_sequence (hmain : ¬ MainClaim) :
    ∃ X : ℕ → Finset Plane, ∀ j : ℕ, j ≤ (X j).card ∧
      ((X j).card : ℝ) ^ ((4 : ℝ) / 3 - 1 / (j + 3 : ℝ)) <
        (unitPairCount (X j) : ℝ) := by
  classical
  have h (j : ℕ) : ∃ X : Finset Plane, j ≤ X.card ∧
      (X.card : ℝ) ^ ((4 : ℝ) / 3 - 1 / (j + 3 : ℝ)) < (unitPairCount X : ℝ) := by
    apply arbitrarily_large_counterexample hmain
    · have hj : (3 : ℝ) ≤ (j : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) j]
      have hinv : 1 / (j + 3 : ℝ) ≤ 1 / 3 := by
        exact one_div_le_one_div_of_le (by norm_num) hj
      linarith
    · have hj : 0 < 1 / (j + 3 : ℝ) := by positivity
      linarith
  exact ⟨fun j => (h j).choose, fun j => (h j).choose_spec⟩

end PlanarUnitDistances

namespace PlanarUnitDistances.AlgebraicSpecialization
open Set Filter Polynomial
open scoped Topology

lemma signs_in_nhds {f : ℝ → ℝ} {θ d : ℝ} (hf : HasDerivAt f d θ)
    (hd : d ≠ 0) (hz : f θ = 0) {V : Set ℝ} (hV : V ∈ 𝓝 θ) :
    (∃ a ∈ V, f a < 0) ∧ (∃ b ∈ V, 0 < f b) := by
  constructor
  · by_contra h
    push Not at h
    have hm : IsLocalMin f θ := by
      change ∀ᶠ x in 𝓝 θ, f θ ≤ f x
      exact mem_of_superset hV (fun x hx => by simpa [hz] using h x hx)
    exact hd (hm.hasDerivAt_eq_zero hf)
  · by_contra h
    push Not at h
    have hm : IsLocalMax f θ := by
      change ∀ᶠ x in 𝓝 θ, f x ≤ f θ
      exact mem_of_superset hV (fun x hx => by simpa [hz] using h x hx)
    exact hd (hm.hasDerivAt_eq_zero hf)

theorem dense_parameter_root {A B : Type*} [TopologicalSpace A]
    {φ : B → A} (hφ : DenseRange φ) {F : A × ℝ → ℝ} (hF : Continuous F)
    {u : A} {θ d : ℝ} (hf : HasDerivAt (fun t => F (u,t)) d θ)
    (hd : d ≠ 0) (hz : F (u,θ) = 0) {W : Set (A × ℝ)}
    (hW : W ∈ 𝓝 (u,θ)) :
    ∃ v : B, ∃ τ : ℝ, (φ v,τ) ∈ W ∧ F (φ v,τ) = 0 ∧
      ∃ a : ℝ, F (φ v,a) < 0 := by
  obtain ⟨U,hU,V,hV,hUV⟩ := mem_nhds_prod_iff.mp hW
  obtain ⟨ε,hε,hεV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨⟨a,ha,haF⟩,⟨b,hb,hbF⟩⟩ := signs_in_nhds hf hd hz
    (Metric.ball_mem_nhds θ hε)
  have hca : Continuous (fun v : A => F (v,a)) :=
    hF.comp (continuous_id.prodMk continuous_const)
  have hcb : Continuous (fun v : A => F (v,b)) :=
    hF.comp (continuous_id.prodMk continuous_const)
  have hna : {v : A | F (v,a) < 0} ∈ 𝓝 u :=
    (isOpen_lt hca continuous_const).mem_nhds haF
  have hpb : {v : A | 0 < F (v,b)} ∈ 𝓝 u :=
    (isOpen_lt continuous_const hcb).mem_nhds hbF
  obtain ⟨v,hvU,hva,hvb⟩ := hφ.mem_nhds (inter_mem hU (inter_mem hna hpb))
  have hc : Continuous (fun t => F (φ v,t)) :=
    hF.comp (continuous_const.prodMk continuous_id)
  obtain ⟨τ,hτ,hτF⟩ := intermediate_value_uIcc hc.continuousOn
    (show 0 ∈ uIcc (F (φ v,a)) (F (φ v,b)) by
      rw [uIcc_of_le (hva.le.trans hvb.le)]; exact ⟨hva.le,hvb.le⟩)
  have hτball : τ ∈ Metric.ball θ ε := by
    rw [Real.ball_eq_Ioo] at ha hb ⊢
    rw [mem_uIcc] at hτ
    rcases hτ with hτ | hτ
    · exact ⟨ha.1.trans_le hτ.1,hτ.2.trans_lt hb.2⟩
    · exact ⟨hb.1.trans_le hτ.1,hτ.2.trans_lt ha.2⟩
  exact ⟨v,τ,hUV ⟨hvU,hεV hτball⟩,hτF,a,hva⟩

abbrev ParameterPolynomial (ι : Type*) := Polynomial (MvPolynomial ι ℚ)

noncomputable def evaluate {ι : Type*} (F : ParameterPolynomial ι)
    (u : ι → ℝ) (θ : ℝ) : ℝ :=
  F.eval₂ (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) u) θ

lemma continuous_parameter_eval {ι : Type*} (F : ParameterPolynomial ι) :
    Continuous (fun p : (ι → ℝ) × ℝ => evaluate F p.1 p.2) := by
  induction F using Polynomial.induction_on' with
  | add p q hp hq =>
    convert hp.add hq using 1
    ext x
    simp [evaluate,eval₂_add]
  | monomial n c =>
    have he : Continuous (fun u : ι → ℝ =>
        MvPolynomial.eval₂ (algebraMap ℚ ℝ) u c) := by
      simpa only [← MvPolynomial.eval_map] using
        (MvPolynomial.continuous_eval (c.map (algebraMap ℚ ℝ)))
    convert (he.comp continuous_fst).mul (continuous_snd.pow n) using 1
    ext x
    simp [evaluate,eval₂_monomial]

theorem rational_simple_root {ι : Type*} (F : ParameterPolynomial ι)
    {u : ι → ℝ} {θ : ℝ} (hz : evaluate F u θ = 0)
    (hd : evaluate F.derivative u θ ≠ 0) {W : Set ((ι → ℝ) × ℝ)}
    (hW : W ∈ 𝓝 (u,θ)) :
    ∃ v : ι → ℚ, ∃ τ : ℝ, ((fun i => (v i : ℝ)),τ) ∈ W ∧
      evaluate F (fun i => (v i : ℝ)) τ = 0 ∧ IsAlgebraic ℚ τ := by
  have hf : HasDerivAt (fun t => evaluate F u t) (evaluate F.derivative u θ) θ := by
    simpa [evaluate,eval₂_eq_eval_map,derivative_map] using
      (F.map (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) u)).hasDerivAt θ
  have hφ : DenseRange (fun v : ι → ℚ => (fun i => (v i : ℝ))) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨v,τ,hτW,hτF,a,ha⟩ := dense_parameter_root hφ
    (continuous_parameter_eval F) hf hd hz hW
  refine ⟨v,τ,hτW,hτF,?_⟩
  let G : Polynomial ℚ := F.map (MvPolynomial.eval v)
  have he (t : ℝ) : G.aeval t = evaluate F (fun i => (v i : ℝ)) t := by
    simp only [G,aeval_def,eval₂_map,evaluate]
    congr 1
    ext i <;> simp
  refine ⟨G,?_,?_⟩
  · intro hG
    have hh := he a
    rw [hG,map_zero] at hh
    linarith
  · rw [he,hτF]

lemma evaluate_rat {ι : Type*} (F : ParameterPolynomial ι) (v : ι → ℚ) (τ : ℝ) :
    evaluate F (fun i => (v i : ℝ)) τ =
      Polynomial.aeval τ (F.map (MvPolynomial.eval v)) := by
  simp only [aeval_def,eval₂_map,evaluate]
  congr 1
  ext i <;> simp

lemma algebraic_polynomial_value (p : Polynomial ℚ) {τ : ℝ}
    (hτ : IsAlgebraic ℚ τ) : IsAlgebraic ℚ (Polynomial.aeval τ p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | monomial n c =>
    simpa only [aeval_monomial] using (isAlgebraic_algebraMap (A := ℝ) c).mul (hτ.pow n)

lemma algebraic_parameter_value {ι : Type*} (F : ParameterPolynomial ι)
    (v : ι → ℚ) {τ : ℝ} (hτ : IsAlgebraic ℚ τ) :
    IsAlgebraic ℚ (evaluate F (fun i => (v i : ℝ)) τ) := by
  rw [evaluate_rat]
  exact algebraic_polynomial_value _ hτ

noncomputable def chartValue {ι κ : Type*} (N D : κ → ParameterPolynomial ι)
    (p : (ι → ℝ) × ℝ) (i : κ) : ℝ := evaluate (N i) p.1 p.2 / evaluate (D i) p.1 p.2

theorem specialize_chart {ι κ η : Type*} [Finite κ] [Finite η]
    (F : ParameterPolynomial ι) (N D : κ → ParameterPolynomial ι)
    (G J : η → ParameterPolynomial ι) (b : η → MvPolynomial ι ℚ)
    {u : ι → ℝ} {θ : ℝ} (hz : evaluate F u θ = 0)
    (hd : evaluate F.derivative u θ ≠ 0)
    (hD : ∀ i, evaluate (D i) u θ ≠ 0)
    (hb : ∀ j, MvPolynomial.eval₂ (algebraMap ℚ ℝ) u (b j) ≠ 0)
    (hId : ∀ j, Polynomial.C (b j)*G j = F*J j)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ι → ℚ, ∃ τ : ℝ, IsAlgebraic ℚ τ ∧
      evaluate F (fun i => (v i : ℝ)) τ = 0 ∧
      (∀ i, evaluate (D i) (fun j => (v j : ℝ)) τ ≠ 0 ∧
        IsAlgebraic ℚ (chartValue N D ((fun j => (v j : ℝ)),τ) i) ∧
        |chartValue N D ((fun j => (v j : ℝ)),τ) i-chartValue N D (u,θ) i| < ε) ∧
      (∀ j, evaluate (G j) (fun i => (v i : ℝ)) τ = 0) := by
  have hden : ∀ᶠ p : (ι → ℝ) × ℝ in 𝓝 (u,θ), ∀ i,
      evaluate (D i) p.1 p.2 ≠ 0 :=
    eventually_all.mpr (fun i => (continuous_parameter_eval (D i)).continuousAt.eventually_ne (hD i))
  have happ : ∀ᶠ p : (ι → ℝ) × ℝ in 𝓝 (u,θ), ∀ i,
      |chartValue N D p i-chartValue N D (u,θ) i| < ε := by
    apply eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun p => chartValue N D p i) (u,θ) :=
      (continuous_parameter_eval (N i)).continuousAt.div
        (continuous_parameter_eval (D i)).continuousAt (hD i)
    have he := hc.eventually (Metric.ball_mem_nhds (chartValue N D (u,θ) i) hε)
    simpa only [Metric.mem_ball,Real.dist_eq] using he
  have hbne : ∀ᶠ p : (ι → ℝ) × ℝ in 𝓝 (u,θ), ∀ j,
      evaluate (Polynomial.C (b j)) p.1 p.2 ≠ 0 := by
    apply eventually_all.mpr
    intro j
    apply (continuous_parameter_eval (Polynomial.C (b j))).continuousAt.eventually_ne
    simpa [evaluate] using hb j
  obtain ⟨v,τ,hW,hF,hτ⟩ := rational_simple_root F hz hd (hden.and (happ.and hbne))
  refine ⟨v,τ,hτ,hF,?_,?_⟩
  · intro i
    refine ⟨hW.1 i,?_,hW.2.1 i⟩
    unfold chartValue
    rw [div_eq_mul_inv]
    exact (algebraic_parameter_value (N i) v hτ).mul
      (IsAlgebraic.inv_iff.mpr (algebraic_parameter_value (D i) v hτ))
  · intro j
    have he := congrArg (Polynomial.eval₂RingHom
      (MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) (fun i => (v i : ℝ))) τ) (hId j)
    change evaluate (Polynomial.C (b j)*G j) _ τ = evaluate (F*J j) _ τ at he
    simp only [evaluate,eval₂_mul] at he
    change evaluate (Polynomial.C (b j)) _ τ * evaluate (G j) _ τ =
      evaluate F _ τ * evaluate (J j) _ τ at he
    rw [hF,zero_mul] at he
    exact (mul_eq_zero.mp he).resolve_left (hW.2.2 j)

end PlanarUnitDistances.AlgebraicSpecialization

namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField

theorem finite_coordinates_primitive {K : Type*} [Field K] [CharZero K]
    [Algebra K ℝ] {κ : Type*} [Finite κ] (x : κ → ℝ)
    (hx : ∀ i, IsAlgebraic K (x i)) :
    ∃ θ : ℝ, IsAlgebraic K θ ∧ ∀ i, ∃ p q : Polynomial K,
      Polynomial.aeval θ q ≠ 0 ∧ x i = Polynomial.aeval θ p / Polynomial.aeval θ q := by
  let M := IntermediateField.adjoin K (Set.range x)
  have : Finite (Set.range x) := Set.finite_range x
  have : FiniteDimensional K M := IntermediateField.finiteDimensional_adjoin
    (fun y hy => by obtain ⟨i,rfl⟩ := hy; exact (hx i).isIntegral)
  obtain ⟨θ,hθ⟩ := Field.exists_primitive_element K M
  refine ⟨(θ : ℝ),?_,?_⟩
  · exact (Algebra.IsAlgebraic.isAlgebraic θ).algHom M.val
  · intro i
    by_cases hi : x i = 0
    · exact ⟨0,1,by simp,by simp [hi]⟩
    let y : M := ⟨x i,IntermediateField.subset_adjoin K (Set.range x) (mem_range_self i)⟩
    have hm : y ∈ IntermediateField.adjoin K {θ} := by rw [hθ]; trivial
    obtain ⟨p,q,hpq⟩ := (IntermediateField.mem_adjoin_simple_iff K y).mp hm
    have he : x i = Polynomial.aeval (θ : ℝ) p / Polynomial.aeval (θ : ℝ) q := by
      have hh := congrArg (fun a : M => (a : ℝ)) hpq
      simpa [y] using hh
    refine ⟨p,q,?_,he⟩
    intro hq
    rw [hq,div_zero] at he
    exact hi he

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Polynomial

theorem clear_polynomial {R K : Type*} [CommRing R] [IsDomain R] [Field K]
    (f : R →+* K)
    (hfrac : ∀ a : K, ∃ r s : R, s ≠ 0 ∧ a * f s = f r)
    (p : Polynomial K) :
    ∃ q : Polynomial R, ∃ d : R, d ≠ 0 ∧ q.map f = C (f d) * p := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨q₁,d₁,hd₁,hq₁⟩ := h₁
    obtain ⟨q₂,d₂,hd₂,hq₂⟩ := h₂
    refine ⟨C d₂ * q₁ + C d₁ * q₂,d₁*d₂,mul_ne_zero hd₁ hd₂,?_⟩
    simp only [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,hq₁,hq₂,
      map_mul]
    ring
  | monomial n a =>
    obtain ⟨r,s,hs,he⟩ := hfrac a
    refine ⟨monomial n r,s,hs,?_⟩
    rw [Polynomial.map_monomial,← he,mul_comm a (f s),← C_mul_monomial]

theorem clear_relation {R K L : Type*} [CommRing R] [IsDomain R]
    [Field K] [Field L] [Algebra K L]
    (f : R →+* K) (hf : Function.Injective f)
    (hfrac : ∀ a : K, ∃ r s : R, s ≠ 0 ∧ a * f s = f r)
    (θ : L) (F : Polynomial R) (d : R) (hd : d ≠ 0)
    (hF : F.map f = C (f d) * minpoly K θ)
    (G : Polynomial R) (hG : Polynomial.aeval θ (G.map f) = 0) :
    ∃ b : R, ∃ J : Polynomial R, b ≠ 0 ∧ C b * G = F * J := by
  obtain ⟨H,hH⟩ := minpoly.dvd K θ hG
  obtain ⟨J,e,he,hJ⟩ := clear_polynomial f hfrac H
  refine ⟨d*e,J,mul_ne_zero hd he,?_⟩
  apply Polynomial.map_injective f hf
  simp only [Polynomial.map_mul,Polynomial.map_C,map_mul,hF,hJ,hH]
  ring

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField

noncomputable abbrev ParameterField {ι : Type*} (u : ι → ℝ) :=
  IntermediateField.adjoin ℚ (Set.range u)

noncomputable def parameterMap {ι : Type*} (u : ι → ℝ) :
    MvPolynomial ι ℚ →ₐ[ℚ] ParameterField u :=
  MvPolynomial.aeval (fun i =>
    ⟨u i,IntermediateField.subset_adjoin ℚ (Set.range u) (mem_range_self i)⟩)

@[simp] theorem coe_parameterMap {ι : Type*} (u : ι → ℝ) (p : MvPolynomial ι ℚ) :
    ((parameterMap u p : ParameterField u) : ℝ) = MvPolynomial.aeval u p := by
  have he : (IntermediateField.val (ParameterField u)).comp (parameterMap u) =
      MvPolynomial.aeval u := by
    ext i
    change ((parameterMap u (MvPolynomial.X i) : ParameterField u) : ℝ) =
      MvPolynomial.aeval u (MvPolynomial.X i)
    simp only [parameterMap,MvPolynomial.aeval_X]
  exact AlgHom.congr_fun he p

theorem parameterMap_injective {ι : Type*} {u : ι → ℝ}
    (hu : AlgebraicIndependent ℚ u) : Function.Injective (parameterMap u) := by
  intro p q hpq
  apply (algebraicIndependent_iff_injective_aeval.mp hu)
  simpa only [coe_parameterMap] using congrArg (fun a : ParameterField u => (a : ℝ)) hpq

theorem parameterMap_fraction {ι : Type*} (u : ι → ℝ) (a : ParameterField u) :
    ∃ r s : MvPolynomial ι ℚ, s ≠ 0 ∧ a * parameterMap u s = parameterMap u r := by
  by_cases ha : a = 0
  · exact ⟨0,1,one_ne_zero,by simp [ha]⟩
  obtain ⟨r,hr,s,hs,h⟩ := IntermediateField.mem_adjoin_iff_div.mp a.property
  rw [Algebra.adjoin_range_eq_range_aeval] at hr hs
  obtain ⟨r,rfl⟩ := hr
  obtain ⟨s,rfl⟩ := hs
  change (a : ℝ) = MvPolynomial.aeval u r / MvPolynomial.aeval u s at h
  have hsne : MvPolynomial.aeval u s ≠ 0 := by
    intro hz
    rw [hz,div_zero] at h
    exact ha (Subtype.ext h)
  refine ⟨r,s,?_,?_⟩
  · intro hz
    exact hsne (by rw [hz,map_zero])
  · apply Subtype.ext
    change (a : ℝ) * ((parameterMap u s : ParameterField u) : ℝ) =
      ((parameterMap u r : ParameterField u) : ℝ)
    rw [coe_parameterMap,coe_parameterMap,h]
    exact div_mul_cancel₀ _ hsne

theorem cleared_minpoly {ι : Type*} {u : ι → ℝ}
    (hu : AlgebraicIndependent ℚ u) {θ : ℝ}
    (hθ : IsAlgebraic (ParameterField u) θ) :
    ∃ F : AlgebraicSpecialization.ParameterPolynomial ι, ∃ d : MvPolynomial ι ℚ,
      d ≠ 0 ∧
      F.map (parameterMap u).toRingHom =
        C (parameterMap u d) * minpoly (ParameterField u) θ ∧
      AlgebraicSpecialization.evaluate F u θ = 0 ∧
      AlgebraicSpecialization.evaluate F.derivative u θ ≠ 0 := by
  obtain ⟨F,d,hd,hF⟩ := clear_polynomial (parameterMap u).toRingHom
    (parameterMap_fraction u) (minpoly (ParameterField u) θ)
  have hev (p : AlgebraicSpecialization.ParameterPolynomial ι) :
      Polynomial.aeval θ (p.map (parameterMap u).toRingHom) =
        AlgebraicSpecialization.evaluate p u θ := by
    have hcomp : (algebraMap (ParameterField u) ℝ).comp (parameterMap u).toRingHom =
        MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) u :=
      RingHom.ext (fun p => coe_parameterMap u p)
    simp only [Polynomial.aeval_def,Polynomial.eval₂_map,AlgebraicSpecialization.evaluate,hcomp]
  have hdn : ((parameterMap u d : ParameterField u) : ℝ) ≠ 0 := by
    intro h
    apply hd
    apply parameterMap_injective hu
    apply Subtype.ext
    simpa only [map_zero,ZeroMemClass.coe_zero] using h
  refine ⟨F,d,hd,hF,?_,?_⟩
  · rw [← hev,hF,map_mul,minpoly.aeval (ParameterField u) θ,mul_zero]
  · have hs : (minpoly (ParameterField u) θ).Separable :=
      (minpoly.irreducible hθ.isIntegral).separable
    have hm := hs.aeval_derivative_ne_zero (minpoly.aeval (ParameterField u) θ)
    have hder := congrArg Polynomial.derivative hF
    rw [Polynomial.derivative_map,Polynomial.derivative_C_mul] at hder
    rw [← hev,hder,map_mul,Polynomial.aeval_C]
    exact mul_ne_zero hdn hm

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField AlgebraicSpecialization

lemma evaluate_as_map {ι : Type*} (u : ι → ℝ) (p : ParameterPolynomial ι) (θ : ℝ) :
    Polynomial.aeval θ (p.map (parameterMap u).toRingHom) = evaluate p u θ := by
  have hcomp : (algebraMap (ParameterField u) ℝ).comp (parameterMap u).toRingHom =
      MvPolynomial.eval₂Hom (algebraMap ℚ ℝ) u :=
    RingHom.ext (fun p => coe_parameterMap u p)
  simp only [Polynomial.aeval_def,Polynomial.eval₂_map,evaluate,hcomp]

theorem coordinate_polynomials {ι κ : Type*} {u : ι → ℝ}
    (hu : AlgebraicIndependent ℚ u) (θ : ℝ) (x : κ → ℝ)
    (hx : ∀ i, ∃ p q : Polynomial (ParameterField u),
      Polynomial.aeval θ q ≠ 0 ∧ x i = Polynomial.aeval θ p / Polynomial.aeval θ q) :
    ∃ N D : κ → ParameterPolynomial ι,
      (∀ i, evaluate (D i) u θ ≠ 0) ∧ ∀ i, chartValue N D (u,θ) i = x i := by
  classical
  have hi (i : κ) : ∃ N D : ParameterPolynomial ι,
      evaluate D u θ ≠ 0 ∧ evaluate N u θ / evaluate D u θ = x i := by
    obtain ⟨p,q,hq,hx⟩ := hx i
    obtain ⟨P,d,hd,hP⟩ := clear_polynomial (parameterMap u).toRingHom
      (parameterMap_fraction u) p
    obtain ⟨Q,e,he,hQ⟩ := clear_polynomial (parameterMap u).toRingHom
      (parameterMap_fraction u) q
    have hn (a : MvPolynomial ι ℚ) (ha : a ≠ 0) :
        ((parameterMap u a : ParameterField u) : ℝ) ≠ 0 := by
      intro hz
      apply ha
      apply parameterMap_injective hu
      apply Subtype.ext
      simpa using hz
    have hPd : evaluate P u θ = ((parameterMap u d : ParameterField u) : ℝ) *
        Polynomial.aeval θ p := by
      rw [← evaluate_as_map,hP,map_mul,Polynomial.aeval_C]
      rfl
    have hQe : evaluate Q u θ = ((parameterMap u e : ParameterField u) : ℝ) *
        Polynomial.aeval θ q := by
      rw [← evaluate_as_map,hQ,map_mul,Polynomial.aeval_C]
      rfl
    have hC (a : MvPolynomial ι ℚ) : evaluate (C a) u θ =
        ((parameterMap u a : ParameterField u) : ℝ) := by
      rw [coe_parameterMap]
      simp only [evaluate,Polynomial.eval₂_C]
      rfl
    have hmul (a b : ParameterPolynomial ι) : evaluate (a*b) u θ =
        evaluate a u θ * evaluate b u θ := Polynomial.eval₂_mul _ _
    refine ⟨C e*P,C d*Q,?_,?_⟩
    · rw [hmul]
      rw [hC,hQe]
      exact mul_ne_zero (hn d hd) (mul_ne_zero (hn e he) hq)
    · rw [hmul,hmul,hC,hC,hPd,hQe,hx]
      have hdR := hn d hd
      have heR := hn e he
      rw [mul_left_comm ((parameterMap u d : ParameterField u) : ℝ)
        ((parameterMap u e : ParameterField u) : ℝ),← mul_assoc,← mul_assoc]
      exact mul_div_mul_left _ _ (mul_ne_zero heR hdR)
  choose N D hD hv using hi
  exact ⟨N,D,hD,hv⟩

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Set Polynomial IntermediateField AlgebraicSpecialization

lemma cleared_unit_equation {K : Type*} [Field K]
    (a b c d e f g h : K) (hb : b ≠ 0) (hd : d ≠ 0) (hf : f ≠ 0) (hh : h ≠ 0) :
    (a*d-c*b)^2*(f*h)^2 + (e*h-g*f)^2*(b*d)^2 - (b*d)^2*(f*h)^2 = 0 ↔
      (a/b-c/d)^2+(e/f-g/h)^2 = 1 := by
  have hid : (a*d-c*b)^2*(f*h)^2 + (e*h-g*f)^2*(b*d)^2 - (b*d)^2*(f*h)^2 =
      ((a/b-c/d)^2+(e/f-g/h)^2-1)*((b*d)^2*(f*h)^2) := by
    field_simp
  rw [hid,mul_eq_zero]
  have hprod : (b*d)^2*(f*h)^2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (mul_ne_zero hb hd)) (pow_ne_zero _ (mul_ne_zero hf hh))
  simp only [hprod,or_false,sub_eq_zero]

noncomputable def unitRelation {ι κ : Type*}
    (N D : κ × Fin 2 → ParameterPolynomial ι) (i j : κ) : ParameterPolynomial ι :=
  (N (i,0)*D (j,0)-N (j,0)*D (i,0))^2 * (D (i,1)*D (j,1))^2 +
    (N (i,1)*D (j,1)-N (j,1)*D (i,1))^2 * (D (i,0)*D (j,0))^2 -
    (D (i,0)*D (j,0))^2 * (D (i,1)*D (j,1))^2

def unitEquation {κ : Type*} (x : κ × Fin 2 → ℝ) (i j : κ) : Prop :=
  (x (i,0)-x (j,0))^2+(x (i,1)-x (j,1))^2 = 1

lemma evaluate_unitRelation {ι κ : Type*} (N D : κ × Fin 2 → ParameterPolynomial ι)
    (u : ι → ℝ) (θ : ℝ) (hD : ∀ k, evaluate (D k) u θ ≠ 0) (i j : κ) :
    evaluate (unitRelation N D i j) u θ = 0 ↔ unitEquation (chartValue N D (u,θ)) i j := by
  simp only [unitRelation,evaluate,eval₂_sub,eval₂_add,eval₂_mul,eval₂_pow,
    unitEquation,chartValue]
  exact cleared_unit_equation _ _ _ _ _ _ _ _ (hD (i,0)) (hD (j,0)) (hD (i,1)) (hD (j,1))

theorem algebraic_unit_approximation {κ : Type*} [Finite κ]
    (x : κ × Fin 2 → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ y : κ × Fin 2 → ℝ, (∀ k, IsAlgebraic ℚ (y k) ∧ |y k-x k| < ε) ∧
      ∀ i j, unitEquation x i j → unitEquation y i j := by
  classical
  obtain ⟨s,hs⟩ := exists_isTranscendenceBasis ℚ ℝ
  let u : s → ℝ := Subtype.val
  have hu : AlgebraicIndependent ℚ u := hs.1
  have : Algebra.IsAlgebraic (ParameterField u) ℝ := hs.isAlgebraic_field
  obtain ⟨θ,hθ,hx⟩ := finite_coordinates_primitive x
    (fun k => Algebra.IsAlgebraic.isAlgebraic (x k) : ∀ k, IsAlgebraic (ParameterField u) (x k))
  obtain ⟨F,d,hd,hF,hz,hder⟩ := cleared_minpoly hu hθ
  obtain ⟨N,D,hD,hval⟩ := coordinate_polynomials hu θ x hx
  let η := {e : κ × κ // unitEquation x e.1 e.2}
  let G : η → ParameterPolynomial s := fun e => unitRelation N D e.val.1 e.val.2
  have hG (e : η) : Polynomial.aeval θ ((G e).map (parameterMap u).toRingHom) = 0 := by
    rw [evaluate_as_map]
    apply (evaluate_unitRelation N D u θ hD _ _).mpr
    simpa only [unitEquation,hval] using e.property
  have hId (e : η) : ∃ b : MvPolynomial s ℚ, ∃ J : ParameterPolynomial s,
      b ≠ 0 ∧ C b*G e = F*J :=
    clear_relation (parameterMap u).toRingHom (parameterMap_injective hu)
      (parameterMap_fraction u) θ F d hd hF (G e) (hG e)
  choose b J hb hId using hId
  have hbval (e : η) : MvPolynomial.eval₂ (algebraMap ℚ ℝ) u (b e) ≠ 0 := by
    intro he
    exact hb e ((algebraicIndependent_iff_injective_aeval.mp hu)
      (show MvPolynomial.aeval u (b e) = MvPolynomial.aeval u 0 by
        simpa only [map_zero,MvPolynomial.aeval_def] using he))
  obtain ⟨v,τ,_,_,hcoord,hunit⟩ := specialize_chart F N D G J b hz hder hD hbval hId hε
  refine ⟨chartValue N D ((fun i => (v i : ℝ)),τ),?_,?_⟩
  · intro k
    exact ⟨(hcoord k).2.1,by simpa only [hval] using (hcoord k).2.2⟩
  · intro i j hij
    exact (evaluate_unitRelation N D _ τ (fun k => (hcoord k).1) i j).mp
      (hunit ⟨(i,j),hij⟩)

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances.PrimitiveChart
open Set Filter
open scoped Topology

lemma plane_dist_sq (p q : EuclideanSpace ℝ (Fin 2)) :
    dist p q ^ 2 = (p 0-q 0)^2+(p 1-q 1)^2 := by
  rw [dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  simp only [WithLp.ofLp_sub,Pi.sub_apply,Real.norm_eq_abs,sq_abs]

lemma plane_unit_iff {κ : Type*} (p : κ → EuclideanSpace ℝ (Fin 2)) (i j : κ) :
    dist (p i) (p j) = 1 ↔ unitEquation (fun k => p k.1 k.2) i j := by
  have he := plane_dist_sq (p i) (p j)
  have hn := dist_nonneg (x := p i) (y := p j)
  unfold unitEquation
  simp only
  constructor <;> intro h <;> nlinarith

lemma plane_close_of_coordinates {δ : ℝ} (hδ : 0 < δ)
    (p q : EuclideanSpace ℝ (Fin 2)) (h : ∀ k, |p k-q k| < δ) :
    dist p q < 2*δ := by
  have h0 := (sq_lt_sq₀ (abs_nonneg (p 0-q 0)) hδ.le).mpr (h 0)
  have h1 := (sq_lt_sq₀ (abs_nonneg (p 1-q 1)) hδ.le).mpr (h 1)
  rw [sq_abs] at h0 h1
  have he := plane_dist_sq p q
  nlinarith [dist_nonneg (x := p) (y := q)]

lemma finite_separation {κ : Type*} [Finite κ] {M : Type*} [MetricSpace M]
    (p : κ → M) (hp : Function.Injective p) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ i j, i ≠ j → ρ < dist (p i) (p j) := by
  have he : ∀ᶠ ρ : ℝ in 𝓝 0, ∀ i j, i ≠ j → ρ < dist (p i) (p j) := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall (by simp [hij])
    · have hd : (0 : ℝ) < dist (p i) (p j) := dist_pos.mpr (hp.ne hij)
      have hlt : Iio (dist (p i) (p j)) ∈ 𝓝 (0 : ℝ) := isOpen_Iio.mem_nhds hd
      exact Filter.mem_of_superset hlt (fun _ h _ => h)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨r/2,by positivity,hball ?_⟩
  rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (by positivity : 0 < r/2)]
  linarith

theorem algebraic_planar_specialization {κ : Type*} [Finite κ]
    (p : κ → EuclideanSpace ℝ (Fin 2)) (hp : Function.Injective p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q : κ → EuclideanSpace ℝ (Fin 2), Function.Injective q ∧
      (∀ i, dist (q i) (p i) < ε ∧ ∀ k, IsAlgebraic ℚ (q i k)) ∧
      ∀ i j, dist (p i) (p j) = 1 → dist (q i) (q j) = 1 := by
  classical
  obtain ⟨ρ,hρ,hsep⟩ := finite_separation p hp
  let δ := min (ε/3) (ρ/6)
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  obtain ⟨y,hy,heq⟩ := algebraic_unit_approximation (fun k => p k.1 k.2) hδ
  let q : κ → EuclideanSpace ℝ (Fin 2) := fun i => WithLp.toLp 2 (fun k => y (i,k))
  have hclose (i : κ) : dist (q i) (p i) < 2*δ :=
    plane_close_of_coordinates hδ _ _ (fun k => (hy (i,k)).2)
  have hερ : 2*δ < ε := by have := min_le_left (ε/3) (ρ/6); dsimp [δ]; linarith
  have hρδ : 4*δ < ρ := by have := min_le_right (ε/3) (ρ/6); dsimp [δ]; linarith
  refine ⟨q,?_,?_,?_⟩
  · intro i j hij
    by_contra hne
    have hdist := dist_triangle (p i) (q i) (p j)
    rw [dist_comm (p i) (q i)] at hdist
    have hi := hclose i
    have hj := hclose j
    have hs := hsep i j hne
    rw [← hij] at hj
    linarith
  · intro i
    exact ⟨(hclose i).trans hερ,fun k => (hy (i,k)).1⟩
  · intro i j h
    exact (plane_unit_iff q i j).mpr (heq i j ((plane_unit_iff p i j).mp h))

end PlanarUnitDistances.PrimitiveChart

namespace PlanarUnitDistances

theorem unitPairCount_map_mono {α : Type*} (s : Finset α)
    (e f : α ↪ Plane) (hunit : ∀ i j, dist (e i) (e j) = 1 → dist (f i) (f j) = 1) :
    unitPairCount (s.map e) ≤ unitPairCount (s.map f) := by
  classical
  simp only [unitPairCount,Finset.sym2_map,Finset.filter_map,Finset.card_map]
  apply Finset.card_le_card
  intro a ha
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ha).1,?_⟩
  have h := (Finset.mem_filter.mp ha).2
  induction a using Sym2.ind with
  | _ i j => exact hunit i j h

theorem algebraic_set_specialization (X : Finset Plane) :
    ∃ Y : Finset Plane, Y.card = X.card ∧ unitPairCount X ≤ unitPairCount Y ∧
      ∀ p ∈ Y, ∀ k, IsAlgebraic ℚ (p k) := by
  classical
  obtain ⟨q,hq,ha,hu⟩ := PrimitiveChart.algebraic_planar_specialization
    (fun p : X => (p : Plane)) Subtype.val_injective (show (0 : ℝ) < 1 by norm_num)
  let e : X ↪ Plane := ⟨q,hq⟩
  let v : X ↪ Plane := ⟨Subtype.val,Subtype.val_injective⟩
  have hv : (Finset.univ : Finset X).map v = X := by
    ext p
    simp [v]
  refine ⟨Finset.univ.map e,?_,?_,?_⟩
  · simp
  · have hm := unitPairCount_map_mono Finset.univ v e hu
    rw [hv] at hm
    exact hm
  · intro p hp
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hp
    exact (ha i).2

theorem mainClaim_iff_algebraic : MainClaim ↔
    ∃ C β : ℝ, 0 < C ∧ 1 ≤ β ∧ β < (4 : ℝ) / 3 ∧
      ∀ X : Finset Plane, (∀ p ∈ X, ∀ k, IsAlgebraic ℚ (p k)) →
        (unitPairCount X : ℝ) ≤ C * (X.card : ℝ)^β := by
  rw [mainClaim_iff_uniform]
  constructor
  · rintro ⟨C,β,hC,hβ,hβ',h⟩
    exact ⟨C,β,hC,hβ,hβ',fun X _ => h X⟩
  · rintro ⟨C,β,hC,hβ,hβ',h⟩
    refine ⟨C,β,hC,hβ,hβ',fun X => ?_⟩
    obtain ⟨Y,hcard,hcount,halg⟩ := algebraic_set_specialization X
    have hb := h Y halg
    rw [hcard] at hb
    exact (Nat.cast_le.mpr hcount).trans hb

theorem algebraic_counterexample_sequence (hmain : ¬ MainClaim) :
    ∃ X : ℕ → Finset Plane, ∀ j : ℕ, j ≤ (X j).card ∧
      ((X j).card : ℝ)^((4 : ℝ)/3-1/(j+3 : ℝ)) < (unitPairCount (X j) : ℝ) ∧
      ∀ p ∈ X j, ∀ k, IsAlgebraic ℚ (p k) := by
  classical
  obtain ⟨X,hX⟩ := counterexample_sequence hmain
  choose Y hcard hcount halg using fun j => algebraic_set_specialization (X j)
  refine ⟨Y,fun j => ?_⟩
  rw [hcard]
  exact ⟨(hX j).1,(hX j).2.trans_le (Nat.cast_le.mpr (hcount j)),halg j⟩

end PlanarUnitDistances

end OAI
