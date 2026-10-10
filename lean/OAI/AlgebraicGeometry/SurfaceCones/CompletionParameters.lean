import OAI.AlgebraicGeometry.SurfaceCones.GradedCompletion
import OAI.AlgebraicGeometry.SurfaceCones.KummerCompletedBlowup

namespace OAI

noncomputable section

attribute [local instance] ExplicitCone.actualCompletion_noetherian
/-! Degree-one Noether normalization needed for the actual section cone.
The generators and all replacements are homogeneous of degree one. -/
noncomputable section
open scoped BigOperators
namespace HomogeneousNoetherNormalization
variable {k L : Type} [Field k] [Field L] [Algebra k L]
open MvPolynomial

lemma cone_monomial {σ : Type} (v : σ → L) (e : σ →₀ ℕ) (c : k) :
    MvPolynomial.aeval (fun i => Polynomial.monomial 1 (v i)) (MvPolynomial.monomial e c) =
      Polynomial.monomial e.degree ((algebraMap k L c) * e.prod (fun i j => v i ^ j)) := by
  classical
  rw [MvPolynomial.aeval_monomial]
  have hp : e.prod (fun i j => (Polynomial.monomial 1 (v i) : Polynomial L) ^ j) =
      Polynomial.monomial e.degree (e.prod (fun i j => v i ^ j)) := by
    simp only [← Polynomial.C_mul_X_pow_eq_monomial, pow_one, mul_pow, ← map_pow,
      Finsupp.prod, Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum,
      Finsupp.degree_apply, ← Polynomial.C_mul_X_pow_eq_monomial]
  rw [hp, Polynomial.algebraMap_apply, Polynomial.C_mul_monomial]

lemma coeff_cone_aeval {σ : Type} (v : σ → L) (f : MvPolynomial σ k) (d : ℕ) :
    (MvPolynomial.aeval (fun i => Polynomial.monomial 1 (v i)) f).coeff d =
      MvPolynomial.aeval v (homogeneousComponent d f) := by
  classical
  nth_rw 1 [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff, homogeneousComponent_apply,
    map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  rw [cone_monomial, Polynomial.coeff_monomial, MvPolynomial.aeval_monomial]

lemma homogeneous_relation {σ : Type} (v : σ → L)
    (h : ¬ Function.Injective (MvPolynomial.aeval (fun i => Polynomial.monomial 1 (v i)) :
      MvPolynomial σ k →ₐ[k] Polynomial L)) :
    ∃ (d : ℕ) (f : MvPolynomial σ k), f ≠ 0 ∧ f.IsHomogeneous d ∧
      MvPolynomial.aeval v f = 0 ∧ d > 0 := by
  classical
  have hex0 : ∃ g : MvPolynomial σ k,
      MvPolynomial.aeval (fun i => Polynomial.monomial 1 (v i)) g = 0 ∧ g ≠ 0 := by
    rw [Function.Injective] at h
    push Not at h
    obtain ⟨a, b, hab, hne⟩ := h
    refine ⟨a - b, ?_, sub_ne_zero.mpr hne⟩
    simpa [map_sub] using sub_eq_zero.mpr hab
  obtain ⟨g, hg, hgne⟩ := hex0
  have hc : ∀ d, MvPolynomial.aeval v (homogeneousComponent d g) = 0 := by
    intro d
    rw [← coeff_cone_aeval, hg]
    simp
  have hex : ∃ d, homogeneousComponent d g ≠ 0 := by
    by_contra! hz
    have hh := sum_homogeneousComponent g
    simp only [hz, Finset.sum_const_zero] at hh
    exact hgne hh.symm
  obtain ⟨d, hd⟩ := hex
  refine ⟨d, homogeneousComponent d g, hd, homogeneousComponent_isHomogeneous _ _, hc d, ?_⟩
  by_contra hn
  have hd0 : d = 0 := by omega
  subst d
  simp only [homogeneousComponent_zero] at hd
  have hh := hc 0
  simp only [homogeneousComponent_zero, MvPolynomial.aeval_C] at hh
  have hz : g.coeff 0 = 0 := (algebraMap k L).injective (by simpa using hh)
  exact hd (by simp [hz])

lemma eval_scalar {σ : Type} {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (a : σ → k) (s : k) :
    MvPolynomial.eval (fun i => s * a i) f = s ^ d * MvPolynomial.eval a f := by
  classical
  rw [f.as_sum, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hdeg := hf.degree_eq_sum_deg_support he
  simp only [MvPolynomial.eval_monomial, mul_pow, Finsupp.prod, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  rw [← hdeg]
  ring

lemma exists_projective_nonvanishing {n d : ℕ} {f : MvPolynomial (Fin (n+1)) k}
    [Infinite k] (hf : f.IsHomogeneous d) (hne : f ≠ 0) :
    ∃ c : Fin n → k, MvPolynomial.eval (Fin.cases 1 c) f ≠ 0 := by
  classical
  have hp : f * MvPolynomial.X (0 : Fin (n+1)) ≠ 0 := mul_ne_zero hne (X_ne_zero _)
  have hh := hf.mul (isHomogeneous_X k (0 : Fin (n+1)))
  have hex : ∃ a : Fin (n+1) → k, MvPolynomial.eval a (f * MvPolynomial.X 0) ≠ 0 := by
    by_contra! hz
    exact hp (hh.eq_zero_of_forall_eval_eq_zero hz)
  obtain ⟨a, ha⟩ := hex
  simp only [map_mul, MvPolynomial.eval_X, mul_ne_zero_iff] at ha
  refine ⟨fun i => (a 0)⁻¹ * a i.succ, ?_⟩
  have he : (fun i => (a 0)⁻¹ * a i) = Fin.cases 1 (fun i => (a 0)⁻¹ * a i.succ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [ha.2]
    · rfl
  rw [← he, eval_scalar hf]
  exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero ha.2)) ha.1

section AffineEvaluation
variable {S σ ι : Type} [CommRing S] [Algebra k S]

lemma coeff_prod_sum (s : Finset ι) (p : ι → Polynomial S) (d : ι → ℕ)
    (h : ∀ i ∈ s, (p i).natDegree ≤ d i) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (p i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le (h i (Finset.mem_insert_self _ _))
        ((Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun j hj =>
          h j (Finset.mem_insert_of_mem hj)))), ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

lemma affine_degree (a b : σ → S) (i : σ) :
    (Polynomial.C (b i) + Polynomial.C (a i) * Polynomial.X).natDegree ≤ 1 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · exact (Polynomial.natDegree_C_mul_le _ _).trans Polynomial.natDegree_X_le

lemma affine_aeval_degree {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (a b : σ → S) :
    (MvPolynomial.aeval (fun i => Polynomial.C (b i) + Polynomial.C (a i) * Polynomial.X) f).natDegree ≤ d := by
  classical
  rw [f.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  rw [MvPolynomial.aeval_monomial, Polynomial.algebraMap_apply]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  change (∏ i ∈ e.support,
    (Polynomial.C (b i) + Polynomial.C (a i) * Polynomial.X) ^ e i).natDegree ≤ d
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ i ∈ e.support, e i := Finset.sum_le_sum fun i _ =>
      (Polynomial.natDegree_pow_le).trans (by simpa using Nat.mul_le_mul_left (e i) (affine_degree a b i))
    _ = d := (hf.degree_eq_sum_deg_support he).symm

lemma affine_aeval_top_coeff {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (a b : σ → S) :
    (MvPolynomial.aeval (fun i => Polynomial.C (b i) + Polynomial.C (a i) * Polynomial.X) f).coeff d =
      MvPolynomial.aeval a f := by
  classical
  rw [f.as_sum, map_sum, map_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro e he
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, Polynomial.algebraMap_apply, Polynomial.coeff_C_mul]
  congr 1
  rw [hf.degree_eq_sum_deg_support he]
  change (∏ i ∈ e.support,
    (Polynomial.C (b i) + Polynomial.C (a i) * Polynomial.X) ^ e i).coeff
    (∑ i ∈ e.support, e i) = ∏ i ∈ e.support, a i ^ e i
  rw [coeff_prod_sum _ _ e (fun i _ => Polynomial.natDegree_pow_le.trans
    (by simpa using Nat.mul_le_mul_left (e i) (affine_degree a b i)))]
  apply Finset.prod_congr rfl
  intro i _
  have hh := Polynomial.coeff_pow_of_natDegree_le (m := e i) (affine_degree a b i)
  simpa using hh

end AffineEvaluation

section LinearChange
variable {A : Type} [CommRing A] [Algebra k A]

lemma integral_head_of_relation {n d : ℕ} {f : MvPolynomial (Fin (n+1)) k}
    (hf : f.IsHomogeneous d) (x : Fin (n+1) → A) (hx : MvPolynomial.aeval x f = 0)
    (c : Fin n → k) (hc : MvPolynomial.eval (Fin.cases 1 c) f ≠ 0) :
    IsIntegral (Algebra.adjoin k (Set.range (fun i => x i.succ - algebraMap k A (c i) * x 0)))
      (x 0) := by
  classical
  let B := Algebra.adjoin k (Set.range (fun i => x i.succ - algebraMap k A (c i) * x 0))
  let b : Fin n → B := fun i => ⟨_, Algebra.subset_adjoin ⟨i, rfl⟩⟩
  let a : Fin (n+1) → B := Fin.cases 1 (fun i => algebraMap k B (c i))
  let b' : Fin (n+1) → B := Fin.cases 0 b
  let v : Fin (n+1) → Polynomial B := fun i =>
    Polynomial.C (b' i) + Polynomial.C (a i) * Polynomial.X
  let q : Polynomial B := MvPolynomial.aeval v f
  let t : k := MvPolynomial.eval (Fin.cases 1 c) f
  have hdeg : q.natDegree ≤ d := affine_aeval_degree hf a b'
  have htop : q.coeff d = algebraMap k B t := by
    rw [affine_aeval_top_coeff hf]
    have hh : (MvPolynomial.aeval a : MvPolynomial (Fin (n+1)) k →ₐ[k] B) =
        (Algebra.ofId k B).comp (MvPolynomial.aeval (Fin.cases 1 c)) := by
      ext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [a]
    rw [hh]
    simp [t]
  let ev : Polynomial B →ₐ[k] A := (Polynomial.aeval (x 0)).restrictScalars k
  have hev : (fun i => ev (v i)) = x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [ev, v, a, b']
    · simp [ev, v, a, b', b, B, sub_add_cancel]
  have hroot : Polynomial.aeval (x 0) q = 0 := by
    change ev (MvPolynomial.aeval v f) = 0
    rw [comp_aeval_apply, hev]
    exact hx
  refine ⟨Polynomial.C (algebraMap k B t⁻¹) * q, ?_, ?_⟩
  · apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one d
    · exact (Polynomial.natDegree_C_mul_le _ _).trans hdeg
    · rw [Polynomial.coeff_C_mul, htop, ← map_mul, inv_mul_cancel₀ hc, map_one]
  · change (Polynomial.aeval (x 0)) (Polynomial.C (algebraMap k B t⁻¹) * q) = 0
    rw [map_mul, hroot, mul_zero]

end LinearChange

lemma cone_aeval_homogeneous {σ : Type} {f : MvPolynomial σ k} {d : ℕ}
    (hf : f.IsHomogeneous d) (v : σ → L) :
    MvPolynomial.aeval (fun i => Polynomial.monomial 1 (v i)) f = Polynomial.monomial d (MvPolynomial.aeval v f) := by
  apply Polynomial.ext
  intro j
  rw [coeff_cone_aeval, homogeneousComponent_of_mem hf, Polynomial.coeff_monomial]
  by_cases h : j = d
  · subst j
    simp only [ite_true]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), map_zero]

def cone {σ : Type} (v : σ → L) : Subalgebra k (Polynomial L) :=
  Algebra.adjoin k (Set.range (fun i => Polynomial.monomial 1 (v i)))

lemma cone_gen_mem {σ : Type} (v : σ → L) (i : σ) : Polynomial.monomial 1 (v i) ∈ cone (k := k) v :=
  Algebra.subset_adjoin ⟨i, rfl⟩

lemma cone_shift_le {n : ℕ} (v : Fin (n+1) → L) (c : Fin n → k) :
    cone (fun i => v i.succ - algebraMap k L (c i) * v 0) ≤ cone (k := k) v := by
  apply Algebra.adjoin_le
  rintro _ ⟨i, rfl⟩
  change Polynomial.monomial 1 (v i.succ - algebraMap k L (c i) * v 0) ∈ cone v
  rw [map_sub, ← Polynomial.C_mul_monomial, ← Polynomial.algebraMap_apply]
  exact (cone (k := k) v).sub_mem (cone_gen_mem v i.succ)
    ((cone (k := k) v).mul_mem ((cone (k := k) v).algebraMap_mem (c i)) (cone_gen_mem v 0))

lemma cone_shift_integral {n d : ℕ} (v : Fin (n+1) → L)
    {f : MvPolynomial (Fin (n+1)) k} (hf : f.IsHomogeneous d) (hv : MvPolynomial.aeval v f = 0)
    (c : Fin n → k) (hc : MvPolynomial.eval (Fin.cases 1 c) f ≠ 0) :
    (Subalgebra.inclusion (cone_shift_le v c)).IsIntegral := by
  classical
  let x : Fin (n+1) → Polynomial L := fun i => Polynomial.monomial 1 (v i)
  let w : Fin n → L := fun i => v i.succ - algebraMap k L (c i) * v 0
  let B := cone (k := k) w
  have hh : (Algebra.adjoin k (Set.range (fun i => x i.succ - algebraMap k (Polynomial L) (c i) * x 0))) = B := by
    congr 2
    funext i
    simp only [x, w, map_sub, Polynomial.algebraMap_apply, Polynomial.C_mul_monomial]
  have hhead : IsIntegral B (x 0) := by
    rw [← hh]
    exact integral_head_of_relation hf x (by rw [cone_aeval_homogeneous hf, hv]; simp) c hc
  have hgen (i : Fin (n+1)) : IsIntegral B (x i) := by
    refine Fin.cases hhead (fun j => ?_) i
    have hw : IsIntegral B (Polynomial.monomial 1 (w j)) :=
      isIntegral_algebraMap (x := (⟨_, cone_gen_mem w j⟩ : B))
    have hc' : IsIntegral B (algebraMap k (Polynomial L) (c j)) :=
      isIntegral_algebraMap (x := algebraMap k B (c j))
    have he : Polynomial.monomial 1 (w j) + algebraMap k (Polynomial L) (c j) * x 0 = x j.succ := by
      simp only [w, x, map_sub, Polynomial.algebraMap_apply, Polynomial.C_mul_monomial, sub_add_cancel]
    rw [← he]
    exact hw.add (hc'.mul hhead)
  have hle : cone (k := k) v ≤ (integralClosure B (Polynomial L)).restrictScalars k :=
    Algebra.adjoin_le (by rintro _ ⟨i, rfl⟩; exact hgen i)
  intro z
  exact RingHom.IsIntegralElem.of_map (g := (cone (k := k) v).val.toRingHom)
    Subtype.val_injective (hle z.property)

/-- Linear changes only: unlike ordinary normalization, the parameters stay
in degree one. The integral map is the literal inclusion into the input cone. -/
theorem exists_linear_normalization [Infinite k] {n : ℕ} (v : Fin n → L) :
    ∃ m ≤ n, ∃ w : Fin m → L, ∃ h : cone (k := k) w ≤ cone v,
      Function.Injective (MvPolynomial.aeval (fun i => Polynomial.monomial 1 (w i)) :
        MvPolynomial (Fin m) k →ₐ[k] Polynomial L) ∧
      (Subalgebra.inclusion h).IsIntegral := by
  induction n with
  | zero =>
    refine ⟨0, le_rfl, v, le_rfl, ?_, ?_⟩
    · intro a b hab
      rw [eq_C_of_isEmpty a, eq_C_of_isEmpty b] at hab ⊢
      exact congrArg MvPolynomial.C ((algebraMap k (Polynomial L)).injective (by simpa using hab))
    · exact RingHom.isIntegral_of_surjective _ (fun z => ⟨z, rfl⟩)
  | succ n ih =>
    by_cases hinj : Function.Injective (MvPolynomial.aeval (fun i => Polynomial.monomial 1 (v i)) :
        MvPolynomial (Fin (n+1)) k →ₐ[k] Polynomial L)
    · exact ⟨n+1, le_rfl, v, le_rfl, hinj,
        RingHom.isIntegral_of_surjective _ (fun z => ⟨z, rfl⟩)⟩
    · obtain ⟨d, f, hne, hf, hv, _⟩ := homogeneous_relation v hinj
      obtain ⟨c, hc⟩ := exists_projective_nonvanishing hf hne
      obtain ⟨m, hmn, w, hw, hwinj, hwint⟩ := ih (fun i => v i.succ - algebraMap k L (c i) * v 0)
      refine ⟨m, hmn.trans (Nat.le_succ n), w, hw.trans (cone_shift_le v c), hwinj, ?_⟩
      exact hwint.trans _ _ (cone_shift_integral v hf hv c hc)

end HomogeneousNoetherNormalization

namespace HomogeneousNoetherNormalization
variable {k L : Type} [Field k] [Field L] [Algebra k L]
open MvPolynomial

def coneEval {σ : Type} (v : σ → L) : MvPolynomial σ k →ₐ[k] cone (k := k) v :=
  (MvPolynomial.aeval (fun i => Polynomial.monomial 1 (v i))).codRestrict (cone v)
    (fun f => by rw [cone, Algebra.adjoin_range_eq_range_aeval]; exact ⟨f, rfl⟩)

lemma coneEval_surjective {σ : Type} (v : σ → L) : Function.Surjective (coneEval (k := k) v) := by
  intro z
  obtain ⟨f, hf⟩ : ∃ f : MvPolynomial σ k, MvPolynomial.aeval (fun i => Polynomial.monomial 1 (v i)) f = z.val := by
    have hz := z.property
    change z.val ∈ Algebra.adjoin k (Set.range (fun i => Polynomial.monomial 1 (v i))) at hz
    rwa [Algebra.adjoin_range_eq_range_aeval] at hz
  exact ⟨f, Subtype.ext hf⟩

instance finiteType_cone {σ : Type} [Finite σ] (v : σ → L) : Algebra.FiniteType k (cone (k := k) v) :=
  Algebra.FiniteType.adjoin_of_finite (Set.finite_range _)

lemma inclusion_finite {σ τ : Type} [Finite τ] {w : σ → L} {v : τ → L}
    {h : cone (k := k) w ≤ cone v} (hi : (Subalgebra.inclusion h).IsIntegral) :
    (Subalgebra.inclusion h).Finite := by
  let f := Subalgebra.inclusion h
  let : Algebra (cone (k := k) w) (cone (k := k) v) := f.toRingHom.toAlgebra
  let : IsScalarTower k (cone (k := k) w) (cone (k := k) v) :=
    IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  have : Algebra.FiniteType (cone (k := k) w) (cone (k := k) v) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  exact hi.to_finite this

/-- For a cone of transcendence degree r, exactly r parameters suffice, all
of them linear rather than arbitrary Noether-normalization polynomials. -/
theorem exists_finite_linear_normalization [Infinite k] {n r : ℕ} (v : Fin n → L)
    (hr : Algebra.trdeg k (cone (k := k) v) = r) :
    ∃ w : Fin r → L, ∃ h : cone (k := k) w ≤ cone v,
      Function.Injective (MvPolynomial.aeval (fun i => Polynomial.monomial 1 (w i)) :
        MvPolynomial (Fin r) k →ₐ[k] Polynomial L) ∧
      (Subalgebra.inclusion h).Finite := by
  obtain ⟨m, _, w, h, hinj, hint⟩ := exists_linear_normalization (k := k) v
  have hw : Function.Injective (coneEval (k := k) w) := by
    intro a b hab
    exact hinj (congrArg Subtype.val hab)
  let e : MvPolynomial (Fin m) k ≃ₐ[k] cone (k := k) w :=
    AlgEquiv.ofBijective (coneEval w) ⟨hw, coneEval_surjective w⟩
  let f := Subalgebra.inclusion h
  let : Algebra (cone (k := k) w) (cone (k := k) v) := f.toRingHom.toAlgebra
  let : IsScalarTower k (cone (k := k) w) (cone (k := k) v) :=
    IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  let : Algebra.IsIntegral (cone (k := k) w) (cone (k := k) v) := ⟨hint⟩
  let : FaithfulSMul (cone (k := k) w) (cone (k := k) v) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (Subalgebra.inclusion_injective h)
  have hm : m = r := by
    have hh := trdeg_add_eq k (cone (k := k) w) (A := cone (k := k) v)
    rw [← e.trdeg_eq, trdeg_eq_zero (R := cone (k := k) w) (A := cone (k := k) v), add_zero, hr] at hh
    simpa [MvPolynomial.trdeg_of_isDomain] using hh
  subst m
  exact ⟨w, h, hinj, inclusion_finite hint⟩

end HomogeneousNoetherNormalization

namespace ExplicitCone
open HomogeneousNoetherNormalization

lemma polynomialAlgebra_trdeg : Algebra.trdeg ℂ polynomialAlgebra = 3 := by
  rw [← SmallCM.trdeg_fractionRing ℂ polynomialAlgebra (RatFunc L)]
  exact rationalCone_trdeg

lemma exists_linear_parameters :
    ∃ w : Fin 3 → L, ∃ h : cone (k := ℂ) w ≤ polynomialAlgebra,
      Function.Injective (MvPolynomial.aeval (fun i => Polynomial.monomial 1 (w i)) :
        MvPolynomial (Fin 3) ℂ →ₐ[ℂ] Polynomial L) ∧
      (Subalgebra.inclusion h).Finite := by
  let e := Fintype.equivFin (Fin 6 × Fin 3)
  let v : Fin (Fintype.card (Fin 6 × Fin 3)) → L := fun i => sectionCoefficient (e.symm i)
  have he : cone (k := ℂ) v = polynomialAlgebra := by
    apply congrArg (Algebra.adjoin ℂ)
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, polynomialGenerator_eq_monomial _⟩
    · rintro ⟨i, rfl⟩
      refine ⟨e i, ?_⟩
      simp only [v, Equiv.symm_apply_apply, polynomialGenerator_eq_monomial]
  rw [← he]
  exact exists_finite_linear_normalization (k := ℂ) (r := 3) v
    (by rw [he]; exact polynomialAlgebra_trdeg)

end ExplicitCone
noncomputable section
namespace SmallCM

lemma precomplete_pi {A ι : Type*} [CommRing A] [Fintype ι]
    (I : Ideal A) [IsPrecomplete I A] : IsPrecomplete I (ι → A) := by
  classical
  apply AdicCompletion.of_surjective_iff.mp
  intro x
  let e := AdicCompletion.piEquivOfFintype I (fun _ : ι => A)
  choose a ha using fun i => AdicCompletion.of_surjective I A (e x i)
  refine ⟨a, e.injective ?_⟩
  funext i
  simpa [e, AdicCompletion.piEquivOfFintype_apply, AdicCompletion.pi,
    AdicCompletion.map_of] using ha i

/-- Adic Nakayama without assuming the target finitely generated. -/
lemma finite_of_adic_finite_quotient {A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (I : Ideal A)
    [IsPrecomplete I A] [IsHausdorff I M]
    [Module.Finite A (M ⧸ (I • ⊤ : Submodule A M))] : Module.Finite A M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A (M ⧸ (I • ⊤ : Submodule A M))
  have := precomplete_pi (ι := Fin n) I
  obtain ⟨g, hg⟩ := Module.projective_lifting_property
    (Submodule.mkQ (I • ⊤ : Submodule A M)) f (Submodule.mkQ_surjective _)
  exact Module.Finite.of_surjective g
    (surjective_of_mkQ_comp_surjective (I := I) (by rw [hg]; exact hf))

end SmallCM

namespace SmallCM
/-- A finite closed fiber stays finite after completion whenever the image
of the original maximal ideal generates the completed maximal ideal. -/
lemma finite_fiber_of_maximal_map {k B R : Type*} [Field k] [IsAlgClosed k]
    [CommRing B] [Algebra k B] [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [Algebra k R]
    [Module.Finite k (IsLocalRing.ResidueField R)]
    (g : B →ₐ[k] R) (I m : Ideal B) (hIm : I ≤ m)
    (hm : m.map g.toRingHom = IsLocalRing.maximalIdeal R)
    [Module.Finite k (B ⧸ I)] : Module.Finite k (R ⧸ I.map g.toRingHom) := by
  let J := I.map g.toRingHom
  have hJm : J ≤ IsLocalRing.maximalIdeal R := by
    rw [← hm]
    exact Ideal.map_mono hIm
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hJm
  let Q := R ⧸ J
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hJ
  have : IsLocalRing Q := IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  have : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective
    (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let h : B ⧸ I →ₐ[k] Q := Ideal.quotientMapₐ J g (Ideal.le_comap_map)
  have hnil : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk J) ≤ nilradical Q := by
    rw [← hm, Ideal.map_map, Ideal.map_le_iff_le_comap]
    intro b hb
    change IsNilpotent (Ideal.Quotient.mk J (g b))
    apply integral_maximal_nilpotent (k := k)
    · exact (Algebra.IsIntegral.isIntegral (Ideal.Quotient.mk I b)).map h
    · apply map_nonunit (Ideal.Quotient.mk J)
      rw [← hm]
      exact Ideal.mem_map_of_mem g hb
  let f : Q →ₐ[k] IsLocalRing.ResidueField R := Ideal.Quotient.factorₐ k hJm
  refine Module.finite_of_surjective_of_ker_le_nilradical f
    (Ideal.Quotient.factor_surjective hJm) ?_ (IsNoetherian.noetherian _)
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply hnil
  apply Ideal.mem_map_of_mem
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx
end SmallCM

namespace SmallCM
lemma finite_of_finite_mapped_fiber {k A R : Type*} [CommRing k] [CommRing A]
    [Algebra k A] [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [Algebra A R] [Algebra k R] [IsScalarTower k A R]
    (I : Ideal A) [IsPrecomplete I A]
    (hm : I.map (algebraMap A R) ≤ IsLocalRing.maximalIdeal R)
    [Module.Finite k (R ⧸ I.map (algebraMap A R))] : Module.Finite A R := by
  have : IsHausdorff (IsLocalRing.maximalIdeal R) R := IsHausdorff.of_isLocalRing
    (IsLocalRing.maximalIdeal R) R (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have : IsHausdorff I R := IsHausdorff.of_map hm
  have : Module.Finite A (R ⧸ (I • ⊤ : Submodule A R)) := by
    rw [Ideal.smul_top_eq_map]
    change Module.Finite A (R ⧸ I.map (algebraMap A R))
    exact Module.Finite.of_restrictScalars_finite k A _
  exact finite_of_adic_finite_quotient I
end SmallCM

noncomputable section
namespace SmallCM

/-- The fiber over the origin of a finite polynomial-algebra map is finite
as a vector space over the coefficient field. -/
lemma finite_polynomial_origin_fiber {k B σ : Type*} [Field k]
    [CommRing B] [Algebra k B] (f : MvPolynomial σ k →ₐ[k] B)
    (hf : f.Finite) :
    Module.Finite k (B ⧸ Ideal.span (Set.range (fun i => f (MvPolynomial.X i)))) := by
  let I : Ideal B := Ideal.span (Set.range (fun i => f (MvPolynomial.X i)))
  let S := MvPolynomial σ k
  let : Algebra S B := f.toRingHom.toAlgebra
  have : Module.Finite S B := hf
  let : Algebra S k := (MvPolynomial.constantCoeff : S →+* k).toAlgebra
  have hh : algebraMap S (B ⧸ I) = (algebraMap k (B ⧸ I)).comp
      (MvPolynomial.constantCoeff : S →+* k) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change Ideal.Quotient.mk I (f (MvPolynomial.C c)) = _
      simp
    · intro i
      change Ideal.Quotient.mk I (f (MvPolynomial.X i)) = _
      simp only [RingHom.comp_apply, MvPolynomial.constantCoeff_X, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  let : IsScalarTower S k (B ⧸ I) := IsScalarTower.of_algebraMap_eq fun a =>
    congrArg (fun g : S →+* B ⧸ I => g a) hh
  exact Module.Finite.of_restrictScalars_finite S k (B ⧸ I)

end SmallCM

namespace SectionCompletion
variable {k K : Type} [Field k] [Field K] [Algebra k K]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]

lemma completionEquiv_polynomial (D : ℕ) (hD : 0 < D)
    (hc : ∀ n, degreeIdeal T (n * D) ≤ degreeIdeal T 1 ^ n) (p : polynomials T) :
    completionEquiv T D hD hc (polynomialToSeries T p) =
      algebraMap (polynomials T) (AdicCompletion (degreeIdeal T 1) (polynomials T)) p := by
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ (degreeIdeal T 1) n
    (toCompletion T D hc (polynomialToSeries T p)) = _
  rw [eval_toCompletion, AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of]
  change Ideal.Quotient.mk _ (truncation T (n * D) (polynomialToSeries T p)) =
    Ideal.Quotient.mk _ p
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  apply hc n
  rw [mem_degreeIdeal]
  intro j hj
  change ((truncation T (n * D) (polynomialToSeries T p)).val - p.val).coeff j = 0
  simp [Polynomial.coeff_sub, coeff_truncation, hj, polynomialToSeries]

lemma maximal_polynomialToSeries [Algebra.FiniteType k (polynomials T)]
    (hzero : T 0 = LinearMap.range (Algebra.linearMap k K))
    [IsLocalRing (series T)] :
    (degreeIdeal T 1).map (polynomialToSeries T).toRingHom =
      IsLocalRing.maximalIdeal (series T) := by
  classical
  have : IsNoetherianRing (polynomials T) := Algebra.FiniteType.isNoetherianRing k _
  obtain ⟨σ, hσ, v, d, hd, hv, hgen⟩ := finite_positive_presentation T hzero
  let := hσ
  let D : ℕ := Finset.univ.sup d + 1
  have hD : 0 < D := Nat.succ_pos _
  have hc : ∀ n, degreeIdeal T (n * D) ≤ degreeIdeal T 1 ^ n :=
    degreeIdeal_cofinal T v d hd hv hgen D hD
      (fun i => (Finset.le_sup (Finset.mem_univ i)).trans (Nat.le_succ _))
  let e := completionEquiv T D hD hc
  have he : (polynomialToSeries T).toRingHom = e.symm.toRingHom.comp
      (algebraMap (polynomials T) (AdicCompletion (degreeIdeal T 1) (polynomials T))) := by
    apply RingHom.ext
    intro p
    apply e.injective
    simpa using completionEquiv_polynomial T D hD hc p
  rw [he, ← Ideal.map_map]
  have : (degreeIdeal T 1).IsMaximal := degreeIdeal_one_isMaximal T hzero
  have : ((degreeIdeal T 1).map
      (algebraMap (polynomials T) (AdicCompletion (degreeIdeal T 1) (polynomials T)))).IsMaximal :=
    AdicCompletion.isMaximal_map_of_le _ _ le_rfl (IsNoetherian.noetherian _)
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.IsMaximal.map_of_surjective_of_ker_le e.symm.surjective (by simp))
end SectionCompletion


noncomputable section
open Polynomial
namespace SectionCompletion
variable {k K σ : Type} [Field k] [IsAlgClosed k] [Field K] [Algebra k K] [Fintype σ]
variable (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]
variable (w : σ → K) (hw : ∀ i, w i ∈ T 1)

def linearPolynomialMap : MvPolynomial σ k →ₐ[k] polynomials T :=
  MvPolynomial.aeval (fun i => ⟨Polynomial.monomial 1 (w i),
    (monomial_mem_polynomials T 1 (w i)).mpr (hw i)⟩)

omit [IsAlgClosed k] in
lemma polynomial_subst_X (i : σ) :
    polynomialToSeries T (linearPolynomialMap T w hw (MvPolynomial.X i)) =
      SectionGenerated.substHom T w (fun _ => 1) (fun _ => one_ne_zero) hw (MvPowerSeries.X i) := by
  apply Subtype.ext
  change ((linearPolynomialMap T w hw (MvPolynomial.X i)).val : PowerSeries K) =
    (MvPowerSeries.substAlgHom (R := k)
      (SectionGenerated.hasSubst w (fun _ : σ => (1 : ℕ)) (fun _ => one_ne_zero)))
        (MvPowerSeries.X i)
  rw [MvPowerSeries.substAlgHom_apply]
  rw [MvPowerSeries.subst_X (SectionGenerated.hasSubst w (fun _ : σ => (1 : ℕ)) (fun _ => one_ne_zero))]
  simp [linearPolynomialMap, SectionGenerated.genSeries, Polynomial.coe_monomial,
    PowerSeries.monomial_eq_C_mul_X_pow]

/-- Completion of finite degree-one Noether normalization stays finite,
proved directly by closed-fiber finiteness and adic Nakayama. -/
lemma finite_linear_substitution [Algebra.FiniteType k (polynomials T)]
    (hzero : T 0 = LinearMap.range (Algebra.linearMap k K))
    (hfin : (linearPolynomialMap T w hw).Finite) :
    (SectionGenerated.substHom T w (fun _ => 1) (fun _ => one_ne_zero) hw).Finite := by
  let R := series T
  let A := MvPowerSeries σ k
  let f := SectionGenerated.substHom T w (fun _ => 1) (fun _ => one_ne_zero) hw
  let g := polynomialToSeries T
  let B := polynomials T
  let I : Ideal B := Ideal.span (Set.range (fun i => linearPolynomialMap T w hw (MvPolynomial.X i)))
  have : IsNoetherianRing R := isNoetherianRing_of_finiteType T hzero
  let : IsLocalRing R := isLocalRing T (zero_piece_closed_inv T hzero)
  have hIm : I ≤ degreeIdeal T 1 := by
    apply Ideal.span_le.mpr
    rintro p ⟨i, rfl⟩
    simp only [linearPolynomialMap, MvPolynomial.aeval_X]
    change (⟨Polynomial.monomial 1 (w i), _⟩ : polynomials T) ∈ degreeIdeal T 1
    exact monomial_mem_degreeIdeal_one T one_ne_zero _ (hw i)
  have : Module.Finite k (B ⧸ I) := SmallCM.finite_polynomial_origin_fiber _ hfin
  have : Module.Finite k (IsLocalRing.ResidueField R) := Module.Finite.of_surjective
    (Algebra.linearMap k _) (residue_bijective T hzero).2
  have : Module.Finite k (R ⧸ I.map g.toRingHom) :=
    SmallCM.finite_fiber_of_maximal_map g I (degreeIdeal T 1) hIm
      (maximal_polynomialToSeries T hzero)
  let : Algebra A R := f.toRingHom.toAlgebra
  let : IsScalarTower k A R := IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  have hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A R) = I.map g.toRingHom := by
    rw [← mvPowerSeries_vars_eq_maximal, Ideal.map_span, Ideal.map_span]
    congr 1
    rw [← Set.range_comp, ← Set.range_comp]
    congr 1
    funext i
    exact (polynomial_subst_X T w hw i).symm
  have : IsPrecomplete (IsLocalRing.maximalIdeal A) A := by
    rw [← mvPowerSeries_vars_eq_maximal]
    infer_instance
  change Module.Finite A R
  have : Module.Finite k (R ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A R)) := by
    rw [hmap]
    infer_instance
  apply SmallCM.finite_of_finite_mapped_fiber (k := k) (IsLocalRing.maximalIdeal A)
  rw [hmap, ← maximal_polynomialToSeries T hzero]
  exact Ideal.map_mono hIm
end SectionCompletion

namespace GradedNormalization
variable {k L σ : Type} [Field k] [IsAlgClosed k] [CharZero k] [Field L]
    [Algebra k L] [Fintype σ]
variable (B : Subalgebra k L[X]) [Algebra.FiniteType k B] [IsFractionRing B (RatFunc L)]

omit [IsAlgClosed k] in
lemma finite_normalization_map
    (hB : ∀ a : k, ∀ p ∈ B, scale a p ∈ B) :
    ∃ j : B →ₐ[k] SectionCompletion.polynomials (piece B),
      j.Finite ∧ ∀ x : B, (j x).val = x.val := by
  rw [polynomial_piece_eq B hB]
  let j : B →ₐ[k] (integralClosure B L[X]).restrictScalars k :=
    B.val.codRestrict _ (fun x => isIntegral_algebraMap (x := x))
  refine ⟨j, ?_, fun _ => rfl⟩
  have hf : RingHom.Finite (A := B) (B := integralClosure B L[X])
      (algebraMap B (integralClosure B L[X])) :=
    RingHom.finite_algebraMap.mpr (finite_polynomial_normalization B)
  exact hf

omit [IsAlgClosed k] [Fintype σ] in
lemma finite_normalized_linear_parameters
    (hB : ∀ a : k, ∀ p ∈ B, scale a p ∈ B)
    (w : σ → L) (h : HomogeneousNoetherNormalization.cone (k := k) w ≤ B)
    (hf : (Subalgebra.inclusion h).Finite) :
    ∃ hw : ∀ i, w i ∈ piece B 1,
      (SectionCompletion.linearPolynomialMap (piece B) w hw).Finite := by
  have hw : ∀ i, w i ∈ piece B 1 := by
    intro i
    have hm : Polynomial.monomial 1 (w i) ∈ B :=
      h (Algebra.subset_adjoin ⟨i, rfl⟩)
    exact isIntegral_algebraMap (x := (⟨_, hm⟩ : B))
  refine ⟨hw, ?_⟩
  obtain ⟨j, hjf, hj⟩ := finite_normalization_map B hB
  let b : MvPolynomial σ k →ₐ[k] B := (Subalgebra.inclusion h).comp
    (HomogeneousNoetherNormalization.coneEval w)
  have hb : b.Finite := hf.comp (AlgHom.Finite.of_surjective _
    (HomogeneousNoetherNormalization.coneEval_surjective w))
  have hu : (j.comp b).Finite := hjf.comp hb
  have he : j.comp b = SectionCompletion.linearPolynomialMap (piece B) w hw := by
    apply MvPolynomial.algHom_ext
    intro i
    apply Subtype.ext
    simp only [AlgHom.comp_apply, hj]
    simp [b, HomogeneousNoetherNormalization.coneEval,
      SectionCompletion.linearPolynomialMap]
  rwa [he] at hu
end GradedNormalization

namespace ExplicitCone
lemma exists_finite_linear_completed_parameters :
    ∃ (w : Fin 3 → L) (hw : ∀ i, w i ∈ pieces 1),
      Function.Injective (MvPolynomial.aeval (fun i => Polynomial.monomial 1 (w i)) :
        MvPolynomial (Fin 3) ℂ →ₐ[ℂ] Polynomial L) ∧
      (SectionGenerated.substHom pieces w (fun _ => 1) (fun _ => one_ne_zero) hw).Finite := by
  obtain ⟨w, h, hinj, hfin⟩ := exists_linear_parameters
  obtain ⟨hw, hfin'⟩ := GradedNormalization.finite_normalized_linear_parameters
    polynomialAlgebra polynomialAlgebra_scale w h hfin
  have : Algebra.FiniteType ℂ (SectionCompletion.polynomials pieces) :=
    GradedNormalization.polynomialPiece_finiteType polynomialAlgebra polynomialAlgebra_scale
  exact ⟨w, hw, hinj, SectionCompletion.finite_linear_substitution pieces w hw zero_piece hfin'⟩
end ExplicitCone

noncomputable section
open scoped BigOperators
namespace HomogeneousParameters
variable {k K σ : Type*} [Field k] [Field K] [Algebra k K]

lemma prod_monomials (v : σ → K) (d : σ → ℕ) (e : σ →₀ ℕ) :
    e.prod (fun i n => (Polynomial.monomial (d i) (v i)) ^ n) =
      Polynomial.monomial (Finsupp.weight d e) (e.prod (fun i n => v i ^ n)) := by
  classical
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, mul_pow, ← map_pow,
    Finsupp.prod, Finset.prod_mul_distrib, ← map_prod, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.mul_comm _ _

lemma linearIndependent_degree_fiber (v : σ → K)
    (hinj : Function.Injective (MvPolynomial.aeval (fun i => Polynomial.monomial 1 (v i)) :
      MvPolynomial σ k →ₐ[k] Polynomial K)) (n : ℕ) :
    LinearIndependent k (fun e : {e : σ →₀ ℕ // Finsupp.weight (fun _ => 1) e = n} =>
      e.val.prod (fun i j => v i ^ j)) := by
  let f : MvPolynomial σ k →ₐ[k] Polynomial K :=
    MvPolynomial.aeval (fun i => Polynomial.monomial 1 (v i))
  have h := (MvPolynomial.basisMonomials σ k).linearIndependent.map'
    f.toLinearMap (LinearMap.ker_eq_bot.mpr hinj)
  have h' := h.comp (fun e : {e : σ →₀ ℕ // Finsupp.weight (fun _ => 1) e = n} => e.val)
    Subtype.val_injective
  apply LinearIndependent.of_comp ((Polynomial.monomial n).restrictScalars k)
  convert h' using 1
  · funext e
    simp only [Function.comp_apply, MvPolynomial.coe_basisMonomials,
      LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply]
    change Polynomial.monomial n _ = f (MvPolynomial.monomial e.val 1)
    rw [MvPolynomial.aeval_monomial, map_one, one_mul, prod_monomials, e.property]
end HomogeneousParameters
namespace SectionGenerated
variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [Fintype σ]
variable (v : σ → K)

lemma linear_subst_eq_zero
    (hinj : Function.Injective (MvPolynomial.aeval (fun i => Polynomial.monomial 1 (v i)) :
      MvPolynomial σ k →ₐ[k] Polynomial K)) (f : MvPowerSeries σ k)
    (hf : MvPowerSeries.subst (genSeries v (fun _ => 1)) f = 0) : f = 0 := by
  classical
  apply MvPowerSeries.ext
  intro e
  let n := Finsupp.weight (fun _ : σ => (1 : ℕ)) e
  let : Fintype {d : σ →₀ ℕ // Finsupp.weight (fun _ => 1) d = n} :=
    (Finsupp.finite_of_nat_weight_eq (fun _ => 1) (fun _ => one_ne_zero) n).fintype
  have hi := HomogeneousParameters.linearIndependent_degree_fiber v hinj n
  have h := coeff_subst_fiber v (fun _ => 1) (fun _ => one_ne_zero) f n
  rw [hf, map_zero, finsum_eq_sum_of_fintype] at h
  have he := Fintype.linearIndependent_iff.mp hi (fun d => MvPowerSeries.coeff d.val f) h.symm
  simpa using he ⟨e, rfl⟩

lemma linear_subst_injective
    (hinj : Function.Injective (MvPolynomial.aeval (fun i => Polynomial.monomial 1 (v i)) :
      MvPolynomial σ k →ₐ[k] Polynomial K)) :
    Function.Injective (MvPowerSeries.substAlgHom (R := k)
      (hasSubst v (fun _ => 1) (fun _ => one_ne_zero))) := by
  intro f g hfg
  apply sub_eq_zero.mp
  apply linear_subst_eq_zero v hinj
  have h0 : (MvPowerSeries.substAlgHom (R := k)
      (hasSubst v (fun _ => 1) (fun _ => one_ne_zero))) (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  simpa only [MvPowerSeries.substAlgHom_apply] using h0

lemma substHom_injective_linear (T : ℕ → Submodule k K) [SetLike.GradedMonoid T]
    (hv : ∀ i, v i ∈ T 1)
    (hinj : Function.Injective (MvPolynomial.aeval (fun i => Polynomial.monomial 1 (v i)) :
      MvPolynomial σ k →ₐ[k] Polynomial K)) :
    Function.Injective (substHom T v (fun _ => 1) (fun _ => one_ne_zero) hv) := by
  intro f g hfg
  apply linear_subst_injective v hinj
  exact congrArg Subtype.val hfg
end SectionGenerated

namespace ExplicitCone
lemma exists_finite_injective_completed_parameters :
    ∃ f : MvPowerSeries (Fin 3) ℂ →ₐ[ℂ] completedRing,
      Function.Injective f ∧ f.Finite := by
  obtain ⟨w, hw, hinj, hfin⟩ := exists_finite_linear_completed_parameters
  exact ⟨SectionGenerated.substHom pieces w (fun _ => 1) (fun _ => one_ne_zero) hw,
    SectionGenerated.substHom_injective_linear w pieces hw hinj, hfin⟩
end ExplicitCone


end
end
end
end
end
end

end OAI
