import Mathlib

namespace OAI

namespace PermanentBorder.Multigraded
open MvPolynomial

variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

abbrev Piece (d : G) := weightedHomogeneousSubmodule K w d

abbrev componentQuotient (I : Ideal (MvPolynomial σ K)) (d : G) :=
  Piece (K := K) w d ⧸
    (I.restrictScalars K).comap (Piece (K := K) w d).subtype

def ComponentClosed (I : Ideal (MvPolynomial σ K)) : Prop :=
  ∀ p ∈ I, ∀ d, weightedHomogeneousComponent w d p ∈ I

lemma project_mul {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (g : MvPolynomial σ K) (d : G) :
    weightedHomogeneousComponent w d (a * g) =
      a * weightedHomogeneousComponent w (d-e) g := by
  classical
  ext z
  simp only [coeff_weightedHomogeneousComponent, coeff_mul]
  have hi : (if Finsupp.weight w z = d then
      ∑ xy ∈ Finset.HasAntidiagonal.antidiagonal z, a.coeff xy.1 * g.coeff xy.2 else 0) =
      ∑ xy ∈ Finset.HasAntidiagonal.antidiagonal z,
        if Finsupp.weight w z = d then a.coeff xy.1 * g.coeff xy.2 else 0 := by
    rw [Finset.sum_ite_irrel]
    simp
  rw [hi]
  apply Finset.sum_congr rfl
  rintro ⟨x,y⟩ hxy
  have hsum : x+y=z := Finset.HasAntidiagonal.mem_antidiagonal.mp hxy
  by_cases hx : a.coeff x = 0
  · simp [hx]
  · have hwe : Finsupp.weight w x = e := ha hx
    have hcond : Finsupp.weight w z = d ↔ Finsupp.weight w y = d-e := by
      rw [← hsum, map_add, hwe]
      rw [eq_sub_iff_add_eq, add_comm]
    simp only [hcond]
    split_ifs <;> simp

lemma componentClosed_sup {I J : Ideal (MvPolynomial σ K)}
    (hI : ComponentClosed w I) (hJ : ComponentClosed w J) :
    ComponentClosed w (I ⊔ J) := by
  intro p hp d
  obtain ⟨i,hi,j,hj,rfl⟩ := Submodule.mem_sup.mp hp
  rw [map_add]
  exact Ideal.add_mem _ (Submodule.mem_sup_left (hI i hi d))
    (Submodule.mem_sup_right (hJ j hj d))

lemma componentClosed_span_single {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) :
    ComponentClosed w (Ideal.span {a}) := by
  intro p hp d
  obtain ⟨g,rfl⟩ := Ideal.mem_span_singleton.mp hp
  rw [project_mul w ha]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton a))

lemma componentClosed_bot : ComponentClosed (K := K) w ⊥ := by
  intro p hp d
  have hp0 : p = 0 := hp
  simp [hp0]

noncomputable def componentMap {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J) (d : G) :
    componentQuotient w I d →ₗ[K] componentQuotient w J d :=
  Submodule.mapQ _ _ LinearMap.id (fun _ hx => h hx)

@[simp] lemma componentMap_mk {I J : Ideal (MvPolynomial σ K)} (h : I ≤ J)
    (d : G) (p : Piece (K := K) w d) :
    componentMap w h d (Submodule.Quotient.mk p) = Submodule.Quotient.mk p := rfl

noncomputable def mulPiece {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (d : G) :
    Piece (K := K) w (d-e) →ₗ[K] Piece (K := K) w d :=
  ((LinearMap.mulLeft K a).comp (Piece (K := K) w (d-e)).subtype).codRestrict _
    (fun p => by
      change IsWeightedHomogeneous w (a * p.val) d
      simpa only [add_sub_cancel] using ha.mul p.property)

@[simp] lemma mulPiece_val {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (d : G) (p : Piece (K := K) w (d-e)) :
    (mulPiece w ha d p).val = a*p.val := rfl

noncomputable def componentMul {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (I J : Ideal (MvPolynomial σ K))
    (h : ∀ p ∈ I, a*p ∈ J) (d : G) :
    componentQuotient w I (d-e) →ₗ[K] componentQuotient w J d :=
  Submodule.mapQ _ _ (mulPiece w ha d) (fun p hp => h p.val hp)

@[simp] lemma componentMul_mk {a : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (I J : Ideal (MvPolynomial σ K))
    (h : ∀ p ∈ I, a*p ∈ J) (d : G) (p : Piece (K := K) w (d-e)) :
    componentMul w ha I J h d (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (mulPiece w ha d p) := rfl

theorem finrank_product_split (I : Ideal (MvPolynomial σ K))
    (hI : ComponentClosed w I) {a b : MvPolynomial σ K} {e : G}
    (ha : a.IsWeightedHomogeneous w e) (d : G)
    [Module.Finite K (Piece (K := K) w d)]
    [Module.Finite K (Piece (K := K) w (d-e))] :
    Module.finrank K (componentQuotient w (I ⊔ Ideal.span {a*b}) d) ≤
      Module.finrank K (componentQuotient w (I ⊔ Ideal.span {a}) d) +
      Module.finrank K (componentQuotient w (I ⊔ Ideal.span {b}) (d-e)) := by
  let B := I ⊔ Ideal.span {a*b}
  let A := I ⊔ Ideal.span {a}
  let C := I ⊔ Ideal.span {b}
  have hBA : B ≤ A := by
    apply sup_le le_sup_left
    apply Ideal.span_le.mpr
    rintro _ rfl
    exact Submodule.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have hm : ∀ p ∈ C, a*p ∈ B := by
    intro p hp
    obtain ⟨i,hi,z,hz,rfl⟩ := Submodule.mem_sup.mp hp
    obtain ⟨g,rfl⟩ := Ideal.mem_span_singleton.mp hz
    rw [mul_add, ← mul_assoc]
    exact Ideal.add_mem _ (Submodule.mem_sup_left (I.mul_mem_left a hi))
      (Submodule.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
  let f := componentMap w hBA d
  let g := componentMul w ha C B hm d
  have hker : LinearMap.ker f ≤ LinearMap.range g := by
    intro x hx
    obtain ⟨p,rfl⟩ := Submodule.mkQ_surjective _ x
    change (Submodule.Quotient.mk p : componentQuotient w A d) = 0 at hx
    have hp : p.val ∈ A := (Submodule.Quotient.mk_eq_zero
      ((A.restrictScalars K).comap (Piece (K := K) w d).subtype)).mp hx
    obtain ⟨i,hi,z,hz,hp⟩ := Submodule.mem_sup.mp hp
    obtain ⟨u,rfl⟩ := Ideal.mem_span_singleton.mp hz
    let v : Piece (K := K) w (d-e) :=
      ⟨weightedHomogeneousComponent w (d-e) u, weightedHomogeneousComponent_mem w u (d-e)⟩
    refine ⟨Submodule.Quotient.mk v, ?_⟩
    change Submodule.Quotient.mk (mulPiece w ha d v) = Submodule.Quotient.mk p
    rw [Submodule.Quotient.eq]
    change a * weightedHomogeneousComponent w (d-e) u - p.val ∈ B
    have he : weightedHomogeneousComponent w d i +
        a * weightedHomogeneousComponent w (d-e) u = p.val := by
      have hh := congrArg (weightedHomogeneousComponent w d) hp
      simpa only [map_add, project_mul w ha,
        weightedHomogeneousComponent_eq_self p.property] using hh
    have hi' := hI i hi d
    have he' : a * weightedHomogeneousComponent w (d-e) u - p.val =
        -(weightedHomogeneousComponent w d i) := by rw [← he]; abel
    rw [he']
    exact Submodule.mem_sup_left (I.neg_mem hi')
  have hk := (Submodule.finrank_mono hker).trans (LinearMap.finrank_range_le g)
  have hf := Submodule.finrank_le (LinearMap.range f)
  have hr := LinearMap.finrank_range_add_finrank_ker f
  dsimp only [B,A,C] at hk hf hr
  omega

structure FactorPair where
  left : MvPolynomial σ K
  right : MvPolynomial σ K
  leftDegree : G
  rightDegree : G
  left_homogeneous : left.IsWeightedHomogeneous w leftDegree
  right_homogeneous : right.IsWeightedHomogeneous w rightDegree

noncomputable def productIdeal : List (FactorPair (K := K) w) → Ideal (MvPolynomial σ K)
  | [] => ⊥
  | q :: qs => Ideal.span {q.left*q.right} ⊔ productIdeal qs

noncomputable def splitBound (I : Ideal (MvPolynomial σ K)) (d : G) :
    List (FactorPair (K := K) w) → ℕ
  | [] => Module.finrank K (componentQuotient w I d)
  | q :: qs => splitBound (I ⊔ Ideal.span {q.left}) d qs +
      splitBound (I ⊔ Ideal.span {q.right}) (d-q.leftDegree) qs

lemma productIdeal_closed (qs : List (FactorPair (K := K) w)) :
    ComponentClosed w (productIdeal w qs) := by
  induction qs with
  | nil => exact componentClosed_bot w
  | cons q qs ih =>
    exact componentClosed_sup w
      (componentClosed_span_single w (q.left_homogeneous.mul q.right_homogeneous)) ih

theorem finrank_le_splitBound [∀ d, Module.Finite K (Piece (K := K) w d)]
    (qs : List (FactorPair (K := K) w)) (I : Ideal (MvPolynomial σ K))
    (hI : ComponentClosed w I) (d : G) :
    Module.finrank K (componentQuotient w (I ⊔ productIdeal w qs) d) ≤
      splitBound w I d qs := by
  induction qs generalizing I d with
  | nil => rw [productIdeal, sup_bot_eq, splitBound]
  | cons q qs ih =>
    have hs := finrank_product_split w (b := q.right) (I ⊔ productIdeal w qs)
      (componentClosed_sup w hI (productIdeal_closed w qs)) q.left_homogeneous d
    have h₁ := ih (I ⊔ Ideal.span {q.left})
      (componentClosed_sup w hI (componentClosed_span_single w q.left_homogeneous)) d
    have h₂ := ih (I ⊔ Ideal.span {q.right})
      (componentClosed_sup w hI (componentClosed_span_single w q.right_homogeneous))
      (d-q.leftDegree)
    calc
      _ ≤ Module.finrank K (componentQuotient w
            ((I ⊔ Ideal.span {q.left}) ⊔ productIdeal w qs) d) +
          Module.finrank K (componentQuotient w
            ((I ⊔ Ideal.span {q.right}) ⊔ productIdeal w qs) (d-q.leftDegree)) := by
        have h₀ : I ⊔ productIdeal w (q::qs) =
            (I ⊔ productIdeal w qs) ⊔ Ideal.span {q.left*q.right} := by
          dsimp only [productIdeal]
          rw [sup_comm (Ideal.span {q.left*q.right}) (productIdeal w qs), ← sup_assoc]
        have hₐ : (I ⊔ productIdeal w qs) ⊔ Ideal.span {q.left} =
            (I ⊔ Ideal.span {q.left}) ⊔ productIdeal w qs := sup_right_comm _ _ _
        have hᵦ : (I ⊔ productIdeal w qs) ⊔ Ideal.span {q.right} =
            (I ⊔ Ideal.span {q.right}) ⊔ productIdeal w qs := sup_right_comm _ _ _
        rw [hₐ,hᵦ] at hs
        rw [h₀]
        exact hs
      _ ≤ _ := Nat.add_le_add h₁ h₂

end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section Blocks
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

noncomputable def blockWeight (group : σ → ι) (v : σ) : ι → ℤ :=
  Pi.single (group v) 1

lemma sum_blockWeight (group : σ → ι) (m : σ →₀ ℕ) :
    ∑ j, Finsupp.weight (blockWeight group) m j = (m.degree : ℤ) := by
  classical
  rw [Finsupp.weight_eq_sum]
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_comm]
  simp only [blockWeight, nsmul_eq_mul, ← Finset.mul_sum]
  rw [Finsupp.degree_eq_weight_one, Finsupp.weight_eq_sum]
  simp

lemma finite_block_degree (group : σ → ι) (d : ι → ℤ) :
    Set.Finite {m : σ →₀ ℕ | Finsupp.weight (blockWeight group) m = d} := by
  apply (Finsupp.finite_of_degree_le (∑ j, d j).toNat).subset
  intro m hm
  have hs := sum_blockWeight group m
  rw [hm] at hs
  change m.degree ≤ (∑ j, d j).toNat
  rw [hs]
  simp

instance blockPiece_finite (group : σ → ι) (d : ι → ℤ) :
    Module.Finite K (Piece (K := K) (blockWeight group) d) := by
  rw [Piece, weightedHomogeneousSubmodule_eq_finsupp_supported]
  have := (finite_block_degree group d).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport K
    {m | Finsupp.weight (blockWeight group) m = d})

end Blocks
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearLeaves
variable {K σ ι : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]

noncomputable def blockExponent (group : σ → ι) (m : σ →₀ ℕ) (j : ι) : ℕ :=
  ∑ v ∈ Finset.univ.filter (group · = j), m v

omit [Fintype ι] in
lemma weight_blockExponent (group : σ → ι) (m : σ →₀ ℕ) (j : ι) :
    Finsupp.weight (blockWeight group) m j = (blockExponent group m j : ℤ) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, blockWeight, nsmul_eq_mul]
  simp [blockExponent, Pi.single_apply, Finset.sum_filter, eq_comm]

lemma prod_blockExponent {S : Type*} [CommMonoid S] (group : σ → ι)
    (m : σ →₀ ℕ) (z : ι → S) :
    ∏ v, z (group v) ^ m v = ∏ j, z j ^ blockExponent group m j := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ group]
  apply Finset.prod_congr rfl
  intro j _
  rw [blockExponent, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro v hv
  rw [(Finset.mem_filter.mp hv).2]

noncomputable def componentEmbed (group : σ → ι) (I : Ideal (MvPolynomial σ K))
    (d : ι → ℤ) : componentQuotient (blockWeight group) I d →ₗ[K]
      (MvPolynomial σ K ⧸ I) :=
  Submodule.liftQ _ ((Ideal.Quotient.mkₐ K I).toLinearMap.comp
    (Piece (K := K) (blockWeight group) d).subtype) (by
      intro p hp
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hp)

omit [Fintype σ] [Fintype ι] in
lemma componentEmbed_injective (group : σ → ι) (I : Ideal (MvPolynomial σ K))
    (d : ι → ℤ) : Function.Injective (componentEmbed group I d) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨p,rfl⟩ := Submodule.Quotient.mk_surjective
    ((I.restrictScalars K).comap (Piece (K := K) (blockWeight group) d).subtype) x
  change Submodule.Quotient.mk p = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact Ideal.Quotient.eq_zero_iff_mem.mp hx

theorem component_finrank_le_one_of_linear_relations (group : σ → ι)
    (I : Ideal (MvPolynomial σ K)) (z : ι → MvPolynomial σ K) (c : σ → K)
    (hrel : ∀ v, X v - C (c v) * z (group v) ∈ I) (d : ι → ℤ) :
    Module.finrank K (componentQuotient (blockWeight group) I d) ≤ 1 := by
  classical
  let q := Ideal.Quotient.mkₐ K I
  let Z := ∏ j, q (z j) ^ (d j).toNat
  have hX (v : σ) : q (X v) = algebraMap K _ (c v) * q (z (group v)) := by
    have h := Ideal.Quotient.eq.mpr (hrel v)
    change q (X v) = q (C (c v) * z (group v)) at h
    rw [map_mul] at h
    exact h.trans (congrArg (· * q (z (group v))) (q.commutes (c v)))
  have hmon (m : σ →₀ ℕ) (r : K) (hm : Finsupp.weight (blockWeight group) m = d) :
      q (monomial m r) ∈ Submodule.span K {Z} := by
    apply Submodule.mem_span_singleton.mpr
    refine ⟨r * ∏ v, c v ^ m v, ?_⟩
    have hexp : ∀ j, blockExponent group m j = (d j).toNat := by
      intro j
      have h := congrFun hm j
      rw [weight_blockExponent] at h
      rw [← h, Int.toNat_natCast]
    rw [monomial_eq, Finsupp.prod_pow, map_mul, map_prod]
    simp only [map_pow, hX, mul_pow, Finset.prod_mul_distrib]
    rw [prod_blockExponent group m (fun j => q (z j))]
    simp only [hexp]
    change (r * ∏ v, c v ^ m v) • Z =
      algebraMap K _ r * ((∏ v, (algebraMap K _ (c v)) ^ m v) * Z)
    have he : (r * ∏ v, c v ^ m v) • Z =
        algebraMap K (MvPolynomial σ K ⧸ I) (r * ∏ v, c v ^ m v) * Z :=
      Algebra.smul_def (R := K) (A := MvPolynomial σ K ⧸ I) (r * ∏ v, c v ^ m v) Z
    rw [he, map_mul, map_prod]
    simp only [map_pow]
    ring
  have hpiece (p : Piece (K := K) (blockWeight group) d) :
      q p.val ∈ Submodule.span K {Z} := by
    rcases p with ⟨p,hp⟩
    induction hp using IsWeightedHomogeneous.induction_on with
    | zero => simp
    | add p₁ p₂ _ _ h₁ h₂ => simpa only [map_add] using Submodule.add_mem _ h₁ h₂
    | monomial m r hm => exact hmon m r hm
  let f := (componentEmbed group I d).codRestrict (Submodule.span K {Z}) (by
    intro x
    obtain ⟨p,rfl⟩ := Submodule.Quotient.mk_surjective
      ((I.restrictScalars K).comap (Piece (K := K) (blockWeight group) d).subtype) x
    exact hpiece p)
  have hf : Function.Injective f := fun a b h =>
    componentEmbed_injective group I d (congrArg Subtype.val h)
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans
    (by
      apply finrank_le_one_iff.mpr
      refine ⟨⟨Z, Submodule.subset_span (Set.mem_singleton Z)⟩, ?_⟩
      intro x
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp x.property
      exact ⟨c, Subtype.ext hc⟩)

theorem component_finrank_zero_of_block_killed (group : σ → ι)
    (I : Ideal (MvPolynomial σ K)) (j : ι)
    (hkill : ∀ v, group v = j → X v ∈ I) (d : ι → ℤ) (hd : 0 < d j) :
    Module.finrank K (componentQuotient (blockWeight group) I d) = 0 := by
  classical
  let q := Ideal.Quotient.mkₐ K I
  have hmon (m : σ →₀ ℕ) (r : K) (hm : Finsupp.weight (blockWeight group) m = d) :
      q (monomial m r) = 0 := by
    have hexp : 0 < blockExponent group m j := by
      have h := congrFun hm j
      rw [weight_blockExponent] at h
      omega
    obtain ⟨v,hv,hmv⟩ := Finset.sum_pos_iff.mp hexp
    have hqv : q (X v) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (hkill v (Finset.mem_filter.mp hv).2)
    rw [monomial_eq, Finsupp.prod_pow, map_mul, map_prod]
    have hz : ∏ v, q (X v ^ m v) = 0 := Finset.prod_eq_zero (Finset.mem_univ v) (by
      rw [map_pow, hqv, zero_pow (Nat.ne_of_gt hmv)])
    rw [hz, mul_zero]
  have hpiece (p : Piece (K := K) (blockWeight group) d) : q p.val = 0 := by
    rcases p with ⟨p,hp⟩
    induction hp using IsWeightedHomogeneous.induction_on with
    | zero => exact map_zero q
    | add p₁ p₂ _ _ h₁ h₂ => rw [map_add, h₁,h₂,add_zero]
    | monomial m r hm => exact hmon m r hm
  apply Module.finrank_eq_zero_iff.mpr
  intro x
  refine ⟨1,one_ne_zero,?_⟩
  rw [one_smul]
  apply componentEmbed_injective group I d
  obtain ⟨p,rfl⟩ := Submodule.Quotient.mk_surjective
    ((I.restrictScalars K).comap (Piece (K := K) (blockWeight group) d).subtype) x
  rw [map_zero]
  exact hpiece p

end LinearLeaves
end PermanentBorder.Multigraded

end OAI
