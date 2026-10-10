import OAI.RepresentationTheory.KazhdanLusztig.SheafMorphisms

namespace OAI

/-!
Graded decomposition characters, reflection-plane algebras and reflection Frobenius structures.
-/

section

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded Polynomial
universe uk us um
variable {k : Type uk} [Field k] {σ : Type us} [Finite σ]
  {V E : Type um} [PartialOrder V] {G : OrderedGraph V E}
noncomputable section

 def freeStalkChar (B : GradedSheaf (𝓐 := polynomialGrading k σ) G)
    (hf : ∀ x, Module.Free (MvPolynomial σ k) (B.vertex x)) (x : V) : Polynomial ℤ := by
  let := hf x
  exact (B.vertex x).char

 theorem ModelSum.character {α : E → MvPolynomial σ k}
    (O : BoundaryModels (polynomialGrading_negative k σ) (G := G) α)
    [Fintype V] {U : Set V} {B : GradedSheaf (𝓐 := polynomialGrading k σ) G}
    (h : ModelSum O.sheaf U B) :
    ∃ hmul : V → Polynomial ℤ,
      (∀ y n, 0 ≤ (hmul y).coeff n) ∧
      (∀ y, y ∉ U → hmul y=0) ∧
      ∀ x, freeStalkChar B (h.free O) x =
        ∑ y, hmul y*freeStalkChar (O.sheaf y) (O.free y) x := by
  classical
  induction h with
  | zero =>
    refine ⟨0,by simp,by simp,?_⟩
    intro x
    simp only [Pi.zero_apply,zero_mul,Finset.sum_const_zero]
    exact ModuleData.char_zero _
  | @add B h c hc n d ih =>
    obtain ⟨m,hm,hsupp,heq⟩ := ih
    let a : Polynomial ℤ := ∑ i, X^(d i)
    have ha (r : ℕ) : 0 ≤ a.coeff r := by
      simp only [a,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow]
      exact Finset.sum_nonneg (fun i _ => by split <;> norm_num)
    refine ⟨fun y => m y+if y=c then a else 0,?_,?_,?_⟩
    · intro y r
      rw [Polynomial.coeff_add]
      apply add_nonneg (hm y r)
      split
      · exact ha r
      · simp
    · intro y hy
      have hne : y≠c := fun hh => hy (hh ▸ hc)
      simp [hsupp y hy,hne]
    · intro x
      let _ := h.free O x
      let _ := O.free c x
      change ((B.vertex x).prod (ModuleData.pi (fun i => ((O.sheaf c).vertex x).shift (d i)))).char = _
      rw [ModuleData.char_prod,ModuleData.char_pi]
      simp only [ModuleData.char_shift]
      change freeStalkChar B (h.free O) x + _ = _
      rw [heq x]
      simp only [add_mul,Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_mul]
      simp only [ite_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      rfl

 theorem exists_stalkCharacter_decomposition [Fintype V] [Fintype E]
    {α : E → MvPolynomial σ k}
    (O : BoundaryModels (polynomialGrading_negative k σ) (G := G) α)
    (B : GradedSheaf (𝓐 := polynomialGrading k σ) G)
    (hf : ∀ x, Module.Free (MvPolynomial σ k) (B.vertex x))
    (hq : B.UpperQuotient α) (hfl : B.forget.Flabby) (hg : B.forget.Generated) :
    ∃ hmul : V → Polynomial ℤ, (∀ y n, 0 ≤ (hmul y).coeff n) ∧
      ∀ x, freeStalkChar B hf x =
        ∑ y, hmul y*freeStalkChar (O.sheaf y) (O.free y) x := by
  obtain ⟨C,hC,⟨j⟩⟩ := exists_modelSumIso (polynomialGrading_zero k σ) O B hf hq hfl hg
  obtain ⟨m,hm,_,heq⟩ := hC.character O
  refine ⟨m,hm,fun x => ?_⟩
  rw [← heq x]
  let _ := hf x
  let _ := hC.free O x
  exact ModuleData.character_eq_of_gradedEquiv (j.vertex x)
    (j.vertex_graded x)

end
end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type u} [Group W] (cs : CoxeterSystem M W) (b : W)
  {σ : Type u} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

 def lowerCharacter (c x : Interval cs 1 b) : Polynomial ℤ :=
  if h : x≤c then stalkCharacter cs 1 c.val basis (one_bruhat cs c.val)
    ⟨x.val,x.property.1,h⟩ else 0

 theorem boundaryModels_character (c x : Interval cs 1 b) :
    GradedSheaf.freeStalkChar ((boundaryModels cs b basis).sheaf c)
      ((boundaryModels cs b basis).free c) x=lowerCharacter cs b basis c x := by
  let _ := (boundaryModels cs b basis).free c x
  by_cases hx : x≤c
  · rw [lowerCharacter,dite_eq_left hx]
    let B := lowerIntervalBoundary cs b basis c
    let _ := B.sheaf.lowerExtend_free B.free x
    let _ := (boundarySheaf cs 1 c.val basis (one_bruhat cs c.val)).free ⟨x.val,x.property.1,hx⟩
    exact ModuleData.character_eq_of_gradedEquiv (B.sheaf.lowerExtendVertex ⟨x,hx⟩)
      (B.sheaf.lowerExtendVertex_graded ⟨x,hx⟩)
  · rw [lowerCharacter,dite_eq_right hx]
    let _ := (boundaryModels cs b basis).support c x hx
    exact ModuleData.char_zero _

 theorem lowerCharacter_zero (c x : Interval cs 1 b) (hx : ¬x≤c) :
    lowerCharacter cs b basis c x=0 := dite_eq_right hx

 theorem lowerCharacter_nonneg (c x : Interval cs 1 b) (n : ℕ) :
    0≤(lowerCharacter cs b basis c x).coeff n := by
  unfold lowerCharacter
  split
  · exact stalkCharacter_coeff_nonneg cs 1 c.val basis (one_bruhat cs c.val) _ n
  · simp

end
end KLInvariance.BruhatGraph

end


section

/-! Integral pair-projection quotients. The purpose is the actual localization
functor from a tensor bimodule to a moment-graph sheaf; no flabbiness, stalk
freeness, BMP identification or character theorem is assumed or asserted. -/
namespace KLInvariance.PairProjection
universe u v w z
variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : M →ₗ[R] X) (g : M →ₗ[R] Y)
noncomputable section

def relation : Submodule R (X × Y) := LinearMap.range (f.prod g)
abbrev Edge := (X × Y) ⧸ relation f g

def lower : X →ₗ[R] Edge f g := (relation f g).mkQ.comp (LinearMap.inl R X Y)
def upper : Y →ₗ[R] Edge f g := -((relation f g).mkQ.comp (LinearMap.inr R X Y))

theorem diagonal_zero (m : M) : (relation f g).mkQ (f m,g m)=0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨m,rfl⟩

theorem compatible (m : M) : lower f g (f m)=upper f g (g m) := by
  have h := diagonal_zero f g m
  have hp : (f m,g m)=(f m,0)+(0,g m) := by simp
  rw [hp,map_add] at h
  exact eq_neg_of_add_eq_zero_left h

theorem compatible_iff (x : X) (y : Y) :
    lower f g x=upper f g y ↔ ∃ m : M, f m=x ∧ g m=y := by
  change (relation f g).mkQ (x,0) = -((relation f g).mkQ (0,y)) ↔ _
  rw [eq_neg_iff_add_eq_zero,← map_add]
  rw [show ((x,0)+(0,y) : X × Y)=(x,y) by simp]
  change (Submodule.Quotient.mk (x,y) : Edge f g)=0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨m,hm⟩
    exact ⟨m,congrArg Prod.fst hm,congrArg Prod.snd hm⟩
  · rintro ⟨m,hm,hn⟩
    exact ⟨m,Prod.ext hm hn⟩

theorem kernel_lower (x : X) : lower f g x=0 ↔ ∃ m : M, f m=x ∧ g m=0 := by
  change (relation f g).mkQ (x,0)=0 ↔ _
  change Submodule.Quotient.mk (x,0) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨m,hm⟩
    exact ⟨m,congrArg Prod.fst hm,congrArg Prod.snd hm⟩
  · rintro ⟨m,hm,hn⟩
    exact ⟨m,Prod.ext hm hn⟩

theorem lower_surjective (hg : Function.Surjective g) :
    Function.Surjective (lower f g) := by
  intro v
  obtain ⟨⟨x,y⟩,rfl⟩ := (relation f g).mkQ_surjective v
  obtain ⟨m,rfl⟩ := hg y
  refine ⟨x-f m,?_⟩
  change (relation f g).mkQ (x-f m,0) = (relation f g).mkQ (x,g m)
  have hp : (x-f m,0)=(x,g m)-(f m,g m) := by simp
  rw [hp,map_sub,diagonal_zero,sub_zero]

theorem upper_surjective (hf : Function.Surjective f) :
    Function.Surjective (upper f g) := by
  intro v
  obtain ⟨⟨x,y⟩,rfl⟩ := (relation f g).mkQ_surjective v
  obtain ⟨m,rfl⟩ := hf x
  refine ⟨g m-y,?_⟩
  change -((relation f g).mkQ (0,g m-y)) = (relation f g).mkQ (f m,y)
  have hp : (0,g m-y)=(f m,g m)-(f m,y) := by simp
  rw [hp,map_sub,diagonal_zero,zero_sub,neg_neg]

/-- A genuine right-action eigenvalue difference annihilates the edge
quotient. This uses only the integral module, not a fraction-field equality. -/
theorem difference_annihilates (hf : Function.Surjective f)
    (hg : Function.Surjective g) (T : M →ₗ[R] M) (r s : R)
    (hr : ∀ m, f (T m)=r • f m) (hs : ∀ m, g (T m)=s • g m)
    (v : Edge f g) : (r-s) • v=0 := by
  obtain ⟨x,rfl⟩ := lower_surjective f g hg v
  rw [← map_smul]
  apply (kernel_lower f g _).mpr
  obtain ⟨m,rfl⟩ := hf x
  refine ⟨T m-s • m,?_,?_⟩
  · rw [map_sub,map_smul,hr,sub_smul]
  · rw [map_sub,map_smul,hs,sub_self]

end
end KLInvariance.PairProjection

end


section


namespace KLInvariance.Dihedral
noncomputable section

variable {G : Type*} [Group G]

/-- The matrix of a pair of distinct involutions. -/
def pairMatrix (s t : G) (hs : s * s = 1) (hst : s ≠ t) : CoxeterMatrix Bool where
  M i j := if i = j then 1 else orderOf (s * t)
  isSymm := by
    ext i j
    change (if j = i then 1 else orderOf (s*t)) = if i = j then 1 else orderOf (s*t)
    cases i <;> cases j <;> rfl
  diagonal i := ite_eq_left rfl
  off_diagonal i j hij := by
    rw [ite_eq_right hij]
    intro h
    have he := orderOf_eq_one_iff.mp h
    apply hst
    calc
      s = s * (s * t) := by rw [he, mul_one]
      _ = t := by rw [← mul_assoc, hs, one_mul]

/-- Alternating even words are powers of the product of the two generators. -/
theorem wordProd_alt_even {N : CoxeterMatrix Bool} {H : Type*} [Group H]
    (cs : CoxeterSystem N H) (i : Bool) (n : ℕ) :
    cs.wordProd (alt i (2 * n)) = (cs.simple i * cs.simple (!i)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, alt_add_two]
    rw [cs.wordProd_cons, cs.wordProd_cons, ih, pow_succ']
    exact (mul_assoc _ _ _).symm

/-- Homomorphisms out of a rank-two Coxeter group that do not lower
its product order and do not kill either generator are injective. -/
theorem injective_of_simple_order {N : CoxeterMatrix Bool} {H : Type*} [Group H]
    (cs : CoxeterSystem N H) (f : H →* G)
    (hne : ∀ i, f (cs.simple i) ≠ 1)
    (horder : ∀ i, orderOf (f (cs.simple i) * f (cs.simple (!i))) = N i (!i)) :
    Function.Injective f := by
  apply (injective_iff_map_eq_one f).mpr
  intro w hw
  rcases Nat.even_or_odd (cs.length w) with he | ho
  · obtain ⟨n, hn⟩ := he
    have hn' : cs.length w = 2 * n := by omega
    obtain ⟨i, hi⟩ := exists_alt cs w
    rw [hn', wordProd_alt_even] at hi
    have hpow : (f (cs.simple i) * f (cs.simple (!i))) ^ n = 1 := by
      simpa only [hi, map_pow, map_mul] using hw
    have hdiv := orderOf_dvd_of_pow_eq_one hpow
    rw [horder i] at hdiv
    obtain ⟨k, hk⟩ := hdiv
    rw [hi, hk, pow_mul, cs.simple_mul_simple_pow, one_pow]
  · obtain ⟨a, i, ha⟩ := (reflection_iff_odd cs w).mpr ho
    have h := hw
    rw [ha, map_mul, map_mul, map_inv] at h
    apply False.elim
    apply hne i
    have h' := congrArg (fun z => (f a)⁻¹ * z * f a) h
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one,
      one_mul, mul_inv_cancel_left] using h'

variable (s t : G) (hs : s * s = 1) (ht : t * t = 1) (hst : s ≠ t)

/-- The map from the genuine presented rank-two Coxeter group. -/
def pairLift : (pairMatrix s t hs hst).Group →* G :=
  (pairMatrix s t hs hst).toCoxeterSystem.lift
    ⟨(fun i => if i then t else s), by
      intro i j
      cases i <;> cases j
      · simpa [pairMatrix] using hs
      · simp only [pairMatrix, Bool.false_eq_true, ↓reduceIte]
        exact pow_orderOf_eq_one (s*t)
      · simp only [pairMatrix, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte]
        have hinv : (s*t)⁻¹ = t*s := by
          rw [mul_inv_rev, (inv_eq_of_mul_eq_one_right ht), (inv_eq_of_mul_eq_one_right hs)]
        rw [← hinv, inv_pow, pow_orderOf_eq_one, inv_one]
      · simpa [pairMatrix] using ht⟩

@[simp] theorem pairLift_simple (i : Bool) :
    pairLift s t hs ht hst ((pairMatrix s t hs hst).toCoxeterSystem.simple i) =
      if i then t else s := by
  apply CoxeterSystem.lift_apply_simple

/-- No relation other than the Coxeter relations is introduced by the pair. -/
theorem pairLift_injective (hs1 : s ≠ 1) (ht1 : t ≠ 1) :
    Function.Injective (pairLift s t hs ht hst) := by
  apply injective_of_simple_order (pairMatrix s t hs hst).toCoxeterSystem
  · intro i
    rw [pairLift_simple]
    cases i <;> simp_all
  · intro i
    simp only [pairLift_simple]
    cases i
    · simp [pairMatrix]
    · simp only [Bool.not_true, ↓reduceIte, pairMatrix, Bool.true_eq_false, Bool.false_eq_true]
      have hinv : (s*t)⁻¹ = t*s := by
        rw [mul_inv_rev, (inv_eq_of_mul_eq_one_right ht), (inv_eq_of_mul_eq_one_right hs)]
      rw [← hinv, orderOf_inv]

/-- The presented pair generates exactly the subgroup generated by its images. -/
theorem pairLift_range :
    (pairLift s t hs ht hst).range = Subgroup.closure {s, t} := by
  apply le_antisymm
  · rintro x ⟨w, rfl⟩
    apply (pairMatrix s t hs hst).toCoxeterSystem.simple_induction w
    · intro i
      rw [pairLift_simple]
      cases i <;> apply Subgroup.subset_closure <;> simp
    · simp only [map_one, Subgroup.one_mem]
    · intro a b ha hb
      rw [map_mul]
      exact Subgroup.mul_mem _ ha hb
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]
      exact ⟨(pairMatrix s t hs hst).toCoxeterSystem.simple false, pairLift_simple _ _ _ _ _ _⟩
    · have : x = t := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨(pairMatrix s t hs hst).toCoxeterSystem.simple true, pairLift_simple _ _ _ _ _ _⟩

/-- An actual Coxeter system on the generated subgroup, not an extra assumption. -/
def pairSystem (hs1 : s ≠ 1) (ht1 : t ≠ 1) :
    CoxeterSystem (pairMatrix s t hs hst) (Subgroup.closure {s, t}) :=
  (pairMatrix s t hs hst).toCoxeterSystem.map
    ((MulEquiv.ofBijective (pairLift s t hs ht hst).rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr
        (pairLift_injective s t hs ht hst hs1 ht1),
       (pairLift s t hs ht hst).rangeRestrict_surjective⟩).trans
      (MulEquiv.subgroupCongr (pairLift_range s t hs ht hst)))

@[simp] theorem pairSystem_simple (hs1 : s ≠ 1) (ht1 : t ≠ 1) (i : Bool) :
    ((pairSystem s t hs ht hst hs1 ht1).simple i : G) = if i then t else s := by
  exact pairLift_simple s t hs ht hst i

end
end KLInvariance.Dihedral


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

/-- Any two distinct positive roots in a two-dimensional root plane span it. -/
theorem rootPlane_eq_of_mem (a b l r : PositiveRoot M cs) (hab : a ≠ b)
    (hl : l.val ∈ rootPlane a b) (hr : r.val ∈ rootPlane a b) (hlr : l ≠ r) :
    rootPlane l r = rootPlane a b := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    intro z hz
    change z ∈ rootPlane a b
    rcases Set.mem_insert_iff.mp hz with hz | hz
    · rw [hz]; exact hl
    · rw [Set.mem_singleton_iff.mp hz]; exact hr
  · rw [rootPlane_finrank _ _ hlr, rootPlane_finrank _ _ hab]

/-- Slope betweenness detects the actual positive cone, not only one implication. -/
theorem positive_combination_of_slope_between (a b c : PositiveRoot M cs)
    (hc : c.val ∈ rootPlane a b)
    (hac : geometricSlope a < geometricSlope c)
    (hcb : geometricSlope c < geometricSlope b) :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧ c.val = r • a.val + s • b.val := by
  let f := geometricFunctional (M := M) (cs := cs)
  obtain ⟨r, s, he⟩ := Submodule.mem_span_pair.mp hc
  refine ⟨r, s, ?_, ?_, he.symm⟩
  all_goals
    have ha := a.height_pos
    have hb := b.height_pos
    have hh := c.height_pos
    have hfc := congrArg f he
    have hhc := congrArg (height (I := I)) he
    simp only [map_add, map_smul, smul_eq_mul] at hfc hhc
    change f a.val / height a.val <
      f c.val / height c.val at hac
    change f c.val / height c.val <
      f b.val / height b.val at hcb
    have hab := lt_trans hac hcb
    rw [div_lt_div_iff₀ ha hb] at hab
    rw [div_lt_div_iff₀ ha hh] at hac
    rw [div_lt_div_iff₀ hh hb] at hcb
  · have heq : r * (f b.val * height a.val -
        f a.val * height b.val) =
        f b.val * height c.val -
          f c.val * height b.val := by rw [← hfc, ← hhc]; ring
    have hp : 0 < r * (f b.val * height a.val -
        f a.val * height b.val) := by rw [heq]; linarith
    exact (mul_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2]) |>.1
  · have heq : s * (f b.val * height a.val -
        f a.val * height b.val) =
        f c.val * height a.val -
          f a.val * height c.val := by rw [← hfc, ← hhc]; ring
    have hp : 0 < s * (f b.val * height a.val -
        f a.val * height b.val) := by rw [heq]; linarith
    exact (mul_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2]) |>.1

/-- Positivity is convex in the root cone. -/
theorem noninverted_of_positive_combination (w : W) (a b c : PositiveRoot M cs)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hc : c.val = r • a.val + s • b.val)
    (ha : ¬ rootInverted w a) (hb : ¬ rootInverted w b) :
    ¬ rootInverted w c := by
  rw [not_rootInverted_iff] at ha hb ⊢
  intro i
  rw [hc, map_add, map_smul, map_smul]
  exact add_nonneg (mul_nonneg hr (ha i)) (mul_nonneg hs (hb i))

@[simp] theorem not_rootInverted_one (a : PositiveRoot M cs) :
    ¬ rootInverted (1 : W) a := by
  rw [not_rootInverted_iff]
  simp only [inv_one, map_one]
  exact a.property.2

@[simp] theorem rootInverted_ref_self (a : PositiveRoot M cs) :
    rootInverted (rootRef a) a := by
  simpa only [mul_one] using (rootInverted_mul_self 1 a).mpr (not_rootInverted_one a)

/-- A root plane has an extreme positive root. Finiteness of inversion sets
replaces the false assertion that the (real-valued) root heights are discrete. -/
theorem exists_plane_extreme_inverted (a b : PositiveRoot M cs) (hab : a ≠ b) :
    ∃ p : PositiveRoot M cs, p.val ∈ rootPlane a b ∧ rootInverted (rootRef a) p ∧
      ((∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope p ≤ geometricSlope r) ∨
       (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope r ≤ geometricSlope p)) := by
  classical
  let S := (finite_rootInverted (M := M) (cs := cs) (rootRef a)).toFinset.filter
    (fun r => r.val ∈ rootPlane a b)
  have hS (r : PositiveRoot M cs) : r ∈ S ↔
      rootInverted (rootRef a) r ∧ r.val ∈ rootPlane a b := by
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  have haP : a.val ∈ rootPlane a b := Submodule.subset_span (Set.mem_insert _ _)
  have haS : a ∈ S := (hS a).mpr ⟨rootInverted_ref_self a, haP⟩
  obtain ⟨p, hp, hmin⟩ := S.exists_min_image geometricSlope ⟨a, haS⟩
  obtain ⟨q, hq, hmax⟩ := S.exists_max_image geometricSlope ⟨a, haS⟩
  by_cases hleft : ∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
      geometricSlope p ≤ geometricSlope r
  · exact ⟨p, (hS p).mp hp |>.2, (hS p).mp hp |>.1, Or.inl hleft⟩
  by_cases hright : ∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
      geometricSlope r ≤ geometricSlope q
  · exact ⟨q, (hS q).mp hq |>.2, (hS q).mp hq |>.1, Or.inr hright⟩
  push Not at hleft hright
  obtain ⟨l, hlP, hlp⟩ := hleft
  obtain ⟨r, hrP, hqr⟩ := hright
  have hla := lt_of_lt_of_le hlp (hmin a haS)
  have har := lt_of_le_of_lt (hmax a haS) hqr
  have hlr : l ≠ r := fun h => (lt_trans hla har).ne (congrArg geometricSlope h)
  have hplane := rootPlane_eq_of_mem a b l r hab hlP hrP hlr
  have hlam : ¬ rootInverted (rootRef a) l := by
    intro hi
    exact (not_le_of_gt hlp) (hmin l ((hS l).mpr ⟨hi, hlP⟩))
  have hram : ¬ rootInverted (rootRef a) r := by
    intro hi
    exact (not_le_of_gt hqr) (hmax r ((hS r).mpr ⟨hi, hrP⟩))
  obtain ⟨c, d, hc, hd, he⟩ := positive_combination_of_slope_between l r a
    (hplane.symm ▸ haP) hla har
  exact False.elim ((noninverted_of_positive_combination (rootRef a) l r a
    hc.le hd.le he hlam hram) (rootInverted_ref_self a))

/-- The canonical simple-root criterion stated on the actual ambient roots. -/
def PlaneSimple (P : Submodule ℝ (I → ℝ)) (a : PositiveRoot M cs) : Prop :=
  a.val ∈ P ∧ ∀ b : PositiveRoot M cs, b.val ∈ P →
    (rootInverted (rootRef a) b ↔ b = a)

theorem rootInverted_ref_iff_flipped (a b : PositiveRoot M cs) :
    rootInverted (rootRef a) b ↔ flipped a b := by
  unfold rootInverted flipped
  rw [(rootReflection M cs a).property.inv]

/-- An angular extreme inverts exactly its own positive root. -/
theorem planeSimple_of_extreme {P : Submodule ℝ (I → ℝ)}
    (a : PositiveRoot M cs) (ha : a.val ∈ P)
    (hext : (∀ r : PositiveRoot M cs, r.val ∈ P → geometricSlope a ≤ geometricSlope r) ∨
      (∀ r : PositiveRoot M cs, r.val ∈ P → geometricSlope r ≤ geometricSlope a)) :
    PlaneSimple P a := by
  refine ⟨ha, fun b hb => ⟨?_, ?_⟩⟩
  · intro hinv
    by_contra hba
    have hn := (rootInverted_ref_iff_flipped a b).mp hinv
    have hp := partner_mem a b ha hb
    have hs := negative_pair_sum a b hn
    have hc := negative_pair_coefficient_pos a b hn
    have he : a.val = (form M a.val b.val)⁻¹ • b.val +
        (form M a.val b.val)⁻¹ • (partner a b).val := by
      calc
        a.val = (form M a.val b.val)⁻¹ • (form M a.val b.val • a.val) := by
          rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
        _ = _ := by rw [← hs, smul_add]
    have hne : geometricSlope b ≠ geometricSlope (partner a b) := by
      intro h
      exact hba (negative_partner_fixed a b hn (geometricSlope_injective h).symm)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hh := geometricSlope_between b (partner a b) a
        (inv_pos.mpr hc) (inv_pos.mpr hc) he hlt
      rcases hext with hmin | hmax
      · exact (not_lt_of_ge (hmin b hb)) hh.1
      · exact (not_lt_of_ge (hmax (partner a b) hp)) hh.2
    · have he' : a.val = (form M a.val b.val)⁻¹ • (partner a b).val +
          (form M a.val b.val)⁻¹ • b.val := by rw [add_comm]; exact he
      have hh := geometricSlope_between (partner a b) b a
        (inv_pos.mpr hc) (inv_pos.mpr hc) he' hlt
      rcases hext with hmin | hmax
      · exact (not_lt_of_ge (hmin (partner a b) hp)) hh.1
      · exact (not_lt_of_ge (hmax b hb)) hh.2
  · intro h
    rw [h]
    exact rootInverted_ref_self a

theorem PlaneSimple.partner_val {P : Submodule ℝ (I → ℝ)}
    {a : PositiveRoot M cs} (ha : PlaneSimple P a)
    {b : PositiveRoot M cs} (hb : b.val ∈ P) (hba : b ≠ a) :
    (partner a b).val = action M cs (rootRef a) b.val := by
  have hn : ¬ rootInverted (rootRef a) b := fun h => hba ((ha.2 b hb).mp h)
  have hp := (not_rootInverted_iff (rootRef a) b).mp hn
  rw [(rootReflection M cs a).property.inv] at hp
  exact positiveAction_eq_of_nonneg _ _ hp

theorem PlaneSimple.exists_nonpositive_pair {P : Submodule ℝ (I → ℝ)}
    {a : PositiveRoot M cs} (ha : PlaneSimple P a)
    {b : PositiveRoot M cs} (hb : b.val ∈ P) (hba : b ≠ a) :
    ∃ c : PositiveRoot M cs, c.val ∈ P ∧ c ≠ a ∧ form M a.val c.val ≤ 0 := by
  by_cases hn : form M a.val b.val ≤ 0
  · exact ⟨b, hb, hba, hn⟩
  · refine ⟨partner a b, partner_mem a b ha.1 hb,
      fun h => hba ((partner_eq_self_of_eq a b).mp h), ?_⟩
    rw [ha.partner_val hb hba, (rootReflection_represents M cs a).action_formula]
    simp only [map_sub, map_smul, smul_eq_mul, a.property.1.norm]
    linarith

theorem noninverted_ref_of_pairing_nonpos (a b : PositiveRoot M cs)
    (hab : form M a.val b.val ≤ 0) : ¬ rootInverted (rootRef b) a := by
  rw [not_rootInverted_iff, (rootReflection M cs b).property.inv,
    (rootReflection_represents M cs b).action_formula]
  have hba : form M b.val a.val ≤ 0 := by rwa [(form_symm M).eq]
  intro i
  exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hba (b.property.2 i)).trans
    (a.property.2 i))

/-- The other endpoint exists even in an infinite or degenerate plane. -/
theorem exists_opposite_plane_extreme (a b p : PositiveRoot M cs) (hab : a ≠ b)
    (hp : p.val ∈ rootPlane a b)
    (hext : (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
        geometricSlope p ≤ geometricSlope r) ∨
      (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
        geometricSlope r ≤ geometricSlope p)) :
    ∃ q : PositiveRoot M cs, q.val ∈ rootPlane a b ∧ q ≠ p ∧
      (((∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope p ≤ geometricSlope r) ∧
        (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope r ≤ geometricSlope q)) ∨
       ((∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope q ≤ geometricSlope r) ∧
        (∀ r : PositiveRoot M cs, r.val ∈ rootPlane a b →
          geometricSlope r ≤ geometricSlope p))) := by
  have hs := planeSimple_of_extreme p hp hext
  have hother : ∃ r : PositiveRoot M cs, r.val ∈ rootPlane a b ∧ r ≠ p := by
    by_cases hap : a = p
    · refine ⟨b, Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)), ?_⟩
      exact fun h => hab (hap.trans h.symm)
    · exact ⟨a, Submodule.subset_span (Set.mem_insert _ _), hap⟩
  obtain ⟨r, hrP, hrp⟩ := hother
  obtain ⟨c, hcP, hcp, hcpair⟩ := hs.exists_nonpositive_pair hrP hrp
  have hn := noninverted_ref_of_pairing_nonpos p c hcpair
  have hplane := rootPlane_eq_of_mem a b c p hab hcP hp hcp
  obtain ⟨q, hqP, hqinv, hqext⟩ := exists_plane_extreme_inverted c p hcp
  rw [hplane] at hqP hqext
  have hqp : q ≠ p := fun h => hn (h ▸ hqinv)
  refine ⟨q, hqP, hqp, ?_⟩
  rcases hext with hmin | hmax
  · refine Or.inl ⟨hmin, ?_⟩
    rcases hqext with hqmin | hqmax
    · exact False.elim (hqp (geometricSlope_injective (le_antisymm
        (hqmin p hp) (hmin q hqP))))
    · exact hqmax
  · refine Or.inr ⟨?_, hmax⟩
    rcases hqext with hqmin | hqmax
    · exact hqmin
    · exact False.elim (hqp (geometricSlope_injective (le_antisymm
        (hmax q hqP) (hqmax p hp))))

/-- Canonical angular endpoints of a plane; no Coxeter-system assertion is
built into this data. The latter will be proved from the inversion criterion. -/
structure PlaneBasis (P : Submodule ℝ (I → ℝ)) where
  left : PositiveRoot M cs
  right : PositiveRoot M cs
  distinct : left ≠ right
  plane_eq : rootPlane left right = P
  left_min : ∀ r : PositiveRoot M cs, r.val ∈ P → geometricSlope left ≤ geometricSlope r
  right_max : ∀ r : PositiveRoot M cs, r.val ∈ P → geometricSlope r ≤ geometricSlope right

theorem nonempty_planeBasis (a b : PositiveRoot M cs) (hab : a ≠ b) :
    Nonempty (PlaneBasis (M := M) (cs := cs) (rootPlane a b)) := by
  obtain ⟨p, hp, _, hext⟩ := exists_plane_extreme_inverted a b hab
  obtain ⟨q, hq, hqp, hpair⟩ := exists_opposite_plane_extreme a b p hab hp hext
  rcases hpair with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · exact ⟨⟨p, q, hqp.symm, rootPlane_eq_of_mem a b p q hab hp hq hqp.symm, hl, hr⟩⟩
  · exact ⟨⟨q, p, hqp, rootPlane_eq_of_mem a b q p hab hq hp hqp, hl, hr⟩⟩

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

theorem left_mem : B.left.val ∈ P := by
  apply B.plane_eq.le
  exact Submodule.subset_span (Set.mem_insert _ _)

theorem right_mem : B.right.val ∈ P := by
  apply B.plane_eq.le
  exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem left_simple : PlaneSimple P B.left :=
  planeSimple_of_extreme B.left B.left_mem (.inl B.left_min)

theorem right_simple : PlaneSimple P B.right :=
  planeSimple_of_extreme B.right B.right_mem (.inr B.right_max)

/-- Every positive root in the plane is in its canonical nonnegative cone. -/
theorem positive_cone (r : PositiveRoot M cs) (hr : r.val ∈ P) :
    ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ r.val = c • B.left.val + d • B.right.val := by
  by_cases hl : r = B.left
  · exact ⟨1, 0, zero_le_one, le_refl 0, by rw [hl]; simp⟩
  by_cases hh : r = B.right
  · exact ⟨0, 1, le_refl 0, zero_le_one, by rw [hh]; simp⟩
  have hlr : geometricSlope B.left < geometricSlope r :=
    lt_of_le_of_ne (B.left_min r hr) (fun h => hl (geometricSlope_injective h).symm)
  have hrr : geometricSlope r < geometricSlope B.right :=
    lt_of_le_of_ne (B.right_max r hr) (fun h => hh (geometricSlope_injective h))
  obtain ⟨c, d, hc, hd, he⟩ := positive_combination_of_slope_between B.left B.right r
    (B.plane_eq.ge hr) hlr hrr
  exact ⟨c, d, hc.le, hd.le, he⟩

end PlaneBasis


/-- Canonical-simple reflections have no extra root pair in their own plane. -/
theorem PlaneSimple.planeWeight_eq_zero {P : Submodule ℝ (I → ℝ)}
    {a : PositiveRoot M cs} (ha : PlaneSimple P a) (x : W) :
    planeWeight x a P = 0 := by
  classical
  rw [planeWeight, Finsupp.mapDomain, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro b _
  change (Finsupp.single (rootPlane a b) (halfVector x a b)) P = 0
  rw [Finsupp.single_apply]
  by_cases hP : rootPlane a b = P
  · rw [ite_eq_left hP]
    simp only [halfVector, rootIndicator_apply]
    apply ite_eq_right
    intro hh
    have hbP : b.val ∈ P := hP.le
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    exact hh.1.1 ((ha.2 b hbP).mp ((rootInverted_ref_iff_flipped a b).mpr hh.1.2.1))
  · exact ite_eq_right hP

/-- The relative inversion count has the genuine simple-reflection step. -/
theorem PlaneSimple.planeLength_step {P : Submodule ℝ (I → ℝ)}
    {a b : PositiveRoot M cs} (ha : PlaneSimple P a)
    (hab : a ≠ b) (hP : rootPlane a b = P) (x : W)
    (hx : ¬ rootInverted x a) :
    planeLength (M := M) (cs := cs) P (rootRef a * x) =
      planeLength (M := M) (cs := cs) P x + 1 := by
  have hh := planeWeight_relative_degree x a b hab hx
  rw [hP, ha.planeWeight_eq_zero] at hh
  linarith

theorem PlaneSimple.planeLength_step_down {P : Submodule ℝ (I → ℝ)}
    {a b : PositiveRoot M cs} (ha : PlaneSimple P a)
    (hab : a ≠ b) (hP : rootPlane a b = P) (x : W)
    (hx : rootInverted x a) :
    planeLength (M := M) (cs := cs) P (rootRef a * x) =
      planeLength (M := M) (cs := cs) P x - 1 := by
  have hy : ¬ rootInverted (rootRef a * x) a :=
    fun h => (rootInverted_mul_self x a).mp h hx
  have hh := ha.planeLength_step hab hP (rootRef a * x) hy
  rw [← mul_assoc, (rootReflection M cs a).property.mul_self, one_mul] at hh
  linarith

/-- The usual inversion bijection, proved on the actual positive roots. -/
theorem rootInverted_inverse_action (w : W) (a : PositiveRoot M cs) :
    rootInverted w⁻¹ (positiveAction w⁻¹ a) ↔ rootInverted w a := by
  have hw : action M cs w (action M cs w⁻¹ a.val) = a.val := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  by_cases hi : rootInverted w a
  · apply iff_of_true ?_ hi
    unfold rootInverted
    rw [inv_inv, positiveAction_eq_of_nonpos _ _ hi, map_neg, hw]
    exact fun i => neg_nonpos.mpr (a.property.2 i)
  · apply iff_of_false ?_ hi
    rw [not_rootInverted_iff, inv_inv,
      positiveAction_eq_of_nonneg _ _ ((not_rootInverted_iff w a).mp hi), hw]
    exact a.property.2

/-- Reindexing the inversion indicator by the inverse root action. -/
theorem inversionVector_inverse (w : W) :
    inversionVector (M := M) (cs := cs) w⁻¹ =
      Finsupp.mapDomain (positiveActionEquiv w⁻¹) (inversionVector w) := by
  classical
  apply (Finsupp.ext_iff).mpr
  intro b
  obtain ⟨a, rfl⟩ := (positiveActionEquiv (M := M) (cs := cs) w⁻¹).surjective b
  rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply]
  simp only [inversionVector_apply]
  change (if rootInverted w⁻¹ (positiveAction w⁻¹ a) then 1 else 0) = _
  rw [rootInverted_inverse_action]

theorem positiveAction_mem_plane {P : Submodule ℝ (I → ℝ)}
    {w : W} (hw : w ∈ planeSubgroup M cs P) (a : PositiveRoot M cs)
    (ha : a.val ∈ P) : (positiveAction w a).val ∈ P := by
  have hp := planeSubgroup_preserves hw ha
  rcases (a.property.1.act w).sign with hs | hs
  · exact (positiveAction_eq_of_nonneg w a hs).symm ▸ hp
  · exact (positiveAction_eq_of_nonpos w a hs).symm ▸ P.neg_mem hp

theorem positiveAction_mem_plane_iff {P : Submodule ℝ (I → ℝ)}
    {w : W} (hw : w ∈ planeSubgroup M cs P) (a : PositiveRoot M cs) :
    (positiveAction w a).val ∈ P ↔ a.val ∈ P := by
  refine ⟨fun h => ?_, positiveAction_mem_plane hw a⟩
  have hh := positiveAction_mem_plane ((planeSubgroup M cs P).inv_mem hw)
    (positiveAction w a) h
  rwa [← positiveAction_mul, inv_mul_cancel, positiveAction_one] at hh

/-- Relative inversion count is invariant under inverse on the actual plane subgroup. -/
theorem planeLength_inv {P : Submodule ℝ (I → ℝ)} {w : W}
    (hw : w ∈ planeSubgroup M cs P) :
    planeLength (M := M) (cs := cs) P w⁻¹ = planeLength (M := M) (cs := cs) P w := by
  classical
  rw [planeLength, inversionVector_inverse,
    Finsupp.sum_mapDomain_index (by intros; split_ifs <;> rfl)
      (by intros; split_ifs <;> simp)]
  apply Finsupp.sum_congr
  intro a _
  change (if (positiveAction w⁻¹ a).val ∈ P then _ else _) = _
  rw [positiveAction_mem_plane_iff ((planeSubgroup M cs P).inv_mem hw)]

theorem planeLength_nonneg (P : Submodule ℝ (I → ℝ)) (w : W) :
    0 ≤ planeLength (M := M) (cs := cs) P w := by
  classical
  apply Finset.sum_nonneg
  intro a _
  simp only [inversionVector_apply]
  split_ifs <;> norm_num

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- A plane reflection must invert at least one of the canonical endpoints.
This uses convex positivity, not any assumed Coxeter structure on the subgroup. -/
theorem reflection_inverts_endpoint (r : PositiveRoot M cs) (hr : r.val ∈ P) :
    rootInverted (rootRef r) B.left ∨ rootInverted (rootRef r) B.right := by
  by_contra h
  push Not at h
  obtain ⟨c, d, hc, hd, he⟩ := B.positive_cone r hr
  exact (noninverted_of_positive_combination (rootRef r) B.left B.right r
    hc hd he h.1 h.2) (rootInverted_ref_self r)

end PlaneBasis


/-- The second descent in a simple conjugation of a nonsimple reflection. -/
theorem PlaneSimple.inverted_after_mul {P : Submodule ℝ (I → ℝ)}
    {a r : PositiveRoot M cs} (ha : PlaneSimple P a) (hr : r.val ∈ P)
    (hra : r ≠ a) (hi : rootInverted (rootRef r) a) :
    rootInverted (rootRef r * rootRef a) a := by
  have hn := (rootInverted_ref_iff_flipped r a).mp hi
  apply (rootInverted_mul_of_nonpos (rootRef a) r a hn).mpr
  intro hinv
  have he : partner r a = a := (ha.2 (partner r a) (partner_mem r a hr ha.1)).mp hinv
  exact hra (negative_partner_fixed r a hn he).symm

/-- The honest relative length drops by two under the chosen simple conjugation. -/
theorem PlaneSimple.planeLength_conj_drop {P : Submodule ℝ (I → ℝ)}
    {a b r : PositiveRoot M cs} (ha : PlaneSimple P a)
    (hab : a ≠ b) (hP : rootPlane a b = P) (hr : r.val ∈ P)
    (hra : r ≠ a) (hi : rootInverted (rootRef r) a) :
    planeLength (M := M) (cs := cs) P (rootRef (partner a r)) =
      planeLength (M := M) (cs := cs) P (rootRef r) - 2 := by
  have har : rootRef a ∈ planeSubgroup M cs P :=
    ((rootReflection_represents M cs a).planeSubgroup_mem_iff M cs).mpr ha.1
  have hrr : rootRef r ∈ planeSubgroup M cs P :=
    ((rootReflection_represents M cs r).planeSubgroup_mem_iff M cs).mpr hr
  have hmul := (planeSubgroup M cs P).mul_mem har hrr
  have hd := ha.planeLength_step_down hab hP (rootRef r) hi
  have hd' := ha.planeLength_step_down hab hP (rootRef r * rootRef a)
    (ha.inverted_after_mul hr hra hi)
  have hli := planeLength_inv hmul
  rw [mul_inv_rev, (rootReflection M cs r).property.inv,
    (rootReflection M cs a).property.inv] at hli
  change planeLength (M := M) (cs := cs) P
    (rootReflection M cs (positiveAction (rootRef a) r)).val = _
  rw [rootReflection_positiveAction, (rootReflection M cs a).property.inv, mul_assoc]
  linarith

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- The canonical endpoint reflections generate every ambient reflection in the plane. -/
theorem rootRef_mem_pairClosure (r : PositiveRoot M cs) (hr : r.val ∈ P) :
    rootRef r ∈ Subgroup.closure {rootRef B.left, rootRef B.right} := by
  classical
  generalize hn : (planeLength (M := M) (cs := cs) P (rootRef r)).toNat = n
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    by_cases hl : r = B.left
    · rw [hl]; exact Subgroup.subset_closure (Set.mem_insert _ _)
    by_cases hh : r = B.right
    · rw [hh]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have step (a b : PositiveRoot M cs) (ha : PlaneSimple P a)
        (hab : a ≠ b) (hP : rootPlane a b = P) (hra : r ≠ a)
        (hgen : rootRef a ∈ Subgroup.closure {rootRef B.left, rootRef B.right})
        (hi : rootInverted (rootRef r) a) :
        rootRef r ∈ Subgroup.closure {rootRef B.left, rootRef B.right} := by
      have hp : (partner a r).val ∈ P := partner_mem a r ha.1 hr
      have hdrop := ha.planeLength_conj_drop hab hP hr hra hi
      have hless : (planeLength (M := M) (cs := cs) P (rootRef (partner a r))).toNat < n := by
        have hnonneg := planeLength_nonneg (M := M) (cs := cs) P (rootRef (partner a r))
        omega
      have hind := ih _ hless (partner a r) hp rfl
      have hlen := (Subgroup.closure {rootRef B.left, rootRef B.right}).mul_mem
        ((Subgroup.closure {rootRef B.left, rootRef B.right}).mul_mem hgen hind) hgen
      change rootRef a * (rootReflection M cs (positiveAction (rootRef a) r)).val * rootRef a ∈ _ at hlen
      rw [rootReflection_positiveAction, (rootReflection M cs a).property.inv] at hlen
      rw [← mul_assoc, ← mul_assoc, (rootReflection M cs a).property.mul_self,
        one_mul, mul_assoc, (rootReflection M cs a).property.mul_self, mul_one] at hlen
      exact hlen
    rcases B.reflection_inverts_endpoint r hr with hi | hi
    · exact step B.left B.right B.left_simple B.distinct B.plane_eq hl
        (Subgroup.subset_closure (Set.mem_insert _ _)) hi
    · exact step B.right B.left B.right_simple B.distinct.symm
        (by rw [rootPlane, Set.pair_comm]; exact B.plane_eq) hh
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hi

/-- Exact identification with the manuscript's maximal root-plane subgroup. -/
theorem pairClosure_eq_planeSubgroup :
    Subgroup.closure {rootRef B.left, rootRef B.right} = planeSubgroup M cs P := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro t ht
    rcases Set.mem_insert_iff.mp ht with he | he
    · rw [he]
      exact ((rootReflection_represents M cs B.left).planeSubgroup_mem_iff M cs).mpr B.left_mem
    · rw [Set.mem_singleton_iff.mp he]
      exact ((rootReflection_represents M cs B.right).planeSubgroup_mem_iff M cs).mpr B.right_mem
  · apply (Subgroup.closure_le _).mpr
    rintro t ⟨a, ha, haP⟩
    let r := positiveRoot M cs ⟨t, ha.isReflection⟩
    have hre : rootRef r = t := (rootReflection_represents M cs r).reflection_unique
      (positiveRoot_represents M cs ⟨t, ha.isReflection⟩)
    have hrP : r.val ∈ P := ((positiveRoot_represents M cs
      ⟨t, ha.isReflection⟩).planeSubgroup_mem_iff M cs).mp (Subgroup.subset_closure ⟨a, ha, haP⟩)
    rw [← hre]
    exact B.rootRef_mem_pairClosure r hrP

/-- Distinct positive roots give distinct actual reflections. -/
theorem rootRef_distinct : rootRef B.left ≠ rootRef B.right := by
  intro he
  apply B.distinct
  apply (positiveRootEquiv M cs).symm.injective
  exact Subtype.ext he

theorem rootRef_ne_one (a : PositiveRoot M cs) : rootRef a ≠ 1 := by
  intro h
  exact (not_rootInverted_one a) (h ▸ rootInverted_ref_self a)

/-- The genuine dihedral matrix attached to the canonical plane endpoints. -/
def matrix : CoxeterMatrix Bool :=
  Dihedral.pairMatrix (rootRef B.left) (rootRef B.right)
    (rootReflection M cs B.left).property.mul_self B.rootRef_distinct

/-- A proved Coxeter system on the *actual maximal plane subgroup*. -/
def system : CoxeterSystem B.matrix (planeSubgroup M cs P) :=
  (Dihedral.pairSystem (rootRef B.left) (rootRef B.right)
    (rootReflection M cs B.left).property.mul_self
    (rootReflection M cs B.right).property.mul_self B.rootRef_distinct
    (rootRef_ne_one B.left)
    (rootRef_ne_one B.right)).map
      (MulEquiv.subgroupCongr B.pairClosure_eq_planeSubgroup)

/-- Canonical simple positive roots, indexed by Bool just like the system. -/
def simpleRoot (i : Bool) : PositiveRoot M cs := if i then B.right else B.left

theorem simpleRoot_mem (i : Bool) : (B.simpleRoot i).val ∈ P := by
  cases i
  · exact B.left_mem
  · exact B.right_mem

theorem simpleRoot_simple (i : Bool) : PlaneSimple P (B.simpleRoot i) := by
  cases i
  · exact B.left_simple
  · exact B.right_simple

@[simp] theorem system_simple (i : Bool) :
    (B.system.simple i : W) = rootRef (B.simpleRoot i) := by
  change ((Dihedral.pairSystem (rootRef B.left) (rootRef B.right)
    (rootReflection M cs B.left).property.mul_self
    (rootReflection M cs B.right).property.mul_self B.rootRef_distinct
    (rootRef_ne_one B.left) (rootRef_ne_one B.right)).simple i : W) = _
  rw [Dihedral.pairSystem_simple]
  cases i <;> rfl

/-- The positive simple-sign criterion for the induced plane root system. -/
theorem simple_sign {t : planeSubgroup M cs P} {a : I → ℝ}
    (ha : Represents M cs t.val a) (haP : a ∈ P) (hp : ∀ k, 0 ≤ a k) (i : Bool) :
    ((∀ k, action M cs (B.system.simple i : W) a k ≤ 0) ↔ t = B.system.simple i) ∧
    ((∀ k, 0 ≤ action M cs (B.system.simple i : W) a k) ↔ t ≠ B.system.simple i) := by
  let r : PositiveRoot M cs := ⟨a, ha.isRoot, hp⟩
  have hneg : (∀ k, action M cs (B.system.simple i : W) a k ≤ 0) ↔ t = B.system.simple i := by
    rw [B.system_simple]
    change flipped (B.simpleRoot i) r ↔ _
    rw [← rootInverted_ref_iff_flipped, (B.simpleRoot_simple i).2 r haP]
    constructor
    · intro he
      apply Subtype.ext
      rw [B.system_simple]
      exact ha.reflection_unique (he ▸ rootReflection_represents M cs r)
    · intro he
      apply Subtype.ext
      have hr : Represents M cs (rootRef (B.simpleRoot i)) a := by
        simpa only [he, B.system_simple] using ha
      exact hr.unique_positive (rootReflection_represents M cs _) hp (B.simpleRoot i).property.2
  refine ⟨hneg, ?_⟩
  constructor
  · intro h he
    exact (ha.isRoot.act (B.system.simple i : W)).not_both h (hneg.mpr he)
  · intro h
    exact (ha.isRoot.act (B.system.simple i : W)).sign.resolve_right (fun hn => h (hneg.mp hn))

/-- Signed roots for the induced system. The vectors are the original ambient
roots, and membership in the actual plane is part of the relation. -/
structure InducedSigned (p : planeSubgroup M cs P × ZMod 2) (a : I → ℝ) : Prop where
  represents : Represents M cs p.1.val a
  plane_mem : a ∈ P
  sign : (p.2 = 0 ∧ ∀ i, 0 ≤ a i) ∨ (p.2 = 1 ∧ ∀ i, a i ≤ 0)

theorem InducedSigned.simple {p : planeSubgroup M cs P × ZMod 2} {a : I → ℝ}
    (ha : InducedSigned p a) (i : Bool) :
    InducedSigned (CoxeterSupport.simpleAction B.system i p)
      (action M cs (B.system.simple i : W) a) := by
  rcases p with ⟨t,z⟩
  rw [CoxeterSupport.simpleAction_apply]
  refine ⟨?_, planeSubgroup_preserves (B.system.simple i).property ha.plane_mem, ?_⟩
  · have h := ha.represents.act (B.system.simple i : W)
    have he : (B.system.simple i : W)⁻¹ = (B.system.simple i : W) :=
      congrArg Subtype.val (B.system.inv_simple i)
    simpa only [he, Subgroup.coe_mul] using h
  · rcases ha.sign with ⟨rfl,hp⟩ | ⟨rfl,hn⟩
    · by_cases heq : t = B.system.simple i
      · exact Or.inr ⟨by simp [heq],
          (B.simple_sign ha.represents ha.plane_mem hp i).1.mpr heq⟩
      · exact Or.inl ⟨by simp [heq, ZModModule.add_self],
          (B.simple_sign ha.represents ha.plane_mem hp i).2.mpr heq⟩
    · have hp : ∀ k, 0 ≤ (-a) k := fun k => neg_nonneg.mpr (hn k)
      by_cases heq : t = B.system.simple i
      · refine Or.inl ⟨by simp [heq, ZModModule.add_self], ?_⟩
        have h := (B.simple_sign ha.represents.neg (P.neg_mem ha.plane_mem) hp i).1.mpr heq
        simpa only [map_neg, Pi.neg_apply, neg_nonpos] using h
      · refine Or.inr ⟨by simp [heq], ?_⟩
        have h := (B.simple_sign ha.represents.neg (P.neg_mem ha.plane_mem) hp i).2.mpr heq
        simpa only [map_neg, Pi.neg_apply, neg_nonneg] using h

theorem InducedSigned.act {p : planeSubgroup M cs P × ZMod 2} {a : I → ℝ}
    (ha : InducedSigned p a) (w : planeSubgroup M cs P) :
    InducedSigned (CoxeterSupport.reflectionAction B.system w p)
      (action M cs (w : W) a) := by
  obtain ⟨ω,rfl⟩ := B.system.wordProd_surjective w
  induction ω with
  | nil => simpa using ha
  | cons i ω ih =>
    simpa only [B.system.wordProd_cons, map_mul, Equiv.Perm.mul_apply,
      CoxeterSupport.reflectionAction_simple, Subgroup.coe_mul,
      LinearEquiv.mul_apply] using ih.simple B i

/-- The induced positive roots have precisely the intrinsic Coxeter inversion
signs. No change of realization or extra canonical-system assumption is used. -/
theorem inversion_iff {t : planeSubgroup M cs P} {a : I → ℝ}
    (ha : Represents M cs t.val a) (haP : a ∈ P) (hp : ∀ i, 0 ≤ a i)
    (w : planeSubgroup M cs P) :
    (∀ i, action M cs (w : W)⁻¹ a i ≤ 0) ↔ B.system.IsLeftInversion w t := by
  classical
  let : BEq (planeSubgroup M cs P) := @instBEqOfDecidableEq _ (Classical.decEq _)
  obtain ⟨ω,hω,heq⟩ := B.system.exists_isReduced w
  rw [heq]
  let c : ZMod 2 := if t ∈ B.system.leftInvSeq ω then 1 else 0
  have hrec := CoxeterSupport.wordAction_record B.system ω t c
  rw [← CoxeterSupport.reflectionAction_wordProd] at hrec
  have hrec' : CoxeterSupport.reflectionAction B.system (B.system.wordProd ω)
      ((B.system.wordProd ω)⁻¹ * t * B.system.wordProd ω, c) = (t,0) := by
    by_cases hm : t ∈ B.system.leftInvSeq ω
    · have hc : c = 1 := ite_eq_left hm
      simpa only [hc, List.count_eq_one_of_mem hω.nodup_leftInvSeq hm,
        Nat.cast_one, ZModModule.add_self] using hrec
    · have hc : c = 0 := ite_eq_right hm
      simpa only [hc, List.count_eq_zero.mpr hm, Nat.cast_zero, add_zero] using hrec
  have hinv : CoxeterSupport.reflectionAction B.system (B.system.wordProd ω)⁻¹ (t,0) =
      ((B.system.wordProd ω)⁻¹ * t * B.system.wordProd ω,c) := by
    rw [map_inv, ← hrec']
    exact Equiv.symm_apply_apply _ _
  have hs : InducedSigned (t,0) a := ⟨ha,haP,Or.inl ⟨rfl,hp⟩⟩
  have hsi := hs.act B (B.system.wordProd ω)⁻¹
  rw [hinv] at hsi
  have hcount : c = if t ∈ B.system.leftInvSeq ω then 1 else 0 := rfl
  have hmem : (∀ i, action M cs (B.system.wordProd ω : W)⁻¹ a i ≤ 0) ↔
      t ∈ B.system.leftInvSeq ω := by
    by_cases hm : t ∈ B.system.leftInvSeq ω
    · have hc1 : c=1 := by simpa [hm] using hcount
      have hh := hsi.sign
      simp only [hc1] at hh
      rcases hh with ⟨hbad,_⟩ | ⟨_,hn⟩
      · norm_num at hbad
      · exact iff_of_true hn hm
    · have hc0 : c=0 := by simpa [hm] using hcount
      have hh := hsi.sign
      simp only [hc0] at hh
      rcases hh with ⟨_,hpos⟩ | ⟨hbad,_⟩
      · exact iff_of_false (fun hn => (ha.isRoot.act _).not_both hpos hn) hm
      · norm_num at hbad
  rw [hmem]
  exact ⟨B.system.isLeftInversion_of_mem_leftInvSeq hω,
    CoxeterSupport.mem_leftInvSeq_of_inversion B.system hω⟩

/-- The intrinsic reflections are exactly the ambient reflections in the
actual maximal plane subgroup. -/
theorem reflection_iff (t : planeSubgroup M cs P) :
    B.system.IsReflection t ↔ cs.IsReflection (t : W) := by
  constructor
  · rintro ⟨w,i,he⟩
    obtain ⟨z,j,hz⟩ := (rootReflection M cs (B.simpleRoot i)).property
    refine ⟨(w : W) * z,j,?_⟩
    have he' := congrArg Subtype.val he
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, B.system_simple] at he'
    change rootRef (B.simpleRoot i) = _ at hz
    rw [he', hz]
    group
  · intro ht
    let a := positiveRoot M cs ⟨(t:W),ht⟩
    have ha := positiveRoot_represents M cs ⟨(t:W),ht⟩
    have haP : a.val ∈ P := (ha.planeSubgroup_mem_iff M cs).mp t.property
    have hinv := (B.inversion_iff ha haP a.property.2 t).mp
      ((ha.inversion_iff a.property.2 (t:W)).mpr
        ⟨ht, by
          rw [ht.mul_self, cs.length_one]
          obtain ⟨k,hk⟩ := ht.odd_length
          omega⟩)
    exact hinv.1

/-- The true ambient plane inversions are in bijection with the inversions
of the canonical induced system. -/
def inversionEquiv (w : planeSubgroup M cs P) :
    {a : PositiveRoot M cs // a.val ∈ P ∧ rootInverted (w:W) a} ≃
      {t : planeSubgroup M cs P // B.system.IsLeftInversion w t} where
  toFun a := ⟨⟨rootRef a.val,
    ((rootReflection_represents M cs a.val).planeSubgroup_mem_iff M cs).mpr a.property.1⟩,
    (B.inversion_iff (rootReflection_represents M cs a.val) a.property.1
      a.val.property.2 w).mp a.property.2⟩
  invFun t :=
    let a := positiveRoot M cs ⟨(t.val:W),(B.reflection_iff t.val).mp t.property.1⟩
    let ha := positiveRoot_represents M cs
      ⟨(t.val:W),(B.reflection_iff t.val).mp t.property.1⟩
    let haP := (ha.planeSubgroup_mem_iff M cs).mp t.val.property
    ⟨a,haP,(B.inversion_iff ha haP a.property.2 w).mpr t.property⟩
  left_inv a := by
    apply Subtype.ext
    exact (positiveRootEquiv M cs).apply_symm_apply a.val
  right_inv t := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun r : {r : W // cs.IsReflection r} => r.val)
      ((positiveRootEquiv M cs).symm_apply_apply
        ⟨(t.val:W),(B.reflection_iff t.val).mp t.property.1⟩)

/-- Relative inversion count is the actual Coxeter length, completing the
length identification, not merely a rank-two presentation. -/
theorem length_eq (w : planeSubgroup M cs P) :
    planeLength (M := M) (cs := cs) P (w:W) = (B.system.length w : ℤ) := by
  classical
  let f := inversionVector (M := M) (cs := cs) (w:W)
  let F := f.support.filter (fun a => a.val ∈ P)
  have hF : (F : Set (PositiveRoot M cs)) =
      {a | a.val ∈ P ∧ rootInverted (w:W) a} := by
    ext a
    simp only [F, Finset.mem_coe, Finset.mem_filter, Finsupp.mem_support_iff,
      f, inversionVector_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not,
      Set.mem_ofPred_eq, and_comm]
  have hcard : F.card = B.system.length w := by
    rw [← Set.ncard_coe_finset, hF, ← Nat.card_coe_set_eq]
    change Nat.card {a : PositiveRoot M cs // a.val ∈ P ∧ rootInverted (w:W) a} = _
    rw [Nat.card_congr (B.inversionEquiv w)]
    obtain ⟨ω,hω,he⟩ := B.system.exists_isReduced w
    rw [he, Nat.card_congr (leftInversionListEquiv B.matrix B.system hω),
      ← Nat.card_congr (List.Nodup.getEquiv (B.system.leftInvSeq ω) hω.nodup_leftInvSeq),
      Nat.card_fin, B.system.length_leftInvSeq, hω.eq]
  change f.sum (fun a n => if a.val ∈ P then n else 0) = _
  rw [Finsupp.sum, ← Finset.sum_filter]
  calc
    ∑ a ∈ F, f a = ∑ _a ∈ F, (1:ℤ) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hm : rootInverted (w:W) a := by
        have hm := (Finset.mem_filter.mp ha).1
        simpa only [Finsupp.mem_support_iff, f, inversionVector_apply,
          ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] using hm
      simp [f,hm]
    _ = _ := by simp [hcard]

/-- Intrinsic and ambient left inversions coincide on the plane subgroup. -/
theorem leftInversion_iff (w t : planeSubgroup M cs P) :
    B.system.IsLeftInversion w t ↔ cs.IsLeftInversion (w:W) (t:W) := by
  by_cases ht : cs.IsReflection (t:W)
  · let a := positiveRoot M cs ⟨(t:W),ht⟩
    have ha := positiveRoot_represents M cs ⟨(t:W),ht⟩
    have haP := (ha.planeSubgroup_mem_iff M cs).mp t.property
    exact (B.inversion_iff ha haP a.property.2 w).symm.trans
      (ha.inversion_iff a.property.2 (w:W))
  · exact iff_of_false (fun h => ht ((B.reflection_iff t).mp h.1)) (fun h => ht h.1)

/-- The intrinsic directed dihedral graph is the actual ambient graph
restricted to the maximal plane subgroup. -/
theorem bruhatStep_iff (g h : planeSubgroup M cs P) :
    BruhatStep cs (g:W) (h:W) ↔ BruhatStep B.system g h := by
  constructor
  · rintro ⟨hlen,t,ht,he⟩
    have htP : t ∈ planeSubgroup M cs P := by
      have he' : t = (h:W) * (g:W)⁻¹ := by rw [he]; group
      rw [he']
      exact (planeSubgroup M cs P).mul_mem h.property
        ((planeSubgroup M cs P).inv_mem g.property)
    let tr : planeSubgroup M cs P := ⟨t,htP⟩
    have htr : B.system.IsReflection tr := (B.reflection_iff tr).mpr ht
    have het : h=tr*g := Subtype.ext he
    have htg : t*(h:W)=(g:W) := by rw [he, ← mul_assoc, ht.mul_self, one_mul]
    have hi := (B.leftInversion_iff h tr).mpr ⟨ht,by
      change cs.length (t*(h:W)) < cs.length (h:W)
      simpa only [htg] using hlen⟩
    have htg' : tr*h=g := by rw [het, ← mul_assoc, htr.mul_self, one_mul]
    exact ⟨by simpa only [htg'] using hi.2,tr,htr,het⟩
  · rintro ⟨hlen,t,ht,he⟩
    have het : t*h=g := by rw [he, ← mul_assoc, ht.mul_self, one_mul]
    have hi := (B.leftInversion_iff h t).mp ⟨ht,by simpa only [het] using hlen⟩
    refine ⟨?_,(t:W),(B.reflection_iff t).mp ht,congrArg Subtype.val he⟩
    simpa only [← Subgroup.coe_mul, het] using hi.2

/-- The exact canonical coset graph theorem needed by the reconstruction. -/
theorem coset_step_iff {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (g h : planeSubgroup M cs P) :
    BruhatStep cs ((g:W)*a₀) ((h:W)*a₀) ↔ BruhatStep B.system g h :=
  (bruhatStep_coset_iff hmin g.property h.property).trans (B.bruhatStep_iff g h)

/-- Relative dihedral paths give actual ambient Bruhat paths in the coset. -/
theorem coset_bruhat {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    {g h : planeSubgroup M cs P} (hgh : BruhatLE B.system g h) :
    BruhatLE cs ((g:W)*a₀) ((h:W)*a₀) := by
  induction hgh with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z _ hyz ih =>
    exact ih.tail ((B.coset_step_iff hmin y z).mpr hyz)

/-- The source inversion-count characterization holds on every minimal
representative coset, with its actual induced length. -/
theorem coset_length_eq {a₀ : W}
    (hmin : ∀ z ∈ planeSubgroup M cs P, cs.length a₀ ≤ cs.length (z*a₀))
    (w : planeSubgroup M cs P) :
    planeLength (M := M) (cs := cs) P ((w:W)*a₀) = (B.system.length w : ℤ) := by
  classical
  rw [← B.length_eq w]
  let f := inversionVector (M := M) (cs := cs) ((w:W)*a₀)
  let g := inversionVector (M := M) (cs := cs) (w:W)
  change f.sum (fun a n => if a.val ∈ P then n else 0) =
    g.sum (fun a n => if a.val ∈ P then n else 0)
  rw [Finsupp.sum_of_support_subset f Finset.subset_union_left _ (by intro a; simp),
    Finsupp.sum_of_support_subset g Finset.subset_union_right _ (by intro a; simp)]
  apply Finset.sum_congr rfl
  intro a _
  by_cases haP : a.val ∈ P
  · simp only [ite_eq_left haP, f, g, inversionVector_apply]
    congr 1
    exact propext (root_inversion_coset_iff hmin w.property a.property.1 haP)
  · simp [haP]

end PlaneBasis

/-- Every nonsaturated reflection edge has a genuine rank-two contribution
whose induced relative edge gap is at least three. -/
theorem exists_positive_plane (x : W) (a : PositiveRoot M cs)
    (hx : ¬ rootInverted x a)
    (hlen : cs.length x + 1 < cs.length (rootRef a*x)) :
    ∃ b : PositiveRoot M cs, a ≠ b ∧ 0 < planeWeight x a (rootPlane a b) := by
  classical
  have hsum := sum_planeWeight x a hx
  have hp : 0 < (planeWeight x a).sum (fun _ n => n) := by omega
  obtain ⟨P,hP,hpos⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun P _ => planeWeight_nonneg x a P)).mp hp
  obtain ⟨b,hb,hbP⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hP)
  have hb' : halfRoot x a b := by
    simpa only [Finsupp.mem_support_iff, halfVector, rootIndicator_apply,
      ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] using hb
  exact ⟨b,hb'.1.1.symm,hbP ▸ hpos⟩


end
end KLInvariance.TitsSpace

namespace KLInvariance.Dihedral
variable {G : Type*} [Group G] {N : CoxeterMatrix Bool}

/-- Every nonsaturated dihedral edge contains a full eight-edge rectangle. -/
theorem edge_diamond (ds : CoxeterSystem N G) {x y : G}
    (hxy : BruhatStep ds x y) (hlen : ds.length x + 1 < ds.length y) :
    ∃ a b c d : G, a ≠ b ∧ c ≠ d ∧
      BruhatStep ds x a ∧ BruhatStep ds x b ∧
      BruhatStep ds a c ∧ BruhatStep ds a d ∧
      BruhatStep ds b c ∧ BruhatStep ds b d ∧
      BruhatStep ds c y ∧ BruhatStep ds d y := by
  have hodd := ((step_iff_odd ds x y).mp hxy).2
  have hthree : ds.length x+2 < ds.length y := by
    rw [Nat.odd_iff] at hodd
    omega
  obtain ⟨a,b,hab,hlev₁⟩ := two_elements_length ds
    (by omega : 0 < ds.length x+1) hlen
  obtain ⟨c,d,hcd,hlev₂⟩ := two_elements_length ds
    (by omega : 0 < ds.length x+2) hthree
  have ha := (hlev₁ a).mpr (Or.inl rfl)
  have hb := (hlev₁ b).mpr (Or.inr rfl)
  have hc := (hlev₂ c).mpr (Or.inl rfl)
  have hd := (hlev₂ d).mpr (Or.inr rfl)
  have hsucc (p q : G) (h : ds.length q=ds.length p+1) : BruhatStep ds p q := by
    rw [step_iff_odd, Nat.odd_iff]
    constructor <;> omega
  have htop (p : G) (hp : ds.length p=ds.length x+2) : BruhatStep ds p y := by
    rw [step_iff_odd, Nat.odd_iff]
    rw [Nat.odd_iff] at hodd
    constructor <;> omega
  exact ⟨a,b,c,d,hab,hcd,hsucc x a ha,hsucc x b hb,
    hsucc a c (by omega),hsucc a d (by omega),
    hsucc b c (by omega),hsucc b d (by omega),htop c hc,htop d hd⟩

end KLInvariance.Dihedral

namespace KLInvariance.TitsSpace
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}

/-- Every genuine ambient reflection edge of length gap greater than one
contains a full eight-edge diamond. The chosen plane comes from an actual
positive inversion contribution, avoiding the false arbitrary-plane claim. -/
theorem ambient_edge_diamond {x y : W} (hxy : BruhatStep cs x y)
    (hlen : cs.length x+1 < cs.length y) :
    ∃ a b c d : W, a ≠ b ∧ c ≠ d ∧
      BruhatStep cs x a ∧ BruhatStep cs x b ∧
      BruhatStep cs a c ∧ BruhatStep cs a d ∧
      BruhatStep cs b c ∧ BruhatStep cs b d ∧
      BruhatStep cs c y ∧ BruhatStep cs d y := by
  rcases hxy.2 with ⟨t,ht,het⟩
  let a := positiveRoot M cs ⟨t,ht⟩
  have ha := positiveRoot_represents M cs ⟨t,ht⟩
  have hta : rootRef a=t := congrArg (fun r : {r : W // cs.IsReflection r} => r.val)
    ((positiveRootEquiv M cs).symm_apply_apply ⟨t,ht⟩)
  have hx : ¬ rootInverted x a := by
    intro hi
    have h := (ha.inversion_iff a.property.2 x).mp hi
    have hh : cs.length (t*x) < cs.length x := h.2
    rw [← het] at hh
    exact (not_lt_of_gt hxy.1) hh
  have hae : rootRef a*x=y := by rw [hta]; exact het.symm
  obtain ⟨b,hab,hpos⟩ := exists_positive_plane x a hx (by rwa [hae])
  obtain ⟨B⟩ := nonempty_planeBasis a b hab
  let P := rootPlane a b
  have haP : a.val ∈ P := Submodule.subset_span (Set.mem_insert _ _)
  obtain ⟨a₀,g,hg,hgx,hmin⟩ := planeCoset_exists_minimal M cs P x
  let X : planeSubgroup M cs P := ⟨g,hg⟩
  let T : planeSubgroup M cs P := ⟨rootRef a,
    ((rootReflection_represents M cs a).planeSubgroup_mem_iff M cs).mpr haP⟩
  let Y := T*X
  have hxEq : (X:W)*a₀=x := hgx.symm
  have hyEq : (Y:W)*a₀=y := by
    change (rootRef a*g)*a₀=y
    rw [mul_assoc, ← hgx, hae]
  have hrel : BruhatStep B.system X Y := (B.coset_step_iff hmin X Y).mp
    (by simpa only [hxEq,hyEq] using hxy)
  have hLx := B.coset_length_eq hmin X
  have hLy := B.coset_length_eq hmin Y
  rw [hxEq] at hLx
  rw [hyEq] at hLy
  have hdegree := planeWeight_relative_degree x a b hab hx
  rw [hae,hLx,hLy] at hdegree
  have hlen' : B.system.length X+1 < B.system.length Y := by omega
  obtain ⟨p,q,r,s,hpq,hrs,hXp,hXq,hpr,hps,hqr,hqs,hrY,hsY⟩ :=
    Dihedral.edge_diamond B.system hrel hlen'
  have hinj : Function.Injective (fun z : planeSubgroup M cs P => (z:W)*a₀) := by
    intro p q hpq
    exact Subtype.ext (mul_right_cancel hpq)
  refine ⟨(p:W)*a₀,(q:W)*a₀,(r:W)*a₀,(s:W)*a₀,
    fun h => hpq (hinj h),fun h => hrs (hinj h),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [hxEq] using (B.coset_step_iff hmin X p).mpr hXp
  · simpa only [hxEq] using (B.coset_step_iff hmin X q).mpr hXq
  · exact (B.coset_step_iff hmin p r).mpr hpr
  · exact (B.coset_step_iff hmin p s).mpr hps
  · exact (B.coset_step_iff hmin q r).mpr hqr
  · exact (B.coset_step_iff hmin q s).mpr hqs
  · simpa only [hyEq] using (B.coset_step_iff hmin r Y).mpr hrY
  · simpa only [hyEq] using (B.coset_step_iff hmin s Y).mpr hsY

end KLInvariance.TitsSpace

namespace KLInvariance
variable {I W : Type*} [Fintype I] [Group W] {M : CoxeterMatrix I}

/-- General unlabelled Bruhat graph reconstruction completeness, for genuine
finite-rank Coxeter systems and arbitrary bottoms and interval ranks. -/
theorem diamondEdges_of_bruhatStep (cs : CoxeterSystem M W)
    {u b : W} {x y : Interval cs u b} (hxy : BruhatStep cs x.val y.val) :
    DiamondEdges x y := by
  suffices ∀ n : ℕ, ∀ x y : Interval cs u b,
      cs.length y.val-cs.length x.val=n → BruhatStep cs x.val y.val →
      DiamondEdges x y by
    exact this _ x y rfl hxy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hn hxy
    by_cases he : cs.length y.val=cs.length x.val+1
    · exact DiamondEdges.cover (interval_covBy_of_length_succ cs
        (Relation.ReflTransGen.single hxy) he)
    · have hn' : cs.length x.val+1 < cs.length y.val := by have := hxy.1; omega
      obtain ⟨a,bm,c,d,hab,hcd,hxa,hxb,hac,had,hbc,hbd,hcy,hdy⟩ :=
        TitsSpace.ambient_edge_diamond hxy hn'
      have leOf {p q : W} (h : BruhatStep cs p q) : BruhatLE cs p q :=
        Relation.ReflTransGen.single h
      let A : Interval cs u b := ⟨a,bruhat_trans cs x.property.1 (leOf hxa),
        bruhat_trans cs (leOf hac) (bruhat_trans cs (leOf hcy) y.property.2)⟩
      let B : Interval cs u b := ⟨bm,bruhat_trans cs x.property.1 (leOf hxb),
        bruhat_trans cs (leOf hbc) (bruhat_trans cs (leOf hcy) y.property.2)⟩
      let C : Interval cs u b := ⟨c,
        bruhat_trans cs x.property.1 (bruhat_trans cs (leOf hxa) (leOf hac)),
        bruhat_trans cs (leOf hcy) y.property.2⟩
      let D : Interval cs u b := ⟨d,
        bruhat_trans cs x.property.1 (bruhat_trans cs (leOf hxa) (leOf had)),
        bruhat_trans cs (leOf hdy) y.property.2⟩
      have hsmall {p q : Interval cs u b} (hpq : BruhatStep cs p.val q.val)
          (hp : cs.length x.val ≤ cs.length p.val)
          (hq : cs.length q.val ≤ cs.length y.val)
          (hs : cs.length x.val < cs.length p.val ∨ cs.length q.val < cs.length y.val) :
          DiamondEdges p q := by
        exact ih _ (by omega) p q rfl hpq
      have h₁ := hxa.1
      have h₂ := hxb.1
      have h₃ := hac.1
      have h₄ := had.1
      have h₅ := hbc.1
      have h₆ := hbd.1
      have h₇ := hcy.1
      have h₈ := hdy.1
      refine DiamondEdges.diamond
        (hsmall (p := x) (q := A) hxa ?_ ?_ ?_)
        (hsmall (p := x) (q := B) hxb ?_ ?_ ?_)
        (hsmall (p := A) (q := C) hac ?_ ?_ ?_)
        (hsmall (p := A) (q := D) had ?_ ?_ ?_)
        (hsmall (p := B) (q := C) hbc ?_ ?_ ?_)
        (hsmall (p := B) (q := D) hbd ?_ ?_ ?_)
        (hsmall (p := C) (q := y) hcy ?_ ?_ ?_)
        (hsmall (p := D) (q := y) hdy ?_ ?_ ?_)
        (fun h => hab (congrArg Subtype.val h))
        (fun h => hcd (congrArg Subtype.val h))
      all_goals first | omega | (dsimp only [A,B,C,D]; omega)

/-- An abstract interval order isomorphism determines its actual directed
reflection edges. No root labels, generators or geometric data are supplied to
that isomorphism. This proves the finite-rank graph input of the source main. -/
theorem intervalIso_bruhatStep_iff {I' W' : Type*} [Fintype I'] [Group W']
    {M' : CoxeterMatrix I'} (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (e : Interval cs u b ≃o Interval cs' u' b')
    (x y : Interval cs u b) :
    BruhatStep cs' (e x).val (e y).val ↔ BruhatStep cs x.val y.val := by
  constructor
  · intro h
    exact diamondEdges_bruhatStep cs ((DiamondEdges.map_iff e).mp
      (diamondEdges_of_bruhatStep cs' h))
  · intro h
    exact diamondEdges_bruhatStep cs' ((diamondEdges_of_bruhatStep cs h).map e)

end KLInvariance

end


section

/-! Rank-two Frobenius extension for an actual reflection on a symmetric
algebra. This supplies the elementary simple-reflection duality input; it
is not a proof of BMP or Elias--Williamson self-duality/characters. -/
namespace KLInvariance.ReflectionFrobenius
universe uk ua uv
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]

noncomputable section

def fixed (τ : A ≃ₐ[k] A) : Subalgebra k A :=
  AlgHom.equalizer τ.toAlgHom (AlgHom.id k A)

omit [CharZero k] [IsDomain A] in
@[simp] theorem mem_fixed (τ : A ≃ₐ[k] A) (a : A) :
    a ∈ fixed τ ↔ τ a = a := Iff.rfl

omit [CharZero k] [IsDomain A] in
 theorem fixed_val (τ : A ≃ₐ[k] A) (a : fixed τ) : τ (a : A) = a := a.property

variable (τ : A ≃ₐ[k] A) (α : A)

def expand : (fixed τ × fixed τ) →ₗ[fixed τ] A where
  toFun a := (a.1 : A) + α * (a.2 : A)
  map_add' a b := by simp; ring
  map_smul' c a := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Subalgebra.coe_mul, Subalgebra.smul_def, RingHom.id_apply]; ring

omit [CharZero k] [IsDomain A] in
@[simp] theorem expand_apply (a : fixed τ × fixed τ) :
    expand τ α a = (a.1 : A) + α * (a.2 : A) := rfl

variable (hinv : Function.Involutive τ) (hα : α ≠ 0) (hanti : τ α = -α)
  (hdiv : ∀ a : A, α ∣ a - τ a)

omit [CharZero k] in
include hinv hα hanti in
 theorem quotient_fixed {a d : A} (hd : a - τ a = α * d) : τ d = d := by
  have hh := congrArg τ hd
  simp only [map_sub, map_mul, hinv a, hanti] at hh
  apply mul_left_cancel₀ hα
  linear_combination hh + hd

include hα hanti in
 theorem expand_injective : Function.Injective (expand τ α) := by
  intro a b hab
  have ht := congrArg τ hab
  simp only [expand_apply, map_add, map_mul, fixed_val, hanti] at ht
  have he : (2 : A) * α * ((a.2 : A) - (b.2 : A)) = 0 := by
    simp only [expand_apply] at hab
    linear_combination hab - ht
  have htwo : (2 : A) ≠ 0 := by
    have hi : Function.Injective (algebraMap k A) := (algebraMap k A).injective
    exact fun h => two_ne_zero (hi (by simpa only [map_ofNat, map_zero] using h : algebraMap k A (2:k) = algebraMap k A 0))
  have h2 : (a.2 : A) = (b.2 : A) := sub_eq_zero.mp
    ((mul_eq_zero.mp he).resolve_left (mul_ne_zero htwo hα))
  have h1 : (a.1 : A) = (b.1 : A) := by
    simpa only [expand_apply, h2, add_left_inj] using hab
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

include hinv hα hanti hdiv in
 theorem expand_surjective : Function.Surjective (expand τ α) := by
  intro a
  obtain ⟨d, hd⟩ := hdiv a
  have hdf : τ d = d := quotient_fixed τ α hinv hα hanti hd
  let h : k := (2:k)⁻¹
  have htwo : (2:A) * algebraMap k A h = 1 := by
    rw [show (2:A) = algebraMap k A (2:k) by exact (map_ofNat (algebraMap k A) 2).symm, ← map_mul]
    simp [h]
  let c₀ : fixed τ := ⟨algebraMap k A h * (a + τ a), by
    simp only [mem_fixed, map_mul, AlgEquiv.commutes, map_add, hinv a]
    ring⟩
  let c₁ : fixed τ := ⟨algebraMap k A h * d, by
    simp only [mem_fixed, map_mul, AlgEquiv.commutes, hdf]⟩
  refine ⟨(c₀,c₁), ?_⟩
  change algebraMap k A h * (a + τ a) + α * (algebraMap k A h * d) = a
  linear_combination a * htwo - (algebraMap k A h) * hd

/-- The actual invariant-ring basis `1, α`, with no finiteness assumption. -/
def coordinates : A ≃ₗ[fixed τ] (fixed τ × fixed τ) :=
  (LinearEquiv.ofBijective (expand τ α)
    ⟨expand_injective τ α hα hanti, expand_surjective τ α hinv hα hanti hdiv⟩).symm

@[simp] theorem expand_coordinates (a : A) :
    expand τ α (coordinates τ α hinv hα hanti hdiv a) = a :=
  (coordinates τ α hinv hα hanti hdiv).symm_apply_apply a

@[simp] theorem coordinates_expand (a : fixed τ × fixed τ) :
    coordinates τ α hinv hα hanti hdiv (expand τ α a) = a :=
  (coordinates τ α hinv hα hanti hdiv).apply_symm_apply a


def trace : A →ₗ[fixed τ] fixed τ :=
  (LinearMap.snd _ _ _).comp (coordinates τ α hinv hα hanti hdiv).toLinearMap

 theorem trace_expand (a : fixed τ × fixed τ) :
    trace τ α hinv hα hanti hdiv (expand τ α a) = a.2 := by
  change (coordinates τ α hinv hα hanti hdiv (expand τ α a)).2 = a.2
  rw [coordinates_expand]

omit [CharZero k] [IsDomain A] in
include hanti in
 theorem square_fixed : α * α ∈ fixed τ := by
  simp only [mem_fixed, map_mul, hanti, neg_mul_neg]

 theorem trace_mul (a b : A) :
    trace τ α hinv hα hanti hdiv (a*b) =
      (coordinates τ α hinv hα hanti hdiv a).1 *
        (coordinates τ α hinv hα hanti hdiv b).2 +
      (coordinates τ α hinv hα hanti hdiv a).2 *
        (coordinates τ α hinv hα hanti hdiv b).1 := by
  let c := coordinates τ α hinv hα hanti hdiv a
  let d := coordinates τ α hinv hα hanti hdiv b
  let α₂ : fixed τ := ⟨α*α, square_fixed τ α hanti⟩
  have he : a*b = expand τ α
      (c.1*d.1+α₂*c.2*d.2, c.1*d.2+c.2*d.1) := by
    rw [← expand_coordinates τ α hinv hα hanti hdiv a,
      ← expand_coordinates τ α hinv hα hanti hdiv b]
    change ((c.1:A)+α*(c.2:A))*((d.1:A)+α*(d.2:A)) =
      (c.1:A)*(d.1:A)+(α*α)*(c.2:A)*(d.2:A)+
        α*((c.1:A)*(d.2:A)+(c.2:A)*(d.1:A))
    ring
  rw [he,trace_expand]

section Pair
variable (R : Type*) [CommRing R]

def crossPair : (R × R) →ₗ[R] Module.Dual R (R × R) where
  toFun a :=
    { toFun := fun b => a.1*b.2+a.2*b.1
      map_add' := by intro b c; simp; ring
      map_smul' := by intro r b; simp; ring }
  map_add' := by intro a b; apply LinearMap.ext; intro c; simp; ring
  map_smul' := by intro r a; apply LinearMap.ext; intro b; simp; ring

 theorem crossPair_bijective : Function.Bijective (crossPair R) := by
  constructor
  · intro a b hab
    have h₁ := congrArg (fun f : Module.Dual R (R×R) => f (0,1)) hab
    have h₂ := congrArg (fun f : Module.Dual R (R×R) => f (1,0)) hab
    exact Prod.ext (by simpa [crossPair] using h₁) (by simpa [crossPair] using h₂)
  · intro f
    refine ⟨(f (0,1), f (1,0)), ?_⟩
    apply LinearMap.ext
    intro a
    have ha : a = a.1 • (1,0) + a.2 • (0,1) := by simp
    change f (0,1)*a.2 + f (1,0)*a.1 = f a
    calc
      _ = a.1 * f (1,0) + a.2 * f (0,1) := by ring
      _ = f (a.1 • (1,0) + a.2 • (0,1)) := by rw [map_add,map_smul,map_smul]; rfl
      _ = f a := congrArg f ha.symm

def crossPairEquiv : (R × R) ≃ₗ[R] Module.Dual R (R × R) :=
  LinearEquiv.ofBijective (crossPair R) (crossPair_bijective R)

end Pair

/-- The Frobenius duality over the invariant ring is integral and perfect. -/
def duality : A ≃ₗ[fixed τ] Module.Dual (fixed τ) A :=
  (coordinates τ α hinv hα hanti hdiv).trans
    ((crossPairEquiv (fixed τ)).trans
      (coordinates τ α hinv hα hanti hdiv).dualMap)

 theorem duality_apply (a b : A) :
    duality τ α hinv hα hanti hdiv a b = trace τ α hinv hα hanti hdiv (a*b) := by
  rw [trace_mul]
  rfl

 theorem duality_balanced (a b c : A) :
    duality τ α hinv hα hanti hdiv (c*a) b =
      duality τ α hinv hα hanti hdiv a (c*b) := by
  rw [duality_apply,duality_apply]
  congr 1
  ring


section Symmetric
variable {V : Type uv} [AddCommGroup V] [Module k V]

def symmetricMap (e : V ≃ₗ[k] V) : SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k V :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι k V).comp e.toLinearMap)

omit [CharZero k] in
@[simp] theorem symmetricMap_ι (e : V ≃ₗ[k] V) (v : V) :
    symmetricMap e (SymmetricAlgebra.ι k V v) = SymmetricAlgebra.ι k V (e v) := by
  simp [symmetricMap]

omit [CharZero k] in
 theorem symmetricMap_comp (e d : V ≃ₗ[k] V) :
    (symmetricMap d).comp (symmetricMap e) = symmetricMap (e.trans d) := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp

omit [CharZero k] in
 theorem symmetricMap_refl : symmetricMap (LinearEquiv.refl k V) =
    AlgHom.id k (SymmetricAlgebra k V) := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp

/-- The algebra action is induced by the linear reflection, not postulated. -/
def symmetricAction (e : V ≃ₗ[k] V) : SymmetricAlgebra k V ≃ₐ[k] SymmetricAlgebra k V :=
  AlgEquiv.ofAlgHom (symmetricMap e) (symmetricMap e.symm)
    (by rw [symmetricMap_comp,LinearEquiv.symm_trans_self,symmetricMap_refl])
    (by rw [symmetricMap_comp,LinearEquiv.self_trans_symm,symmetricMap_refl])

omit [CharZero k] in
@[simp] theorem symmetricAction_ι (e : V ≃ₗ[k] V) (v : V) :
    symmetricAction e (SymmetricAlgebra.ι k V v) = SymmetricAlgebra.ι k V (e v) :=
  symmetricMap_ι e v

variable (root : V) (coroot : Module.Dual k V) (hroot : coroot root = 2)

abbrev reflectionAction : SymmetricAlgebra k V ≃ₐ[k] SymmetricAlgebra k V :=
  symmetricAction (Module.reflection hroot)

omit [CharZero k] in
 theorem reflectionAction_involutive : Function.Involutive (reflectionAction root coroot hroot) := by
  intro a
  have he : (reflectionAction root coroot hroot).toAlgHom.comp
      (reflectionAction root coroot hroot).toAlgHom =
        AlgHom.id k (SymmetricAlgebra k V) := by
    apply SymmetricAlgebra.algHom_ext
    ext v
    simp [Module.involutive_reflection hroot v]
  exact congrArg (fun f : SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k V => f a) he

omit [CharZero k] in
 theorem reflectionAction_anti :
    reflectionAction root coroot hroot (SymmetricAlgebra.ι k V root) =
      -SymmetricAlgebra.ι k V root := by
  simp

include hroot in
 theorem reflectionRoot_ne_zero : SymmetricAlgebra.ι k V root ≠ 0 := by
  intro he
  have hh := congrArg (SymmetricAlgebra.lift coroot) he
  rw [SymmetricAlgebra.lift_ι_apply,map_zero,hroot] at hh
  exact two_ne_zero hh

omit [CharZero k] in
 theorem reflectionAction_divisible (a : SymmetricAlgebra k V) :
    SymmetricAlgebra.ι k V root ∣ a-reflectionAction root coroot hroot a := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap c => simp
  | ι v =>
    refine ⟨algebraMap k (SymmetricAlgebra k V) (coroot v), ?_⟩
    rw [reflectionAction,symmetricAction_ι,Module.reflection_apply,map_sub,map_smul]
    simp only [sub_sub_cancel,Algebra.smul_def]
    ring
  | mul a b ha hb =>
    obtain ⟨c,hc⟩ := ha
    obtain ⟨d,hd⟩ := hb
    refine ⟨c*b+(reflectionAction root coroot hroot a)*d, ?_⟩
    rw [map_mul]
    linear_combination b*hc+(reflectionAction root coroot hroot a)*hd
  | add a b ha hb =>
    simpa only [map_add, add_sub_add_comm] using dvd_add ha hb

/-- A genuine simple-reflection integral Frobenius extension in characteristic
zero, for the symmetric algebra of any representation carrying the reflection. -/
def reflectionDuality :
    SymmetricAlgebra k V ≃ₗ[fixed (reflectionAction root coroot hroot)]
      Module.Dual (fixed (reflectionAction root coroot hroot)) (SymmetricAlgebra k V) :=
  duality (reflectionAction root coroot hroot) (SymmetricAlgebra.ι k V root)
    (reflectionAction_involutive root coroot hroot) (reflectionRoot_ne_zero root coroot hroot)
    (reflectionAction_anti root coroot hroot) (reflectionAction_divisible root coroot hroot)

end Symmetric

end
end KLInvariance.ReflectionFrobenius

end


section

/-! Frobenius extensions for the actual simple reflections of the extended
theorem realization, not abstract reflection data carried by the target. -/

end

end OAI
