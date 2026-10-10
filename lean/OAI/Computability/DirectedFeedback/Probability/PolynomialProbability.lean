import Mathlib
import OAI.Computability.DirectedFeedback.Games.GenericPolynomial

namespace OAI

namespace DFVSGames.Quadratic

open scoped BigOperators

noncomputable section

variable {F V : Type*} [Field F] [Fintype F] [CharP F 2]
variable [Algebra (ZMod 2) F] [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]

theorem isGeneric_range_of_injective
    (z : V →ₗ[ZMod 2] (Fin 3 → F)) (hz : Function.Injective z)
    (hseparate : ∀ v w : V, v ≠ 0 → w ≠ 0 →
      (∃ t : F, z v = t • z w) → v = w)
    (halign : ∀ g : V →ₗ[ZMod 2] (Fin 3 → F),
      (alignmentEvent z g (fun v => alignmentRightHandSide (z v))).card ≤
        3 * Module.finrank (ZMod 2) V) :
    IsGeneric (LinearMap.range z) := by
  classical
  let : Fintype (LinearMap.range z) := Subtype.fintype (Membership.mem (LinearMap.range z))
  let e : V ≃ₗ[ZMod 2] LinearMap.range z := LinearEquiv.ofInjective z hz
  have he (v : V) : ((e v : LinearMap.range z) : Fin 3 → F) = z v := rfl
  have hes (s : LinearMap.range z) : z (e.symm s) = (s : Fin 3 → F) :=
    LinearEquiv.ofInjective_symm_apply z s
  have hzero (v : V) : e v ≠ 0 ↔ v ≠ 0 := by
    constructor
    · intro h hv
      apply h
      rw [hv, map_zero]
    · intro h hv
      apply h
      apply e.injective
      simpa only [map_zero] using hv
  constructor
  · intro s t hs ht hprop
    have hs' : e.symm s ≠ 0 := by
      intro h
      apply hs
      have hh := congrArg e h
      simpa only [e.apply_symm_apply, map_zero] using hh
    have ht' : e.symm t ≠ 0 := by
      intro h
      apply ht
      have hh := congrArg e h
      simpa only [e.apply_symm_apply, map_zero] using hh
    have hinput : e.symm s = e.symm t := by
      apply hseparate _ _ hs' ht'
      simpa only [hes] using hprop
    exact e.symm.injective hinput
  · intro g
    have hevent (v : V) :
        v ∈ alignmentEvent z (g.comp e.toLinearMap)
          (fun v => alignmentRightHandSide (z v)) ↔
        e v ∈ alignmentEvent (fun s : LinearMap.range z => (s : Fin 3 → F)) g
          (fun s : LinearMap.range z => alignmentRightHandSide (s : Fin 3 → F)) := by
      simp only [alignmentEvent, Finset.mem_filter, Finset.mem_univ, true_and,
        LinearMap.comp_apply, LinearEquiv.coe_coe, he, hzero]
    have hcard :
        (alignmentEvent z (g.comp e.toLinearMap)
          (fun v => alignmentRightHandSide (z v))).card =
        (alignmentEvent (fun s : LinearMap.range z => (s : Fin 3 → F)) g
          (fun s : LinearMap.range z => alignmentRightHandSide (s : Fin 3 → F))).card := by
      apply Finset.card_bij (fun v _ => e v)
      · intro v hv
        exact (hevent v).mp hv
      · intro v hv w hw h
        exact e.injective h
      · intro s hs
        refine ⟨e.symm s, (hevent (e.symm s)).mpr ?_, e.apply_symm_apply s⟩
        simpa only [e.apply_symm_apply] using hs
    calc
      _ = (alignmentEvent z (g.comp e.toLinearMap)
          (fun v => alignmentRightHandSide (z v))).card := hcard.symm
      _ ≤ 3 * Module.finrank (ZMod 2) V := halign _
      _ = 3 * Module.finrank (ZMod 2) (LinearMap.range z) :=
        congrArg (fun d : ℕ => 3 * d) e.finrank_eq

omit [Fintype F] [CharP F 2] in

theorem finrank_range_binary_parameters {J : Type*} [Fintype J]
    (z : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) (hz : Function.Injective z) :
    Module.finrank (ZMod 2) (LinearMap.range z) = Fintype.card J := by
  rw [LinearMap.finrank_range_of_inj hz, Module.finrank_fintype_fun_eq_card]

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open scoped BigOperators

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Fintype F]

def assignmentProbability {n : ℕ} (event : (Fin n → F) → Prop) : ℚ≥0 := by
  classical
  exact ((Finset.univ.filter event).card : ℚ≥0) / (Fintype.card F : ℚ≥0) ^ n

omit [Field F] in
theorem assignmentProbability_mono {n : ℕ}
    {event event' : (Fin n → F) → Prop} (h : ∀ x, event x → event' x) :
    assignmentProbability event ≤ assignmentProbability event' := by
  classical
  apply div_le_div_of_nonneg_right _ zero_le
  exact_mod_cast Finset.card_le_card
    (show Finset.univ.filter event ⊆ Finset.univ.filter event' from by
      intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h x (Finset.mem_filter.mp hx).2⟩)

theorem assignmentProbability_eval_zero_le {n : ℕ}
    (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) :
    assignmentProbability (fun x => MvPolynomial.eval x p = 0) ≤
      (p.totalDegree : ℚ≥0) / Fintype.card F := by
  classical
  simpa [assignmentProbability] using
    MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset F)

omit [Fintype F] in

theorem totalDegree_map_eq_of_injective {σ : Type*}
    (φ : K →+* F) (hφ : Function.Injective φ) (p : MvPolynomial σ K) :
    (MvPolynomial.map φ p).totalDegree = p.totalDegree := by
  classical
  unfold MvPolynomial.totalDegree
  rw [MvPolynomial.support_map_of_injective p hφ]

theorem assignmentProbability_eval₂_zero_le {n : ℕ}
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0) :
    assignmentProbability (fun x => MvPolynomial.eval₂ φ x p = 0) ≤
      (p.totalDegree : ℚ≥0) / Fintype.card F := by
  have hp' : MvPolynomial.map φ p ≠ 0 := by
    intro hz
    apply hp
    apply MvPolynomial.map_injective φ hφ
    simpa using hz
  have h := assignmentProbability_eval_zero_le (MvPolynomial.map φ p) hp'
  simpa only [← MvPolynomial.eval₂_eq_eval_map,
    totalDegree_map_eq_of_injective φ hφ] using h

theorem assignmentProbability_le_of_polynomial {n : ℕ}
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0)
    (event : (Fin n → F) → Prop)
    (hvanish : ∀ x, event x → MvPolynomial.eval₂ φ x p = 0) :
    assignmentProbability event ≤ (p.totalDegree : ℚ≥0) / Fintype.card F :=
  (assignmentProbability_mono hvanish).trans
    (assignmentProbability_eval₂_zero_le φ hφ p hp)

theorem assignmentProbability_union_le {n : ℕ} {J : Type*} [Fintype J]
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : J → MvPolynomial (Fin n) K) (hp : ∀ j, p j ≠ 0)
    (event : J → (Fin n → F) → Prop)
    (hvanish : ∀ j x, event j x → MvPolynomial.eval₂ φ x (p j) = 0) :
    assignmentProbability (fun x => ∃ j, event j x) ≤
      ((∑ j, (p j).totalDegree : ℕ) : ℚ≥0) / Fintype.card F := by
  classical
  let P : MvPolynomial (Fin n) K := ∏ j, p j
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)
  have hvanishP : ∀ x, (∃ j, event j x) → MvPolynomial.eval₂ φ x P = 0 := by
    intro x hx
    obtain ⟨j, hj⟩ := hx
    change (MvPolynomial.eval₂Hom φ x) P = 0
    simp only [P, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (hvanish j x hj)
  have hbound := assignmentProbability_le_of_polynomial φ hφ P hP _ hvanishP
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ zero_le
  exact_mod_cast MvPolynomial.totalDegree_finsetProd Finset.univ p

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open scoped BigOperators

noncomputable section

variable {σ τ K F : Type*} [Field K] [Field F] [Fintype F]

def reindexAssignments (e : σ ≃ τ) : (σ → F) ≃ (τ → F) where
  toFun x := fun t => x (e.symm t)
  invFun y := fun s => y (e s)
  left_inv x := by funext s; simp
  right_inv y := by funext t; simp

def finiteAssignmentProbability [Fintype σ] (event : (σ → F) → Prop) : ℚ≥0 := by
  classical
  exact ((Finset.univ.filter event).card : ℚ≥0) /
    (Fintype.card F : ℚ≥0) ^ Fintype.card σ

omit [Field F] in
theorem finiteAssignmentProbability_reindex [Fintype σ] {n : ℕ}
    (e : σ ≃ Fin n) (event : (σ → F) → Prop) :
    finiteAssignmentProbability event =
      assignmentProbability (fun y : Fin n → F => event (fun s => y (e s))) := by
  classical
  have hcard : Fintype.card σ = n := by simpa using Fintype.card_congr e
  have hevent (x : σ → F) :
      event x ↔ event (fun s => reindexAssignments e x (e s)) := by
    simp [reindexAssignments]
  have hsub := Fintype.card_congr ((reindexAssignments (F := F) e).subtypeEquiv
    (p := event) (q := fun y : Fin n → F => event (fun s => y (e s))) hevent)
  have hfilter : (Finset.univ.filter event).card =
      (Finset.univ.filter (fun y : Fin n → F => event (fun s => y (e s)))).card := by
    simpa only [Fintype.card_subtype] using hsub
  simp only [finiteAssignmentProbability, assignmentProbability, hfilter, hcard]

theorem finiteAssignmentProbability_le_of_polynomial [Fintype σ]
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial σ K) (hp : p ≠ 0)
    (event : (σ → F) → Prop)
    (hvanish : ∀ x, event x → MvPolynomial.eval₂ φ x p = 0) :
    finiteAssignmentProbability event ≤ (p.totalDegree : ℚ≥0) / Fintype.card F := by
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let p' := MvPolynomial.renameEquiv K e p
  have hp' : p' ≠ 0 := by
    intro h
    apply hp
    apply (MvPolynomial.renameEquiv K e).injective
    simpa only [map_zero] using h
  rw [finiteAssignmentProbability_reindex e event]
  have hbound := assignmentProbability_le_of_polynomial φ hφ p' hp'
    (fun y => event (fun s => y (e s))) (by
      intro y hy
      change MvPolynomial.eval₂ φ y (MvPolynomial.rename e p) = 0
      rw [MvPolynomial.eval₂_rename]
      exact hvanish (fun s => y (e s)) hy)
  simpa only [p', MvPolynomial.totalDegree_renameEquiv] using hbound

theorem finiteAssignmentProbability_eval₂_zero_le [Fintype σ]
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : MvPolynomial σ K) (hp : p ≠ 0) :
    finiteAssignmentProbability (fun x => MvPolynomial.eval₂ φ x p = 0) ≤
      (p.totalDegree : ℚ≥0) / Fintype.card F :=
  finiteAssignmentProbability_le_of_polynomial φ hφ p hp _ (fun _ h => h)

theorem finiteAssignmentProbability_union_le [Fintype σ] {J : Type*} [Fintype J]
    (φ : K →+* F) (hφ : Function.Injective φ)
    (p : J → MvPolynomial σ K) (hp : ∀ j, p j ≠ 0)
    (event : J → (σ → F) → Prop)
    (hvanish : ∀ j x, event j x → MvPolynomial.eval₂ φ x (p j) = 0) :
    finiteAssignmentProbability (fun x => ∃ j, event j x) ≤
      ((∑ j, (p j).totalDegree : ℕ) : ℚ≥0) / Fintype.card F := by
  classical
  let e : σ ≃ Fin (Fintype.card σ) := Fintype.equivFin σ
  let p' : J → MvPolynomial (Fin (Fintype.card σ)) K :=
    fun j => MvPolynomial.renameEquiv K e (p j)
  have hp' (j : J) : p' j ≠ 0 := by
    intro h
    apply hp j
    apply (MvPolynomial.renameEquiv K e).injective
    simpa only [map_zero] using h
  rw [finiteAssignmentProbability_reindex e]
  have hbound := assignmentProbability_union_le φ hφ p' hp'
    (fun j y => event j (fun s => y (e s))) (by
      intro j y hy
      change MvPolynomial.eval₂ φ y (MvPolynomial.rename e (p j)) = 0
      rw [MvPolynomial.eval₂_rename]
      exact hvanish j (fun s => y (e s)) hy)
  simpa only [p', MvPolynomial.totalDegree_renameEquiv] using hbound

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

noncomputable section

theorem exists_genericity_polynomial (J : Type*) [Fintype J] :
    ∃ P : MvPolynomial (Fin 3 × J) (ZMod 2), P ≠ 0 ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
        (x : (Fin 3 × J) → F),
        MvPolynomial.eval₂ (algebraMap (ZMod 2) F) x P ≠ 0 →
        Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range := by
  classical
  obtain ⟨A, hA, halign⟩ := exists_all_lifts_alignment_polynomial J
  refine ⟨separationPolynomial J * A, mul_ne_zero (separationPolynomial_ne_zero J) hA, ?_⟩
  intro F _ _ _ _ x hP
  rw [MvPolynomial.eval₂_mul] at hP
  have hparts := mul_ne_zero_iff.mp hP
  have hsep := parameterMap_separated_of_eval_ne_zero x hparts.1
  refine ⟨hsep.1, isGeneric_range_of_injective (parameterMap x) hsep.1 hsep.2 ?_⟩
  intro g
  simpa only [Module.finrank_fintype_fun_eq_card] using halign F x hparts.2 g

theorem exists_genericity_error_numerator (J : Type*) [Fintype J] :
    ∃ D : ℕ, 0 < D ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F],
        finiteAssignmentProbability (fun x : (Fin 3 × J) → F =>
          ¬(Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range)) ≤
            (D : ℚ≥0) / Fintype.card F := by
  classical
  obtain ⟨P, hP, hgood⟩ := exists_genericity_polynomial J
  refine ⟨P.totalDegree + 1, Nat.succ_pos _, ?_⟩
  intro F _ _ _ _
  have h := finiteAssignmentProbability_le_of_polynomial
    (algebraMap (ZMod 2) F) (algebraMap (ZMod 2) F).injective P hP
    (fun x : (Fin 3 × J) → F =>
      ¬(Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range))
    (by
      intro x hx
      by_contra hne
      exact hx (hgood F x hne))
  apply h.trans
  apply div_le_div_of_nonneg_right _ zero_le
  exact_mod_cast Nat.le_succ P.totalDegree

end

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

noncomputable section

variable {F J : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F] [Fintype J]

def parameterMapEquiv : ((Fin 3 × J) → F) ≃
    ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) where
  toFun := parameterMap
  invFun g ij := g ((Pi.basisFun (ZMod 2) J) ij.2) ij.1
  left_inv x := by
    funext ij
    exact parameterMap_basis x ij.2 ij.1
  right_inv g := by
    apply (Pi.basisFun (ZMod 2) J).ext
    intro j
    funext i
    exact parameterMap_basis _ j i

omit [CharP F 2] in
theorem parameterMap_event_card
    (event : ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) → Prop) :
    Nat.card {x : (Fin 3 × J) → F // event (parameterMap x)} =
      Nat.card {g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F) // event g} := by
  exact Nat.card_congr ((parameterMapEquiv (F := F) (J := J)).subtypeEquiv
    (p := fun x => event (parameterMap x)) (q := event) (fun _ => Iff.rfl))

variable [Fintype F]

omit [CharP F 2] in
theorem parameterMap_event_probability
    (event : ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) → Prop) :
    (finiteAssignmentProbability (fun x => event (parameterMap x)) : ℚ) =
      (Nat.card {g : (J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F) // event g} : ℚ) /
        Nat.card ((J → ZMod 2) →ₗ[ZMod 2] (Fin 3 → F)) := by
  classical
  have hall := Nat.card_congr (parameterMapEquiv (F := F) (J := J))
  have hevent := parameterMap_event_card event
  rw [← hevent, ← hall]
  simp [finiteAssignmentProbability, Nat.card_eq_fintype_card, Fintype.card_subtype,
    ] ; congr 1 ; ext x ; simp

end

end DFVSGames.Quadratic

noncomputable section

open scoped BigOperators
open Module
open DFVSGames.Gadget.Orientation

namespace DFVSGames.Quadratic.UniformSubspaces

variable {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]

def Injection (K V W : Type*) [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] :=
  {J : V →ₗ[K] W // Function.Injective J}

instance injectionAction : MulAction (W ≃ₗ[K] W) (Injection K V W) where
  smul a J := ⟨a.toLinearMap.comp J.val, a.injective.comp J.property⟩
  one_smul J := by
    apply Subtype.ext
    ext x
    rfl
  mul_smul a b J := by
    apply Subtype.ext
    ext x
    rfl

omit [FiniteDimensional K W] in

theorem injection_transitive (J₁ J₂ : Injection K V W) :
    ∃ a : W ≃ₗ[K] W, a • J₁ = J₂ := by
  let e₁ := LinearEquiv.ofInjective J₁.val J₁.property
  let e₂ := LinearEquiv.ofInjective J₂.val J₂.property
  let e : LinearMap.range J₁.val ≃ₗ[K] LinearMap.range J₂.val := e₁.symm.trans e₂
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨a, ?_⟩
  apply Subtype.ext
  ext x
  have h := (ha (e₁ x)).symm
  change a (J₁.val x) = ((e₂ (e₁.symm (e₁ x))) : W) at h
  change a (J₁.val x) = J₂.val x
  simpa only [LinearEquiv.symm_apply_apply, e₂, LinearEquiv.ofInjective_apply] using h

def image (J : Injection K V W) : RankSpace K W (finrank K V) :=
  ⟨LinearMap.range J.val, LinearMap.finrank_range_of_inj J.property⟩

omit [FiniteDimensional K V] [FiniteDimensional K W] in
theorem image_action (a : W ≃ₗ[K] W) (J : Injection K V W) :
    image (a • J) = a • image J := by
  apply Subtype.ext
  exact LinearMap.range_comp J.val a.toLinearMap

variable [Fintype (W ≃ₗ[K] W)] [Fintype (Injection K V W)]
    [Fintype (RankSpace K W (finrank K V))]

theorem mean_image (J₀ : Injection K V W) (f : RankSpace K W (finrank K V) → ℚ) :
    (∑ J : Injection K V W, f (image J)) / Fintype.card (Injection K V W) =
      (∑ S : RankSpace K W (finrank K V), f S) /
        Fintype.card (RankSpace K W (finrank K V)) := by
  have h := mean_action J₀ (injection_transitive J₀) (fun J => f (image J))
  simp_rw [image_action] at h
  exact h.symm.trans (mean_oriented_subspace (image J₀) f)

theorem bad_image_count_ratio (J₀ : Injection K V W)
    (Bad : RankSpace K W (finrank K V) → Prop) :
    (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) /
        Fintype.card (Injection K V W) =
      (Nat.card {S : RankSpace K W (finrank K V) // Bad S} : ℚ) /
        Fintype.card (RankSpace K W (finrank K V)) := by
  classical
  have h := mean_image J₀ (fun S => if Bad S then 1 else 0)
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

theorem bad_subspace_bound (J₀ : Injection K V W)
    (Bad : RankSpace K W (finrank K V) → Prop) (α β : ℚ) (hα : 0 ≤ α) (hβ : β < 1)
    (hbad : (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) ≤
      α * Nat.card (V →ₗ[K] W))
    (hinj : (1 - β) * Nat.card (V →ₗ[K] W) ≤ Fintype.card (Injection K V W)) :
    (Nat.card {S : RankSpace K W (finrank K V) // Bad S} : ℚ) /
        Fintype.card (RankSpace K W (finrank K V)) ≤ α / (1 - β) := by
  rw [← bad_image_count_ratio J₀ Bad]
  have : Nonempty (Injection K V W) := ⟨J₀⟩
  have hi : (0 : ℚ) < Fintype.card (Injection K V W) := by
    exact_mod_cast Fintype.card_pos
  have hd : 0 < 1 - β := sub_pos.mpr hβ
  apply (div_le_div_iff₀ hi hd).mpr
  calc
    (Nat.card {J : Injection K V W // Bad (image J)} : ℚ) * (1 - β) ≤
        (α * Nat.card (V →ₗ[K] W)) * (1 - β) :=
      mul_le_mul_of_nonneg_right hbad hd.le
    _ = α * ((1 - β) * Nat.card (V →ₗ[K] W)) := by ring
    _ ≤ α * Fintype.card (Injection K V W) := mul_le_mul_of_nonneg_left hinj hα

end DFVSGames.Quadratic.UniformSubspaces
end

noncomputable section

open Module
open DFVSGames.Gadget.Orientation

namespace DFVSGames.Quadratic

private theorem conditioning_counts_inline_GenericSubspaceProbability {A : Type*} [Fintype A] [Nonempty A]
    (P Q : A → Prop) (α : ℚ) (hα : α < 1)
    (hbad : (Nat.card {a : A // ¬(P a ∧ Q a)} : ℚ) / Nat.card A ≤ α) :
    (∃ a : A, P a ∧ Q a) ∧
      (Nat.card {a : {a : A // P a} // ¬Q a.1} : ℚ) ≤ α * Nat.card A ∧
      (1 - α) * Nat.card A ≤ (Nat.card {a : A // P a} : ℚ) := by
  classical
  have hpos : (0 : ℚ) < Nat.card A := by exact_mod_cast Nat.card_pos
  have hbadCount := (div_le_iff₀ hpos).mp hbad
  have hgood : ∃ a : A, P a ∧ Q a := by
    by_contra h
    have hall : ∀ a : A, ¬(P a ∧ Q a) := fun a ha => h ⟨a, ha⟩
    have hcard : Nat.card {a : A // ¬(P a ∧ Q a)} = Nat.card A := by
      simp [Nat.card_eq_fintype_card, Fintype.card_subtype, hall]
    rw [hcard, div_self hpos.ne'] at hbad
    exact (not_le_of_gt hα) hbad
  have hnoninj : Nat.card {a : A // ¬P a} ≤ Nat.card {a : A // ¬(P a ∧ Q a)} := by
    apply Nat.card_le_card_of_injective
      (fun a : {a : A // ¬P a} => (⟨a.1, fun h => a.2 h.1⟩ : {a : A // ¬(P a ∧ Q a)}))
    intro a b h
    exact Subtype.ext (congrArg (fun c : {a : A // ¬(P a ∧ Q a)} => c.val) h)
  have hbadInj : Nat.card {a : {a : A // P a} // ¬Q a.1} ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by
    apply Nat.card_le_card_of_injective
      (fun a : {a : {a : A // P a} // ¬Q a.1} =>
        (⟨a.1.1, fun h => a.2 h.2⟩ : {a : A // ¬(P a ∧ Q a)}))
    intro a b h
    apply Subtype.ext
    exact Subtype.ext (congrArg (fun c : {a : A // ¬(P a ∧ Q a)} => c.val) h)
  have hpartitionNat : Nat.card {a : A // P a} + Nat.card {a : A // ¬P a} = Nat.card A := by
    have hle := Fintype.card_subtype_le P
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    omega
  have hpartition : (Nat.card {a : A // P a} : ℚ) +
      Nat.card {a : A // ¬P a} = Nat.card A := by exact_mod_cast hpartitionNat
  have hn : (Nat.card {a : A // ¬P a} : ℚ) ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by exact_mod_cast hnoninj
  have hb : (Nat.card {a : {a : A // P a} // ¬Q a.1} : ℚ) ≤
      Nat.card {a : A // ¬(P a ∧ Q a)} := by exact_mod_cast hbadInj
  refine ⟨hgood, hb.trans hbadCount, ?_⟩
  linarith

variable {F J : Type*} [Field F] [Fintype F] [CharP F 2]
    [Algebra (ZMod 2) F] [Fintype J]

theorem generic_subspace_and_probability_of_parameter_error (α : ℚ)
    (hα₀ : 0 ≤ α) (hα : α < 1)
    (herror : (finiteAssignmentProbability (fun x : (Fin 3 × J) → F =>
      ¬(Function.Injective (parameterMap x) ∧ IsGeneric (parameterMap x).range)) : ℚ) ≤ α) :
    (∃ S : RankSpace (ZMod 2) (Fin 3 → F) (Fintype.card J), IsGeneric S.1) ∧
      nongenericFraction F (Fintype.card J) ≤ α / (1 - α) := by
  classical
  let V := J → ZMod 2
  let W := Fin 3 → F
  let A := V →ₗ[ZMod 2] W
  let P : A → Prop := fun g => Function.Injective g
  let Q : A → Prop := fun g => IsGeneric g.range
  let : Fintype A := Fintype.ofEquiv ((Fin 3 × J) → F) parameterMapEquiv
  let : Fintype (Submodule (ZMod 2) W) :=
    Fintype.ofInjective (fun S : Submodule (ZMod 2) W => (S : Set W)) SetLike.coe_injective
  let : Fintype (W ≃ₗ[ZMod 2] W) :=
    Fintype.ofInjective (fun a : W ≃ₗ[ZMod 2] W => (a : W → W)) DFunLike.coe_injective
  let : Fintype (UniformSubspaces.Injection (ZMod 2) V W) :=
    inferInstanceAs (Fintype {g : A // Function.Injective g})
  let : Fintype (RankSpace (ZMod 2) W (finrank (ZMod 2) V)) :=
    inferInstanceAs (Fintype {S : Submodule (ZMod 2) W // finrank (ZMod 2) S = finrank (ZMod 2) V})
  have hcount : (Nat.card {g : A // ¬(P g ∧ Q g)} : ℚ) / Nat.card A ≤ α := by
    rw [parameterMap_event_probability (fun g : A => ¬(P g ∧ Q g))] at herror
    exact herror
  have hc := conditioning_counts_inline_GenericSubspaceProbability P Q α hα hcount
  obtain ⟨g, hgP, hgQ⟩ := hc.1
  let J₀ : UniformSubspaces.Injection (ZMod 2) V W := ⟨g, hgP⟩
  have hdim : finrank (ZMod 2) V = Fintype.card J :=
    Module.finrank_fintype_fun_eq_card (ZMod 2)
  have hfrac := UniformSubspaces.bad_subspace_bound J₀
    (fun S : RankSpace (ZMod 2) W (finrank (ZMod 2) V) => ¬IsGeneric S.1)
    α α hα₀ hα hc.2.1 (by
      rw [← Nat.card_eq_fintype_card]
      exact hc.2.2)
  refine ⟨?_, ?_⟩
  · refine ⟨⟨g.range, ?_⟩, hgQ⟩
    simpa only [V, Module.finrank_fintype_fun_eq_card] using
      (LinearMap.finrank_range_of_inj hgP)
  · rw [← Nat.card_eq_fintype_card] at hfrac
    change nongenericFraction F (finrank (ZMod 2) V) ≤ α / (1 - α) at hfrac
    simpa only [hdim] using hfrac

theorem exists_generic_subspace_error_numerator (J : Type*) [Fintype J] :
    ∃ D : ℕ, 0 < D ∧
      ∀ (F : Type*) [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F],
        (D : ℚ) / Fintype.card F < 1 →
        (∃ S : RankSpace (ZMod 2) (Fin 3 → F) (Fintype.card J), IsGeneric S.1) ∧
          nongenericFraction F (Fintype.card J) ≤
            ((D : ℚ) / Fintype.card F) / (1 - (D : ℚ) / Fintype.card F) := by
  obtain ⟨D, hD, hbound⟩ := exists_genericity_error_numerator J
  refine ⟨D, hD, ?_⟩
  intro F _ _ _ _ hsmall
  apply generic_subspace_and_probability_of_parameter_error ((D : ℚ) / Fintype.card F)
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hsmall
  exact_mod_cast hbound F

theorem conditional_error_le_of_small (α ε : ℚ) (hα : 0 ≤ α)
    (hhalf : α ≤ 1 / 2) (hε : α ≤ ε / 2) : α / (1 - α) ≤ ε := by
  have hd : 0 < 1 - α := by linarith
  apply (div_le_iff₀ hd).mpr
  have hε₀ : 0 ≤ ε := by linarith
  have hprod : 0 ≤ ε * (1 / 2 - α) := mul_nonneg hε₀ (by linarith)
  nlinarith

end DFVSGames.Quadratic
end

namespace DFVSGames.Quadratic

abbrev BinaryField (d : ℕ) := GaloisField 2 d

theorem card_binaryField (d : ℕ) (hd : 0 < d) :
    Nat.card (BinaryField d) = 2 ^ d :=
  GaloisField.card 2 d (Nat.ne_of_gt hd)

theorem finrank_binaryField (d : ℕ) (hd : 0 < d) :
    Module.finrank (ZMod 2) (BinaryField d) = d :=
  GaloisField.finrank 2 (Nat.ne_of_gt hd)

theorem finrank_binaryField_triple (d : ℕ) (hd : 0 < d) :
    Module.finrank (ZMod 2) (Fin 3 → BinaryField d) = 3 * d := by
  rw [← Module.finrank_mul_finrank (ZMod 2) (BinaryField d) (Fin 3 → BinaryField d),
    finrank_binaryField d hd, Module.finrank_fin_fun, mul_comm]

def fieldDegree (cardThreshold rankThreshold : ℕ) : ℕ :=
  cardThreshold + rankThreshold + 1

theorem fieldDegree_pos (N r : ℕ) : 0 < fieldDegree N r := by
  simp [fieldDegree]

theorem threshold_lt_two_pow_fieldDegree (N r : ℕ) : N < 2 ^ fieldDegree N r := by
  have h : N ≤ fieldDegree N r := by unfold fieldDegree; omega
  exact lt_of_le_of_lt h Nat.lt_two_pow_self

theorem rankThreshold_le_triple_fieldDegree (N r : ℕ) : r ≤ 3 * fieldDegree N r := by
  unfold fieldDegree
  omega

theorem exists_binary_field_degree (N r : ℕ) :
    ∃ d : ℕ, 0 < d ∧ N < 2 ^ d ∧ r ≤ 3 * d :=
  ⟨fieldDegree N r, fieldDegree_pos N r, threshold_lt_two_pow_fieldDegree N r,
    rankThreshold_le_triple_fieldDegree N r⟩

theorem chosen_binaryField_thresholds (N r : ℕ) :
    N < Nat.card (BinaryField (fieldDegree N r)) ∧
      r ≤ Module.finrank (ZMod 2) (Fin 3 → BinaryField (fieldDegree N r)) := by
  rw [card_binaryField _ (fieldDegree_pos N r),
    finrank_binaryField_triple _ (fieldDegree_pos N r)]
  exact ⟨threshold_lt_two_pow_fieldDegree N r, rankThreshold_le_triple_fieldDegree N r⟩

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

open scoped BigOperators
open DFVSGames.Gadget.Orientation

noncomputable section

noncomputable instance binaryFieldFintype (d : ℕ) : Fintype (BinaryField d) :=
  Fintype.ofFinite _

theorem exists_uniform_generic_field (r₀ : ℕ) (ε : ℚ) (hε : 0 < ε) :
    ∃ d : ℕ, 0 < d ∧ r₀ ≤ 3 * d ∧
      (∀ r : ℕ, r ≤ r₀ → nongenericFraction (BinaryField d) r ≤ ε) ∧
      (∃ S : RankSpace (ZMod 2) (Fin 3 → BinaryField d) r₀, IsGeneric S.1) := by
  classical
  have hex (r : ℕ) := exists_generic_subspace_error_numerator (Fin r)
  choose D hD hbound using hex
  let M : ℕ := ∑ r ∈ Finset.range (r₀ + 1), D r
  have hDM (r : ℕ) (hr : r ≤ r₀) : D r ≤ M := by
    apply Finset.single_le_sum (fun _ _ => Nat.zero_le _)
    exact Finset.mem_range.mpr (by omega)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (2 * (M : ℚ)) (2 * (M : ℚ) / ε))
  let d := fieldDegree N r₀
  have hd : 0 < d := fieldDegree_pos N r₀
  have hqN : (N : ℚ) < Fintype.card (BinaryField d) := by
    exact_mod_cast (by
      simpa only [Nat.card_eq_fintype_card] using
        (chosen_binaryField_thresholds N r₀).1)
  have hq : (0 : ℚ) < Fintype.card (BinaryField d) := by
    exact_mod_cast Fintype.card_pos
  have hqM : 2 * (M : ℚ) < Fintype.card (BinaryField d) :=
    (le_max_left _ _).trans_lt (hN.trans hqN)
  have hqε : 2 * (M : ℚ) / ε < Fintype.card (BinaryField d) :=
    (le_max_right _ _).trans_lt (hN.trans hqN)
  have hεq : 2 * (M : ℚ) < (Fintype.card (BinaryField d) : ℚ) * ε :=
    (div_lt_iff₀ hε).mp hqε
  have hsmall (r : ℕ) (hr : r ≤ r₀) :
      (D r : ℚ) / Fintype.card (BinaryField d) ≤ 1 / 2 ∧
      (D r : ℚ) / Fintype.card (BinaryField d) ≤ ε / 2 := by
    have hDr : (D r : ℚ) ≤ M := by exact_mod_cast hDM r hr
    constructor
    · apply (div_le_iff₀ hq).mpr
      nlinarith
    · apply (div_le_iff₀ hq).mpr
      nlinarith
  have hready (r : ℕ) (hr : r ≤ r₀) :=
    hbound r (BinaryField d) (show (D r : ℚ) / Fintype.card (BinaryField d) < 1 by
      have := (hsmall r hr).1
      linarith)
  refine ⟨d, hd, rankThreshold_le_triple_fieldDegree N r₀, ?_, ?_⟩
  · intro r hr
    have hb := (hready r hr).2
    simp only [Fintype.card_fin] at hb
    apply hb.trans
    exact conditional_error_le_of_small _ _
      (div_nonneg (Nat.cast_nonneg _) hq.le) (hsmall r hr).1 (hsmall r hr).2
  · obtain ⟨S, hS⟩ := (hready r₀ le_rfl).1
    refine ⟨⟨S.1, ?_⟩, hS⟩
    simpa only [Fintype.card_fin] using S.2

end

end DFVSGames.Quadratic

namespace DFVSGames.Gadget.BaseConstruction

open Quadratic QuadraticStageNoise Harmonic Parameters
open scoped Classical

noncomputable section

variable {F : Type} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance indexDecidableEq : DecidableEq (BlockOrientationIndex F) := Classical.decEq _

local instance indexNonempty : Nonempty (BlockOrientationIndex F) := by
  have hA : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  obtain ⟨A⟩ := hA
  exact ⟨⟨A, chosenBlockOrientation A⟩⟩

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem theta_le_one : fieldLineTheta F ≤ 1 := by
  have hc : (1 : ℚ) ≤ Nat.card (FieldLine F) := by
    exact_mod_cast (Nat.succ_le_iff.mpr (card_FieldLine_pos (F := F)))
  exact (inv_anti₀ (by norm_num : (0 : ℚ) < 1) hc).trans_eq (by norm_num)

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem rate_eq_one_sub_theta : rate F = 1 - fieldLineTheta F := by
  rw [rate, fieldLineTheta_eq, one_div]

theorem quotient_detection
    (r₀ : ℕ) (ε : ℚ) (hr₀ : 0 < r₀)
    (hbudget : badRankCoefficient r₀ * ε ≤ 1)
    (hgeneric : ∀ r : ℕ, r ≤ r₀ → nongenericFraction F r ≤ ε)
    (S₀ : Submodule (ZMod 2) (Vec F))
    (hrank : Module.finrank (ZMod 2) S₀ = r₀) (hS₀ : IsGeneric S₀)
    {E : Type} [AddCommGroup E] [Module (ZMod 2) E]
    (T : (quotientStage (F := F) (depth r₀ (fieldLineTheta F))).Input →ₗ[ZMod 2] E)
    (hinj : Function.Injective
      (T.comp (quotientStage (F := F) (depth r₀ (fieldLineTheta F))).embed)) :
    (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
      if T ((quotientStage (F := F) (depth r₀ (fieldLineTheta F))).noise t) ≠ 0
      then 1 else 0) := by
  classical
  let n := depth r₀ (fieldLineTheta F)
  let : Fintype (stage (F := F) n).Noise := DescentProbability.noiseFintype
    (blockEmbedding (F := F)) aggregate_blockEmbedding_surjective Q n
  have hJ : Function.Surjective
      (aggregate (OrientedBlockKernel.orientedBlockLinear (F := F))) := by
    exact aggregate_blockEmbedding_surjective (F := F)
  have hfull : ∀ L : Lift (stage (F := F) n)
      (⊤ : Submodule (ZMod 2) (Module.Dual (ZMod 2) (Vec F))),
      (1 / 4 : ℚ) ≤ probability (fun t => ∃ z, L.family z ((stage n).noise t) ≠ 0) := by
    intro L
    exact BaseDetection.full_lift_detection hJ r₀ ε hr₀ hbudget hgeneric S₀ hrank hS₀ L
  have h := QuotientDetection.target_detection_after_quotient
    (stage (F := F) n) T (1 / 4) hfull hinj
  change (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average
    (fun t : (stage (F := F) n).Noise =>
      if T (StageQuotient.noise (stage (F := F) n) t) ≠ 0 then 1 else 0)
  rw [StageNoiseRecurrence.average_eq_expect]
  exact h

theorem quotient_error_le (p : ℚ) (r₀ : ℕ)
    (hgeom : (1 - fieldLineTheta F) ^ depth r₀ (fieldLineTheta F) ≤ p) :
    StageNoiseRecurrence.error
      (quotientStage (F := F) (depth r₀ (fieldLineTheta F))) ≤ p := by
  rw [quotientStage_error, rate_eq_one_sub_theta]
  have hpow : 0 ≤ (1 - fieldLineTheta F) ^ depth r₀ (fieldLineTheta F) :=
    pow_nonneg (sub_nonneg.mpr theta_le_one) _
  have hcoef : 1 - 1 / (Nat.card F : ℚ) ^ 3 ≤ 1 :=
    sub_le_self _ (by positivity)
  exact (mul_le_of_le_one_left hpow hcoef).trans hgeom

theorem exists_base (p : ℚ) (hp : 0 < p) :
    ∃ d : ℕ, 0 < d ∧ ∃ n : ℕ,
      StageNoiseRecurrence.error (quotientStage (F := BinaryField d) n) ≤ p ∧
      ∀ (E : Type) [AddCommGroup E] [Module (ZMod 2) E]
        (T : (quotientStage (F := BinaryField d) n).Input →ₗ[ZMod 2] E),
        Function.Injective (T.comp (quotientStage (F := BinaryField d) n).embed) →
        (1 / 4 : ℚ) ≤ StageNoiseRecurrence.average (fun t =>
          if T ((quotientStage (F := BinaryField d) n).noise t) ≠ 0 then 1 else 0) := by
  obtain ⟨r₀, ε, hr₀, hε, _hεone, hbudget, hgeom⟩ := effective_parameters p hp
  obtain ⟨d, hd, _hdim, hgeneric, S₀, hS₀⟩ :=
    exists_uniform_generic_field r₀ ε hε
  refine ⟨d, hd, depth r₀ (fieldLineTheta (BinaryField d)), ?_, ?_⟩
  · exact quotient_error_le p r₀
      (hgeom _ BaseDetection.theta_pos theta_le_one)
  · intro E _ _ T hinj
    exact quotient_detection r₀ ε hr₀ hbudget hgeneric S₀.1 S₀.2 hS₀ T hinj

end

end DFVSGames.Gadget.BaseConstruction

end OAI
