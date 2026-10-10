import Mathlib
import OAI.Computability.DirectedFeedback.Games.ActualAdviceSampling

namespace OAI

namespace DFVSGames.Gadget

open scoped BigOperators

variable {k I P R X B S : Type*} [Field k] [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X]
variable [AddCommGroup B] [Module k B]
variable [AddCommGroup S] [Module k S]

def tupleEmbed (e : R →ₗ[k] P) : (I → R) →ₗ[k] (I → P) where
  toFun h i := e (h i)
  map_add' u v := by ext; simp
  map_smul' c v := by ext; simp

omit [Fintype I] in
theorem tupleEmbed_single (e : R →ₗ[k] P) (i : I) (h : R) :
    tupleEmbed e (Pi.single i h) = Pi.single i (e h) := by
  ext j
  by_cases hij : i = j
  · subst j; simp [tupleEmbed]
  · simp [tupleEmbed, hij]

theorem shiftAggregate_single (J : I → B →ₗ[k] X × B)
    (lam : R →ₗ[k] B) (i : I) (h : R) :
    shiftAggregate J lam (Pi.single i h) = J i (lam h) := by
  classical
  simp [shiftAggregate, aggregate, Pi.single_apply, apply_ite, map_zero]

theorem parent_lift_common_child
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (hlam : Function.Surjective lam)
    (ψ : S →ₗ[k] ((I → P) →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z (h : parentShifts J lam),
      ψ z (parentEmbed J lam e h) = ζ z (parentLogical J lam h)) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ i z h,
      ψ z (Pi.single i (e h)) =
        γ z (J i (lam h)).1 + ζ z (J i (lam h)).2 := by
  let a := (LinearMap.fst k X B).comp (shiftAggregate J lam)
  let b := (LinearMap.snd k X B).comp (shiftAggregate J lam)
  let Ψ : S →ₗ[k] ((I → R) →ₗ[k] k) :=
    { toFun := fun z => (ψ z).comp (tupleEmbed e)
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  have ha : Function.Surjective a :=
    aggregate_fst_surjective _ (shiftAggregate_surjective J hJ lam hlam)
  obtain ⟨γ, hγ⟩ := common_parent_factorization a b ha Ψ ζ (by
    intro z h hh
    exact hlift z ⟨h, hh⟩)
  refine ⟨γ, fun i z h => ?_⟩
  have heq := hγ z (Pi.single i h)
  change ψ z (tupleEmbed e (Pi.single i h)) =
    γ z (shiftAggregate J lam (Pi.single i h)).1 +
      ζ z (shiftAggregate J lam (Pi.single i h)).2 at heq
  simpa only [tupleEmbed_single, shiftAggregate_single] using heq

theorem parent_lift_child_kernel
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (hlam : Function.Surjective lam)
    (ψ : S →ₗ[k] ((I → P) →ₗ[k] k)) (ζ : S →ₗ[k] (B →ₗ[k] k))
    (hlift : ∀ z (h : parentShifts J lam),
      ψ z (parentEmbed J lam e h) = ζ z (parentLogical J lam h))
    (i : I) (z : S) (h : R) (hh : lam h = 0) :
    ψ z (Pi.single i (e h)) = 0 := by
  obtain ⟨γ, hγ⟩ := parent_lift_common_child J hJ e lam hlam ψ ζ hlift
  simpa [hh] using hγ i z h

end DFVSGames.Gadget

namespace DFVSGames.Gadget

universe u v

variable {k : Type u} {B : Type v} [Field k]
variable [AddCommGroup B] [Module k B] [Finite B]

structure Lift (s : Stage k B) (S : Submodule k (B →ₗ[k] k)) where
  family : S →ₗ[k] (s.Input →ₗ[k] k)
  agrees : ∀ z h, family z (s.embed h) = z.val (s.logical h)

def Lift.restrict {s : Stage k B} {S T : Submodule k (B →ₗ[k] k)}
    (L : Lift s T) (hST : S ≤ T) : Lift s S where
  family := L.family.comp (Submodule.inclusion hST)
  agrees := by intro z h; exact L.agrees _ h

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X]

def singleInput (i : I) (P : Type v) [AddCommGroup P] [Module k P] :
    P →ₗ[k] (I → P) where
  toFun p := Pi.single i p
  map_add' a b := by ext j; by_cases h : i = j <;> simp [h]
  map_smul' c p := by ext j; by_cases h : i = j <;> simp [h]

def childCharacter (J : I → B →ₗ[k] X × B)
    {S : Submodule k (B →ₗ[k] k)} (γ : S →ₗ[k] (X →ₗ[k] k)) (i : I) :
    S →ₗ[k] (B →ₗ[k] k) where
  toFun z := (γ z).comp ((LinearMap.fst k X B).comp (J i)) +
    z.val.comp ((LinearMap.snd k X B).comp (J i))
  map_add' a b := by ext; simp; abel
  map_smul' c z := by ext; simp [smul_add]

omit [Finite B] in
theorem exists_common_child_character
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S) :
    ∃ γ : S →ₗ[k] (X →ₗ[k] k), ∀ i z h,
      L.family z (Pi.single i (s.embed h)) = childCharacter J γ i z (s.logical h) := by
  have hlift : ∀ z (h : parentShifts J s.logical),
      L.family z (parentEmbed J s.logical s.embed h) =
        z.val (parentLogical J s.logical h) := by
    intro z h
    exact L.agrees z h
  have hcommon := parent_lift_common_child (S := S) J hJ s.embed s.logical
    s.logical_surjective
  obtain ⟨γ, hγ⟩ := hcommon L.family S.subtype hlift
  exact ⟨γ, fun i z h => hγ i z h⟩

def descendantFamily {s : Stage k B} {S : Submodule k (B →ₗ[k] k)}
    (ψ : S →ₗ[k] ((I → s.Input) →ₗ[k] k)) (i : I)
    (φ : S →ₗ[k] (B →ₗ[k] k))
    (sectionMap : LinearMap.range φ →ₗ[k] S) :
    LinearMap.range φ →ₗ[k] (s.Input →ₗ[k] k) where
  toFun z := (ψ (sectionMap z)).comp (singleInput i s.Input)
  map_add' a b := by ext; simp
  map_smul' c z := by ext; simp

omit [Finite B] in

theorem exists_descendant_lift
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S)
    (γ : S →ₗ[k] (X →ₗ[k] k))
    (hγ : ∀ i z h, L.family z (Pi.single i (s.embed h)) =
      childCharacter J γ i z (s.logical h)) (i : I) :
    ∃ (L' : Lift s (LinearMap.range (childCharacter J γ i)))
      (sectionMap : LinearMap.range (childCharacter J γ i) →ₗ[k] S),
      (∀ z, childCharacter J γ i (sectionMap z) = z.val) ∧
      (∀ z p, L'.family z p = L.family (sectionMap z) (Pi.single i p)) := by
  let φ : S →ₗ[k] (B →ₗ[k] k) := childCharacter J γ i
  let : Module.Free k (LinearMap.range φ) :=
    Module.Free.of_divisionRing k (LinearMap.range φ)
  let : Module.Projective k (LinearMap.range φ) := Module.Projective.of_free
  obtain ⟨σ, hσ⟩ := φ.rangeRestrict.exists_rightInverse_of_surjective
    φ.range_rangeRestrict
  have hσ' (z : LinearMap.range φ) : φ (σ z) = z.val :=
    congrArg Subtype.val (congrArg (fun f => f z) hσ)
  let L' : Lift s (LinearMap.range φ) :=
    { family := descendantFamily L.family i φ σ
      agrees := by
        intro z h
        change L.family (σ z) (Pi.single i (s.embed h)) = z.val (s.logical h)
        rw [hγ, hσ'] }
  exact ⟨L', σ, hσ', fun z p => rfl⟩

omit [Finite B] in

theorem descendant_detection_implies_parent
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (Q : X → B) (s : Stage k B) (S : Submodule k (B →ₗ[k] k))
    (L : Lift (Stage.next J hJ Q s) S)
    {S' : Submodule k (B →ₗ[k] k)} (L' : Lift s S')
    (sectionMap : S' →ₗ[k] S) (i : I)
    (hfamily : ∀ z p, L'.family z p = L.family (sectionMap z) (Pi.single i p))
    (n : s.Noise) (hdetect : ∃ z, L'.family z (s.noise n) ≠ 0) :
    ∃ z, L.family z ((Stage.next J hJ Q s).noise (i, n)) ≠ 0 := by
  obtain ⟨z, hz⟩ := hdetect
  refine ⟨sectionMap z, ?_⟩
  simpa only [hfamily, Stage.next] using hz

end DFVSGames.Gadget

noncomputable section

open scoped BigOperators
open Module

namespace DFVSGames.Gadget.Orientation

section FiniteAction

variable {G X : Type*} [Group G] [MulAction G X] [Fintype G] [Fintype X]

omit [Fintype X] in

theorem sum_action_eq (x y : X) (h : ∃ a : G, a • x = y) (f : X → ℚ) :
    (∑ g : G, f (g • x)) = ∑ g : G, f (g • y) := by
  obtain ⟨a, rfl⟩ := h
  symm
  exact Fintype.sum_equiv (Equiv.mulRight a) _ _ (fun g => by simp [mul_smul])

theorem card_mul_sum_action (x : X)
    (transitive : ∀ y : X, ∃ a : G, a • x = y) (f : X → ℚ) :
    (Fintype.card X : ℚ) * (∑ g : G, f (g • x)) =
      (Fintype.card G : ℚ) * (∑ y : X, f y) := by
  calc
    (Fintype.card X : ℚ) * (∑ g : G, f (g • x)) =
        ∑ y : X, ∑ g : G, f (g • x) := by simp
    _ = ∑ y : X, ∑ g : G, f (g • y) := by
      apply Finset.sum_congr rfl
      intro y _
      exact sum_action_eq x y (transitive y) f
    _ = ∑ g : G, ∑ y : X, f (g • y) := Finset.sum_comm
    _ = ∑ _g : G, ∑ y : X, f y := by
      apply Finset.sum_congr rfl
      intro g _
      exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
    _ = (Fintype.card G : ℚ) * (∑ y : X, f y) := by simp

theorem mean_action (x : X)
    (transitive : ∀ y : X, ∃ a : G, a • x = y) (f : X → ℚ) :
    (∑ g : G, f (g • x)) / Fintype.card G =
      (∑ y : X, f y) / Fintype.card X := by
  have : Nonempty X := ⟨x⟩
  have hG : (Fintype.card G : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hX : (Fintype.card X : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  apply (div_eq_div_iff hG hX).2
  simpa [mul_comm] using card_mul_sum_action x transitive f

end FiniteAction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]

theorem exists_map_eq_of_finrank_eq (E F : Submodule K V)
    (h : finrank K E = finrank K F) :
    ∃ a : V ≃ₗ[K] V, E.map a.toLinearMap = F := by
  let e : E ≃ₗ[K] F := LinearEquiv.ofFinrankEq E F h
  obtain ⟨a, ha⟩ := Submodule.exists_linearEquiv_restrict_eq e
  refine ⟨a, ?_⟩
  ext v
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (ha ⟨u, hu⟩) ▸ (e ⟨u, hu⟩).property
  · intro hv
    obtain ⟨u, hu⟩ := e.surjective ⟨v, hv⟩
    refine ⟨u, u.property, ?_⟩
    exact (ha u).symm.trans (congrArg Subtype.val hu)

omit [FiniteDimensional K V] in

theorem rank_map (E : Submodule K V) (a : V ≃ₗ[K] V) :
    finrank K (E.map a.toLinearMap) = finrank K E :=
  a.finrank_map_eq E

def RankSpace (K V : Type*) [Field K] [AddCommGroup V] [Module K V] (r : ℕ) :=
  {E : Submodule K V // finrank K E = r}

instance rankSpaceAction (r : ℕ) : MulAction (V ≃ₗ[K] V) (RankSpace K V r) where
  smul a E := ⟨E.val.map a.toLinearMap, (a.finrank_map_eq E.val).trans E.property⟩
  one_smul E := by
    apply Subtype.ext
    exact E.val.map_id
  mul_smul a b E := by
    apply Subtype.ext
    exact E.val.map_comp b.toLinearMap a.toLinearMap

theorem rankSpace_transitive {r : ℕ} (E F : RankSpace K V r) :
    ∃ a : V ≃ₗ[K] V, a • E = F := by
  obtain ⟨a, ha⟩ := exists_map_eq_of_finrank_eq E.val F.val
    (E.property.trans F.property.symm)
  exact ⟨a, Subtype.ext ha⟩

theorem mean_oriented_subspace {r : ℕ} [Fintype (V ≃ₗ[K] V)]
    [Fintype (RankSpace K V r)] (E : RankSpace K V r) (f : RankSpace K V r → ℚ) :
    (∑ a : V ≃ₗ[K] V, f (a • E)) / Fintype.card (V ≃ₗ[K] V) =
      (∑ F : RankSpace K V r, f F) / Fintype.card (RankSpace K V r) :=
  mean_action E (rankSpace_transitive E) f

variable {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U]

theorem rank_dual_pullback (E : Submodule K (Module.Dual K U)) (J : B ≃ₗ[K] U) :
    finrank K (E.map J.dualMap.toLinearMap) = finrank K E :=
  J.dualMap.finrank_map_eq E

def orientationEquiv (J₀ : B ≃ₗ[K] U) : (B ≃ₗ[K] U) ≃ (U ≃ₗ[K] U) where
  toFun J := J₀.symm.trans J
  invFun a := J₀.trans a
  left_inv J := by ext x; simp
  right_inv a := by ext x; simp

theorem mean_map_equiv [FiniteDimensional K U] (E : Submodule K B) (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)] [Fintype (U ≃ₗ[K] U)]
    [Fintype (RankSpace K U (finrank K E))]
    (f : RankSpace K U (finrank K E) → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ F : RankSpace K U (finrank K E), f F) /
        Fintype.card (RankSpace K U (finrank K E)) := by
  let E₀ : RankSpace K U (finrank K E) :=
    ⟨E.map J₀.toLinearMap, J₀.finrank_map_eq E⟩
  have hsum : (∑ J : B ≃ₗ[K] U, f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) =
      ∑ a : U ≃ₗ[K] U, f (a • E₀) := by
    apply Fintype.sum_equiv (orientationEquiv J₀)
    intro J
    congr 1
    apply Subtype.ext
    change E.map J.toLinearMap =
      (E.map J₀.toLinearMap).map (J₀.symm.trans J).toLinearMap
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp
  rw [hsum, Fintype.card_congr (orientationEquiv J₀)]
  exact mean_oriented_subspace E₀ f

def dualOrientationEquiv [FiniteDimensional K B] [FiniteDimensional K U] :
    (B ≃ₗ[K] U) ≃ (Module.Dual K U ≃ₗ[K] Module.Dual K B) where
  toFun J := J.dualMap
  invFun e := ((Module.evalEquiv K B).trans e.dualMap).trans (Module.evalEquiv K U).symm
  left_inv J := by
    ext b
    apply (Module.evalEquiv K U).injective
    ext φ
    simp
  right_inv e := by
    ext φ b
    simp

theorem mean_dual_pullback [FiniteDimensional K B] [FiniteDimensional K U]
    (E : Submodule K (Module.Dual K U)) (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)]
    [Fintype (Module.Dual K U ≃ₗ[K] Module.Dual K B)]
    [Fintype (Module.Dual K B ≃ₗ[K] Module.Dual K B)]
    [Fintype (RankSpace K (Module.Dual K B) (finrank K E))]
    (f : RankSpace K (Module.Dual K B) (finrank K E) → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨E.map J.dualMap.toLinearMap, J.dualMap.finrank_map_eq E⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ F : RankSpace K (Module.Dual K B) (finrank K E), f F) /
        Fintype.card (RankSpace K (Module.Dual K B) (finrank K E)) := by
  let e := dualOrientationEquiv (K := K) (B := B) (U := U)
  have hsum := Fintype.sum_equiv e
    (fun J : B ≃ₗ[K] U => f ⟨E.map J.dualMap.toLinearMap, J.dualMap.finrank_map_eq E⟩)
    (fun J : Module.Dual K U ≃ₗ[K] Module.Dual K B =>
      f ⟨E.map J.toLinearMap, J.finrank_map_eq E⟩) (fun _ => rfl)
  rw [hsum, Fintype.card_congr e]
  exact mean_map_equiv E J₀.dualMap f

end DFVSGames.Gadget.Orientation
end

noncomputable section

open scoped BigOperators

namespace DFVSGames.Gadget.OrientationVectors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem exists_equiv_map_nonzero (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ e : V ≃ₗ[K] V, e x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton K V x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton K V y hy
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨e, ?_⟩
  have h := (he (ex 1)).symm
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h

theorem equiv_apply_ne_zero {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] (J : B ≃ₗ[K] U) {b : B} (hb : b ≠ 0) :
    J b ≠ 0 := by
  intro h
  apply hb
  exact J.injective (h.trans (map_zero J).symm)

instance nonzeroAction : MulAction (V ≃ₗ[K] V) {x : V // x ≠ 0} where
  smul a x := ⟨a x.val, equiv_apply_ne_zero a x.property⟩
  one_smul x := by apply Subtype.ext; rfl
  mul_smul a b x := by apply Subtype.ext; rfl

theorem nonzero_transitive (x y : {v : V // v ≠ 0}) :
    ∃ a : V ≃ₗ[K] V, a • x = y := by
  obtain ⟨a, ha⟩ := exists_equiv_map_nonzero (K := K) x.val y.val x.property y.property
  exact ⟨a, Subtype.ext ha⟩

theorem mean_oriented_nonzero [Fintype (V ≃ₗ[K] V)]
    [Fintype {x : V // x ≠ 0}] (x : {v : V // v ≠ 0})
    (f : {v : V // v ≠ 0} → ℚ) :
    (∑ a : V ≃ₗ[K] V, f (a • x)) / Fintype.card (V ≃ₗ[K] V) =
      (∑ y : {v : V // v ≠ 0}, f y) / Fintype.card {v : V // v ≠ 0} :=
  Orientation.mean_action x (nonzero_transitive x) f

theorem mean_iso_nonzero {B U : Type*} [AddCommGroup B] [Module K B]
    [AddCommGroup U] [Module K U] (J₀ : B ≃ₗ[K] U)
    [Fintype (B ≃ₗ[K] U)] [Fintype (U ≃ₗ[K] U)]
    [Fintype {u : U // u ≠ 0}] (b : B) (hb : b ≠ 0)
    (f : {u : U // u ≠ 0} → ℚ) :
    (∑ J : B ≃ₗ[K] U, f ⟨J b, equiv_apply_ne_zero J hb⟩) /
        Fintype.card (B ≃ₗ[K] U) =
      (∑ u : {u : U // u ≠ 0}, f u) / Fintype.card {u : U // u ≠ 0} := by
  let x : {u : U // u ≠ 0} := ⟨J₀ b, equiv_apply_ne_zero J₀ hb⟩
  have hsum : (∑ J : B ≃ₗ[K] U, f ⟨J b, equiv_apply_ne_zero J hb⟩) =
      ∑ a : U ≃ₗ[K] U, f (a • x) := by
    apply Fintype.sum_equiv (Orientation.orientationEquiv J₀)
    intro J
    congr 1
    apply Subtype.ext
    change J b = (J₀.symm.trans J) (J₀ b)
    simp
  rw [hsum, Fintype.card_congr (Orientation.orientationEquiv J₀)]
  exact mean_oriented_nonzero x f

end DFVSGames.Gadget.OrientationVectors
end

namespace DFVSGames.Quadratic

abbrev Vec (F : Type*) := Fin 3 → F

variable {F : Type*} [Field F]

def Q (x : Vec F) : Vec F := ![x 1 * x 2, x 0 * x 2, x 0 * x 1]

def D (x a : Vec F) : Vec F :=
  ![x 1 * a 2 + a 1 * x 2, x 0 * a 2 + a 0 * x 2,
    x 0 * a 1 + a 0 * x 1]

def dot (v y : Vec F) : F := v 0 * y 0 + v 1 * y 1 + v 2 * y 2

@[simp] theorem Q_zero : Q (0 : Vec F) = 0 := by
  ext i
  fin_cases i <;> simp [Q]

theorem Q_add (x a : Vec F) : Q (x + a) = Q x + Q a + D x a := by
  ext i
  fin_cases i <;> simp [Q, D] <;> ring

@[simp] theorem D_zero_left (a : Vec F) : D 0 a = 0 := by
  ext i
  fin_cases i <;> simp [D]

@[simp] theorem D_zero_right (x : Vec F) : D x 0 = 0 := by
  ext i
  fin_cases i <;> simp [D]

theorem D_comm (x a : Vec F) : D x a = D a x := by
  ext i
  fin_cases i <;> simp [D, add_comm]

theorem D_add_left (x y a : Vec F) : D (x + y) a = D x a + D y a := by
  ext i
  fin_cases i <;> simp [D] <;> ring

theorem D_add_right (x a b : Vec F) : D x (a + b) = D x a + D x b := by
  rw [D_comm, D_add_left, D_comm a x, D_comm b x]

theorem D_smul_left (t : F) (x a : Vec F) : D (t • x) a = t • D x a := by
  ext i
  fin_cases i <;> simp [D, smul_eq_mul] <;> ring

theorem D_smul_right (t : F) (x a : Vec F) : D x (t • a) = t • D x a := by
  rw [D_comm, D_smul_left, D_comm a x]

@[simp] theorem dot_zero_right (v : Vec F) : dot v 0 = 0 := by simp [dot]
@[simp] theorem dot_zero_left (y : Vec F) : dot 0 y = 0 := by simp [dot]

theorem dot_add_right (v y z : Vec F) : dot v (y + z) = dot v y + dot v z := by
  simp [dot]
  ring

theorem dot_smul_right (v y : Vec F) (t : F) : dot v (t • y) = t * dot v y := by
  simp [dot, smul_eq_mul]
  ring

theorem dot_smul_left (v y : Vec F) (t : F) : dot (t • v) y = t * dot v y := by
  simp [dot, smul_eq_mul]
  ring

def line (v : Vec F) : Submodule F (Vec F) := Submodule.span F {v}

def hyperplane (v : Vec F) : Submodule F (Vec F) where
  carrier := {y | dot v y = 0}
  zero_mem' := dot_zero_right v
  add_mem' := by
    intro y z hy hz
    rw [Set.mem_ofPred_eq, dot_add_right, hy, hz, add_zero]
  smul_mem' := by
    intro t y hy
    rw [Set.mem_ofPred_eq, dot_smul_right, hy, mul_zero]

@[simp] theorem mem_hyperplane (v y : Vec F) : y ∈ hyperplane v ↔ dot v y = 0 := Iff.rfl

theorem mem_line_iff (v a : Vec F) : a ∈ line v ↔ ∃ t : F, t • v = a :=
  Submodule.mem_span_singleton

variable [CharP F 2]

@[simp] theorem vec_add_self (x : Vec F) : x + x = 0 := by
  ext i
  exact CharTwo.add_self_eq_zero (x i)

theorem D_eq_polar (x a : Vec F) : D x a = Q (x + a) + Q x + Q a := by
  rw [Q_add]
  have h : Q x + Q a + D x a + Q x + Q a =
      D x a + (Q x + Q x) + (Q a + Q a) := by ac_rfl
  rw [h, vec_add_self, vec_add_self, add_zero, add_zero]

private theorem cross_self_zero_inline_Block (u w s t : F) :
    (t * u) * (s * w) + (s * u) * (t * w) = 0 := by
  calc
    _ = (t * s * u * w) + (t * s * u * w) := by ring
    _ = 0 := CharTwo.add_self_eq_zero _

theorem D_smul_smul_zero (v : Vec F) (t s : F) : D (t • v) (s • v) = 0 := by
  ext i
  fin_cases i <;> simp [D, smul_eq_mul, cross_self_zero_inline_Block]

theorem dot_D_smul (v x : Vec F) (t : F) : dot v (D x (t • v)) = 0 := by
  change v 0 * (x 1 * (t * v 2) + (t * v 1) * x 2) +
      v 1 * (x 0 * (t * v 2) + (t * v 0) * x 2) +
      v 2 * (x 0 * (t * v 1) + (t * v 0) * x 1) = 0
  calc
    _ = (t * (v 0 * v 2 * x 1 + v 0 * v 1 * x 2 + v 1 * v 2 * x 0)) +
        (t * (v 0 * v 2 * x 1 + v 0 * v 1 * x 2 + v 1 * v 2 * x 0)) := by ring
    _ = 0 := CharTwo.add_self_eq_zero _

theorem D_mem_hyperplane (v x a : Vec F) (ha : a ∈ line v) :
    D x a ∈ hyperplane v := by
  obtain ⟨t, rfl⟩ := (mem_line_iff v a).mp ha
  exact dot_D_smul v x t

theorem D_eq_zero_of_mem_line (v a b : Vec F)
    (ha : a ∈ line v) (hb : b ∈ line v) : D a b = 0 := by
  obtain ⟨t, rfl⟩ := (mem_line_iff v a).mp ha
  obtain ⟨s, rfl⟩ := (mem_line_iff v b).mp hb
  exact D_smul_smul_zero v t s

theorem Q_add_of_mem_line (v a b : Vec F)
    (ha : a ∈ line v) (hb : b ∈ line v) : Q (a + b) = Q a + Q b := by
  rw [Q_add, D_eq_zero_of_mem_line v a b ha hb, add_zero]

variable [Algebra (ZMod 2) F]

def U (v : Vec F) : Submodule (ZMod 2) (Vec F × Vec F) where
  carrier := {p | p.1 ∈ line v ∧ dot v (p.2 + Q p.1) = 0}
  zero_mem' := by simp [Q_zero]
  add_mem' := by
    intro p q hp hq
    refine ⟨(line v).add_mem hp.1 hq.1, ?_⟩
    change dot v ((p.2 + q.2) + Q (p.1 + q.1)) = 0
    rw [Q_add_of_mem_line v p.1 q.1 hp.1 hq.1]
    have h : (p.2 + q.2) + (Q p.1 + Q q.1) =
        (p.2 + Q p.1) + (q.2 + Q q.1) := by ac_rfl
    rw [h, dot_add_right, hp.2, hq.2, add_zero]
  smul_mem' := by
    intro c p hp
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · simp [Q_zero]
    · simpa using hp

@[simp] theorem mem_U (v : Vec F) (p : Vec F × Vec F) :
    p ∈ U v ↔ p.1 ∈ line v ∧ dot v (p.2 + Q p.1) = 0 := Iff.rfl

theorem pair_mem_U (v a w : Vec F) (ha : a ∈ line v) (hw : w ∈ hyperplane v) :
    (a, Q a + w) ∈ U v := by
  refine ⟨ha, ?_⟩
  change dot v (Q a + w + Q a) = 0
  have h : Q a + w + Q a = w + (Q a + Q a) := by ac_rfl
  simpa [h] using hw

theorem mem_U_iff_exists (v : Vec F) (p : Vec F × Vec F) :
    p ∈ U v ↔ ∃ a ∈ line v, ∃ w ∈ hyperplane v, p = (a, Q a + w) := by
  constructor
  · intro hp
    refine ⟨p.1, hp.1, p.2 + Q p.1, hp.2, ?_⟩
    apply Prod.ext
    · rfl
    · change p.2 = Q p.1 + (p.2 + Q p.1)
      have h : Q p.1 + (p.2 + Q p.1) = p.2 + (Q p.1 + Q p.1) := by ac_rfl
      rw [h, vec_add_self, add_zero]
  · rintro ⟨a, ha, w, hw, rfl⟩
    exact pair_mem_U v a w ha hw

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

abbrev FieldLine (F : Type*) [Field F] := Projectivization F (Vec F)

variable {F : Type*} [Field F]

noncomputable def lineGenerator (A : FieldLine F) : Vec F := A.rep

theorem lineGenerator_ne_zero (A : FieldLine F) : lineGenerator A ≠ 0 :=
  A.rep_nonzero

theorem line_lineGenerator (A : FieldLine F) : line (lineGenerator A) = A.submodule :=
  A.submodule_eq.symm

theorem fieldLine_finrank (A : FieldLine F) : Module.finrank F A.submodule = 1 :=
  A.finrank_submodule

variable [Finite F]

theorem card_FieldLine : Nat.card (FieldLine F) = Nat.card F ^ 2 + Nat.card F + 1 := by
  have h := Projectivization.card_of_finrank F (Vec F) (n := 3)
    (Module.finrank_fin_fun (R := F))
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, add_comm, add_left_comm, add_assoc] using h

theorem card_fieldLine_submodules :
    Nat.card {A : Submodule F (Vec F) // Module.finrank F A = 1} =
      Nat.card F ^ 2 + Nat.card F + 1 := by
  rw [← Nat.card_congr (Projectivization.equivSubmodule F (Vec F))]
  exact card_FieldLine

theorem card_FieldLine_pos : 0 < Nat.card (FieldLine F) := by
  rw [card_FieldLine]
  exact Nat.succ_pos _

theorem reciprocal_card_FieldLine :
    (Nat.card (FieldLine F) : ℚ)⁻¹ =
      ((Nat.card F : ℚ) ^ 2 + Nat.card F + 1)⁻¹ := by
  rw [card_FieldLine]
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]

end DFVSGames.Quadratic

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]

abbrev lineBinary (v : Vec F) : Submodule (ZMod 2) (Vec F) :=
  (line v).restrictScalars (ZMod 2)

abbrev hyperplaneBinary (v : Vec F) : Submodule (ZMod 2) (Vec F) :=
  (hyperplane v).restrictScalars (ZMod 2)

omit [Algebra (ZMod 2) F] in
private theorem Q_cancel_inline_BlockDimension (a w : Vec F) : Q a + (w + Q a) = w := by
  calc
    _ = w + (Q a + Q a) := by ac_rfl
    _ = w := by rw [vec_add_self, add_zero]

def blockParametrization (v : Vec F) :
    (lineBinary v × hyperplaneBinary v) ≃ₗ[ZMod 2] U v where
  toFun p := ⟨((p.1 : Vec F), Q (p.1 : Vec F) + (p.2 : Vec F)),
    pair_mem_U v p.1 p.2 p.1.2 p.2.2⟩
  invFun p := (⟨p.1.1, p.2.1⟩, ⟨p.1.2 + Q p.1.1, p.2.2⟩)
  left_inv := by
    intro p
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      change Q (p.1 : Vec F) + (p.2 : Vec F) + Q (p.1 : Vec F) = p.2
      have h : Q (p.1 : Vec F) + (p.2 : Vec F) + Q (p.1 : Vec F) =
          Q (p.1 : Vec F) + ((p.2 : Vec F) + Q (p.1 : Vec F)) := by rw [add_assoc]
      rw [h, Q_cancel_inline_BlockDimension]
  right_inv := by
    intro p
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact Q_cancel_inline_BlockDimension p.1.1 p.1.2
  map_add' := by
    intro p q
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Q ((p.1 : Vec F) + (q.1 : Vec F)) + ((p.2 : Vec F) + (q.2 : Vec F)) =
        (Q (p.1 : Vec F) + (p.2 : Vec F)) + (Q (q.1 : Vec F) + (q.2 : Vec F))
      rw [Q_add_of_mem_line v p.1 q.1 p.1.2 q.1.2]
      ac_rfl
  map_smul' := by
    intro c p
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · apply Subtype.ext
      apply Prod.ext <;> simp [Q_zero]
    · simp

def dotLinear (v : Vec F) : Vec F →ₗ[F] F where
  toFun := dot v
  map_add' := dot_add_right v
  map_smul' := by intro t y; exact dot_smul_right v y t

omit [CharP F 2] [Algebra (ZMod 2) F] in
@[simp] theorem dotLinear_apply (v y : Vec F) : dotLinear v y = dot v y := rfl

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem dotLinear_ker (v : Vec F) : LinearMap.ker (dotLinear v) = hyperplane v := rfl

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem dotLinear_surjective (v : Vec F) (hv : v ≠ 0) :
    Function.Surjective (dotLinear v) := by
  classical
  have hi : ∃ i : Fin 3, v i ≠ 0 := by
    by_cases h : ∀ i, v i = 0
    · exact False.elim (hv (funext h))
    · exact not_forall.mp h
  obtain ⟨i, hi⟩ := hi
  intro z
  refine ⟨Pi.single i (z / v i), ?_⟩
  have hsingle (j : Fin 3) (a : F) : dot v (Pi.single j a) = v j * a := by
    fin_cases j <;> simp [dot]
  change dot v (Pi.single i (z / v i)) = z
  rw [hsingle]
  calc
    v i * (z / v i) = (v i * (v i)⁻¹) * z := by ring
    _ = z := by rw [mul_inv_cancel₀ hi, one_mul]

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem finrank_hyperplane (v : Vec F) (hv : v ≠ 0) :
    Module.finrank F (hyperplane v) = 2 := by
  have h := (dotLinear v).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (dotLinear_surjective v hv),
    finrank_top, Module.finrank_self, dotLinear_ker,
    Module.finrank_fin_fun] at h
  omega

omit [CharP F 2] [Algebra (ZMod 2) F] in
theorem finrank_line (v : Vec F) (hv : v ≠ 0) :
    Module.finrank F (line v) = 1 :=
  finrank_span_singleton hv

variable [FiniteDimensional (ZMod 2) F]

omit [CharP F 2] in
theorem finrank_lineBinary (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (lineBinary v) = Module.finrank (ZMod 2) F := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F (lineBinary v),
    ((line v).restrictScalarsEquiv (ZMod 2)).finrank_eq, finrank_line v hv, mul_one]

omit [CharP F 2] in
theorem finrank_hyperplaneBinary (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (hyperplaneBinary v) = 2 * Module.finrank (ZMod 2) F := by
  rw [← Module.finrank_mul_finrank (ZMod 2) F (hyperplaneBinary v),
    ((hyperplane v).restrictScalarsEquiv (ZMod 2)).finrank_eq, finrank_hyperplane v hv,
    mul_comm]

theorem finrank_U (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (U v) = 3 * Module.finrank (ZMod 2) F := by
  rw [← (blockParametrization v).finrank_eq, Module.finrank_prod,
    finrank_lineBinary v hv, finrank_hyperplaneBinary v hv]
  omega

theorem finrank_U_eq_finrank_vec (v : Vec F) (hv : v ≠ 0) :
    Module.finrank (ZMod 2) (U v) = Module.finrank (ZMod 2) (Vec F) := by
  rw [finrank_U v hv, ← Module.finrank_mul_finrank (ZMod 2) F (Vec F),
    Module.finrank_fin_fun, mul_comm]

end DFVSGames.Quadratic

end OAI
