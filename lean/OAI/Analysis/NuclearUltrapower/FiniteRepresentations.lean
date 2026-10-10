import Mathlib

namespace OAI

section
noncomputable section
universe u v w
open scoped TensorProduct Topology
open Filter
noncomputable section
open scoped InnerProductSpace

namespace NuclearUltrapower

/-- A nonzero finite-dimensional unitary representation. -/
structure FiniteUnitaryRep (Γ : Type u) [Group Γ] where
  carrier : Type v
  [normed : NormedAddCommGroup carrier]
  [inner : InnerProductSpace ℂ carrier]
  [complete : CompleteSpace carrier]
  [finite : FiniteDimensional ℂ carrier]
  [nontrivial : Nontrivial carrier]
  action : Γ →* (carrier ≃ₗᵢ[ℂ] carrier)

attribute [instance] FiniteUnitaryRep.normed FiniteUnitaryRep.inner
  FiniteUnitaryRep.complete FiniteUnitaryRep.finite FiniteUnitaryRep.nontrivial
instance {Γ : Type u} [Group Γ] : CoeSort (FiniteUnitaryRep.{u,v} Γ) (Type v) :=
  ⟨FiniteUnitaryRep.carrier⟩

variable {Γ : Type u} [Group Γ]

namespace FiniteUnitaryRep

/-- Irreducibility with exactly the invariant-subspace convention of the source. -/
def Irreducible (π : FiniteUnitaryRep.{u,v} Γ) : Prop :=
  ∀ W : Submodule ℂ π, (∀ g x, x ∈ W → π.action g x ∈ W) → W = ⊥ ∨ W = ⊤

def pull (π : FiniteUnitaryRep.{u,v} Γ) (θ : Monoid.End Γ) : FiniteUnitaryRep.{u,v} Γ :=
  { π with action := π.action.comp θ }

@[simp] theorem pull_action (π : FiniteUnitaryRep.{u,v} Γ) (θ : Monoid.End Γ) (g : Γ) :
    (π.pull θ).action g = π.action (θ g) := rfl

@[simp] theorem pull_one (π : FiniteUnitaryRep.{u,v} Γ) : π.pull 1 = π := by
  cases π
  simp [pull, show (1 : Monoid.End Γ) = MonoidHom.id Γ from rfl]

@[simp] theorem pull_pull (π : FiniteUnitaryRep.{u,v} Γ) (θ ψ : Monoid.End Γ) :
    (π.pull θ).pull ψ = π.pull (θ * ψ) := rfl

/-- Isometric inclusion as a subrepresentation: no quotients of representations. -/
def Embeds (π τ : FiniteUnitaryRep.{u,v} Γ) : Prop :=
  ∃ T : π →ₗᵢ[ℂ] τ, ∀ g x, T (π.action g x) = τ.action g (T x)

/-- Unitary equivalence, not merely equality of dimensions. -/
def Equivalent (π τ : FiniteUnitaryRep.{u,v} Γ) : Prop :=
  ∃ T : π ≃ₗᵢ[ℂ] τ, ∀ g x, T (π.action g x) = τ.action g (T x)

@[refl] theorem embeds_refl (π : FiniteUnitaryRep.{u,v} Γ) : π.Embeds π :=
  ⟨LinearIsometry.id, fun _ _ => rfl⟩

@[refl] theorem equivalent_refl (π : FiniteUnitaryRep.{u,v} Γ) : π.Equivalent π :=
  ⟨LinearIsometryEquiv.refl ℂ π, fun _ _ => rfl⟩

@[trans] theorem Embeds.trans {π τ ρ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Embeds τ) (k : τ.Embeds ρ) : π.Embeds ρ := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨U, hU⟩ := k
  exact ⟨U.comp T, fun g x => by change U (T (π.action g x)) = _; rw [hT, hU]; rfl⟩

@[symm] theorem Equivalent.symm {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Equivalent τ) : τ.Equivalent π := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T.symm, fun g x => ?_⟩
  apply T.injective
  simp only [T.apply_symm_apply, hT]

@[trans] theorem Equivalent.trans {π τ ρ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Equivalent τ) (k : τ.Equivalent ρ) : π.Equivalent ρ := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨U, hU⟩ := k
  exact ⟨T.trans U, fun g x => by change U (T (π.action g x)) = _; rw [hT, hU]; rfl⟩

theorem Equivalent.embeds {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Equivalent τ) : π.Embeds τ := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T.toLinearIsometry, hT⟩

theorem Embeds.pull {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Embeds τ) (θ : Monoid.End Γ) : (π.pull θ).Embeds (τ.pull θ) := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun g => hT (θ g)⟩

theorem Equivalent.pull {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Equivalent τ) (θ : Monoid.End Γ) : (π.pull θ).Equivalent (τ.pull θ) := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T, fun g => hT (θ g)⟩

/-- Equidimensional subrepresentations are unitary equivalences. -/
theorem Embeds.equivalent_of_finrank_eq {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Embeds τ) (hd : Module.finrank ℂ π = Module.finrank ℂ τ) : π.Equivalent τ := by
  obtain ⟨T, hT⟩ := h
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).mp T.injective
  exact ⟨LinearIsometryEquiv.ofSurjective T hs, hT⟩

/-- Irreducibility is preserved under unitary equivalence. -/
theorem Equivalent.irreducible {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Equivalent τ) (hπ : π.Irreducible) : τ.Irreducible := by
  obtain ⟨T, hT⟩ := h
  intro W hW
  have hi : ∀ g x, x ∈ W.comap T.toLinearEquiv.toLinearMap →
      π.action g x ∈ W.comap T.toLinearEquiv.toLinearMap := by
    intro g x hx
    change T (π.action g x) ∈ W
    rw [hT]
    exact hW g (T x) hx
  rcases hπ _ hi with hb | ht
  · left
    apply bot_unique
    intro y hy
    change y = 0
    obtain ⟨x, rfl⟩ := T.surjective y
    have hx : x ∈ W.comap T.toLinearEquiv.toLinearMap := hy
    rw [hb, Submodule.mem_bot] at hx
    simp [hx]
  · right
    apply top_unique
    intro y _
    obtain ⟨x, rfl⟩ := T.surjective y
    have hx : x ∈ W.comap T.toLinearEquiv.toLinearMap := by rw [ht]; trivial
    exact hx

/-- A nonzero subrepresentation of an irreducible representation is the whole. -/
theorem Embeds.equivalent_of_irreducible {π τ : FiniteUnitaryRep.{u,v} Γ}
    (h : π.Embeds τ) (hτ : τ.Irreducible) : π.Equivalent τ := by
  obtain ⟨T, hT⟩ := h
  have hr : ∀ g x, x ∈ T.toLinearMap.range → τ.action g x ∈ T.toLinearMap.range := by
    rintro g x ⟨y, rfl⟩
    exact ⟨π.action g y, hT g y⟩
  rcases hτ _ hr with hb | ht
  · have hz : T.toLinearMap = 0 := LinearMap.range_eq_bot.mp hb
    obtain ⟨x, hx⟩ := exists_ne (0 : π)
    have hzx : T x = 0 := congrArg (fun L : π →ₗ[ℂ] τ => L x) hz
    have := T.injective (show T x = T 0 by rw [hzx, map_zero])
    exact False.elim (hx this)
  · exact ⟨LinearIsometryEquiv.ofSurjective T (LinearMap.range_eq_top.mp ht), hT⟩

/-- If a deeper pullback is irreducible, every preceding pullback is irreducible. -/
theorem irreducible_of_pull {π : FiniteUnitaryRep.{u,v} Γ} (θ : Monoid.End Γ)
    (h : (π.pull θ).Irreducible) : π.Irreducible := by
  intro W hW
  exact h W (fun g => hW (θ g))

/-- Periodicity forces *every* positive pullback to remain irreducible, the
critical step often missed when a predecessor chain has a nonempty tail. -/
theorem irreducible_pull_of_periodic {π : FiniteUnitaryRep.{u,v} Γ}
    (hπ : π.Irreducible) (θ : Monoid.End Γ) {p : ℕ} (hp : 0 < p)
    (he : π.Equivalent (π.pull (θ ^ p))) (j : ℕ) : (π.pull (θ ^ j)).Irreducible := by
  have hit (k : ℕ) : π.Equivalent (π.pull (θ ^ (p * k))) := by
    induction k with
    | zero => simpa using π.equivalent_refl
    | succ k ih =>
        have ht := he.pull (θ ^ (p * k))
        rw [pull_pull, ← pow_add] at ht
        simpa [Nat.mul_succ, Nat.add_comm] using ih.trans ht
  have hj : j ≤ p * j := Nat.le_mul_of_pos_left j hp
  have hi := (hit j).irreducible hπ
  have heq : (π.pull (θ ^ j)).pull (θ ^ (p * j - j)) = π.pull (θ ^ (p * j)) := by
    rw [pull_pull, ← pow_add, Nat.add_sub_of_le hj]
  rw [← heq] at hi
  exact irreducible_of_pull _ hi

/-- Source lem:finite-predecessor-cycle, expressed using any finite list of
representatives. Duplicates are harmless; no bijective predecessor selection is
assumed, and the possibly nonempty tail is fully accounted for. -/
theorem finite_predecessor_cycle {ι : Type*} [Finite ι]
    (π : ι → FiniteUnitaryRep.{u,v} Γ) (hπ : ∀ i, (π i).Irreducible)
    (θ : Monoid.End Γ) (hprev : ∀ i, ∃ j, (π i).Embeds ((π j).pull θ)) (i : ι) :
    ∃ p : ℕ, 0 < p ∧ (π i).Equivalent ((π i).pull (θ ^ p)) := by
  classical
  let f : ι → ι := fun i => (hprev i).choose
  have hf (i : ι) : (π i).Embeds ((π (f i)).pull θ) := (hprev i).choose_spec
  have hc (n : ℕ) (i : ι) : (π i).Embeds ((π (f^[n] i)).pull (θ ^ n)) := by
    induction n generalizing i with
    | zero => simpa using (π i).embeds_refl
    | succ n ih =>
        have ht := (hf i).trans ((ih (f i)).pull θ)
        simpa only [pull_pull, ← pow_succ, Function.iterate_succ_apply] using ht
  have hex : ∃ l m : ℕ, l < m ∧ f^[l] i = f^[m] i := by
    obtain ⟨l, m, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => f^[n] i)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨l, m, hlt, heq⟩
    · exact ⟨m, l, hlt, heq.symm⟩
  obtain ⟨l, m, hlm, heq⟩ := hex
  let p := m - l
  have hp : 0 < p := Nat.sub_pos_of_lt hlm
  have heq' : f^[p] (f^[l] i) = f^[l] i := by
    rw [← Function.iterate_add_apply]
    dsimp [p]
    rw [Nat.sub_add_cancel hlm.le, ← heq]
  have hb : (π (f^[l] i)).Embeds ((π (f^[l] i)).pull (θ ^ p)) := by
    simpa only [heq'] using hc p (f^[l] i)
  have he := hb.equivalent_of_finrank_eq rfl
  have hi := irreducible_pull_of_periodic (hπ (f^[l] i)) θ hp he l
  have hin := (hc l i).equivalent_of_irreducible hi
  have hmid := he.pull (θ ^ l)
  have hend := (hin.pull (θ ^ p)).symm
  simp only [pull_pull, ← pow_add] at hmid hend
  rw [Nat.add_comm l p] at hend
  exact ⟨p, hp, hin.trans (hmid.trans hend)⟩

/-- Restriction to an invariant subspace, with the inherited Hilbert norm. -/
def restrict (π : FiniteUnitaryRep.{u,v} Γ) (W : Submodule ℂ π)
    (hW : ∀ g x, x ∈ W → π.action g x ∈ W) [Nontrivial W] : FiniteUnitaryRep.{u,v} Γ where
  carrier := W
  action := {
    toFun g := {
      toFun x := ⟨π.action g x, hW g x x.property⟩
      invFun x := ⟨π.action g⁻¹ x, hW g⁻¹ x x.property⟩
      left_inv x := by ext; change (π.action g⁻¹ * π.action g) x.val = x.val; rw [← map_mul]; simp
      right_inv x := by ext; change (π.action g * π.action g⁻¹) x.val = x.val; rw [← map_mul]; simp
      map_add' x y := by ext; simp
      map_smul' c x := by ext; simp
      norm_map' x := (π.action g).norm_map x }
    map_one' := by ext; simp
    map_mul' g h := by ext; simp [map_mul] }

theorem restrict_embeds (π : FiniteUnitaryRep.{u,v} Γ) (W : Submodule ℂ π)
    (hW : ∀ g x, x ∈ W → π.action g x ∈ W) [Nontrivial W] :
    (π.restrict W hW).Embeds π :=
  ⟨W.subtypeₗᵢ, fun _ _ => rfl⟩

/-- Every nonzero finite-dimensional unitary representation has an irreducible
subrepresentation. This uses minimal dimension, not a semisimplicity assumption. -/
theorem exists_irreducible (π : FiniteUnitaryRep.{u,v} Γ) :
    ∃ τ : FiniteUnitaryRep.{u,v} Γ, τ.Irreducible ∧ τ.Embeds π := by
  let P (n : ℕ) := ∃ W : Submodule ℂ π, W ≠ ⊥ ∧
    (∀ g x, x ∈ W → π.action g x ∈ W) ∧ Module.finrank ℂ W = n
  have hP : ∃ n, P n := ⟨Module.finrank ℂ (⊤ : Submodule ℂ π),
    ⊤, top_ne_bot, fun _ _ _ => Submodule.mem_top, rfl⟩
  classical
  obtain ⟨W, hW0, hW, hdim⟩ := Nat.find_spec hP
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  refine ⟨π.restrict W hW, ?_, π.restrict_embeds W hW⟩
  intro V hV
  change Submodule ℂ W at V
  by_cases hV0 : V = ⊥
  · exact Or.inl hV0
  right
  let U : Submodule ℂ π := V.map W.subtype
  have hU0 : U ≠ ⊥ := by
    intro hU
    apply hV0
    apply le_antisymm ?_ bot_le
    intro x hx
    have hmem : (x : π) ∈ U := ⟨x, hx, rfl⟩
    rw [hU] at hmem
    exact W.subtype_injective hmem
  have hU (g : Γ) (x : π) (hx : x ∈ U) : π.action g x ∈ U := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨(π.restrict W hW).action g y, hV g y hy, rfl⟩
  have heq : Module.finrank ℂ U = Module.finrank ℂ V :=
    LinearEquiv.finrank_eq (V.equivMapOfInjective W.subtype W.subtype_injective).symm
  have hmin : Nat.find hP ≤ Module.finrank ℂ V := by
    rw [← heq]
    exact Nat.find_min' hP ⟨U, hU0, hU, rfl⟩
  have he : Module.finrank ℂ V = Module.finrank ℂ (π.restrict W hW) := by
    apply le_antisymm (Submodule.finrank_le V)
    exact hdim ▸ hmin
  exact Submodule.eq_top_of_finrank_eq he

end FiniteUnitaryRep
end NuclearUltrapower

end
end
end

end OAI
