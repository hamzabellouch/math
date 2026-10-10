import OAI.MathematicalPhysics.Heisenberg.ExchangeDeterminants

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix

namespace Heisenberg.LayeredExchange
open Exposure
variable {V W Ω : Type*} [Fintype V] [Fintype W] [Fintype Ω]
  [DecidableEq V] [DecidableEq W]
variable {R : Type*} [CommRing R]

lemma forwardHom_subtype (π : Equiv.Perm V) (P : V → Prop) [DecidablePred P]
    (h : ∀ x,P (π x) ↔ P x) :
    (forwardHom (R:=R) π).submatrix (fun x : {i // P i} => x.val) (fun x => x.val) =
      forwardHom (R:=R) (π.subtypePerm h) := by
  ext i j
  change (π.permMatrix R) j.val i.val = ((π.subtypePerm h).permMatrix R) j i
  simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    Option.mem_some_iff]
  congr 1
  apply propext
  constructor
  · exact fun he => Subtype.ext he
  · exact fun he => congrArg Subtype.val he

lemma forwardHom_reindex (π : Equiv.Perm V) (e : W ≃ V) :
    (forwardHom (R:=R) π).submatrix e e = forwardHom (R:=R) (e.symm.permCongr π) := by
  ext i j
  change (π.permMatrix R) (e j) (e i) = ((e.symm.permCongr π).permMatrix R) j i
  simp only [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
    Option.mem_some_iff,Equiv.permCongr_apply,Equiv.symm_symm]
  congr 1
  exact propext e.symm_apply_eq.symm

lemma determinantLaw_holes {μ : Ω → R} {π : Ω → Equiv.Perm V}
    (h : DeterminantLaw μ (fun ω => forwardHom (R:=R) (π ω)))
    (P : V → Prop) [DecidablePred P] (hi : ∀ ω x,P (π ω x) ↔ P x) :
    DeterminantLaw μ (fun ω => forwardHom (R:=R) ((π ω).subtypePerm (hi ω))) := by
  have hh := h.subtype P
  convert hh using 1
  funext ω
  exact (forwardHom_subtype (π ω) P (hi ω)).symm

lemma determinantLaw_reindexed {μ : Ω → R} {π : Ω → Equiv.Perm V}
    (h : DeterminantLaw μ (fun ω => forwardHom (R:=R) (π ω))) (e : W ≃ V) :
    DeterminantLaw μ (fun ω => forwardHom (R:=R) (e.symm.permCongr (π ω))) := by
  have hh := h.reindex e
  convert hh using 1
  funext ω
  exact (forwardHom_reindex (π ω) e).symm

end Heisenberg.LayeredExchange

open scoped Classical
namespace Heisenberg.Cycle

section
open Equiv
variable {V : Type*}
abbrev Classes (π : Perm V) := Quotient (Perm.SameCycle.setoid π)
def classOf (π : Perm V) (i : V) : Classes π := Quotient.mk _ i
lemma classOf_eq_iff (π : Perm V) (i j : V) :
    classOf π i = classOf π j ↔ π.SameCycle i j := Quotient.eq
@[simp] lemma classOf_apply (π : Perm V) (i : V) :
    classOf π (π i) = classOf π i :=
  (classOf_eq_iff π _ _).mpr ((Perm.SameCycle.refl π i).apply_left)
abbrev MissingClasses (π : Perm V) (P : Set V) :=
  {c : Classes π // ∀ i ∈ P, c ≠ classOf π i}
noncomputable def missingCount (π : Perm V) (P : Set V) : ℕ :=
  Nat.card (MissingClasses π P)

def colorSpace (π : Perm V) (P : Set V) : Submodule (ZMod 2) (V → ZMod 2) where
  carrier := {f | (∀ i, f (π i) = f i) ∧ ∀ i ∈ P, f i = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro f g ⟨hf,hfP⟩ ⟨hg,hgP⟩
    exact ⟨fun i => by simp [hf,hg],fun i hi => by simp [hfP i hi,hgP i hi]⟩
  smul_mem' := by
    rintro r f ⟨hf,hfP⟩
    exact ⟨fun i => by simp [hf],fun i hi => by simp [hfP i hi]⟩

lemma colorSpace_mem (π : Perm V) (P : Set V) (f : V → ZMod 2) :
    f ∈ colorSpace π P ↔ (∀ i, f (π i) = f i) ∧ ∀ i ∈ P, f i = 0 := Iff.rfl

variable [Fintype V]

lemma color_eq_of_sameCycle (π : Perm V) (P : Set V) (f : colorSpace π P)
    {i j : V} (h : π.SameCycle i j) : f.val i = f.val j := by
  obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
  have ha : ∀ n, f.val ((π^n) i) = f.val i := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ',Perm.mul_apply,f.property.1,ih]
  rw [← hn,ha]

def colorEquiv (π : Perm V) (P : Set V) :
    colorSpace π P ≃ (MissingClasses π P → ZMod 2) where
  toFun f c := Quotient.lift f.val (fun i j h => color_eq_of_sameCycle π P f h) c.val
  invFun c := ⟨fun i => if h : ∀ j ∈ P, classOf π i ≠ classOf π j then c ⟨classOf π i,h⟩ else 0, by
    constructor
    · intro i
      simp only [classOf_apply]
    · intro i hi
      exact dite_eq_right (by intro h; exact h i hi rfl)⟩
  left_inv f := by
    apply Subtype.ext
    funext i
    dsimp
    split_ifs with h
    · rfl
    · obtain ⟨j,hj,hij⟩ := by simpa only [not_forall,not_not] using h
      have he := color_eq_of_sameCycle π P f ((classOf_eq_iff π i j).mp hij)
      exact (he.trans (f.property.2 j hj)).symm
  right_inv c := by
    funext q
    rcases q with ⟨q,hq⟩
    induction q using Quotient.inductionOn with | _ i =>
      dsimp
      split_ifs with h
      · rfl
      · exact (h hq).elim

 theorem card_colorSpace (π : Perm V) (P : Set V) :
    Nat.card (colorSpace π P) = 2 ^ missingCount π P := by
  let := Fintype.ofFinite (MissingClasses π P)
  rw [Nat.card_congr (colorEquiv π P),Nat.card_fun]
  simp [missingCount]

lemma finrank_comparison {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (A B : Submodule K W) (f : W →ₗ[K] K)
    (h : ∀ x ∈ A, f x = 0 → x ∈ B) :
    Module.finrank K A ≤ Module.finrank K B + 1 := by
  let g : A →ₗ[K] K := f.comp A.subtype
  let k : LinearMap.ker g →ₗ[K] B :=
    { toFun := fun x => ⟨x.val.val,h x.val.val x.val.property x.property⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  have hk : Function.Injective k := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : B => z.val) he
  have hd := k.finrank_le_finrank_of_injective hk
  have hr : Module.finrank K (LinearMap.range g) ≤ 1 := by
    simpa using (LinearMap.range g).finrank_le
  have ht := g.finrank_range_add_finrank_ker
  omega

 theorem missingCount_swap_le (π : Perm V) (P : Set V) (a b : V) :
    missingCount (π * swap a b) P ≤ missingCount π P + 1 := by
  let f : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun c => c a - c b
      map_add' := by intro x y; simp only [Pi.add_apply]; ring
      map_smul' := by intro r x; simp only [Pi.smul_apply, smul_sub, RingHom.id_apply] }
  have hr : Module.finrank (ZMod 2) (colorSpace (π * swap a b) P) ≤
      Module.finrank (ZMod 2) (colorSpace π P) + 1 := by
    apply finrank_comparison _ _ f
    intro c hc he
    have hab : c a = c b := sub_eq_zero.mp he
    refine ⟨?_,hc.2⟩
    intro i
    have ht := hc.1 (swap a b i)
    simpa only [Perm.mul_apply,swap_apply_self] using ht.trans (by
      by_cases hi : i = a
      · subst i; simpa using hab.symm
      by_cases hi' : i = b
      · subst i; simpa using hab
      rw [swap_apply_of_ne_of_ne hi hi'])
  have hc (σ : Perm V) : missingCount σ P = Module.finrank (ZMod 2) (colorSpace σ P) := by
    have h1 := card_colorSpace σ P
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := colorSpace σ P)
    have he : (2:ℕ) ^ missingCount σ P = 2 ^ Module.finrank (ZMod 2) (colorSpace σ P) := by
      rw [← h1]
      simpa using h2
    exact Nat.pow_right_injective (by decide : 1 < (2:ℕ)) he
  simpa only [hc] using hr

 theorem weight_swap_le (π : Perm V) (P : Set V) (a b : V) :
    (2:ℝ) ^ missingCount (π * swap a b) P ≤ 2 * (2:ℝ) ^ missingCount π P := by
  calc
    _ ≤ (2:ℝ) ^ (missingCount π P + 1) :=
      pow_le_pow_right₀ (by norm_num) (missingCount_swap_le π P a b)
    _ = _ := by rw [pow_succ]; ring

end

open Equiv
variable {V : Type*} [Fintype V]

def MissingSet (π : Perm V) (P : Set V) : Set V :=
  {i | ∀ j ∈ P, classOf π i ≠ classOf π j}

omit [Fintype V] in
lemma missing_apply (π : Perm V) (P : Set V) (i : V) :
    π i ∈ MissingSet π P ↔ i ∈ MissingSet π P := by
  simp only [MissingSet,Set.mem_ofPred_eq,classOf_apply]

omit [Fintype V] in
lemma missing_disjoint_pins (π : Perm V) (P : Set V) : Disjoint (MissingSet π P) P := by
  apply Set.disjoint_left.mpr
  intro i hi hP
  exact hi i hP rfl

lemma color_zero_not_missing (π : Perm V) (P : Set V) (f : colorSpace π P)
    (i : V) (hi : i ∉ MissingSet π P) : f.val i = 0 := by
  obtain ⟨j,hj⟩ := (not_forall.mp hi)
  obtain ⟨hjP,hij⟩ := Classical.not_imp.mp hj
  exact (color_eq_of_sameCycle π P f ((classOf_eq_iff π i j).mp (not_not.mp hij))).trans (f.property.2 j hjP)

theorem missing_weight_rigid (π τ : Perm V) (P : Set V)
    (hset : MissingSet π P = MissingSet τ P)
    (hval : ∀ i ∈ MissingSet π P, π i = τ i) :
    missingCount π P = missingCount τ P := by
  have hspace : colorSpace π P = colorSpace τ P := by
    apply le_antisymm
    · intro f hf
      refine ⟨?_,hf.2⟩
      intro i
      by_cases hi : i ∈ MissingSet π P
      · rw [← hval i hi]; exact hf.1 i
      · have hτ : τ i ∉ MissingSet π P := by
          rw [hset] at hi ⊢
          exact fun h => hi ((missing_apply τ P i).mp h)
        exact (color_zero_not_missing π P ⟨f,hf⟩ _ hτ).trans (color_zero_not_missing π P ⟨f,hf⟩ _ hi).symm
    · intro f hf
      refine ⟨?_,hf.2⟩
      intro i
      by_cases hi : i ∈ MissingSet π P
      · rw [hval i hi]; exact hf.1 i
      · have hπ : π i ∉ MissingSet τ P := by
          rw [← hset]
          exact fun h => hi ((missing_apply π P i).mp h)
        rw [hset] at hi
        exact (color_zero_not_missing τ P ⟨f,hf⟩ _ hπ).trans (color_zero_not_missing τ P ⟨f,hf⟩ _ hi).symm
  have he := congrArg (fun A : Submodule (ZMod 2) (V → ZMod 2) => Nat.card A) hspace
  rw [card_colorSpace,card_colorSpace] at he
  exact Nat.pow_right_injective (by decide : 1 < (2:ℕ)) he

lemma exposed_subset_missing (π τ : Perm V) (P : Set V)
    (hval : ∀ i ∈ MissingSet π P, π i = τ i) :
    MissingSet π P ⊆ MissingSet τ P := by
  intro i hi j hj he
  obtain ⟨n,hn⟩ := ((classOf_eq_iff τ i j).mp he).exists_nat_pow_eq
  have hiter : ∀ n : ℕ, (τ^n) i ∈ MissingSet π P := by
    intro n
    induction n with
    | zero => exact hi
    | succ n ih =>
      rw [pow_succ',Perm.mul_apply,← hval _ ih]
      exact (missing_apply π P _).mpr ih
  exact missing_disjoint_pins π P |>.le_bot ⟨hn ▸ hiter n,hj⟩

def OutsideHit (τ : Perm V) (P A : Set V) : Prop :=
  ∀ i ∉ A, ∃ j ∈ P, τ.SameCycle i j

lemma sameMissing_iff_outsideHit (π τ : Perm V) (P : Set V)
    (hval : ∀ i ∈ MissingSet π P, π i = τ i) :
    MissingSet τ P = MissingSet π P ↔ OutsideHit τ P (MissingSet π P) := by
  have hsub := exposed_subset_missing π τ P hval
  constructor
  · intro h i hi
    have hn : i ∉ MissingSet τ P := by rwa [h]
    simp only [MissingSet,Set.mem_ofPred_eq,not_forall,not_not] at hn
    obtain ⟨j,hj,hij⟩ := hn
    exact ⟨j,hj,(classOf_eq_iff τ i j).mp hij⟩
  · intro h
    apply Set.Subset.antisymm _ hsub
    intro i hi
    by_contra hn
    obtain ⟨j,hj,hij⟩ := h i hn
    exact hi j hj ((classOf_eq_iff τ i j).mpr hij)

end Heisenberg.Cycle
end

end OAI
