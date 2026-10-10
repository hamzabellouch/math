import OAI.Algebra.OddKaplansky.Diagrams

namespace OAI

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6

section
noncomputable section
open scoped Classical
open Monoid Function
namespace OddKaplansky.MultipleHNN

universe u v
variable {H : Type u} [Group H] {I : Type v}
variable (A B : I → Subgroup H) (φ : ∀ i, A i ≃* B i)

def con : Con (Monoid.Coprod H (FreeGroup I)) := conGen fun x y =>
  ∃ (i : I) (a : A i), x = Coprod.inr (FreeGroup.of i) * Coprod.inl (a : H) ∧
    y = Coprod.inl (φ i a : H) * Coprod.inr (FreeGroup.of i)

def Extension := (con A B φ).Quotient

instance : Group (Extension A B φ) := by delta Extension; infer_instance

def of : H →* Extension A B φ := (con A B φ).mk'.comp Coprod.inl

def letter (i : I) : Extension A B φ := (con A B φ).mk' (Coprod.inr (FreeGroup.of i))

lemma letter_mul_of (i : I) (a : A i) :
    letter A B φ i * of A B φ a = of A B φ (φ i a) * letter A B φ i :=
  (Con.eq _).mpr <| ConGen.Rel.of _ _ ⟨i, a, rfl, rfl⟩

def lift {G : Type portUniverse1} [Group G] (f : H →* G) (t : I → G)
    (ht : ∀ i (a : A i), t i * f a = f (φ i a) * t i) : Extension A B φ →* G :=
  Con.lift _ (Coprod.lift f (FreeGroup.lift t)) (Con.conGen_le.mpr (by
    rintro _ _ ⟨i, a, rfl, rfl⟩
    simp [ht]))

@[simp] lemma lift_of {G : Type portUniverse2} [Group G] (f : H →* G) (t : I → G)
    (ht : ∀ i (a : A i), t i * f a = f (φ i a) * t i) (h : H) :
    lift A B φ f t ht (of A B φ h) = f h := by
  change Coprod.lift f (FreeGroup.lift t) (Coprod.inl h) = f h
  simp

@[simp] lemma lift_letter {G : Type portUniverse3} [Group G] (f : H →* G) (t : I → G)
    (ht : ∀ i (a : A i), t i * f a = f (φ i a) * t i) (i : I) :
    lift A B φ f t ht (letter A B φ i) = t i := by
  change Coprod.lift f (FreeGroup.lift t) (Coprod.inr (FreeGroup.of i)) = t i
  simp

theorem finite_partial_realization (S : Finset I) :
    ∃ (G : Type (max u v)) (_ : Group G) (f : H →* G),
      Function.Injective f ∧ ∃ t : I → G,
        ∀ i ∈ S, ∀ a : A i, t i * f a = f (φ i a) * t i := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨ULift.{v} H, inferInstance, (MulEquiv.ulift : ULift.{v} H ≃* H).symm.toMonoidHom,
      (MulEquiv.ulift : ULift.{v} H ≃* H).symm.injective, fun _ => 1, ?_⟩
    simp
  | @insert i S hi ih =>
    obtain ⟨G, hG, f, hf, t, ht⟩ := ih
    let fA := (A i).equivMapOfInjective f hf
    let fB := (B i).equivMapOfInjective f hf
    let ψ : (A i).map f ≃* (B i).map f := fA.symm.trans ((φ i).trans fB)
    let E := HNNExtension G ((A i).map f) ((B i).map f) ψ
    let emb : G →* E := HNNExtension.of
    let t' : I → E := fun j => if j = i then HNNExtension.t else emb (t j)
    refine ⟨E, inferInstance, emb.comp f,
      (HNNExtension.of_injective ψ).comp hf, t', ?_⟩
    intro j hj a
    rcases Finset.mem_insert.mp hj with rfl | hj
    · have h := HNNExtension.t_mul_of (φ := ψ) (fA a)
      simpa [t', fA, fB, ψ, emb] using h
    · by_cases hji : j = i
      · subst j
        have h := HNNExtension.t_mul_of (φ := ψ) (fA a)
        simpa [t', fA, fB, ψ, emb] using h
      · simpa [t', hji, ← map_mul] using congrArg emb (ht j hj a)

theorem of_injective [Fintype I] : Function.Injective (of A B φ) := by
  obtain ⟨G, hG, f, hf, t, ht⟩ := finite_partial_realization A B φ Finset.univ
  intro x y h
  apply hf
  have h' := congrArg (lift A B φ f t (fun i a => ht i (Finset.mem_univ i) a)) h
  simpa using h'

@[elab_as_elim]
theorem induction_on {P : Extension A B φ → Prop} (x : Extension A B φ)
    (hof : ∀ h, P (of A B φ h)) (ht : ∀ i, P (letter A B φ i))
    (hmul : ∀ x y, P x → P y → P (x * y)) (hinv : ∀ x, P x → P x⁻¹) : P x := by
  change ∀ left right : (con A B φ).Quotient, P left → P right → P (left * right) at hmul
  change ∀ element : (con A B φ).Quotient, P element → P element⁻¹ at hinv
  change ∀ element : H, P ((con A B φ).mk' (Coprod.inl element)) at hof
  obtain ⟨w, rfl⟩ := (Con.mk'_surjective (c := con A B φ)) x
  induction w using Coprod.induction_on with
  | inl h => exact hof h
  | inr w =>
    induction w using FreeGroup.induction_on with
    | one => simpa only [map_one] using hof 1
    | of i => exact ht i
    | inv_of i ih =>
      change P ((con A B φ).mk' (Coprod.inr ((FreeGroup.of i)⁻¹)))
      rw [map_inv, map_inv]
      exact hinv _ ih
    | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb
  | mul a b ha hb => simpa only [map_mul] using hmul _ _ ha hb

theorem of_central (z : H) (hz : ∀ h : H, Commute h z)
    (ha : ∀ i, z ∈ A i) (hφ : ∀ i, (φ i ⟨z, ha i⟩ : H) = z) :
    ∀ x : Extension A B φ, Commute x (of A B φ z) := by
  intro x
  induction x using induction_on A B φ with
  | hof h => exact (hz h).map (of A B φ)
  | ht i =>
    have h := letter_mul_of A B φ i ⟨z, ha i⟩
    rw [hφ i] at h
    exact h
  | hmul x y hx hy => exact hx.mul_left hy
  | hinv x hx => exact hx.inv_left

instance [Finite I] [Group.FG H] : Group.FG (Extension A B φ) := by
  obtain ⟨S, hS, hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG H)
  let T : Set (Extension A B φ) := of A B φ '' S ∪ Set.range (letter A B φ)
  apply Group.fg_iff.mpr
  refine ⟨T, ?_, (hfin.image _).union (Set.finite_range _)⟩
  apply top_unique
  intro x hxTop
  clear hxTop
  induction x using induction_on A B φ with
  | hof h =>
    have hh : h ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top h
    induction hh using Subgroup.closure_induction with
    | mem h hh => exact Subgroup.subset_closure (Or.inl ⟨h, hh, rfl⟩)
    | one => simp
    | mul h k _ _ hh hk => simpa using (Subgroup.closure T).mul_mem hh hk
    | inv h _ hh => simpa using (Subgroup.closure T).inv_mem hh
  | ht i => exact Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  | hmul x y hx hy => exact (Subgroup.closure T).mul_mem hx hy
  | hinv x hx => exact (Subgroup.closure T).inv_mem hx

end OddKaplansky.MultipleHNN

namespace OddKaplansky.StarAmalgam
open Monoid
variable {I G : Type} [Group G] {D S : I → Type}
variable [∀ i, Group (D i)] [∀ i, Group (S i)]
variable (f : ∀ i, S i →* G) (g : ∀ i, S i →* D i)

abbrev Free := Coprod G (CoprodI D)

def con : Con (Free (G := G) (D := D)) := conGen fun x y =>
  ∃ (i : I) (s : S i), x = Coprod.inl (f i s) ∧ y = Coprod.inr (CoprodI.of (g i s))

def Amalgam := (con f g).Quotient
instance : _root_.Group (Amalgam f g) := by delta Amalgam; infer_instance

def ofBase : G →* Amalgam f g := (con f g).mk'.comp Coprod.inl

def ofFactor (i : I) : D i →* Amalgam f g :=
  (con f g).mk'.comp (Coprod.inr.comp CoprodI.of)

lemma identify (i : I) (s : S i) : ofBase f g (f i s) = ofFactor f g i (g i s) :=
  (Con.eq _).mpr <| ConGen.Rel.of _ _ ⟨i, s, rfl, rfl⟩

def lift {E : Type portUniverse4} [_root_.Group E] (b : G →* E) (d : ∀ i, D i →* E)
    (h : ∀ i s, b (f i s) = d i (g i s)) : Amalgam f g →* E :=
  Con.lift _ (Coprod.lift b (CoprodI.lift d)) (Con.conGen_le.mpr (by
    rintro _ _ ⟨i, s, rfl, rfl⟩
    simp [h]))

@[simp] lemma lift_base {E : Type portUniverse5} [_root_.Group E] (b : G →* E) (d : ∀ i, D i →* E)
    (h : ∀ i s, b (f i s) = d i (g i s)) (x : G) :
    lift f g b d h (ofBase f g x) = b x := by
  change Coprod.lift b (CoprodI.lift d) (Coprod.inl x) = b x
  simp

@[simp] lemma lift_factor {E : Type portUniverse6} [_root_.Group E] (b : G →* E) (d : ∀ i, D i →* E)
    (h : ∀ i s, b (f i s) = d i (g i s)) (i : I) (x : D i) :
    lift f g b d h (ofFactor f g i x) = d i x := by
  change Coprod.lift b (CoprodI.lift d) (Coprod.inr (CoprodI.of x)) = d i x
  simp

theorem faithful_realization [Fintype I]
    (hf : ∀ i, Function.Injective (f i)) (hg : ∀ i, Function.Injective (g i)) :
    ∃ (E : Type) (_ : _root_.Group E) (b : G →* E) (d : ∀ i, D i →* E),
      Function.Injective b ∧ (∀ i, Function.Injective (d i)) ∧
      ∀ i s, b (f i s) = d i (g i s) := by
  let a : ∀ i, S i →* Free (G := G) (D := D) := fun i =>
    Coprod.inr.comp (CoprodI.of.comp (g i))
  let b₀ : ∀ i, S i →* Free (G := G) (D := D) := fun i => Coprod.inl.comp (f i)
  have ha : ∀ i, Function.Injective (a i) := fun i =>
    Coprod.inr_injective.comp ((CoprodI.of_injective i).comp (hg i))
  have hb : ∀ i, Function.Injective (b₀ i) := fun i => Coprod.inl_injective.comp (hf i)
  let ea : ∀ i, S i ≃* (a i).range := fun i =>
    MulEquiv.ofBijective (a i).rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr (ha i), (a i).rangeRestrict_surjective⟩
  let eb : ∀ i, S i ≃* (b₀ i).range := fun i =>
    MulEquiv.ofBijective (b₀ i).rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr (hb i), (b₀ i).rangeRestrict_surjective⟩
  let A := fun i => (a i).range
  let B := fun i => (b₀ i).range
  let φ : ∀ i, A i ≃* B i := fun i => (ea i).symm.trans (eb i)
  let E := MultipleHNN.Extension A B φ
  let emb : Free (G := G) (D := D) →* E := MultipleHNN.of A B φ
  have hemb : Function.Injective emb := MultipleHNN.of_injective A B φ
  let b : G →* E := emb.comp Coprod.inl
  let d : ∀ i, D i →* E := fun i =>
    (MulAut.conj (MultipleHNN.letter A B φ i)).toMonoidHom.comp
      (emb.comp (Coprod.inr.comp CoprodI.of))
  refine ⟨E, inferInstance, b, d, hemb.comp Coprod.inl_injective, ?_, ?_⟩
  · intro i
    exact (MulAut.conj _).injective.comp
      (hemb.comp (Coprod.inr_injective.comp (CoprodI.of_injective i)))
  · intro i s
    have h := MultipleHNN.letter_mul_of A B φ i (ea i s)
    have hφ : φ i (ea i s) = eb i s := by simp [φ]
    rw [hφ] at h
    change MultipleHNN.letter A B φ i * emb (a i s) =
      emb (b₀ i s) * MultipleHNN.letter A B φ i at h
    have hh := congrArg (fun x => x * (MultipleHNN.letter A B φ i)⁻¹) h
    simpa [b, d, a, b₀, mul_assoc] using hh.symm

variable [Fintype I]

theorem ofBase_injective (hf : ∀ i, Function.Injective (f i))
    (hg : ∀ i, Function.Injective (g i)) : Function.Injective (ofBase f g) := by
  obtain ⟨E, hE, b, d, hb, hd, h⟩ := faithful_realization f g hf hg
  intro x y hxy
  apply hb
  simpa using congrArg (lift f g b d h) hxy

theorem ofFactor_injective (hf : ∀ i, Function.Injective (f i))
    (hg : ∀ i, Function.Injective (g i)) (i : I) : Function.Injective (ofFactor f g i) := by
  obtain ⟨E, hE, b, d, hb, hd, h⟩ := faithful_realization f g hf hg
  intro x y hxy
  apply hd i
  simpa using congrArg (lift f g b d h) hxy

end OddKaplansky.StarAmalgam

end
end

end OAI
