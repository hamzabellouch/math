import OAI.GroupTheory.Congruence.Basic
import OAI.GroupTheory.Congruence.Elementary
import OAI.GroupTheory.Congruence.Transfer

namespace OAI

/-!
Block stabilization, homology actions, quotient vanishing, and congruence cokernels.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.Blocks

section
open CoboundaryExpanders.Construction

def gammaStabilization (p a b m : ℕ) : Gamma p a m →* Gamma p (a + b) m where
  toFun g := ⟨stabilizeSL a b g.val, by
    change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m))
      (stabilizeSL a b g.val) = 1
    rw [stabilizeSL_map, g.property, map_one]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' g h := Subtype.ext (map_mul _ _ _)

def gammaReindex (p N m : ℕ) (e : Fin N ≃ Fin N) : Gamma p N m ≃* Gamma p N m where
  toFun g := ⟨reindexSL e g.val, by
    change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) (reindexSL e g.val) = 1
    rw [reindexSL_map, g.property, map_one]⟩
  invFun g := ⟨reindexSL e.symm g.val, by
    change Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk (powerIdeal p m)) (reindexSL e.symm g.val) = 1
    rw [reindexSL_map, g.property, map_one]⟩
  left_inv g := by apply Subtype.ext; exact (reindexSL e).left_inv g.val
  right_inv g := by apply Subtype.ext; exact (reindexSL e).right_inv g.val
  map_mul' g h := Subtype.ext (map_mul _ _ _)

end

open CoboundaryExpanders.Elementary CoboundaryExpanders.Construction
variable {A : Type*} [CommRing A]

@[simp] theorem reindexSL_E {N : ℕ} (e : Fin N ≃ Fin N) {i j : Fin N}
    (hij : i ≠ j) (c : A) :
    reindexSL e (E hij c) = E (show e i ≠ e j from fun he => hij (e.injective he)) c := by
  ext a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply,
    Matrix.one_apply, e.injective.eq_iff]

theorem stabilize_commutes_tail (a b : ℕ) (g : Matrix.SpecialLinearGroup (Fin a) A)
    {i j : Fin b} (hij : i ≠ j) (c : A) :
    Commute (E (show Fin.natAdd a i ≠ Fin.natAdd a j from
      fun he => hij (Fin.ext (by have := congrArg Fin.val he; simpa using this))) c)
      (stabilizeSL a b g) := by
  apply elementary_commutes_of_complement
  · exact stabilizeSL_right_row a b g j
  · exact fun k => stabilizeSL_right_col a b g k i

theorem exists_pair_permutation (a : ℕ) (i j : Fin (a + 2)) (hij : i ≠ j) :
    ∃ e : Equiv.Perm (Fin (a + 2)), e (Fin.natAdd a 0) = i ∧ e (Fin.natAdd a 1) = j := by
  classical
  let f : Fin 2 → Fin (a + 2) := Fin.natAdd a
  let g : Fin 2 → Fin (a + 2) := fun x => if x = 0 then i else j
  have hf : Function.Injective f := by
    intro x y h
    apply Fin.ext
    have he := congrArg Fin.val h
    change a + x.val = a + y.val at he
    omega
  have hg : Function.Injective g := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [g]
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  exact ⟨e, by simpa [f, g] using he 0, by simpa [f, g] using he 1⟩

theorem elementary_centralizes_complement (p a m : ℕ) (i j : Fin (a + 2))
    (hij : i ≠ j) (c : R p) :
    ∃ e : Equiv.Perm (Fin (a + 2)), ∀ x : Gamma p a m,
      Commute (E hij c)
        ((gammaReindex p (a + 2) m e (gammaStabilization p a 2 m x)).val) := by
  obtain ⟨e, hi, hj⟩ := exists_pair_permutation a i j hij
  refine ⟨e, fun x => ?_⟩
  have hc := stabilize_commutes_tail a 2 x.val (show (0 : Fin 2) ≠ 1 by decide) c
  have hm := hc.map (reindexSL e).toMonoidHom
  change Commute (reindexSL e (E _ c)) (reindexSL e (stabilizeSL a 2 x.val)) at hm
  rw [reindexSL_E] at hm
  change Commute (E hij c) (reindexSL e (stabilizeSL a 2 x.val))
  simpa only [hi, hj] using hm

end CoboundaryExpanders.Blocks

namespace CoboundaryExpanders.Actions
universe u
variable {k G H K : Type u} [CommRing k] [Group G] [Group H] [Group K]

def coeff (f : H →* G) : Rep.trivial k H k ⟶ Rep.res f (Rep.trivial k G k) :=
  𝟙 (Rep.trivial k H k)

def induced (f : H →* G) (j : ℕ) :
    groupHomology (Rep.trivial k H k) j ⟶ groupHomology (Rep.trivial k G k) j :=
  groupHomology.map f (coeff f) j

@[simp] theorem induced_id (j : ℕ) : induced (k := k) (MonoidHom.id G) j = 𝟙 _ :=
  groupHomology.map_id j

theorem induced_congr {f g : H →* G} (h : f = g) (j : ℕ) :
    induced (k := k) f j = induced g j := by rw [h]

theorem induced_comp (f : H →* G) (g : G →* K) (j : ℕ) :
    induced (k := k) (g.comp f) j = induced f j ≫ induced g j := by
  unfold induced
  rw [← groupHomology.map_comp]
  exact groupHomology.map_congr rfl rfl j

theorem induced_equiv_surjective (e : H ≃* G) (j : ℕ) :
    Function.Surjective (induced (k := k) e.toMonoidHom j) := by
  have he := induced_comp (k := k) e.symm.toMonoidHom e.toMonoidHom j
  have hc : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [hc, induced_id] at he
  intro x
  refine ⟨induced e.symm.toMonoidHom j x, ?_⟩
  exact (congrArg (fun f => ModuleCat.Hom.hom f x) he).symm

variable (S : Subgroup G) [S.Normal]

def conjugation (g : G) (j : ℕ) :
    groupHomology (Rep.trivial k S k) j ⟶ groupHomology (Rep.trivial k S k) j :=
  induced (MulAut.conjNormal (H := S) g).toMonoidHom j

@[simp] theorem conjugation_one (j : ℕ) : conjugation (k := k) S 1 j = 𝟙 _ := by
  unfold conjugation
  have he : (MulAut.conjNormal (H := S) (1 : G)).toMonoidHom = MonoidHom.id S := by
    ext x; simp
  rw [he, induced_id]

theorem conjugation_mul (g h : G) (j : ℕ) :
    conjugation (k := k) S (g * h) j = conjugation S h j ≫ conjugation S g j := by
  unfold conjugation
  rw [← induced_comp]
  apply induced_congr
  ext x
  simp [MulAut.conjNormal_apply, mul_assoc]

def fixingSubgroup (j : ℕ) : Subgroup G where
  carrier := {g | conjugation (k := k) S g j = 𝟙 _}
  one_mem' := conjugation_one S j
  mul_mem' := by
    intro g h hg hh
    change conjugation S (g * h) j = _
    rw [conjugation_mul, hg, hh, Category.id_comp]
  inv_mem' := by
    intro g hg
    have he := conjugation_mul (k := k) S g g⁻¹ j
    rw [mul_inv_cancel, conjugation_one] at he
    change conjugation S g j = 𝟙 _ at hg
    rw [hg, Category.comp_id] at he
    exact he.symm

theorem centralizer_fixes_image (φ : H →* S) (g : G)
    (hcomm : ∀ x : H, Commute g ((φ x : S) : G)) (j : ℕ) :
    induced (k := k) φ j ≫ conjugation S g j = induced φ j := by
  unfold conjugation
  rw [← induced_comp]
  apply induced_congr
  ext x
  change g * (φ x : G) * g⁻¹ = (φ x : G)
  rw [(hcomm x).eq, mul_assoc, mul_inv_cancel, mul_one]

theorem centralizer_fixes_of_surjective (φ : H →* S) (g : G)
    (hcomm : ∀ x : H, Commute g ((φ x : S) : G)) (j : ℕ)
    (hsurj : Function.Surjective (induced (k := k) φ j)) :
    g ∈ fixingSubgroup (k := k) S j := by
  change conjugation S g j = 𝟙 _
  have he := centralizer_fixes_image (k := k) S φ g hcomm j
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  exact congrArg (fun f => ModuleCat.Hom.hom f y) he

end CoboundaryExpanders.Actions

namespace CoboundaryExpanders.Blocks
open CoboundaryExpanders.Construction CoboundaryExpanders.Elementary
open CoboundaryExpanders.Actions CategoryTheory

instance gammaNormal (p a m : ℕ) : (Gamma p a m).Normal :=
  MonoidHom.normal_ker _

theorem elementary_fixes_complement_image (p a m : ℕ) (i j : Fin (a + 2))
    (hij : i ≠ j) (c : R p) (r : ℕ) :
    ∃ e : Equiv.Perm (Fin (a + 2)),
      induced (k := ZMod 2)
          ((gammaReindex p (a + 2) m e).toMonoidHom.comp (gammaStabilization p a 2 m)) r ≫
        conjugation (Gamma p (a + 2) m) (E hij c) r =
      induced ((gammaReindex p (a + 2) m e).toMonoidHom.comp (gammaStabilization p a 2 m)) r := by
  obtain ⟨e, he⟩ := elementary_centralizes_complement p a m i j hij c
  refine ⟨e, ?_⟩
  apply centralizer_fixes_image (k := ZMod 2)
  exact he

theorem trivial_action_of_stabilization (p a m r : ℕ) [Fact p.Prime]
    (hsurj : Function.Surjective (induced (k := ZMod 2) (gammaStabilization p a 2 m) r))
    (g : Matrix.SpecialLinearGroup (Fin (a + 2)) (R p)) :
    conjugation (k := ZMod 2) (Gamma p (a + 2) m) g r = 𝟙 _ := by
  change g ∈ fixingSubgroup (k := ZMod 2) (Gamma p (a + 2) m) r
  apply polynomial_SL_mem_of_roots
  intro i j hij c
  obtain ⟨e, he⟩ := elementary_centralizes_complement p a m i j hij c
  apply centralizer_fixes_of_surjective (Gamma p (a + 2) m)
    ((gammaReindex p (a + 2) m e).toMonoidHom.comp (gammaStabilization p a 2 m)) (E hij c) he r
  rw [induced_comp]
  exact (induced_equiv_surjective (k := ZMod 2) (gammaReindex p (a + 2) m e) r).comp hsurj

def StabilizationObligation : Prop :=
  ∀ p : ℕ, p.Prime → Odd p → ∀ h a : ℕ, 2 * h + 1 ≤ a →
    ∀ m : ℕ, 1 ≤ m → ∀ j : ℕ, j ≤ h →
      Function.Surjective (induced (k := ZMod 2) (gammaStabilization p a 1 m) j)

end CoboundaryExpanders.Blocks

namespace CoboundaryExpanders.QuotientVanishing
open CategoryTheory CoboundaryExpanders.Construction CoboundaryExpanders.Actions

variable (p a m : ℕ) [NeZero p]
abbrev K := (uReduction p a m).ker

def gammaInU (hm : 1 ≤ m) : Gamma p a m ≃* K p a m where
  toFun x := ⟨⟨x.val, gamma_le_U p a m hm x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem gammaInU_conj (hm : 1 ≤ m) (g : U p a) :
    (MulAut.conjNormal (H := K p a m) g).toMonoidHom.comp (gammaInU p a m hm).toMonoidHom =
    (gammaInU p a m hm).toMonoidHom.comp (MulAut.conjNormal (H := Gamma p a m) g.val).toMonoidHom := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  apply Subtype.ext
  rfl

theorem conjugation_in_U (hm : 1 ≤ m) (j : ℕ)
    (hconj : ∀ g : Matrix.SpecialLinearGroup (Fin a) (R p),
      conjugation (k := ZMod 2) (Gamma p a m) g j = 𝟙 _) (g : U p a) :
    conjugation (k := ZMod 2) (K p a m) g j = 𝟙 _ := by
  have hh := induced_congr (k := ZMod 2) (gammaInU_conj p a m hm g) j
  rw [induced_comp, induced_comp] at hh
  change induced (gammaInU p a m hm).toMonoidHom j ≫ conjugation (K p a m) g j =
    conjugation (Gamma p a m) g.val j ≫ induced (gammaInU p a m hm).toMonoidHom j at hh
  rw [hconj, Category.id_comp] at hh
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := induced_equiv_surjective (k := ZMod 2) (gammaInU p a m hm) j x
  exact congrArg (fun f => ModuleCat.Hom.hom f y) hh

theorem gamma_isZero_of_U_and_action (hp : p.Prime) (hodd : Odd p)
    (hm : 1 ≤ m) (j : ℕ)
    (hU : Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (U p a) (ZMod 2)) j))
    (hconj : ∀ g : Matrix.SpecialLinearGroup (Fin a) (R p),
      conjugation (k := ZMod 2) (Gamma p a m) g j = 𝟙 _) :
    Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p a m) (ZMod 2)) j) := by
  have : Finite (U p a ⧸ K p a m) := inferInstanceAs (Finite (Gquot p a m))
  let : Fintype (U p a ⧸ K p a m) := Fintype.ofFinite _
  have hindex : (Fintype.card (U p a ⧸ K p a m) : ZMod 2) = 1 := by
    have h := odd_gquot_card p a m hp hodd
    change Odd (Nat.card (U p a ⧸ K p a m)) at h
    rw [Nat.card_eq_fintype_card] at h
    obtain ⟨r, hr⟩ := h
    rw [hr]
    have htwo : (2 : ZMod 2) = 0 := by decide
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, htwo, zero_mul, zero_add]
  have hz : Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (K p a m) (ZMod 2)) j) := by
    apply Transfer.subgroup_homology_isZero_of_conjugation (K p a m) hindex j
    · intro g
      exact conjugation_in_U p a m hm j hconj g
    · exact hU
  let f := induced (k := ZMod 2) (gammaInU p a m hm).symm.toMonoidHom j
  have : Epi f := (ModuleCat.epi_iff_surjective f).mpr
    (induced_equiv_surjective (k := ZMod 2) (gammaInU p a m hm).symm j)
  exact Limits.IsZero.of_epi f hz

theorem gamma_isZero_of_U_and_stabilization (hp : p.Prime) (hodd : Odd p)
    (hm : 1 ≤ m) (j : ℕ)
    (hU : Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (U p (a + 2)) (ZMod 2)) j))
    (hst : Function.Surjective
      (induced (k := ZMod 2) (Blocks.gammaStabilization p a 2 m) j)) :
    Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (a + 2) m) (ZMod 2)) j) := by
  have : Fact p.Prime := ⟨hp⟩
  apply gamma_isZero_of_U_and_action p (a + 2) m hp hodd hm j hU
  exact Blocks.trivial_action_of_stabilization p a m j hst

end CoboundaryExpanders.QuotientVanishing

namespace CoboundaryExpanders.Construction
open CategoryTheory

theorem congruence_homology_transition_surjective
    (p a m n : ℕ) (hp : p.Prime) (hodd : Odd p) (hm : 1 ≤ m) (hmn : m ≤ n)
    (j : ℕ) : Function.Surjective
      (groupHomology.map (Subgroup.inclusion (gamma_antitone p a hmn))
        (CoboundaryExpanders.Transfer.trivialCoefficients (k := ZMod 2)
          (Subgroup.inclusion (gamma_antitone p a hmn))) j) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : ((Gamma p a n).subgroupOf (Gamma p a m)).Normal := normalDeeper p a m n
  have : Finite (Gamma p a m ⧸ (Gamma p a n).subgroupOf (Gamma p a m)) :=
    finiteCongruenceQuotient p a m n
  let := Fintype.ofFinite (Gamma p a m ⧸ (Gamma p a n).subgroupOf (Gamma p a m))
  apply CoboundaryExpanders.Transfer.nested_subgroup_inclusion_surjective
  have ho := odd_congruence_index p a m n hp hodd hm
  rw [deeperCongruence_eq, Nat.card_eq_fintype_card] at ho
  obtain ⟨r, hr⟩ := ho
  rw [hr]
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp [Nat.cast_add, Nat.cast_mul, htwo]

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.Blocks

section
open CoboundaryExpanders.Construction

@[simp] theorem gammaStabilization_coe (p a b m : ℕ) (x : Gamma p a m) :
    (gammaStabilization p a b m x).val = stabilizeSL a b x.val := rfl

theorem gammaStabilization_natural (p a b m n : ℕ)
    (ha : Gamma p a n ≤ Gamma p a m)
    (hab : Gamma p (a + b) n ≤ Gamma p (a + b) m) :
    (Subgroup.inclusion hab).comp (gammaStabilization p a b n) =
      (gammaStabilization p a b m).comp (Subgroup.inclusion ha) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [MonoidHom.comp_apply, Subgroup.coe_inclusion, gammaStabilization_coe]

end

variable {A : Type*} [CommRing A]

@[simp] theorem stabilizeSL_left_block (a b : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin a) A) (i j : Fin a) :
    stabilizeSL a b g (Fin.castAdd b i) (Fin.castAdd b j) = g i j := by
  change reindexSL finSumFinEquiv (blockSL a b g)
    (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = _
  rw [reindexSL_apply]
  rfl

theorem stabilizeSL_entry (a b : ℕ)
    (g : Matrix.SpecialLinearGroup (Fin a) A) (i j : Fin (a + b)) :
    stabilizeSL a b g i j =
      if hi : i.val < a then
        if hj : j.val < a then g ⟨i.val, hi⟩ ⟨j.val, hj⟩ else (1 : Matrix _ _ A) i j
      else (1 : Matrix _ _ A) i j := by
  by_cases hi : i.val < a
  · rw [dite_eq_left hi]
    by_cases hj : j.val < a
    · rw [dite_eq_left hj]
      exact stabilizeSL_left_block a b g ⟨i.val, hi⟩ ⟨j.val, hj⟩
    · rw [dite_eq_right hj]
      let j' : Fin b := ⟨j.val - a, by omega⟩
      have hj' : j = Fin.natAdd a j' := by apply Fin.ext; dsimp [j']; omega
      rw [hj', stabilizeSL_right_col]
  · rw [dite_eq_right hi]
    let i' : Fin b := ⟨i.val - a, by omega⟩
    have hi' : i = Fin.natAdd a i' := by apply Fin.ext; dsimp [i']; omega
    rw [hi', stabilizeSL_right_row]

theorem stabilizeSL_two (a : ℕ) (g : Matrix.SpecialLinearGroup (Fin a) A) :
    stabilizeSL (a + 1) 1 (stabilizeSL a 1 g) = stabilizeSL a 2 g := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  rw [stabilizeSL_entry, stabilizeSL_entry]
  by_cases hi : i.val < a + 1
  · rw [dite_eq_left hi]
    by_cases hj : j.val < a + 1
    · rw [dite_eq_left hj, stabilizeSL_entry]
      simp only [Fin.val_mk, Matrix.one_apply, Fin.ext_iff]
    · rw [dite_eq_right hj]
      by_cases hi' : i.val < a
      · rw [dite_eq_left hi', dite_eq_right (by omega : ¬ j.val < a)]
      · rw [dite_eq_right hi']
  · rw [dite_eq_right hi, dite_eq_right (by omega : ¬ i.val < a)]

open CoboundaryExpanders.Construction

theorem gammaStabilization_two (p a m : ℕ) :
    (gammaStabilization p (a + 1) 1 m).comp (gammaStabilization p a 1 m) =
      gammaStabilization p a 2 m := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [MonoidHom.comp_apply, gammaStabilization_coe, stabilizeSL_two]

end CoboundaryExpanders.Blocks

namespace CoboundaryExpanders.Cokernel
variable {k : Type*} [CommRing k]
variable {A A' B B' : Type*}
  [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
  [Module k A] [Module k A'] [Module k B] [Module k B']

abbrev Coker (f : A →ₗ[k] B) := B ⧸ LinearMap.range f

def transition (f : A →ₗ[k] B) (f' : A' →ₗ[k] B')
    (u : A' →ₗ[k] A) (v : B' →ₗ[k] B) (h : v.comp f' = f.comp u) :
    Coker f' →ₗ[k] Coker f :=
  (LinearMap.range f').mapQ (LinearMap.range f) v (by
    rintro y ⟨x, rfl⟩
    change v (f' x) ∈ LinearMap.range f
    exact ⟨u x, (LinearMap.congr_fun h x).symm⟩)

@[simp] theorem transition_mk (f : A →ₗ[k] B) (f' : A' →ₗ[k] B')
    (u : A' →ₗ[k] A) (v : B' →ₗ[k] B) (h : v.comp f' = f.comp u) (x : B') :
    transition f f' u v h (Submodule.Quotient.mk x) = Submodule.Quotient.mk (v x) := rfl

theorem transition_surjective (f : A →ₗ[k] B) (f' : A' →ₗ[k] B')
    (u : A' →ₗ[k] A) (v : B' →ₗ[k] B) (h : v.comp f' = f.comp u)
    (hv : Function.Surjective v) : Function.Surjective (transition f f' u v h) := by
  intro x
  obtain ⟨x, rfl⟩ := (Submodule.Quotient.mk_surjective (LinearMap.range f)) x
  obtain ⟨y, rfl⟩ := hv x
  exact ⟨Submodule.Quotient.mk y, rfl⟩

theorem surjective_iff_coker_subsingleton (f : A →ₗ[k] B) :
    Function.Surjective f ↔ Subsingleton (Coker f) :=
  LinearMap.range_eq_top.symm.trans Submodule.Quotient.subsingleton_iff.symm

theorem surjective_of_zero_coker_transition
    (f : A →ₗ[k] B) (f' : A' →ₗ[k] B')
    (u : A' →ₗ[k] A) (v : B' →ₗ[k] B) (h : v.comp f' = f.comp u)
    (hv : Function.Surjective v)
    (hz : transition f f' u v h = 0) : Function.Surjective f := by
  apply (surjective_iff_coker_subsingleton f).mpr
  have hs := transition_surjective f f' u v h hv
  have he : ∀ x : Coker f, x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := hs x
    rw [hz]; rfl
  exact ⟨fun x y => (he x).trans (he y).symm⟩

end CoboundaryExpanders.Cokernel

namespace CoboundaryExpanders.CongruenceCokernels
open CoboundaryExpanders.Construction CoboundaryExpanders.Blocks
open CoboundaryExpanders.Actions CategoryTheory

abbrev H (p a m j : ℕ) := groupHomology (Rep.trivial (ZMod 2) (Gamma p a m) (ZMod 2)) j

def stabilization (p a m j : ℕ) : H p a m j →ₗ[ZMod 2] H p (a + 1) m j :=
  (induced (gammaStabilization p a 1 m) j).hom

def transition (p a m n j : ℕ) (hmn : m ≤ n) : H p a n j →ₗ[ZMod 2] H p a m j :=
  (induced (Subgroup.inclusion (gamma_antitone p a hmn)) j).hom

theorem group_natural (p a m n : ℕ) (hmn : m ≤ n) :
    (Subgroup.inclusion (gamma_antitone p (a + 1) hmn)).comp (gammaStabilization p a 1 n) =
      (gammaStabilization p a 1 m).comp (Subgroup.inclusion (gamma_antitone p a hmn)) :=
  gammaStabilization_natural p a 1 m n (gamma_antitone p a hmn)
    (gamma_antitone p (a + 1) hmn)

theorem natural (p a m n j : ℕ) (hmn : m ≤ n) :
    (transition p (a + 1) m n j hmn).comp (stabilization p a n j) =
      (stabilization p a m j).comp (transition p a m n j hmn) := by
  have hh := induced_congr (k := ZMod 2) (group_natural p a m n hmn) j
  rw [induced_comp, induced_comp] at hh
  exact congrArg ModuleCat.Hom.hom hh

abbrev C (p a m j : ℕ) := Cokernel.Coker (stabilization p a m j)

def cokerTransition (p a m n j : ℕ) (hmn : m ≤ n) : C p a n j →ₗ[ZMod 2] C p a m j :=
  Cokernel.transition (stabilization p a m j) (stabilization p a n j)
    (transition p a m n j hmn) (transition p (a + 1) m n j hmn) (natural p a m n j hmn)

def ProZero (p a j : ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∃ n : ℕ, ∃ hmn : m ≤ n, cokerTransition p a m n j hmn = 0

theorem transition_surjective (p a m n j : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hm : 1 ≤ m) (hmn : m ≤ n) :
    Function.Surjective (transition p a m n j hmn) := by
  exact congruence_homology_transition_surjective p a m n hp hodd hm hmn j

theorem cokerTransition_surjective (p a m n j : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hm : 1 ≤ m) (hmn : m ≤ n) :
    Function.Surjective (cokerTransition p a m n j hmn) := by
  apply Cokernel.transition_surjective
  exact transition_surjective p (a + 1) m n j hp hodd hm hmn

theorem stabilization_surjective_of_proZero (p a m j : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hm : 1 ≤ m) (hz : ProZero p a j) :
    Function.Surjective (stabilization p a m j) := by
  obtain ⟨n, hmn, hn⟩ := hz m hm
  apply Cokernel.surjective_of_zero_coker_transition
    (stabilization p a m j) (stabilization p a n j)
    (transition p a m n j hmn) (transition p (a + 1) m n j hmn)
    (natural p a m n j hmn)
  · exact transition_surjective p (a + 1) m n j hp hodd hm hmn
  · exact hn

theorem two_step_surjective_of_proZero (p a m j : ℕ) (hp : p.Prime)
    (hodd : Odd p) (hm : 1 ≤ m) (hz : ProZero p a j) (hz' : ProZero p (a + 1) j) :
    Function.Surjective (induced (k := ZMod 2) (gammaStabilization p a 2 m) j) := by
  have hh := induced_congr (k := ZMod 2) (gammaStabilization_two p a m) j
  rw [induced_comp] at hh
  rw [← hh]
  exact (stabilization_surjective_of_proZero p (a + 1) m j hp hodd hm hz').comp
    (stabilization_surjective_of_proZero p a m j hp hodd hm hz)

theorem gamma_isZero_of_U_and_proZero (p a m j : ℕ) [NeZero p] (hp : p.Prime)
    (hodd : Odd p) (hm : 1 ≤ m)
    (hU : Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (U p (a + 2)) (ZMod 2)) j))
    (hz : ProZero p a j) (hz' : ProZero p (a + 1) j) :
    Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (a + 2) m) (ZMod 2)) j) := by
  exact QuotientVanishing.gamma_isZero_of_U_and_stabilization p a m hp hodd hm j hU
    (two_step_surjective_of_proZero p a m j hp hodd hm hz hz')

end CoboundaryExpanders.CongruenceCokernels

end

end OAI
