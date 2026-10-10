import OAI.CategoryTheory.ThickClosure.PerfectModules

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.LaurentDg
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [Ring R] {D : ℕ}

abbrev familyTotal (X : ℤ → ModuleCat.{u} R) := DirectSum ℤ (fun i => X i)
abbrev familyInc (X : ℤ → ModuleCat.{u} R) (i : ℤ) : X i →ₗ[R] familyTotal X :=
  DirectSum.lof R ℤ (fun i => X i) i

def familyDifferential (X : ℤ → ModuleCat.{u} R) (d : ∀ i, X (i+1) ⟶ X i) :
    familyTotal X →ₗ[R] familyTotal X :=
  DirectSum.toModule R ℤ (familyTotal X) (fun i =>
    (familyInc X (i-1)).comp ((eqToHom (congrArg X (by omega : i = i-1+1))) ≫ d (i-1)).hom)

structure ActionModule (R : Type u) [Ring R] (D : ℕ) where
  X : ℤ → ModuleCat.{u} R
  d : ∀ i, X (i+1) ⟶ X i
  dd : ∀ i, d (i+1) ≫ d i = 0
  action : LaurentPolynomial R →+* AddMonoid.End (familyTotal X)
  coefficient : ∀ (r : R) (z : familyTotal X), action (AddMonoidAlgebra.single 0 r) z = r • z
  homogeneous : ∀ (q i : ℤ) (x : X i), ∃ y : X (i+(D:ℤ)*q),
    action (AddMonoidAlgebra.single q 1) (familyInc X i x) = familyInc X _ y
  differential : ∀ (a : LaurentPolynomial R) (z : familyTotal X),
    familyDifferential X d (action a z) = action a (familyDifferential X d z)

structure PowerData (X : ℤ → ModuleCat.{u} R) (d : ∀ i, X (i+1) ⟶ X i) where
  power : ∀ i j : ℤ, (i : ZMod D) = (j : ZMod D) → (X i ≅ X j)
  refl : ∀ i, power i i rfl = Iso.refl _
  trans : ∀ (i j k : ℤ) (h : (i : ZMod D) = (j : ZMod D))
    (h' : (j : ZMod D) = (k : ZMod D)),
    power i j h ≪≫ power j k h' = power i k (h.trans h')
  comm : ∀ (i j : ℤ) (h : (i : ZMod D) = (j : ZMod D)),
    (power (i+1) (j+1) (by simpa only [Int.cast_add, Int.cast_one] using
      (congrArg (fun x : ZMod D => x+1) h))).hom ≫ d j = d i ≫ (power i j h).hom

def ActionModule.presentation (G : ActionModule R D) (P : PowerData (D:=D) G.X G.d) : Module R D :=
  ⟨G.X, G.d, G.dd, P.power, P.refl, P.trans, P.comm⟩

def totalMap {X Y : ℤ → ModuleCat.{u} R} (f : ∀ i, X i ⟶ Y i) :
    familyTotal X →ₗ[R] familyTotal Y :=
  DirectSum.toModule R ℤ (familyTotal Y) (fun i => (familyInc Y i).comp (f i).hom)

lemma familyInc_injective (X : ℤ → ModuleCat.{u} R) (i : ℤ) :
    Function.Injective (familyInc X i) := DirectSum.of_injective i

lemma familyDifferential_inc_succ (X : ℤ → ModuleCat.{u} R)
    (d : ∀ i, X (i+1) ⟶ X i) (i : ℤ) (x : X (i+1)) :
    familyDifferential X d (familyInc X (i+1) x) = familyInc X i (d i x) := by
  unfold familyDifferential
  rw [DirectSum.toModule_lof]
  have aux (j : ℤ) (h : j = i) (h' : i+1 = j+1) :
      familyInc X j (((eqToHom (congrArg X h') ≫ d j).hom) x) = familyInc X i (d i x) := by
    subst j
    rfl
  exact aux (i+1-1) (by omega) (by omega)

namespace ActionModule

@[instance_reducible]
def asModule (G : ActionModule R D) : _root_.Module (LaurentPolynomial R) (familyTotal G.X) :=
  Module.compHom _ G.action

lemma monomial_add (G : ActionModule R D) (q r : ℤ) (z : familyTotal G.X) :
    G.action (AddMonoidAlgebra.single (q+r) 1) z =
      G.action (AddMonoidAlgebra.single q 1) (G.action (AddMonoidAlgebra.single r 1) z) := by
  have h := congrArg (fun e : AddMonoid.End (familyTotal G.X) => e z)
    (G.action.map_mul (AddMonoidAlgebra.single q 1) (AddMonoidAlgebra.single r 1))
  simpa only [AddMonoidAlgebra.single_mul_single, one_mul, AddMonoid.End.coe_mul, Function.comp_apply] using h

lemma monomial_zero (G : ActionModule R D) (z : familyTotal G.X) :
    G.action (AddMonoidAlgebra.single 0 1) z = z := by
  simpa only [one_smul] using G.coefficient 1 z

lemma monomial_smul (G : ActionModule R D) (q : ℤ) (r : R) (z : familyTotal G.X) :
    G.action (AddMonoidAlgebra.single q 1) (r • z) =
      r • G.action (AddMonoidAlgebra.single q 1) z := by
  have hcomm : AddMonoidAlgebra.single q (1:R) * AddMonoidAlgebra.single 0 r =
      AddMonoidAlgebra.single 0 r * AddMonoidAlgebra.single q 1 := by
    simp only [AddMonoidAlgebra.single_mul_single, add_zero, zero_add, one_mul, mul_one]
  have h := congrArg (fun a => G.action a z) hcomm
  simpa only [map_mul, AddMonoid.End.coe_mul, Function.comp_apply, G.coefficient] using h

lemma exists_powerValue (G : ActionModule R D) (q i j : ℤ)
    (h : j = i+(D:ℤ)*q) (x : G.X i) :
    ∃ y : G.X j, G.action (AddMonoidAlgebra.single q 1) (familyInc G.X i x) = familyInc G.X j y := by
  subst j
  exact G.homogeneous q i x

noncomputable def powerValue (G : ActionModule R D) (q i j : ℤ)
    (h : j = i+(D:ℤ)*q) (x : G.X i) : G.X j :=
  Classical.choose (exists_powerValue G q i j h x)

lemma powerValue_spec (G : ActionModule R D) (q i j : ℤ)
    (h : j = i+(D:ℤ)*q) (x : G.X i) :
    familyInc G.X j (powerValue G q i j h x) =
      G.action (AddMonoidAlgebra.single q 1) (familyInc G.X i x) :=
  (Classical.choose_spec (exists_powerValue G q i j h x)).symm

noncomputable def powerLinear (G : ActionModule R D) (q i j : ℤ)
    (h : j = i+(D:ℤ)*q) : G.X i →ₗ[R] G.X j where
  toFun := powerValue G q i j h
  map_add' x y := by
    apply familyInc_injective G.X j
    simp only [powerValue_spec, map_add]
  map_smul' r x := by
    apply familyInc_injective G.X j
    simp only [powerValue_spec, map_smul, monomial_smul, RingHom.id_apply]

lemma powerLinear_spec (G : ActionModule R D) (q i j : ℤ)
    (h : j = i+(D:ℤ)*q) (x : G.X i) :
    familyInc G.X j (powerLinear G q i j h x) =
      G.action (AddMonoidAlgebra.single q 1) (familyInc G.X i x) := powerValue_spec G q i j h x

noncomputable def exponent (hD : 0 < D) (i j : ℤ) (h : (i : ZMod D) = (j : ZMod D)) : ℤ :=
  Classical.choose ((exponent_exists_unique hD i j).mp h).exists

lemma exponent_spec (hD : 0 < D) (i j : ℤ) (h : (i : ZMod D) = (j : ZMod D)) :
    j = i+(D:ℤ)*exponent hD i j h :=
  Classical.choose_spec ((exponent_exists_unique hD i j).mp h).exists

lemma exponent_eq (hD : 0 < D) (i j q : ℤ) (h : (i : ZMod D) = (j : ZMod D))
    (hq : j = i+(D:ℤ)*q) : exponent hD i j h = q :=
  ((exponent_exists_unique hD i j).mp h).unique (exponent_spec hD i j h) hq

noncomputable def directMap (G : ActionModule R D) (hD : 0 < D) (i j : ℤ)
    (h : (i : ZMod D) = (j : ZMod D)) : G.X i ⟶ G.X j :=
  ModuleCat.ofHom (powerLinear G (exponent hD i j h) i j (exponent_spec hD i j h))

lemma directMap_spec (G : ActionModule R D) (hD : 0 < D) (i j q : ℤ)
    (h : (i : ZMod D) = (j : ZMod D)) (hq : j = i+(D:ℤ)*q) (x : G.X i) :
    familyInc G.X j (directMap G hD i j h x) =
      G.action (AddMonoidAlgebra.single q 1) (familyInc G.X i x) := by
  have he := exponent_eq hD i j q h hq
  exact (powerLinear_spec G _ i j (exponent_spec hD i j h) x).trans (by rw [he])

lemma directMap_refl (G : ActionModule R D) (hD : 0 < D) (i : ℤ) :
    directMap G hD i i rfl = 𝟙 _ := by
  ext x
  apply familyInc_injective G.X i
  rw [directMap_spec G hD i i 0 rfl (by simp), monomial_zero]
  rfl

lemma directMap_trans (G : ActionModule R D) (hD : 0 < D) (i j k : ℤ)
    (h : (i : ZMod D) = (j : ZMod D)) (h' : (j : ZMod D) = (k : ZMod D)) :
    directMap G hD i j h ≫ directMap G hD j k h' = directMap G hD i k (h.trans h') := by
  let q := exponent hD i j h
  let r := exponent hD j k h'
  have hq : j = i+(D:ℤ)*q := exponent_spec hD i j h
  have hr : k = j+(D:ℤ)*r := exponent_spec hD j k h'
  have hsum : k = i+(D:ℤ)*(r+q) := by rw [hr, hq]; ring
  ext x
  apply familyInc_injective G.X k
  change familyInc G.X k (directMap G hD j k h' (directMap G hD i j h x)) = _
  rw [directMap_spec G hD j k r h' hr, directMap_spec G hD i j q h hq,
    directMap_spec G hD i k (r+q) (h.trans h') hsum, monomial_add]

noncomputable def directIso (G : ActionModule R D) (hD : 0 < D) (i j : ℤ)
    (h : (i : ZMod D) = (j : ZMod D)) : G.X i ≅ G.X j where
  hom := directMap G hD i j h
  inv := directMap G hD j i h.symm
  hom_inv_id := by rw [directMap_trans, directMap_refl]
  inv_hom_id := by rw [directMap_trans, directMap_refl]

lemma directMap_d (G : ActionModule R D) (hD : 0 < D) (i j : ℤ)
    (h : (i : ZMod D) = (j : ZMod D)) :
    directMap G hD (i+1) (j+1) (by simpa only [Int.cast_add, Int.cast_one] using
      (congrArg (fun x : ZMod D => x+1) h)) ≫ G.d j = G.d i ≫ directMap G hD i j h := by
  let q := exponent hD i j h
  have hq : j = i+(D:ℤ)*q := exponent_spec hD i j h
  have hq' : j+1 = i+1+(D:ℤ)*q := by omega
  ext x
  apply familyInc_injective G.X j
  change familyInc G.X j (G.d j (directMap G hD (i+1) (j+1) _ x)) =
    familyInc G.X j (directMap G hD i j h (G.d i x))
  rw [← familyDifferential_inc_succ, directMap_spec G hD (i+1) (j+1) q _ hq',
    G.differential, familyDifferential_inc_succ, directMap_spec G hD i j q h hq]

noncomputable def reconstructed (G : ActionModule R D) (hD : 0 < D) :
    PowerData (D:=D) G.X G.d where
  power := directIso G hD
  refl i := by apply Iso.ext; exact directMap_refl G hD i
  trans i j k h h' := by apply Iso.ext; exact directMap_trans G hD i j k h h'
  comm i j h := directMap_d G hD i j h

end ActionModule

lemma representation_single_total (M : Module R D) (q : ℤ) (r : R) (z : total M) :
    laurentRepresentation M (AddMonoidAlgebra.single q r) z = r • shiftPower M q z := by
  unfold laurentRepresentation
  erw [AddMonoidAlgebra.liftNCRingHom_single]
  rfl

lemma totalMap_inc {X Y : ℤ → ModuleCat.{u} R} (f : ∀ i, X i ⟶ Y i)
    (i : ℤ) (x : X i) :
    totalMap f (familyInc X i x) = familyInc Y i (f i x) :=
  DirectSum.toModule_lof _ _ _

theorem action_reconstructs (hD : 0 < D) (G : ActionModule R D) :
    ∃ P : PowerData (D:=D) G.X G.d,
      laurentRepresentation (G.presentation P) = G.action := by
  refine ⟨G.reconstructed hD, ?_⟩
  apply AddMonoidAlgebra.ringHom_ext
  · intro r
    apply AddMonoidHom.ext
    intro z
    erw [representation_single_total, shiftPower_zero]
    exact (G.coefficient r z).symm
  · intro q
    apply DirectSum.addHom_ext
    intro i x
    change laurentRepresentation (G.presentation (G.reconstructed hD))
      (AddMonoidAlgebra.single q 1) (inc _ i x) = _
    rw [laurentRepresentation_single, one_smul]
    exact ActionModule.directMap_spec G hD i (i+(D:ℤ)*q) q (power_cast i q) rfl x

theorem morphism_action_iff (M N : Module R D) (f : ∀ i, M.X i ⟶ N.X i) :
    (∀ (i j : ℤ) (h : (i : ZMod D) = (j : ZMod D)),
      f i ≫ (N.power i j h).hom = (M.power i j h).hom ≫ f j) ↔
    (∀ (a : LaurentPolynomial R) (z : total M),
      totalMap f (laurentRepresentation M a z) = laurentRepresentation N a (totalMap f z)) := by
  constructor
  · intro hf
    have ht (q : ℤ) : (totalMap f).comp (shiftPower M q) =
        (shiftPower N q).comp (totalMap f) := by
      apply DirectSum.linearMap_ext
      intro i
      ext x : 1
      change totalMap f (shiftPower M q (inc M i x)) = shiftPower N q (totalMap f (inc M i x))
      simp only [shiftPower_inc, move, LinearMap.comp_apply, totalMap_inc]
      change inc N _ (((M.power i _ _).hom ≫ f _) x) =
        inc N _ ((f i ≫ (N.power i _ _).hom) x)
      rw [hf]
    intro a z
    induction a using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      rw [map_add, map_add]
      change totalMap f (laurentRepresentation M a z + laurentRepresentation M b z) =
        laurentRepresentation N a (totalMap f z) + laurentRepresentation N b (totalMap f z)
      rw [map_add, ha, hb]
    | single q r =>
      rw [representation_single_total, representation_single_total, map_smul]
      exact congrArg (fun z => r • z) (LinearMap.congr_fun (ht q) z)
  · intro hf i j h
    obtain ⟨q, hq⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub i j D).mp h
    have ej : j = i+(D:ℤ)*q := by omega
    subst j
    ext x
    apply familyInc_injective N.X (i+(D:ℤ)*q)
    change inc N _ ((N.power i _ h).hom (f i x)) = inc N _ (f _ ((M.power i _ h).hom x))
    have hh := hf (AddMonoidAlgebra.single q 1) (inc M i x)
    simpa only [laurentRepresentation_single, one_smul, totalMap_inc] using hh.symm
lemma totalMap_id (X : ℤ → ModuleCat.{u} R) : totalMap (fun i => 𝟙 (X i)) = LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro i
  ext x : 1
  simpa only [LinearMap.comp_apply, LinearMap.id_apply, ModuleCat.id_apply] using
    totalMap_inc (fun i => 𝟙 (X i)) i x

lemma totalMap_comp {X Y Z : ℤ → ModuleCat.{u} R}
    (f : ∀ i, X i ⟶ Y i) (g : ∀ i, Y i ⟶ Z i) :
    totalMap (fun i => f i ≫ g i) = (totalMap g).comp (totalMap f) := by
  apply DirectSum.linearMap_ext
  intro i
  ext x : 1
  simp only [LinearMap.comp_apply, totalMap_inc]
  rfl

namespace ActionModule
@[ext] structure Hom (M N : ActionModule R D) where
  f : ∀ i, M.X i ⟶ N.X i
  comm_d : ∀ i, f (i+1) ≫ N.d i = M.d i ≫ f i
  comm_action : ∀ (a : LaurentPolynomial R) (z : familyTotal M.X),
    totalMap f (M.action a z) = N.action a (totalMap f z)

instance : Category (ActionModule R D) where
  Hom M N := Hom M N
  id M := ⟨fun i => 𝟙 _, by intro i; simp, by intro a z; rw [totalMap_id]; rfl⟩
  comp f g := ⟨fun i => f.f i ≫ g.f i,
    by intro i; rw [Category.assoc, g.comm_d, ← Category.assoc, f.comm_d, Category.assoc],
    by intro a z; rw [totalMap_comp]; simp only [LinearMap.comp_apply, f.comm_action, g.comm_action]⟩
  id_comp f := by apply Hom.ext; funext i; exact Category.id_comp _
  comp_id f := by apply Hom.ext; funext i; exact Category.comp_id _
  assoc f g h := by apply Hom.ext; funext i; exact Category.assoc _ _ _

@[simp] lemma id_f (M : ActionModule R D) (i : ℤ) : (𝟙 M : M ⟶ M).f i = 𝟙 _ := rfl
@[simp] lemma comp_f {M N P : ActionModule R D} (f : M ⟶ N) (g : N ⟶ P) (i : ℤ) :
    (f ≫ g).f i = f.f i ≫ g.f i := rfl
end ActionModule
lemma familyDifferential_eq (M : Module R D) :
    familyDifferential M.X M.d = totalDifferential M := by
  apply DirectSum.linearMap_ext
  intro n
  obtain ⟨i, rfl⟩ : ∃ i : ℤ, n = i+1 := ⟨n-1, by omega⟩
  ext x : 1
  simp only [LinearMap.comp_apply, familyDifferential_inc_succ, totalDifferential_inc_succ]

def asAction (M : Module R D) : ActionModule R D where
  X := M.X
  d := M.d
  dd := M.dd
  action := laurentRepresentation M
  coefficient r z := by rw [representation_single_total, shiftPower_zero]; rfl
  homogeneous q i x := ⟨(M.power i _ (power_cast i q)).hom x,
    by simpa only [one_smul] using laurentRepresentation_single M q i 1 x⟩
  differential a z := by
    rw [familyDifferential_eq]
    exact (congrArg (fun e : AddMonoid.End (total M) => e z)
      (laurentRepresentation_commute M a).eq).symm

def actionFunctor : Module R D ⥤ ActionModule R D where
  obj := asAction
  map f := ⟨f.f, f.comm_d, (morphism_action_iff _ _ _).mp f.comm_power⟩
  map_id M := by apply ActionModule.Hom.ext; rfl
  map_comp f g := by apply ActionModule.Hom.ext; rfl

instance actionFunctor_faithful : (actionFunctor (R:=R) (D:=D)).Faithful where
  map_injective := by
    intro M N f g h
    apply Module.Hom.ext
    exact congrArg ActionModule.Hom.f h

instance actionFunctor_full : (actionFunctor (R:=R) (D:=D)).Full where
  map_surjective := by
    intro M N f
    refine ⟨⟨f.f, f.comm_d, (morphism_action_iff M N f.f).mpr f.comm_action⟩, ?_⟩
    apply ActionModule.Hom.ext
    rfl

noncomputable def presentationActionIso (G : ActionModule R D)
    (P : PowerData (D:=D) G.X G.d) (hρ : laurentRepresentation (G.presentation P) = G.action) :
    asAction (G.presentation P) ≅ G where
  hom := ⟨fun i => 𝟙 (G.X i), by
    intro i
    change 𝟙 (G.X (i+1)) ≫ G.d i = G.d i ≫ 𝟙 (G.X i)
    simp, by
    intro a z
    change totalMap (fun i => 𝟙 (G.X i)) (laurentRepresentation (G.presentation P) a z) =
      G.action a (totalMap (fun i => 𝟙 (G.X i)) z)
    rw [totalMap_id]
    exact congrArg (fun ρ : LaurentPolynomial R →+* AddMonoid.End (familyTotal G.X) => ρ a z) hρ⟩
  inv := ⟨fun i => 𝟙 (G.X i), by
    intro i
    change 𝟙 (G.X (i+1)) ≫ G.d i = G.d i ≫ 𝟙 (G.X i)
    simp, by
    intro a z
    change totalMap (fun i => 𝟙 (G.X i)) (G.action a z) =
      laurentRepresentation (G.presentation P) a (totalMap (fun i => 𝟙 (G.X i)) z)
    rw [totalMap_id]
    exact (congrArg (fun ρ : LaurentPolynomial R →+* AddMonoid.End (familyTotal G.X) => ρ a z) hρ).symm⟩
  hom_inv_id := by apply ActionModule.Hom.ext; funext i; exact Category.id_comp _
  inv_hom_id := by apply ActionModule.Hom.ext; funext i; exact Category.id_comp _

lemma actionFunctor_essSurj (hD : 0 < D) : (actionFunctor (R:=R) (D:=D)).EssSurj where
  mem_essImage G := by
    obtain ⟨P, hp⟩ := action_reconstructs hD G
    exact ⟨G.presentation P, ⟨presentationActionIso G P hp⟩⟩

theorem actual_action_equivalence (hD : 0 < D) :
    ∃ E : Module R D ≌ ActionModule R D,
      (∀ M, (E.functor.obj M).X = M.X ∧ HEq (E.functor.obj M).d M.d) ∧
      (∀ {M N : Module R D} (f : M ⟶ N) (i : ℤ), HEq ((E.functor.map f).f i) (f.f i)) := by
  let : (actionFunctor (R:=R) (D:=D)).EssSurj := actionFunctor_essSurj hD
  let : (actionFunctor (R:=R) (D:=D)).IsEquivalence := {}
  refine ⟨(actionFunctor (R:=R) (D:=D)).asEquivalence, ?_, ?_⟩
  · intro M
    exact ⟨rfl, HEq.rfl⟩
  · intro M N f i
    exact HEq.rfl
end HahnWilson.LaurentDg

end

end OAI
