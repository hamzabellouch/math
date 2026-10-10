import OAI.CategoryTheory.ThickClosure.PeriodicDerived

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.LaurentDg
universe u w
variable (R : Type u) [Ring R] (D : ℕ)

structure Module where
  X : ℤ → ModuleCat.{u} R
  d : ∀ n : ℤ, X (n + 1) ⟶ X n
  dd : ∀ n, d (n + 1) ≫ d n = 0
  power : ∀ i j : ℤ, (i : ZMod D) = (j : ZMod D) → (X i ≅ X j)
  power_refl : ∀ i, power i i rfl = Iso.refl _
  power_trans : ∀ (i j k : ℤ) (h : (i : ZMod D) = (j : ZMod D))
      (h' : (j : ZMod D) = (k : ZMod D)),
    power i j h ≪≫ power j k h' = power i k (h.trans h')
  power_d : ∀ (i j : ℤ) (h : (i : ZMod D) = (j : ZMod D)),
    (power (i + 1) (j + 1) (by simpa only [Int.cast_add, Int.cast_one] using (congrArg (fun x : ZMod D => x + 1) h))).hom ≫ d j =
      d i ≫ (power i j h).hom

namespace Module
variable {R D}
@[ext] structure Hom (M N : Module R D) where
  f : ∀ i, M.X i ⟶ N.X i
  comm_d : ∀ i, f (i + 1) ≫ N.d i = M.d i ≫ f i
  comm_power : ∀ (i j : ℤ) (h : (i : ZMod D) = (j : ZMod D)),
    f i ≫ (N.power i j h).hom = (M.power i j h).hom ≫ f j

instance : Category (Module R D) where
  Hom M N := Hom M N
  id M := ⟨fun i => 𝟙 _, by intros; simp, by intros; simp⟩
  comp f g := ⟨fun i => f.f i ≫ g.f i,
    by intro i; rw [Category.assoc, g.comm_d, ← Category.assoc, f.comm_d, Category.assoc],
    by intro i j h; rw [Category.assoc, g.comm_power, ← Category.assoc, f.comm_power, Category.assoc]⟩
  id_comp f := by apply Hom.ext; funext i; exact Category.id_comp _
  comp_id f := by apply Hom.ext; funext i; exact Category.comp_id _
  assoc f g h := by apply Hom.ext; funext i; exact Category.assoc _ _ _

@[simp] lemma id_f (M : Module R D) (i : ℤ) : (𝟙 M : M ⟶ M).f i = 𝟙 _ := rfl
@[simp] lemma comp_f {M N P : Module R D} (f : M ⟶ N) (g : N ⟶ P) (i : ℤ) :
  (f ≫ g).f i = f.f i ≫ g.f i := rfl
@[simp] lemma power_hom_refl (M : Module R D) (i : ℤ) :
    (M.power i i rfl).hom = 𝟙 _ := by rw [M.power_refl]; rfl
@[simp, reassoc] lemma power_hom_trans (M : Module R D) (i j k : ℤ)
    (h : (i : ZMod D) = (j : ZMod D)) (h' : (j : ZMod D) = (k : ZMod D)) :
    (M.power i j h).hom ≫ (M.power j k h').hom = (M.power i k (h.trans h')).hom :=
  congrArg Iso.hom (M.power_trans i j k h h')
end Module

variable {R D}

def rep (i : ZMod D) : ℤ := Classical.choose (ZMod.intCast_surjective i)
@[simp] lemma rep_cast (i : ZMod D) : ((rep i : ℤ) : ZMod D) = i :=
  Classical.choose_spec (ZMod.intCast_surjective i)

lemma rep_next (i : ZMod D) :
    ((rep (i + 1) : ℤ) : ZMod D) = ((rep i + 1 : ℤ) : ZMod D) := by simp

def reduceD (M : Module R D) (i : ZMod D) :
    M.X (rep (i+1)) ⟶ M.X (rep i) :=
  (M.power (rep (i+1)) (rep i+1) (rep_next i)).hom ≫ M.d (rep i)

lemma reduceD_sq (M : Module R D) (i : ZMod D) :
    reduceD M (i+1) ≫ reduceD M i = 0 := by
  dsimp [reduceD]
  rw [Category.assoc, ← Category.assoc (M.d (rep (i+1))),
    ← M.power_d _ _ (rep_next i)]
  simp only [Category.assoc, M.dd, CategoryTheory.Limits.comp_zero]

abbrev reduceObj (M : Module R D) : ChainComplex (ModuleCat.{u} R) (ZMod D) :=
  ChainComplex.of (fun i => M.X (rep i)) (reduceD M) (reduceD_sq M)

lemma reduceObj_d (M : Module R D) (i : ZMod D) :
    (reduceObj M).d (i+1) i = reduceD M i := by
  exact ChainComplex.of_d (fun i => M.X (rep i)) (reduceD M) i

lemma reduceObj_d_eq (M : Module R D) (i j : ZMod D) (h : i = j+1) :
    (reduceObj M).d i j =
      (M.power (rep i) (rep j+1) (by simp [h])).hom ≫ M.d (rep j) := by
  subst i
  exact ChainComplex.of_d (fun i => M.X (rep i)) (reduceD M) j

def reduce : Module R D ⥤ ChainComplex (ModuleCat.{u} R) (ZMod D) where
  obj := reduceObj
  map f := ChainComplex.ofHom (fun i => f.f (rep i)) (by
    intro i
    rw [reduceObj_d, reduceObj_d]
    dsimp [reduceD]
    rw [← Category.assoc, f.comm_power, Category.assoc, f.comm_d]
    exact (Category.assoc _ _ _).symm)
  map_id M := by ext i; rfl
  map_comp f g := by ext i; rfl

def inflateObj (P : ChainComplex (ModuleCat.{u} R) (ZMod D)) : Module R D where
  X n := P.X (n : ZMod D)
  d n := P.d ((n+1 : ℤ) : ZMod D) (n : ZMod D)
  dd n := P.d_comp_d _ _ _
  power i j h := P.XIsoOfEq h
  power_refl i := rfl
  power_trans i j k h h' := by
    apply Iso.ext
    exact P.XIsoOfEq_hom_comp_XIsoOfEq_hom h h'
  power_d i j h := by simp [HomologicalComplex.XIsoOfEq_hom_comp_d,
    HomologicalComplex.d_comp_XIsoOfEq_hom]

def inflate : ChainComplex (ModuleCat.{u} R) (ZMod D) ⥤ Module R D where
  obj := inflateObj
  map f := ⟨fun i => f.f (i : ZMod D),
    by intro n; exact f.comm _ _,
    by intro i j h; exact HomologicalComplex.XIsoOfEq_hom_naturality f h⟩
  map_id M := by apply Module.Hom.ext; rfl
  map_comp f g := by apply Module.Hom.ext; rfl

namespace Module
@[simp] lemma power_hom_eqToHom (M : Module R D) {i j : ℤ} (h : i = j) :
    (M.power i j (congrArg (fun n : ℤ => (n : ZMod D)) h)).hom =
      eqToHom (congrArg M.X h) := by subst j; simp

def isoMk {M N : Module R D} (e : ∀ i, M.X i ≅ N.X i)
    (hd : ∀ i, (e (i+1)).hom ≫ N.d i = M.d i ≫ (e i).hom)
    (hp : ∀ (i j : ℤ) (h : (i : ZMod D) = (j : ZMod D)),
      (e i).hom ≫ (N.power i j h).hom = (M.power i j h).hom ≫ (e j).hom) : M ≅ N where
  hom := ⟨fun i => (e i).hom, hd, hp⟩
  inv := ⟨fun i => (e i).inv, by
    intro i
    apply (cancel_epi (e (i+1)).hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hd, Category.assoc,
      Iso.hom_inv_id, Category.comp_id], by
    intro i j h
    apply (cancel_epi (e i).hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc, hp, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]⟩
  hom_inv_id := by apply Hom.ext; funext i; exact (e i).hom_inv_id
  inv_hom_id := by apply Hom.ext; funext i; exact (e i).inv_hom_id
end Module

noncomputable def counitApp (P : ChainComplex (ModuleCat.{u} R) (ZMod D)) :
    reduceObj (inflateObj P) ≅ P :=
  HomologicalComplex.Hom.isoOfComponents (fun i => P.XIsoOfEq (rep_cast i)) (by
    intro i j hij
    have hij' : j + 1 = i := hij
    subst i
    rw [reduceObj_d]
    simp only [reduceD, inflateObj,
      HomologicalComplex.XIsoOfEq_hom_comp_d,
      HomologicalComplex.d_comp_XIsoOfEq_hom])

noncomputable def counit : inflate (R:=R) (D:=D) ⋙ reduce ≅ 𝟭 _ :=
  NatIso.ofComponents counitApp (by
    intro P Q f
    apply HomologicalComplex.Hom.ext
    funext i
    exact HomologicalComplex.XIsoOfEq_hom_naturality f (rep_cast i))

noncomputable def unitApp (M : Module R D) : M ≅ inflateObj (reduceObj M) :=
  Module.isoMk (fun n => M.power n (rep (n : ZMod D)) (rep_cast _).symm) (by
    intro n
    change (M.power (n+1) (rep ((n+1 : ℤ) : ZMod D)) (rep_cast _).symm).hom ≫
      (reduceObj M).d ((n+1 : ℤ) : ZMod D) (n : ZMod D) =
      M.d n ≫ (M.power n (rep (n : ZMod D)) (rep_cast _).symm).hom
    rw [reduceObj_d_eq M _ _ (by push_cast; rfl)]
    rw [← Category.assoc, Module.power_hom_trans]
    exact M.power_d n (rep (n : ZMod D)) (rep_cast _).symm) (by
    intro i j h
    change _ ≫ ((reduceObj M).XIsoOfEq h).hom = _
    change _ ≫ eqToHom (congrArg M.X (congrArg rep h)) = _
    rw [← M.power_hom_eqToHom (congrArg rep h), Module.power_hom_trans]
    exact (M.power_hom_trans i j (rep (j : ZMod D)) h (rep_cast _).symm).symm)

noncomputable def unit : 𝟭 (Module R D) ≅ reduce ⋙ inflate :=
  NatIso.ofComponents unitApp (by
    intro M N f
    apply Module.Hom.ext
    funext n
    exact f.comm_power n (rep (n : ZMod D)) (rep_cast _).symm)

noncomputable def equivalence : Module R D ≌ ChainComplex (ModuleCat.{u} R) (ZMod D) :=
  CategoryTheory.Equivalence.mk reduce inflate unit counit

def forgetObj (M : Module R D) : ChainComplex (ModuleCat.{u} R) ℤ :=
  ChainComplex.of M.X M.d M.dd

def forget : Module R D ⥤ ChainComplex (ModuleCat.{u} R) ℤ where
  obj := forgetObj
  map f := ChainComplex.ofHom f.f (by intro n; simpa only [forgetObj, ChainComplex.of_d] using f.comm_d n)
  map_id M := by ext n; rfl
  map_comp f g := by ext n; rfl

abbrev unroll : ChainComplex (ModuleCat.{u} R) (ZMod D) ⥤
    ChainComplex (ModuleCat.{u} R) ℤ := inflate ⋙ forget

def unrollScIso (n : ℤ) : unroll (R:=R) (D:=D) ⋙
    shortComplexFunctor' (ModuleCat.{u} R) (.down ℤ) (n+1) n (n-1) ≅
    shortComplexFunctor' (ModuleCat.{u} R) (.down (ZMod D))
      (((n+1 : ℤ) : ZMod D)) (n : ZMod D) (((n-1 : ℤ) : ZMod D)) := by
  refine NatIso.ofComponents (fun P => ?_) ?_
  · refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · simp [shortComplexFunctor', unroll, inflate, inflateObj, forget, forgetObj, ChainComplex.of.d]
    · simp [shortComplexFunctor', unroll, inflate, inflateObj, forget, forgetObj, ChainComplex.of.d]
  · intro P Q f
    apply ShortComplex.hom_ext <;>
      simp [unroll, inflate, inflateObj, forget, forgetObj, ShortComplex.isoMk, shortComplexFunctor']

def unrollHomologyIso (n : ℤ) :
    unroll (R:=R) (D:=D) ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down ℤ) n ≅
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down (ZMod D)) (n : ZMod D) :=
  Functor.isoWhiskerLeft unroll
    (homologyFunctorIso' (ModuleCat.{u} R) (.down ℤ) (n+1) n (n-1) (by simp) (by simp)) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight (unrollScIso n) _ ≪≫
  (homologyFunctorIso' (ModuleCat.{u} R) (.down (ZMod D))
    (((n+1 : ℤ) : ZMod D)) (n : ZMod D) (((n-1 : ℤ) : ZMod D))
    (by simp) (by simp)).symm

def homology (n : ℤ) : Module R D ⥤ ModuleCat.{u} R :=
  forget ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down ℤ) n

def homologyIso (n : ℤ) : homology (R:=R) (D:=D) n ≅
    reduce ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down (ZMod D)) (n : ZMod D) :=
  (Functor.leftUnitor _).symm ≪≫
  Functor.isoWhiskerRight unit _ ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft reduce ((Functor.associator _ _ _).symm ≪≫ unrollHomologyIso n)

def quasiIso : MorphismProperty (Module R D) := fun _ _ f =>
  QuasiIso (forget.map f)

lemma quasiIso_iff {M N : Module R D} (f : M ⟶ N) :
    quasiIso f ↔ QuasiIso (reduce.map f) := by
  change QuasiIso (forget.map f) ↔ _
  rw [_root_.quasiIso_iff, _root_.quasiIso_iff]
  simp only [quasiIsoAt_iff_isIso_homologyMap]
  have hh (n : ℤ) : IsIso (homologyMap (forget.map f) n) ↔
      IsIso (homologyMap (reduce.map f) (n : ZMod D)) := by
    exact NatIso.isIso_map_iff (homologyIso n) f
  refine ⟨fun h i => ?_, fun h n => (hh n).mpr (h (n : ZMod D))⟩
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective i
  exact (hh n).mp (h n)

section DerivedMaps
variable (R D)
variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]

abbrev Derived := HomologicalComplexUpToQuasiIso (ModuleCat.{u} R) (.down (ZMod D))

abbrev localization : Module R D ⥤ Derived R D :=
  reduce ⋙ HomologicalComplexUpToQuasiIso.Q

theorem localization_isLocalization :
    (localization R D).IsLocalization (quasiIso (R:=R) (D:=D)) := by
  let Q : ChainComplex (ModuleCat.{u} R) (ZMod D) ⥤ Derived R D :=
    HomologicalComplexUpToQuasiIso.Q
  let W := HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))
  apply Functor.IsLocalization.of_equivalence_source Q W (localization R D)
    (quasiIso (R:=R) (D:=D)) equivalence.symm
  · intro P P' f hf
    apply MorphismProperty.le_isoClosure
    change QuasiIso (forget.map (inflate.map f))
    rw [_root_.quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    change IsIso ((unroll ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.down ℤ) n).map f)
    rw [NatIso.isIso_map_iff (unrollHomologyIso n)]
    have : QuasiIso f := hf
    exact inferInstanceAs (IsIso (homologyMap f (n : ZMod D)))
  · intro M N f hf
    have : QuasiIso (reduce.map f) := (quasiIso_iff f).mp hf
    exact Localization.inverts Q W (reduce.map f) ((quasiIso_iff f).mp hf)
  · exact (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight counit Q ≪≫ Functor.leftUnitor Q

end DerivedMaps

lemma exponent_exists_unique (hD : 0 < D) (i j : ℤ) :
    (i : ZMod D) = (j : ZMod D) ↔ ∃! q : ℤ, j = i + (D : ℤ) * q := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q, by omega, ?_⟩
    intro q' hq'
    have h : (D : ℤ) * q' = (D : ℤ) * q := by omega
    exact mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hD)) h
  · rintro ⟨q, hq, _⟩
    exact ⟨q, by omega⟩

variable [(HomologicalComplex.quasiIso (ModuleCat.{u} R) (.down (ZMod D))).HasLocalization.{w}]

abbrev derivedHomology (n : ℤ) : Derived R D ⥤ ModuleCat.{u} R :=
  HomologicalComplexUpToQuasiIso.homologyFunctor _ _ (n : ZMod D)

def localizationHomologyIso (n : ℤ) :
    localization R D ⋙ derivedHomology n ≅ homology (R:=R) (D:=D) n :=
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft reduce
    (HomologicalComplexUpToQuasiIso.homologyFunctorFactors (ModuleCat.{u} R)
      (.down (ZMod D)) (n : ZMod D)) ≪≫
  (homologyIso n).symm

end HahnWilson.LaurentDg

end

end OAI
