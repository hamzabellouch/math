import OAI.Algebra.Finitistic.Bar.RecursiveTotalFlatten

namespace OAI
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open scoped DirectSum
noncomputable section
namespace DerivedBar.RecursiveTotal
universe u
variable {D : Type u} [Ring D]
local notation "c" => ComplexShape.down ℕ
local instance (r n : ℕ) : DecidableEq (Index r n) := Classical.decEq _

section Sums
variable {I : Type} [Finite I] [DecidableEq I] (V : I → ModuleCat.{u} D)
  (G : ModuleCat.{u} D ⥤ ModuleCat.{u} D) [G.Additive]
local instance : Fintype I := Fintype.ofFinite I

/-- Distribution over a finite direct sum, defined by its coproduct property. -/
def sumDesc {Y : ModuleCat.{u} D} (f : ∀ t, G.obj (V t) ⟶ Y) :
    G.obj (ModuleCat.of D (⨁ t, V t)) ⟶ Y :=
  (isColimitOfPreserves G (ModuleCat.coproductCoconeIsColimit V)).desc
    { pt := Y
      ι := Discrete.natTrans (fun t => f t.as) }

@[reassoc (attr := simp)]
theorem lof_sumDesc {Y : ModuleCat.{u} D} (f : ∀ t, G.obj (V t) ⟶ Y) (t : I) :
    G.map (ModuleCat.ofHom (DirectSum.lof D I (fun t => V t) t)) ≫
      sumDesc V G f = f t :=
  (isColimitOfPreserves G (ModuleCat.coproductCoconeIsColimit V)).fac _ ⟨t⟩

theorem sum_hom_ext {Y : ModuleCat.{u} D}
    {f g : G.obj (ModuleCat.of D (⨁ t, V t)) ⟶ Y}
    (h : ∀ t, G.map (ModuleCat.ofHom (DirectSum.lof D I (fun t => V t) t)) ≫ f =
      G.map (ModuleCat.ofHom (DirectSum.lof D I (fun t => V t) t)) ≫ g) : f=g := by
  apply (isColimitOfPreserves G (ModuleCat.coproductCoconeIsColimit V)).hom_ext
  rintro ⟨t⟩
  exact h t
end Sums

variable (B : ℕ → ModuleCat.{u} D ⥤ ChainComplex (ModuleCat.{u} D) ℕ)
  [∀ r, (B r).Additive] (Z : ChainComplex (ModuleCat.{u} D) ℕ)

abbrev flat (r n : ℕ) : ModuleCat.{u} D :=
  ModuleCat.of D (⨁ t : Index r n, summand B Z r n t)

def lof (r n : ℕ) (t : Index r n) : summand B Z r n t ⟶ flat B Z r n :=
  ModuleCat.ofHom (DirectSum.lof D (Index r n) (fun t => summand B Z r n t) t)

abbrev assemble (r n : ℕ) : flat B Z r n ⟶ (iter B Z r).X n :=
  (flattenIso B Z r n (𝟭 _)).inv

@[reassoc (attr := simp)]
theorem lof_assemble (r n : ℕ) (t : Index r n) :
    lof B Z r n t ≫ assemble B Z r n = inclusion B Z r n t := by
  apply (cancel_mono (flattenIso B Z r n (𝟭 _)).hom).mp
  change lof B Z r n t ≫ (flattenIso B Z r n (𝟭 _)).inv ≫ _ = _
  rw [Iso.inv_hom_id, Category.comp_id]
  exact (inclusion_desc B Z r (𝟭 _)
    (fun t => ModuleCat.ofHom (DirectSum.lof D (Index r n)
      (fun t => (𝟭 (ModuleCat D)).obj (summand B Z r n t)) t)) t).symm

/-- The horizontal face in a literal outer block; there is no face at length zero. -/
def horizontal (r n i q : ℕ) (h : i+q=n+1) (t : Index r q) :
    (degreeFunctor B r i).obj (summand B Z r q t) ⟶ flat B Z (r+1) n :=
  match i with
  | 0 => 0
  | i+1 => ((B r).obj (summand B Z r q t)).d (i+1) i ≫
      lof B Z (r+1) n ⟨⟨⟨i,q⟩,by omega⟩,t⟩

/-- The vertical face applies the already defined inner differential, with
exactly the totalization sign (-1)^i, then distributes the resulting finite sum. -/
def vertical (r n i q : ℕ) (h : i+q=n+1) (t : Index r q)
    (d : ∀ q, flat B Z r (q+1) ⟶ flat B Z r q) :
    (degreeFunctor B r i).obj (summand B Z r q t) ⟶ flat B Z (r+1) n :=
  match q with
  | 0 => 0
  | q+1 => ((-1 : ℤˣ)^i) •
      ((degreeFunctor B r i).map (lof B Z r (q+1) t ≫ d q) ≫
        sumDesc (summand B Z r q) (degreeFunctor B r i)
          (fun s => lof B Z (r+1) n ⟨⟨⟨i,q⟩,by omega⟩,s⟩))

/-- Independently recursive differential on the flattened direct sum. Its
construction uses only the original functor differentials, finite-sum distribution,
and the previously constructed inner differential, never the total differential. -/
def differential : (r n : ℕ) → flat B Z r (n+1) ⟶ flat B Z r n
  | 0, n => ModuleCat.ofHom (DirectSum.toModule D _ _
      (fun _ => (Z.d (n+1) n ≫ lof B Z 0 n ()).hom))
  | r+1, n => ModuleCat.ofHom (DirectSum.toModule D _ _
      (fun t => (horizontal B Z r n t.1.val.1 t.1.val.2 t.1.property t.2 +
        vertical B Z r n t.1.val.1 t.1.val.2 t.1.property t.2
          (differential r)).hom))

@[reassoc (attr := simp)]
theorem lof_differential_succ (r n i q : ℕ) (h : i+q=n+1) (t : Index r q) :
    lof B Z (r+1) (n+1) ⟨⟨⟨i,q⟩,h⟩,t⟩ ≫ differential B Z (r+1) n =
      horizontal B Z r n i q h t + vertical B Z r n i q h t (differential B Z r) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  simp only [lof, differential, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply]
  erw [DirectSum.toModule_lof]
  rfl

@[reassoc (attr := simp)]
theorem sumDesc_assemble (r n i q : ℕ) (h : i+q=n) :
    sumDesc (summand B Z r q) (degreeFunctor B r i)
      (fun s => lof B Z (r+1) n ⟨⟨⟨i,q⟩,h⟩,s⟩) ≫ assemble B Z (r+1) n =
    (degreeFunctor B r i).map (assemble B Z r q) ≫
      (bicomplex B r (iter B Z r)).ιTotal c i q n h := by
  apply sum_hom_ext
  intro t
  erw [lof_sumDesc_assoc, lof_assemble]
  erw [← Category.assoc, ← Functor.map_comp]
  change _ = (degreeFunctor B r i).map (lof B Z r q t ≫ assemble B Z r q) ≫ _
  rw [lof_assemble]
  rfl

/-- The horizontal face agrees with the actual total on every nested tensor. -/
theorem horizontal_assemble (r n i q : ℕ) (h : i+q=n+1) (t : Index r q) :
    horizontal B Z r n i q h t ≫ assemble B Z (r+1) n =
      (degreeFunctor B r i).map (inclusion B Z r q t) ≫
        (bicomplex B r (iter B Z r)).d₁ c i q n := by
  cases i with
  | zero =>
    erw [horizontal, zero_comp, HomologicalComplex₂.d₁_eq_zero _ _ _ _ _ (by simp), comp_zero]
    rfl
  | succ i =>
    erw [horizontal, Category.assoc, lof_assemble,
      HomologicalComplex₂.d₁_eq _ _ (by rfl : (c).Rel (i+1) i) q n (by change i+q=n; omega)]
    change _ = _ ≫ ((1 : ℤˣ) • _)
    erw [one_smul]
    change ((B r).obj (summand B Z r q t)).d (i+1) i ≫
        (degreeFunctor B r i).map (inclusion B Z r q t) ≫ _ =
      (degreeFunctor B r (i+1)).map (inclusion B Z r q t) ≫
        ((B r).obj ((iter B Z r).X q)).d (i+1) i ≫ _
    exact (((B r).map (inclusion B Z r q t)).comm_assoc (i+1) i
      ((bicomplex B r (iter B Z r)).ιTotal c i q n (by change i+q=n; omega))).symm

/-- The signed vertical face agrees with the actual total whenever the inner
comparison has been proved; the induction below discharges that premise. -/
theorem vertical_assemble (r n i q : ℕ) (h : i+q=n+1) (t : Index r q)
    (ih : ∀ q, differential B Z r q ≫ assemble B Z r q =
      assemble B Z r (q+1) ≫ (iter B Z r).d (q+1) q) :
    vertical B Z r n i q h t (differential B Z r) ≫ assemble B Z (r+1) n =
      (degreeFunctor B r i).map (inclusion B Z r q t) ≫
        (bicomplex B r (iter B Z r)).d₂ c i q n := by
  cases q with
  | zero =>
    erw [vertical, zero_comp, HomologicalComplex₂.d₂_eq_zero _ _ _ _ _ (by simp), comp_zero]
    rfl
  | succ q =>
    erw [vertical, HomologicalComplex₂.d₂_eq _ _ i (by rfl : (c).Rel (q+1) q) n
      (by change i+q=n; omega)]
    change _ = _ ≫ (((-1 : ℤˣ)^i) • _)
    erw [Linear.units_smul_comp, Linear.comp_units_smul, Category.assoc,
      sumDesc_assemble]
    congr 1
    erw [← Category.assoc, ← Functor.map_comp, Category.assoc, ih,
      ← Category.assoc, lof_assemble, Functor.map_comp, Category.assoc]

theorem differential_assemble (r n : ℕ) :
    differential B Z r n ≫ assemble B Z r n =
      assemble B Z r (n+1) ≫ (iter B Z r).d (n+1) n := by
  induction r generalizing n with
  | zero =>
    apply sum_hom_ext (summand B Z 0 (n+1)) (𝟭 _)
    intro t
    cases t
    have hf : lof B Z 0 (n+1) () ≫ differential B Z 0 n =
        Z.d (n+1) n ≫ lof B Z 0 n () := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      simp only [lof, differential, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
        LinearMap.comp_apply]
      erw [DirectSum.toModule_lof]
      rfl
    change lof B Z 0 (n+1) () ≫ _ = lof B Z 0 (n+1) () ≫ _
    erw [← Category.assoc, hf, Category.assoc, lof_assemble, lof_assemble_assoc]
    simp only [inclusion, iter]
    exact Category.comp_id _
  | succ r ih =>
    apply sum_hom_ext (summand B Z (r+1) (n+1)) (𝟭 _)
    rintro ⟨⟨⟨i,q⟩,h⟩,t⟩
    change lof B Z (r+1) (n+1) _ ≫ _ = lof B Z (r+1) (n+1) _ ≫ _
    erw [lof_differential_succ_assoc, add_comp, horizontal_assemble,
      vertical_assemble B Z r n i q h t ih, lof_assemble_assoc]
    simp only [inclusion, iter, HomologicalComplex₂.total_d, comp_add]
    erw [Category.assoc, Category.assoc, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]
    rfl

/-- Square-zero is a consequence of the proved differential comparison. -/
theorem differential_sq (r n : ℕ) :
    differential B Z r (n+1) ≫ differential B Z r n = 0 := by
  apply (cancel_mono (assemble B Z r n)).mp
  rw [Category.assoc, differential_assemble, ← Category.assoc,
    differential_assemble, Category.assoc, HomologicalComplex.d_comp_d,
    comp_zero, zero_comp]

/-- The direct sum with its independently recursive signed differential. -/
def flatComplex (r : ℕ) : ChainComplex (ModuleCat.{u} D) ℕ :=
  ChainComplex.of (flat B Z r) (differential B Z r) (differential_sq B Z r)

/-- An actual chain isomorphism flattening every recursive total, with both
horizontal and signed vertical differential verified on literal summands. -/
def flattenChainIso (r : ℕ) : flatComplex B Z r ≅ iter B Z r :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (flattenIso B Z r n (𝟭 _)).symm)
    (by
      intro i j hij
      change j+1=i at hij
      subst i
      change assemble B Z r (j+1) ≫ (iter B Z r).d (j+1) j =
        (flatComplex B Z r).d (j+1) j ≫ assemble B Z r j
      simpa only [flatComplex, ChainComplex.of_d] using
        (differential_assemble B Z r j).symm)
end DerivedBar.RecursiveTotal

end

end OAI
