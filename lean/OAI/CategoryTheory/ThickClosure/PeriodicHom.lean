import OAI.CategoryTheory.ThickClosure.PeriodicDerived

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.PeriodicHom
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HahnWilson.PeriodicSplitting HahnWilson.PeriodicDerived
universe u w
variable {R : Type u} [Ring R] {D : ℕ}

abbrev homotopyQuotient : PeriodicComplex R D ⥤
    HomotopyCategory (ModuleCat.{u} R) (.down (ZMod D)) :=
  HomotopyCategory.quotient _ _

variable (G : ZMod D → ModuleCat.{u} R) {P : PeriodicComplex R D}

lemma diagonal_map_cycle (f : diagonalComplex G ⟶ P) (i : ZMod D) :
    f.f i ≫ P.d i (i - 1) = 0 := by
  rw [f.comm, diagonalComplex_d, CategoryTheory.Limits.zero_comp]

noncomputable def cycleClass (f : diagonalComplex G ⟶ P) (i : ZMod D) :
    G i ⟶ P.homology i :=
  P.liftCycles' (f.f i) (i - 1) (down_prev i) (diagonal_map_cycle G f i) ≫ P.homologyπ i

lemma source_cycle_naturality (f : diagonalComplex G ⟶ P) (i : ZMod D) :
    (diagonalComplex G).liftCycles' (𝟙 (G i)) (i - 1) (down_prev i) (by rw [Category.id_comp]; exact diagonalComplex_d G _ _) ≫
      cyclesMap f i =
      P.liftCycles' (f.f i) (i - 1) (down_prev i) (diagonal_map_cycle G f i) := by
  apply (cancel_mono (P.iCycles i)).mp
  simp only [Category.assoc, cyclesMap_i, liftCycles_i_assoc, liftCycles_i,
    Category.id_comp]

lemma cycleClass_eq (f : diagonalComplex G ⟶ P) (i : ZMod D) :
    cycleClass G f i =
      (diagonalComplex G).liftCycles' (𝟙 (G i)) (i - 1) (down_prev i) (by rw [Category.id_comp]; exact diagonalComplex_d G _ _) ≫
        (diagonalComplex G).homologyπ i ≫ homologyMap f i := by
  unfold cycleClass
  rw [← source_cycle_naturality, Category.assoc, homologyπ_naturality]

lemma null_homotopy_of_cycleClass_zero [∀ i, Projective (G i)]
    (f : diagonalComplex G ⟶ P) (hf : ∀ i, cycleClass G f i = 0) :
    Nonempty (Homotopy f 0) := by
  classical
  let S (i : ZMod D) := ShortComplex.mk (P.toCycles (i + 1) i) (P.homologyπ i)
    (P.toCycles_comp_homologyπ (i + 1) i)
  have hS (i : ZMod D) : (S i).Exact :=
    (S i).exact_of_g_is_cokernel (P.homologyIsCokernel (i + 1) i
      ((ComplexShape.down (ZMod D)).prev_eq' rfl))
  let z (i : ZMod D) :=
    P.liftCycles' (f.f i) (i - 1) (down_prev i) (diagonal_map_cycle G f i)
  have hzi (i : ZMod D) : z i ≫ (S i).g = 0 := hf i
  let h (i : ZMod D) : G i ⟶ P.X (i + 1) :=
    (hS i).liftFromProjective (z i) (hzi i)
  have hk (i : ZMod D) : h i ≫ P.d (i + 1) i = f.f i := by
    have he := congrArg (fun a => a ≫ P.iCycles i)
      ((hS i).liftFromProjective_comp (z i) (hzi i))
    change (h i ≫ P.toCycles (i + 1) i) ≫ P.iCycles i = z i ≫ P.iCycles i at he
    simpa only [Category.assoc, toCycles_i, z, liftCycles_i] using he
  let h' (i j : ZMod D) (hji : (ComplexShape.down (ZMod D)).Rel j i) :
      (diagonalComplex G).X i ⟶ P.X j :=
    h i ≫ (P.XIsoOfEq hji).hom
  have he : f = Homotopy.nullHomotopicMap' h' := by
    ext i : 1
    rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.down (ZMod D)).Rel (i + 1) i from rfl)
      (down_prev i), diagonalComplex_d, CategoryTheory.Limits.zero_comp, zero_add]
    dsimp [h']
    simpa using (hk i).symm
  exact ⟨(Homotopy.ofEq he).trans (Homotopy.nullHomotopy' h')⟩

theorem homotopy_zero_iff [∀ i, Projective (G i)]
    (f : diagonalComplex G ⟶ P) :
    Nonempty (Homotopy f 0) ↔ ∀ i, homologyMap f i = 0 := by
  constructor
  · rintro ⟨h⟩ i
    simpa using h.homologyMap_eq i
  · intro hf
    apply null_homotopy_of_cycleClass_zero G f
    intro i
    rw [cycleClass_eq, hf i, CategoryTheory.Limits.comp_zero,
      CategoryTheory.Limits.comp_zero]

lemma cycleClass_comp {P' : PeriodicComplex R D} (f : diagonalComplex G ⟶ P)
    (q : P ⟶ P') (i : ZMod D) :
    cycleClass G (f ≫ q) i = cycleClass G f i ≫ homologyMap q i := by
  simp only [cycleClass_eq, homologyMap_comp, Category.assoc]

lemma cycleClass_sub (f g : diagonalComplex G ⟶ P) (i : ZMod D) :
    cycleClass G (f - g) i = cycleClass G f i - cycleClass G g i := by
  simp only [cycleClass_eq, homologyMap_sub, Preadditive.comp_sub]

lemma quotient_eq_of_cycleClass_eq [∀ i, Projective (G i)]
    (f g : diagonalComplex G ⟶ P) (h : ∀ i, cycleClass G f i = cycleClass G g i) :
    homotopyQuotient.map f = homotopyQuotient.map g := by
  apply sub_eq_zero.mp
  rw [← Functor.map_sub, HomotopyCategory.quotient_map_eq_zero_iff]
  apply null_homotopy_of_cycleClass_zero G
  intro i
  rw [cycleClass_sub, h i, sub_self]

noncomputable def mapOfClasses [∀ i, Projective (G i)]
    (v : ∀ i, G i ⟶ P.homology i) : diagonalComplex G ⟶ P where
  f i := Projective.factorThru (v i) (P.homologyπ i) ≫ P.iCycles i
  comm' i j hij := by
    rw [Category.assoc, iCycles_d, CategoryTheory.Limits.comp_zero, diagonalComplex_d,
      CategoryTheory.Limits.zero_comp]

lemma cycleClass_mapOfClasses [∀ i, Projective (G i)]
    (v : ∀ i, G i ⟶ P.homology i) (i : ZMod D) :
    cycleClass G (mapOfClasses G v) i = v i := by
  unfold cycleClass
  have he : P.liftCycles' ((mapOfClasses G v).f i) (i - 1) (down_prev i)
      (diagonal_map_cycle G (mapOfClasses G v) i) =
      Projective.factorThru (v i) (P.homologyπ i) := by
    apply (cancel_mono (P.iCycles i)).mp
    rw [liftCycles_i]
    rfl
  rw [he, Projective.factorThru_comp]

theorem free_hom_quasiIso_bijective [∀ i, Projective (G i)]
    {P' : PeriodicComplex R D} (q : P ⟶ P') [QuasiIso q] :
    Function.Bijective (fun f : homotopyQuotient.obj (diagonalComplex G) ⟶
        homotopyQuotient.obj P => f ≫ homotopyQuotient.map q) := by
  constructor
  · intro f g h
    obtain ⟨f, rfl⟩ := homotopyQuotient.map_surjective f
    obtain ⟨g, rfl⟩ := homotopyQuotient.map_surjective g
    have he : homotopyQuotient.map (f ≫ q) = homotopyQuotient.map (g ≫ q) := by
      simpa only [Functor.map_comp] using h
    have hh := HomotopyCategory.homotopyOfEq _ _ he
    apply sub_eq_zero.mp
    rw [← Functor.map_sub, HomotopyCategory.quotient_map_eq_zero_iff, homotopy_zero_iff]
    intro i
    rw [homologyMap_sub, sub_eq_zero]
    apply (cancel_mono (homologyMap q i)).mp
    simpa only [homologyMap_comp] using hh.homologyMap_eq i
  · intro f
    obtain ⟨f, rfl⟩ := homotopyQuotient.map_surjective f
    let v (i : ZMod D) := cycleClass G f i ≫ inv (homologyMap q i)
    refine ⟨homotopyQuotient.map (mapOfClasses G v), ?_⟩
    dsimp only
    rw [← Functor.map_comp]
    apply quotient_eq_of_cycleClass_eq
    intro i
    rw [cycleClass_comp, cycleClass_mapOfClasses]
    simp [v]

end HahnWilson.PeriodicHom

end

end OAI
