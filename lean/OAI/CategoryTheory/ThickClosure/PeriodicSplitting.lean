import OAI.CategoryTheory.ThickClosure.PrincipalModules

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open LinearMap Submodule
open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace HahnWilson.PeriodicSplitting
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open HahnWilson.PrincipalModules
universe u
variable {R : Type u} [Ring R] {D : ℕ}

def homologyDiagonal (P : ChainComplex (ModuleCat.{u} R) (ZMod D)) :
    ChainComplex (ModuleCat.{u} R) (ZMod D) :=
  ChainComplex.of (fun i => P.homology i) (fun _ => 0) (fun _ => by simp)

section Resolution
variable {ι : Type*} [AddCommGroup ι] [One ι] [DecidableEq ι]
variable (F G : ι → ModuleCat.{u} R) (r : ∀ i, G i ⟶ F i)

abbrev resolutionTerm (i : ι) : ModuleCat.{u} R := F i ⊞ G (i - 1)

def resolutionD (i : ι) : resolutionTerm F G (i + 1) ⟶ resolutionTerm F G i :=
  biprod.snd ≫ eqToHom (congrArg G (add_sub_cancel_right i 1)) ≫ r i ≫ biprod.inl

omit [DecidableEq ι] in
lemma resolutionD_sq (i : ι) :
    resolutionD F G r (i + 1) ≫ resolutionD F G r i = 0 := by
  dsimp [resolutionD]
  simp only [CategoryTheory.Category.assoc, biprod.inl_snd_assoc,
    CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]

abbrev resolutionComplex : ChainComplex (ModuleCat.{u} R) ι :=
  ChainComplex.of (resolutionTerm F G) (resolutionD F G r) (resolutionD_sq F G r)

@[simp] lemma resolutionComplex_d (i : ι) :
    (resolutionComplex F G r).d (i + 1) i = resolutionD F G r i :=
  ChainComplex.of_d _ _ _

lemma resolutionComplex_d_prev (i : ι) :
    (resolutionComplex F G r).d i (i - 1) =
      biprod.snd ≫ r (i - 1) ≫ biprod.inl := by
  have hnat {j k : ι} (h : j = k) :
      eqToHom (congrArg (resolutionTerm F G) h) ≫ biprod.snd =
      biprod.snd ≫ eqToHom (congrArg (fun l => G (l - 1)) h) := by
    subst k
    simp
  change ChainComplex.of.d _ _ _ _ = _
  rw [ChainComplex.of.d, dite_eq_left (sub_add_cancel i 1).symm]
  dsimp only [resolutionD]
  rw [← CategoryTheory.Category.assoc, hnat]
  simp only [CategoryTheory.Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  exact (sub_add_cancel i 1).symm

variable {F G r} (P : ChainComplex (ModuleCat.{u} R) ι)
variable (a : ∀ i, F i ⟶ P.X i) (b : ∀ i, G (i - 1) ⟶ P.X i)
variable (ha : ∀ i j, a i ≫ P.d i j = 0)
variable (hb : ∀ i, b (i + 1) ≫ P.d (i + 1) i =
  eqToHom (congrArg G (add_sub_cancel_right i 1)) ≫ r i ≫ a i)

def resolutionMap : resolutionComplex F G r ⟶ P :=
  ChainComplex.ofHom (fun i => biprod.desc (a i) (b i)) (by
    intro i
    apply biprod.hom_ext'
    · simp [resolutionD, CategoryTheory.Category.assoc, ha]
    · simp [resolutionD, CategoryTheory.Category.assoc, hb])

@[simp, reassoc] lemma resolutionMap_inl (i : ι) :
    biprod.inl ≫ (resolutionMap P a b ha hb).f i = a i := by
  exact biprod.inl_desc _ _

end Resolution

section ResolutionHomology
variable {ι : Type*} [AddCommGroup ι] [One ι] [DecidableEq ι]
variable (F G H : ι → ModuleCat.{u} R) (r : ∀ i, G i ⟶ F i)
variable (p : ∀ i, F i ⟶ H i) (hr : ∀ i, Mono (r i))
variable (hrp : ∀ i, r i ≫ p i = 0)
variable (hp : ∀ i, IsColimit (CokernelCofork.ofπ (p i) (hrp i)))

def resolutionLeftHomologyData (i : ι) :
    ((resolutionComplex F G r).sc' (i + 1) i (i - 1)).LeftHomologyData := by
  letI := hr (i - 1)
  let S := (resolutionComplex F G r).sc' (i + 1) i (i - 1)
  have wi : (biprod.inl : F i ⟶ S.X₂) ≫ S.g = 0 := by
    change biprod.inl ≫ (resolutionComplex F G r).d i (i - 1) = 0
    rw [resolutionComplex_d_prev]
    simp
  let hker : IsLimit (KernelFork.ofι (biprod.inl : F i ⟶ S.X₂) wi) :=
    isKernelCompMono (biprod.isKernelSndKernelFork (F i) (G (i - 1)))
      (r (i - 1) ≫ biprod.inl) (resolutionComplex_d_prev F G r i)
  let η : resolutionTerm F G (i + 1) ⟶ G i :=
    biprod.snd ≫ eqToHom (congrArg G (add_sub_cancel_right i 1))
  letI : Epi η := by dsimp [η]; infer_instance
  have heq : hker.lift (KernelFork.ofι S.f S.zero) = η ≫ r i := by
    apply (cancel_mono (biprod.inl : F i ⟶ S.X₂)).mp
    have hfac := hker.fac (KernelFork.ofι S.f S.zero) WalkingParallelPair.zero
    change hker.lift (KernelFork.ofι S.f S.zero) ≫ biprod.inl = S.f at hfac
    exact hfac.trans (resolutionComplex_d F G r i)
  refine {
    K := F i
    H := H i
    i := biprod.inl
    π := p i
    wi := wi
    hi := hker
    wπ := ?_
    hπ := ?_ }
  · change hker.lift (KernelFork.ofι S.f S.zero) ≫ p i = 0
    exact (congrArg (fun f => f ≫ p i) heq).trans
      ((CategoryTheory.Category.assoc η (r i) (p i)).trans
        ((congrArg (fun f => η ≫ f) (hrp i)).trans CategoryTheory.Limits.comp_zero))
  · exact isCokernelEpiComp (hp i) η heq

@[simp] lemma resolutionLeftHomologyData_i (i : ι) :
    (resolutionLeftHomologyData F G H r p hr hrp hp i).i = biprod.inl := rfl
@[simp] lemma resolutionLeftHomologyData_π (i : ι) :
    (resolutionLeftHomologyData F G H r p hr hrp hp i).π = p i := rfl

end ResolutionHomology

def leftHomologyMapOfSquares {S₁ S₂ : ShortComplex (ModuleCat.{u} R)}
    (f : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
    (u : h₁.K ⟶ h₂.K) (v : h₁.H ⟶ h₂.H)
    (hi : u ≫ h₂.i = h₁.i ≫ f.τ₂) (hp : h₁.π ≫ v = u ≫ h₂.π) :
    ShortComplex.LeftHomologyMapData f h₁ h₂ where
  φK := u
  φH := v
  commi := hi
  commπ := hp
  commf' := by
    apply (cancel_mono h₂.i).mp
    simp only [CategoryTheory.Category.assoc, hi,
      h₂.f'_i, h₁.f'_i_assoc]
    exact f.comm₁₂.symm

section LiftResolution
variable {ι : Type*} [AddCommGroup ι] [One ι] [DecidableEq ι]
variable (P : ChainComplex (ModuleCat.{u} R) ι)
variable (L : ∀ i, (P.sc' (i + 1) i (i - 1)).LeftHomologyData)
variable (F G : ι → ModuleCat.{u} R) (r : ∀ i, G i ⟶ F i)
variable (p : ∀ i, F i ⟶ (L i).H) (hrp : ∀ i, r i ≫ p i = 0)
variable [hF : ∀ i, Projective (F i)] [hG : ∀ i, Projective (G i)]

noncomputable def chosenCycleLift (i : ι) : F i ⟶ (L i).K :=
  Projective.factorThru (p i) (L i).π

omit [DecidableEq ι] in
@[simp, reassoc] lemma chosenCycleLift_π (i : ι) :
    chosenCycleLift P L F p i ≫ (L i).π = p i :=
  Projective.factorThru_comp _ _

noncomputable def chosenBoundaryLift (i : ι) : G i ⟶ P.X (i + 1) := by
  let S := ShortComplex.mk (L i).f' (L i).π (L i).f'_π
  have hS : S.Exact := S.exact_of_g_is_cokernel (L i).hπ
  exact hS.liftFromProjective (r i ≫ chosenCycleLift P L F p i) (by
    change (r i ≫ chosenCycleLift P L F p i) ≫ (L i).π = 0
    rw [CategoryTheory.Category.assoc, chosenCycleLift_π, hrp])

omit [DecidableEq ι] in
@[simp, reassoc] lemma chosenBoundaryLift_f' (i : ι) :
    chosenBoundaryLift P L F G r p hrp i ≫ (L i).f' =
      r i ≫ chosenCycleLift P L F p i := by
  let S := ShortComplex.mk (L i).f' (L i).π (L i).f'_π
  exact ShortComplex.Exact.liftFromProjective_comp
    (S.exact_of_g_is_cokernel (L i).hπ) _ _

noncomputable def resolutionCycleMap (i : ι) : F i ⟶ P.X i :=
  chosenCycleLift P L F p i ≫ (L i).i

noncomputable def resolutionBoundaryMap (i : ι) : G (i - 1) ⟶ P.X i :=
  chosenBoundaryLift P L F G r p hrp (i - 1) ≫
    eqToHom (congrArg P.X (sub_add_cancel i 1))

lemma resolutionCycleMap_d (i j : ι) : resolutionCycleMap P L F p i ≫ P.d i j = 0 := by
  by_cases h : (ComplexShape.down ι).Rel i j
  · have hj : j = i - 1 := by
      have := (ComplexShape.down ι).next_eq' h
      have hj' := (ComplexShape.down ι).next_eq' (show (ComplexShape.down ι).Rel i (i - 1) from sub_add_cancel i 1)
      exact this.symm.trans hj'
    subst j
    exact (CategoryTheory.Category.assoc _ _ _).trans
      ((congrArg (fun f => chosenCycleLift P L F p i ≫ f) (L i).wi).trans CategoryTheory.Limits.comp_zero)
  · rw [P.shape _ _ h, CategoryTheory.Limits.comp_zero]

omit [DecidableEq ι] in
lemma resolutionBoundaryMap_d (i : ι) :
    resolutionBoundaryMap P L F G r p hrp (i + 1) ≫ P.d (i + 1) i =
      eqToHom (congrArg G (add_sub_cancel_right i 1)) ≫
        r i ≫ resolutionCycleMap P L F p i := by
  have hnat {j k : ι} (h : j = k) :
      chosenBoundaryLift P L F G r p hrp j ≫
          eqToHom (congrArg (fun l => P.X (l + 1)) h) =
        eqToHom (congrArg G h) ≫ chosenBoundaryLift P L F G r p hrp k := by
    subst k
    simp
  have hb : resolutionBoundaryMap P L F G r p hrp (i + 1) =
      eqToHom (congrArg G (add_sub_cancel_right i 1)) ≫
        chosenBoundaryLift P L F G r p hrp i :=
    hnat (add_sub_cancel_right i 1)
  rw [hb, CategoryTheory.Category.assoc]
  congr 1
  change chosenBoundaryLift P L F G r p hrp i ≫ (P.sc' (i + 1) i (i - 1)).f = _
  exact (congrArg (fun z => chosenBoundaryLift P L F G r p hrp i ≫ z)
      (L i).f'_i.symm).trans
    ((CategoryTheory.Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ (L i).i) (chosenBoundaryLift_f' P L F G r p hrp i)).trans
        (CategoryTheory.Category.assoc _ _ _)))

noncomputable def comparisonMap : resolutionComplex F G r ⟶ P :=
  resolutionMap P (resolutionCycleMap P L F p) (resolutionBoundaryMap P L F G r p hrp)
    (resolutionCycleMap_d P L F p) (resolutionBoundaryMap_d P L F G r p hrp)

end LiftResolution

section ComparisonHomology
variable {ι : Type*} [AddCommGroup ι] [One ι] [DecidableEq ι]
variable (P : ChainComplex (ModuleCat.{u} R) ι)
variable (L : ∀ i, (P.sc' (i + 1) i (i - 1)).LeftHomologyData)
variable (F G : ι → ModuleCat.{u} R) (r : ∀ i, G i ⟶ F i)
variable (p : ∀ i, F i ⟶ (L i).H) (hrp : ∀ i, r i ≫ p i = 0)
variable [hF : ∀ i, Projective (F i)] [hG : ∀ i, Projective (G i)]
variable (hr : ∀ i, Mono (r i))
variable (hp : ∀ i, IsColimit (CokernelCofork.ofπ (p i) (hrp i)))

include hr hp in
lemma comparisonMap_quasiIso : QuasiIso (comparisonMap P L F G r p hrp) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff' _ (i + 1) i (i - 1)
    ((ComplexShape.down ι).prev_eq' rfl)
    ((ComplexShape.down ι).next_eq' (sub_add_cancel i 1))]
  let f := (shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.down ι)
    (i + 1) i (i - 1)).map (comparisonMap P L F G r p hrp)
  let h := resolutionLeftHomologyData F G (fun i => (L i).H) r p hr hrp hp i
  let u := chosenCycleLift P L F p i
  have hi : u ≫ (L i).i = h.i ≫ f.τ₂ := by
    change resolutionCycleMap P L F p i =
      biprod.inl ≫ (comparisonMap P L F G r p hrp).f i
    exact (resolutionMap_inl _ _ _ _ _ _).symm
  have hπ : h.π ≫ 𝟙 (L i).H = u ≫ (L i).π := by
    change p i ≫ 𝟙 _ = chosenCycleLift P L F p i ≫ (L i).π
    simp
  exact (leftHomologyMapOfSquares f h (L i) u (𝟙 _) hi hπ).quasiIso_iff.mpr
    (inferInstance : IsIso (𝟙 (L i).H))

end ComparisonHomology

section Diagonal
variable {ι : Type*} [AddCommGroup ι] [One ι] [DecidableEq ι]

noncomputable def cyclicHomologyData (P : ChainComplex (ModuleCat.{u} R) ι) (i : ι) :
    (P.sc' (i + 1) i (i - 1)).LeftHomologyData :=
  (P.sc i).homologyData.left.ofIso (P.isoSc' (i + 1) i (i - 1)
    ((ComplexShape.down ι).prev_eq' rfl)
    ((ComplexShape.down ι).next_eq' (sub_add_cancel i 1)))

abbrev diagonalComplex (H : ι → ModuleCat.{u} R) : ChainComplex (ModuleCat.{u} R) ι :=
  ChainComplex.of H (fun _ => 0) (fun _ => by simp)

@[simp] lemma diagonalComplex_d (H : ι → ModuleCat.{u} R) (i j : ι) :
    (diagonalComplex H).d i j = 0 := by
  change ChainComplex.of.d H (fun _ => 0) i j = 0
  unfold ChainComplex.of.d
  split <;> simp

variable (F G H : ι → ModuleCat.{u} R) (r : ∀ i, G i ⟶ F i)
variable (p : ∀ i, F i ⟶ H i) (hrp : ∀ i, r i ≫ p i = 0)

def diagonalMap : resolutionComplex F G r ⟶ diagonalComplex H :=
  resolutionMap (diagonalComplex H) p (fun _ => 0)
    (fun i j => (congrArg (fun z => p i ≫ z) (diagonalComplex_d H i j)).trans
      CategoryTheory.Limits.comp_zero) (fun i => by simp [hrp])

variable (hr : ∀ i, Mono (r i))
variable (hp : ∀ i, IsColimit (CokernelCofork.ofπ (p i) (hrp i)))

include hr hp in
lemma diagonalMap_quasiIso : QuasiIso (diagonalMap F G H r p hrp) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff' _ (i + 1) i (i - 1)
    ((ComplexShape.down ι).prev_eq' rfl)
    ((ComplexShape.down ι).next_eq' (sub_add_cancel i 1))]
  let f := (shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.down ι)
    (i + 1) i (i - 1)).map (diagonalMap F G H r p hrp)
  let h := resolutionLeftHomologyData F G H r p hr hrp hp i
  let S := (diagonalComplex H).sc' (i + 1) i (i - 1)
  have hf : S.f = 0 := diagonalComplex_d H _ _
  have hg : S.g = 0 := diagonalComplex_d H _ _
  let h' := ShortComplex.LeftHomologyData.ofZeros S hf hg
  have hi : p i ≫ h'.i = h.i ≫ f.τ₂ := by
    change p i ≫ 𝟙 _ = biprod.inl ≫ (diagonalMap F G H r p hrp).f i
    exact (Category.comp_id _).trans (biprod.inl_desc _ _).symm
  have hπ : h.π ≫ 𝟙 (H i) = p i ≫ h'.π := rfl
  exact (leftHomologyMapOfSquares f h h' (p i) (𝟙 _) hi hπ).quasiIso_iff.mpr
    (inferInstance : IsIso (𝟙 (H i)))

end Diagonal

theorem exists_categorical_resolution [IsDomain R] [IsPrincipalIdealRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ (n m : ℕ) (r : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R))
      (p : ModuleCat.of R (Fin n → R) ⟶ M) (w : r ≫ p = 0),
      Mono r ∧ Nonempty (IsColimit (CokernelCofork.ofπ p w)) := by
  obtain ⟨n,m,r,p,hr,hp,hex⟩ := finite_free_resolution (R := R) M
  have he : Function.Exact r p := LinearMap.exact_iff.mpr hex.symm
  let r' : ModuleCat.of R (Fin m → R) ⟶ ModuleCat.of R (Fin n → R) := ModuleCat.ofHom r
  let p' : ModuleCat.of R (Fin n → R) ⟶ M := ModuleCat.ofHom p
  have w : r' ≫ p' = 0 := by
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun x => he.apply_apply_eq_zero x)
  exact ⟨n,m,r',p',w,(ModuleCat.mono_iff_injective r').mpr hr,
    ⟨ModuleCat.isColimitCokernelCofork r' p' he hp⟩⟩

theorem periodic_homology_splitting [IsDomain R] [IsPrincipalIdealRing R]
    [IsPrincipalIdealRing Rᵐᵒᵖ] (_hD : 0 < D) (_hDeven : Even D)
    (P : ChainComplex (ModuleCat.{u} R) (ZMod D))
    (hfin : ∀ i, Module.Finite R (P.homology i)) :
    ∃ (Q : ChainComplex (ModuleCat.{u} R) (ZMod D))
      (f : Q ⟶ P) (g : Q ⟶ homologyDiagonal P),
      QuasiIso f ∧ QuasiIso g ∧
      ∀ i, Module.Free R (Q.X i) ∧ Module.Finite R (Q.X i) := by
  classical
  let L := cyclicHomologyData P
  have hex (i : ZMod D) := @exists_categorical_resolution R _ _ _ (P.homology i) (hfin i)
  choose n m r p w hr hp using hex
  let F : ZMod D → ModuleCat.{u} R := fun i => ModuleCat.of R (Fin (n i) → R)
  let G : ZMod D → ModuleCat.{u} R := fun i => ModuleCat.of R (Fin (m i) → R)
  let Q := resolutionComplex F G r
  let : ∀ i, Projective (F i) := fun i => inferInstance
  let : ∀ i, Projective (G i) := fun i => inferInstance
  let f : Q ⟶ P := comparisonMap P L F G r p w
  let g : Q ⟶ homologyDiagonal P := diagonalMap F G (fun i => P.homology i) r p w
  refine ⟨Q,f,g,comparisonMap_quasiIso P L F G r p w hr (fun i => (hp i).some),
    diagonalMap_quasiIso F G (fun i => P.homology i) r p w hr (fun i => (hp i).some),?_⟩
  intro i
  let e := (ModuleCat.biprodIsoProd (F i) (G (i - 1))).toLinearEquiv
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩

end HahnWilson.PeriodicSplitting

end

end OAI
