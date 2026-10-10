import OAI.GroupTheory.Congruence.Coinvariants
import OAI.GroupTheory.Congruence.Stabilization
import OAI.Combinatorics.Coboundary.Links

namespace OAI

/-!
Partial resolutions, orbit projectivity, and homology of finite congruence coset complexes.
-/

noncomputable section
open CategoryTheory
open scoped BigOperators
open CategoryTheory Finsupp
open CategoryTheory Finsupp MonoidalCategory
open scoped BigOperators Matrix
open scoped Matrix
open scoped MonoidAlgebra
open CategoryTheory CategoryTheory.Limits

namespace CoboundaryExpanders.PartialResolution
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : ChainComplex C ℕ) (h : ℕ)
variable (P : ProjectiveResolution (kernel (K.d (h + 1) h)))

abbrev X (n : ℕ) : C := if n ≤ h + 1 then K.X n else P.complex.X (n - (h + 2))

def lowIso (n : ℕ) (hn : n ≤ h + 1) : X K h P n ≅ K.X n :=
  eqToIso (ite_eq_left hn)

def highIso (n : ℕ) (hn : ¬ n ≤ h + 1) :
    X K h P n ≅ P.complex.X (n - (h + 2)) := eqToIso (ite_eq_right hn)

def augment : P.complex.X 0 ⟶ kernel (K.d (h + 1) h) :=
  P.π.f 0 ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).hom

@[reassoc (attr := simp)] theorem augment_condition :
    P.complex.d 1 0 ≫ augment K h P = 0 := by
  unfold augment
  rw [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]

instance : Epi (augment K h P) := by unfold augment; infer_instance

def d (n : ℕ) : X K h P (n + 1) ⟶ X K h P n :=
  if hn : n + 1 ≤ h + 1 then
    (lowIso K h P (n+1) hn).hom ≫ K.d (n+1) n ≫
      (lowIso K h P n (by omega)).inv
  else if he : n = h + 1 then
    (highIso K h P (n+1) hn).hom ≫
      eqToHom (congrArg P.complex.X (show n+1-(h+2)=0 by omega)) ≫
      augment K h P ≫ kernel.ι (K.d (h+1) h) ≫
      eqToHom (congrArg K.X he.symm) ≫ (lowIso K h P n (by omega)).inv
  else
    (highIso K h P (n+1) hn).hom ≫
      P.complex.d (n+1-(h+2)) (n-(h+2)) ≫
      (highIso K h P n (by omega)).inv

@[reassoc (attr := simp)] theorem lowIso_inv_hom (n : ℕ) (h₁ h₂ : n ≤ h+1) :
    (lowIso K h P n h₁).inv ≫ (lowIso K h P n h₂).hom = 𝟙 _ := by
  simp

@[reassoc (attr := simp)] theorem highIso_inv_hom (n : ℕ) (h₁ h₂ : ¬ n ≤ h+1) :
    (highIso K h P n h₁).inv ≫ (highIso K h P n h₂).hom = 𝟙 _ := by
  simp

theorem d_comp_d (n : ℕ) : d K h P (n + 1) ≫ d K h P n = 0 := by
  by_cases hn2 : n + 2 ≤ h + 1
  · have hn1 : n + 1 ≤ h + 1 := by omega
    simp [d, hn2, hn1, Category.assoc]
  · by_cases hn1 : n + 1 ≤ h + 1
    · have he : n = h := by omega
      subst n
      simp [d, Category.assoc]
    · by_cases hn0 : n = h + 1
      · subst n
        have he : h+1+1+1-(h+2) = 1 := by omega
        simp [d, Category.assoc]
        rw [he]
        simp
      · have hn' : n ≠ h := by omega
        simp [d, hn2, hn1, hn0, hn', Category.assoc]

def complex : ChainComplex C ℕ := ChainComplex.of (X K h P) (d K h P) (d_comp_d K h P)

@[simp] theorem complex_d (n : ℕ) :
    (complex K h P).d (n+1) n = d K h P n := by
  simp only [complex, ChainComplex.of_d]

def short (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (d K h P (n+1)) (d K h P n) (d_comp_d K h P n)

def kernelShort : ShortComplex C :=
  ShortComplex.mk (augment K h P ≫ kernel.ι (K.d (h+1) h)) (K.d (h+1) h)
    (by simp)

theorem kernelShort_exact : (kernelShort K h P).Exact := by
  rw [ShortComplex.exact_iff_epi_kernel_lift]
  change Epi (kernel.lift (K.d (h+1) h)
    (augment K h P ≫ kernel.ι (K.d (h+1) h)) (by simp))
  have he : kernel.lift (K.d (h+1) h)
      (augment K h P ≫ kernel.ι (K.d (h+1) h)) (by simp) = augment K h P := by
    apply (cancel_mono (kernel.ι (K.d (h+1) h))).mp
    exact kernel.lift_ι _ _ _
  rw [he]
  infer_instance

def augmentShort : ShortComplex C :=
  ShortComplex.mk (P.complex.d 1 0) (augment K h P ≫ kernel.ι (K.d (h+1) h))
    (by simp)

theorem augmentShort_exact : (augmentShort K h P).Exact := by
  let S : ShortComplex C := ShortComplex.mk _ _ P.complex_d_comp_π_f_zero
  let φ : S ⟶ augmentShort K h P :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := (HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).hom ≫
        kernel.ι (K.d (h+1) h)
      comm₁₂ := by simp [S, augmentShort]
      comm₂₃ := by
        change 𝟙 (P.complex.X 0) ≫ (augment K h P ≫ kernel.ι (K.d (h+1) h)) =
          P.π.f 0 ≫
            ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).hom ≫
              kernel.ι (K.d (h+1) h))
        rw [Category.id_comp, augment, Category.assoc] }
  have : Epi φ.τ₁ := by
    change Epi (𝟙 (P.complex.X 1))
    infer_instance
  have : IsIso φ.τ₂ := by
    change IsIso (𝟙 (P.complex.X 0))
    infer_instance
  have : Mono φ.τ₃ := by
    change Mono ((HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 _).hom ≫
      kernel.ι (K.d (h+1) h))
    infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp P.exact₀

def lowShortIso (n : ℕ) (hn : n+2 ≤ h+1) :
    short K h P n ≅ ShortComplex.mk _ _ (K.d_comp_d (n+2) (n+1) n) :=
  ShortComplex.isoMk (lowIso K h P (n+2) hn)
    (lowIso K h P (n+1) (by omega)) (lowIso K h P n (by omega))
      (by dsimp [short]; simp [d, show n+1+1 ≤ h+1 by omega, Category.assoc])
      (by dsimp [short]; simp [d, show n+1 ≤ h+1 by omega, Category.assoc])

def kernelShortIso : short K h P h ≅ kernelShort K h P :=
  ShortComplex.isoMk
    (highIso K h P (h+2) (by omega) ≪≫ eqToIso (by simp [kernelShort]))
    (lowIso K h P (h+1) (by omega)) (lowIso K h P h (by omega))
    (by dsimp [short, kernelShort]; simp [d, Category.assoc])
    (by dsimp [short, kernelShort]; simp [d, Category.assoc])

def augmentShortIso : short K h P (h+1) ≅ augmentShort K h P :=
  ShortComplex.isoMk
    (highIso K h P (h+3) (by omega) ≪≫ eqToIso (by congr 1; omega))
    (highIso K h P (h+2) (by omega) ≪≫ eqToIso (by simp [augmentShort]))
    (lowIso K h P (h+1) (by omega))
    (by dsimp [short, augmentShort]; simp [d, Category.assoc])
    (by dsimp [short, augmentShort]; simp [d, Category.assoc])

lemma d_high (n : ℕ) (hn : h+2 ≤ n) :
    d K h P n = (highIso K h P (n+1) (by omega)).hom ≫
      P.complex.d (n+1-(h+2)) (n-(h+2)) ≫ (highIso K h P n (by omega)).inv := by
  rw [d, dite_eq_right (by omega), dite_eq_right (by omega)]

def tailShortIso (r : ℕ) : short K h P (h+2+r) ≅
    ShortComplex.mk _ _ (P.complex.d_comp_d (r+2) (r+1) r) :=
  ShortComplex.isoMk
    (highIso K h P (h+2+r+2) (by omega) ≪≫ P.complex.XIsoOfEq (by omega))
    (highIso K h P (h+2+r+1) (by omega) ≪≫ P.complex.XIsoOfEq (by omega))
    (highIso K h P (h+2+r) (by omega) ≪≫ P.complex.XIsoOfEq (by omega))
    (by
      dsimp [short]
      rw [d_high K h P _ (by omega)]
      simp [Category.assoc])
    (by
      dsimp [short]
      rw [d_high K h P _ (by omega)]
      simp [Category.assoc])

theorem complex_exactAt_succ
    (hK : ∀ n, n < h → K.ExactAt (n+1)) (n : ℕ) :
    (complex K h P).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', complex_d]
  change (short K h P n).Exact
  by_cases hn : n < h
  · apply (ShortComplex.exact_iff_of_iso (lowShortIso K h P n (by omega))).mpr
    exact (HomologicalComplex.exactAt_iff' K (n+2) (n+1) n (by simp) (by simp)).mp (hK n hn)
  · by_cases hn' : n = h
    · subst n
      exact (ShortComplex.exact_iff_of_iso (kernelShortIso K h P)).mpr (kernelShort_exact K h P)
    · by_cases hn'' : n = h+1
      · subst n
        exact (ShortComplex.exact_iff_of_iso (augmentShortIso K h P)).mpr (augmentShort_exact K h P)
      · obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (show h+2 ≤ n by omega)
        exact (ShortComplex.exact_iff_of_iso (tailShortIso K h P r)).mpr (P.exact_succ r)

theorem complex_projective (hK : ∀ n ≤ h+1, Projective (K.X n)) (n : ℕ) :
    Projective ((complex K h P).X n) := by
  by_cases hn : n ≤ h+1
  · exact Projective.of_iso (lowIso K h P n hn).symm (hK n hn)
  · exact Projective.of_iso (highIso K h P n hn).symm inferInstance

variable {Z : C} (ε : K.X 0 ⟶ Z) (hε : K.d 1 0 ≫ ε = 0)

def π : complex K h P ⟶ (ChainComplex.single₀ C).obj Z :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨(lowIso K h P 0 (by omega)).hom ≫ ε, by
      rw [complex_d]
      change d K h P 0 ≫ (lowIso K h P 0 (by omega)).hom ≫ ε = 0
      simp [d, Category.assoc, hε]⟩

def augmentationShortIso :
    ShortComplex.mk ((complex K h P).d 1 0) ((π K h P ε hε).f 0)
      (by
        rw [← HomologicalComplex.Hom.comm]
        simp
        exact comp_zero) ≅
    ShortComplex.mk (K.d 1 0) ε hε :=
  ShortComplex.isoMk (lowIso K h P 1 (by omega))
    (lowIso K h P 0 (by omega)) (Iso.refl Z)
    (by
      dsimp only
      rw [complex_d]
      change (lowIso K h P 1 (by omega)).hom ≫ K.d 1 0 =
        d K h P 0 ≫ (lowIso K h P 0 (by omega)).hom
      simp [d, Category.assoc])
    (by simp [π])

def resolution
    (hproj : ∀ n ≤ h+1, Projective (K.X n))
    (hexact : ∀ n, n < h → K.ExactAt (n+1))
    (hzero : (ShortComplex.mk (K.d 1 0) ε hε).Exact) [Epi ε] :
    ProjectiveResolution Z where
  complex := complex K h P
  projective := complex_projective K h P hproj
  π := π K h P ε hε
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · exact (ShortComplex.exact_and_epi_g_iff_of_iso
          (augmentationShortIso K h P ε hε)).mpr ⟨hzero, inferInstance⟩
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact complex_exactAt_succ K h P hexact n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

lemma complex_d_low (a b : ℕ) (ha : a ≤ h+1) (hb : b ≤ h+1) :
    (complex K h P).d a b = (lowIso K h P a ha).hom ≫ K.d a b ≫
      (lowIso K h P b hb).inv := by
  by_cases he : a = b+1
  · subst a
    rw [complex_d, d, dite_eq_left ha]
  · rw [(complex K h P).shape a b (by simpa using Ne.symm he),
      K.shape a b (by simpa using Ne.symm he)]
    simp
    rfl

lemma low_comm (a b : ℕ) (ha : a ≤ h+1) (hb : b ≤ h+1) :
    (lowIso K h P a ha).hom ≫ K.d a b =
      (complex K h P).d a b ≫ (lowIso K h P b hb).hom := by
  exact (Iso.comp_inv_eq (lowIso K h P b hb)).mp
    ((Category.assoc _ _ _).trans (complex_d_low K h P a b ha hb).symm)

universe v' u'
variable {D : Type u'} [Category.{v'} D] [Abelian D]
    (F : C ⥤ D) [F.Additive]

def mappedLowShortIso (j : ℕ) (hj : j ≤ h) :
    ((F.mapHomologicalComplex _).obj (complex K h P)).sc' (j+1) j (j-1) ≅
    ((F.mapHomologicalComplex _).obj K).sc' (j+1) j (j-1) :=
  ShortComplex.isoMk (F.mapIso (lowIso K h P (j+1) (by omega)))
    (F.mapIso (lowIso K h P j (by omega)))
    (F.mapIso (lowIso K h P (j-1) (by omega)))
    (by
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg F.map (low_comm K h P (j+1) j (by omega) (by omega)))
    (by
      change F.map _ ≫ F.map _ = F.map _ ≫ F.map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg F.map (low_comm K h P j (j-1) (by omega) (by omega)))

def mappedHomologyIso (j : ℕ) (hj : j ≤ h) :
    ((F.mapHomologicalComplex _).obj (complex K h P)).homology j ≅
    ((F.mapHomologicalComplex _).obj K).homology j :=
  (HomologicalComplex.homologyFunctorIso' D (ComplexShape.down ℕ)
    (j+1) j (j-1) (by simp) (by cases j <;> simp)).app _ ≪≫
  (ShortComplex.homologyFunctor D).mapIso (mappedLowShortIso K h P F j hj) ≪≫
  ((HomologicalComplex.homologyFunctorIso' D (ComplexShape.down ℕ)
    (j+1) j (j-1) (by simp) (by cases j <;> simp)).app _).symm

def derivedIso [HasProjectiveResolutions C]
    (hproj : ∀ n ≤ h+1, Projective (K.X n))
    (hexact : ∀ n, n < h → K.ExactAt (n+1))
    (hzero : (ShortComplex.mk (K.d 1 0) ε hε).Exact) [Epi ε]
    (j : ℕ) (hj : j ≤ h) :
    (F.leftDerived j).obj Z ≅ ((F.mapHomologicalComplex _).obj K).homology j :=
  (resolution K h P ε hε hproj hexact hzero).isoLeftDerivedObj F j ≪≫
    mappedHomologyIso K h P F j hj

end CoboundaryExpanders.PartialResolution

namespace CoboundaryExpanders.CoinvariantHomology
open CategoryTheory.MonoidalCategory
variable (k G : Type) [CommRing k] [Group G]

def trivialTensorIso : (Rep.coinvariantsTensor k G).obj (Rep.trivial k G k) ≅
    Rep.coinvariantsFunctor k G :=
  Functor.isoWhiskerRight (leftUnitorNatIso (Rep k G)) (Rep.coinvariantsFunctor k G) ≪≫
    Functor.leftUnitor _

variable (K : ChainComplex (Rep k G) ℕ)

def coinvariantChainsIso : K.coinvariantsTensorObj (Rep.trivial k G k) ≅
    ((Rep.coinvariantsFunctor k G).mapHomologicalComplex _).obj K :=
  (NatIso.mapHomologicalComplex (trivialTensorIso k G) _).app K

def homologyIso [DecidableEq G] (h : ℕ)
    (ε : K.X 0 ⟶ Rep.trivial k G k) (hε : K.d 1 0 ≫ ε = 0)
    (hproj : ∀ n ≤ h+1, Projective (K.X n))
    (hexact : ∀ n, n < h → K.ExactAt (n+1))
    (hzero : (ShortComplex.mk (K.d 1 0) ε hε).Exact) [Epi ε]
    (j : ℕ) (hj : j ≤ h) :
    groupHomology (Rep.trivial k G k) j ≅
      (((Rep.coinvariantsFunctor k G).mapHomologicalComplex _).obj K).homology j :=
  groupHomologyIsoTor _ j ≪≫
    PartialResolution.derivedIso K h (projectiveResolution (kernel (K.d (h+1) h)))
      ε hε ((Rep.coinvariantsTensor k G).obj (Rep.trivial k G k))
        hproj hexact hzero j hj ≪≫
    (HomologicalComplex.homologyFunctor _ _ j).mapIso (coinvariantChainsIso k G K)

end CoboundaryExpanders.CoinvariantHomology

namespace CoboundaryExpanders.TypedCosetFaces
open CategoryTheory
open InfiniteChains
variable {G I : Type} [Group G] [DecidableEq G] [DecidableEq I] [Nonempty I]
  (H : I → Subgroup G)

theorem groupHomology_isZero_of_acyclic [∀ i, Finite (H i)]
    (hodd : ∀ i, Odd (Nat.card (H i))) (h : ℕ)
    (hexact : ∀ n, n < h → (complex H).chainComplex.ExactAt (n+1))
    (hzero : Function.Exact ((complex H).boundary 1) ((complex H).sumCoefficients 1))
    (j : ℕ) (hj : j+1 ≤ h) :
    Limits.IsZero (groupHomology (Rep.trivial k G k) (j+1)) := by
  let a : I := Classical.choice inferInstance
  let _ : Nonempty ((complex H).Face 1) :=
    ⟨baseFace H 1 ⟨{a},Set.mem_univ _,by simp⟩⟩
  let ε : ((complex H).repComplex (G := G)).X 0 ⟶ Rep.trivial k G k :=
    (complex H).augmentationRep
  let _ : Epi ε := (complex H).augmentationRep_epi
  have hε : ((complex H).repComplex (G := G)).d 1 0 ≫ ε = 0 := by
    change (complex H).boundaryRep 1 ≫ (complex H).augmentationRep = 0
    exact (complex H).augmentationRep_boundary
  have hz : (ShortComplex.mk (((complex H).repComplex (G := G)).d 1 0)
      ε hε).Exact := by
    change (ShortComplex.mk ((complex H).boundaryRep 1)
      (complex H).augmentationRep _).Exact
    exact (complex H).augmentationRep_exact hzero
  let e := CoinvariantHomology.homologyIso k G ((complex H).repComplex (G := G)) h
    ε hε
    (fun n _ => projective_chains H hodd n)
    (fun n hn => (complex H).repComplex_exactAt n (hexact n hn)) hz (j+1) hj
  exact (coinvariant_homology_isZero H j).of_iso e

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
open CategoryTheory InfiniteChains
variable (p n : ℕ) [Fact p.Prime]

abbrev infiniteCosetComplex (hn : 1 ≤ n) :=
  TypedCosetFaces.complex (uLocalGroup p n hn)

lemma uLocalGroup_odd (hn : 1 ≤ n) (hp : Odd p) (i : Fin (n+1)) :
    Odd (Nat.card (uLocalGroup p n hn i)) := by
  let f : uLocalGroup p n hn i →* localGroup p n hn i :=
    { toFun := uLocalEmbedding p n hn i
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact (localGroup_odd p n hn hp i).of_dvd_nat
    (Subgroup.card_dvd_of_injective f (uLocalEmbedding p n hn i).injective)

def OppositionAcyclic (hn : 1 ≤ n) : Prop :=
  Function.Exact ((infiniteCosetComplex p n hn).boundary 1)
    ((infiniteCosetComplex p n hn).sumCoefficients 1) ∧
  ∀ j : ℕ, 0 < j → j < n-1 → (infiniteCosetComplex p n hn).chainComplex.ExactAt j

theorem u_homology_isZero_of_opposition (hn : 2 ≤ n) (hp : Odd p)
    (hL : OppositionAcyclic p n (by omega)) (j : ℕ) (hj : 0 < j) (hjn : j < n-1) :
    Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (U p (n+1)) (ZMod 2)) j) := by
  classical
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  apply TypedCosetFaces.groupHomology_isZero_of_acyclic (uLocalGroup p n (by omega))
    (uLocalGroup_odd p n (by omega) hp) (n-2)
  · intro r hr
    exact hL.2 (r+1) (by omega) (by omega)
  · exact hL.1
  · omega

theorem gamma_isZero_of_opposition_and_proZero (hn : 2 ≤ n) (hp : Odd p)
    (hL : OppositionAcyclic p n (by omega)) (m j : ℕ)
    (hm : 1 ≤ m) (hj : 0 < j) (hjn : j < n-1)
    (hz : CongruenceCokernels.ProZero p (n-1) j)
    (hz' : CongruenceCokernels.ProZero p n j) :
    Limits.IsZero (groupHomology (Rep.trivial (ZMod 2) (Gamma p (n+1) m) (ZMod 2)) j) := by
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, n = a+2 := ⟨n-2, by omega⟩
  have hU := u_homology_isZero_of_opposition p (a+2) hn hp hL j hj hjn
  exact CongruenceCokernels.gamma_isZero_of_U_and_proZero p (a+1) m j Fact.out hp hm
    hU (by simpa using hz) (by simpa only [Nat.add_assoc] using hz')

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.KernelCosetOrbits
variable {G Q : Type} [Group G] [Group Q] (f : G →* Q) (H : Subgroup G)

def cosetMap : G ⧸ H → Q ⧸ H.map f :=
  Quotient.map f (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    exact ⟨a⁻¹*b, QuotientGroup.leftRel_apply.mp hab, by simp⟩)

@[simp] lemma cosetMap_mk (a : G) :
    cosetMap f H (QuotientGroup.mk a) = QuotientGroup.mk (f a) := rfl

lemma cosetMap_smul (k : f.ker) (a : G ⧸ H) :
    cosetMap f H (k • a) = cosetMap f H a := by
  induction a using Quotient.inductionOn with | h a =>
    change QuotientGroup.mk (f (k.val*a)) = QuotientGroup.mk (f a)
    rw [map_mul, show f k.val = 1 from k.property, one_mul]

lemma cosetMap_eq_iff (a b : G ⧸ H) :
    cosetMap f H a = cosetMap f H b ↔ MulAction.orbitRel f.ker (G ⧸ H) a b := by
  induction a using Quotient.inductionOn with | h a =>
  induction b using Quotient.inductionOn with | h b =>
  constructor
  · intro hab
    obtain ⟨h, hh, he⟩ := QuotientGroup.leftRel_apply.mp (Quotient.exact hab)
    have hk : a*h*b⁻¹ ∈ f.ker := by
      change f (a*h*b⁻¹) = 1
      rw [map_mul, map_mul, map_inv, he]
      simp
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨⟨a*h*b⁻¹, hk⟩, ?_⟩
    change QuotientGroup.mk ((a*h*b⁻¹)*b) = QuotientGroup.mk a
    simp only [inv_mul_cancel_right]
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    simpa using H.inv_mem hh
  · intro hab
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.mp hab
    rw [← hk]
    exact cosetMap_smul f H k _

def orbitMap : MulAction.orbitRel.Quotient f.ker (G ⧸ H) → Q ⧸ H.map f :=
  Quotient.lift (cosetMap f H) (fun a b hab => (cosetMap_eq_iff f H a b).mpr hab)

lemma orbitMap_bijective (hf : Function.Surjective f) : Function.Bijective (orbitMap f H) := by
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with | h a =>
    induction b using Quotient.inductionOn with | h b =>
    exact Quotient.sound ((cosetMap_eq_iff f H a b).mp hab)
  · intro q
    induction q using Quotient.inductionOn with | h q =>
      obtain ⟨g, rfl⟩ := hf q
      exact ⟨Quotient.mk _ (QuotientGroup.mk g), rfl⟩

def orbitEquiv (hf : Function.Surjective f) :
    MulAction.orbitRel.Quotient f.ker (G ⧸ H) ≃ Q ⧸ H.map f :=
  Equiv.ofBijective (orbitMap f H) (orbitMap_bijective f H hf)

@[simp] lemma orbitEquiv_mk (hf : Function.Surjective f) (g : G) :
    orbitEquiv f H hf (Quotient.mk _ (QuotientGroup.mk g)) = QuotientGroup.mk (f g) := rfl

theorem stabilizer_eq_bot (hH : Set.InjOn f H) (a : G ⧸ H) :
    MulAction.stabilizer f.ker a = ⊥ := by
  apply le_antisymm _ bot_le
  intro k hk
  induction a using Quotient.inductionOn with | h a =>
    have hfix : QuotientGroup.mk (k.val*a) = (QuotientGroup.mk a : G ⧸ H) := hk
    have hmem : a⁻¹*k.val*a ∈ H := by
      have ht := QuotientGroup.leftRel_apply.mp (Quotient.exact hfix.symm)
      simpa [mul_assoc] using ht
    have he : f (a⁻¹*k.val*a) = f 1 := by
      simp only [map_mul, map_inv, show f k.val = 1 from k.property, map_one]
      simp
    have hx := hH hmem H.one_mem he
    have hk1 : k.val = 1 := by
      have hh := congrArg (fun z => a*z*a⁻¹) hx
      simpa [mul_assoc] using hh
    exact Subtype.ext hk1

def project {J : Subgroup G} (h : H ≤ J) : G ⧸ H → G ⧸ J :=
  Quotient.map id (fun _ _ hab => QuotientGroup.leftRel_apply.mpr
    (h (QuotientGroup.leftRel_apply.mp hab)))

lemma cosetMap_project {J : Subgroup G} (h : H ≤ J) (a : G ⧸ H) :
    cosetMap f J (project H h a) =
      project (H.map f) (Subgroup.map_mono h) (cosetMap f H a) := by
  induction a using Quotient.inductionOn with | h a => rfl

end CoboundaryExpanders.KernelCosetOrbits

namespace CoboundaryExpanders.TypedCosetFaces

section
open InfiniteChains
attribute [local instance 1100] InfiniteChains.Complex.faceMulAction
variable {G Q I : Type} [Group G] [Group Q] [DecidableEq I]
variable (H : I → Subgroup G) (f : G →* Q)
abbrev imageGroups : I → Subgroup Q := fun i => (H i).map f

def vertexMap : Vertex H → Vertex (imageGroups H f) :=
  fun x => ⟨x.1, KernelCosetOrbits.cosetMap f (H x.1) x.2⟩

omit [DecidableEq I] in
@[simp] lemma vertexMap_vertex (g : G) (i : I) :
    vertexMap H f (vertex H g i) = vertex (imageGroups H f) (f g) i := rfl

omit [DecidableEq I] in
@[simp] lemma image_face (g : G) (A : Finset I) :
    (face H g A).image (vertexMap H f) = face (imageGroups H f) (f g) A := by
  simp [face, Finset.image_image, Function.comp_def]

omit [DecidableEq I] in
lemma vertexMap_injOn (s : Finset (Vertex H)) (hs : IsFace H s) :
    Set.InjOn (vertexMap H f) s := by
  obtain ⟨g,A,rfl⟩ := hs
  intro x hx y hy hxy
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hy
  have he : i=j := congrArg Sigma.fst hxy
  subst j
  rfl

def quotientFaceMap (n : ℕ) (s : (complex H).Face n) :
    (complex (imageGroups H f)).Face n :=
  ⟨s.val.image (vertexMap H f), by
    obtain ⟨g,A,hA⟩ := s.property.1
    rw [← hA, image_face]
    exact ⟨f g,A,rfl⟩,
    (Finset.card_image_of_injOn (vertexMap_injOn H f s.val s.property.1)).trans s.property.2⟩

@[simp] lemma quotientFaceMap_graded (n : ℕ) (A : Types (I := I) n) (g : G) :
    quotientFaceMap H f n (gradedFace H n ⟨A,QuotientGroup.mk g⟩) =
      gradedFace (imageGroups H f) n ⟨A,QuotientGroup.mk (f g)⟩ := by
  apply Subtype.ext
  exact image_face H f g A.val

lemma quotientFaceMap_surjective (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (quotientFaceMap H f n) := by
  intro s
  obtain ⟨⟨A,q⟩,rfl⟩ := (gradedFace_bijective (imageGroups H f) n).2 s
  induction q using Quotient.inductionOn with | h q =>
    obtain ⟨g,rfl⟩ := hf q
    exact ⟨gradedFace H n ⟨A,QuotientGroup.mk g⟩,quotientFaceMap_graded H f n A g⟩

instance kernelInvariant : Fact ((complex H).Invariant (G := f.ker)) := ⟨by
  rintro k s ⟨g,A,rfl⟩
  change (face H g A).map (MulAction.toPerm (k.val)).toEmbedding ∈ (complex H).faces
  rw [map_face]
  exact ⟨k.val*g,A,rfl⟩⟩

lemma kernel_smul_graded (n : ℕ) (k : f.ker) (A : Types (I := I) n) (g : G) :
    k • gradedFace H n ⟨A,QuotientGroup.mk g⟩ =
      gradedFace H n ⟨A,QuotientGroup.mk (k.val*g)⟩ := by
  apply Subtype.ext
  exact map_face H k.val g A.val

lemma quotientFaceMap_invariant (n : ℕ) (k : f.ker) (s : (complex H).Face n) :
    quotientFaceMap H f n (k • s) = quotientFaceMap H f n s := by
  obtain ⟨⟨A,q⟩,rfl⟩ := (gradedFace_bijective H n).2 s
  induction q using Quotient.inductionOn with | h g =>
  rw [kernel_smul_graded, quotientFaceMap_graded, quotientFaceMap_graded]
  rw [map_mul, show f k.val = 1 from k.property, one_mul]

lemma quotientFaceMap_eq_iff
    (hinter : ∀ A : Finset I, (stabilizer H A).map f = stabilizer (imageGroups H f) A)
    (n : ℕ) (s t : (complex H).Face n) :
    quotientFaceMap H f n s = quotientFaceMap H f n t ↔
      MulAction.orbitRel f.ker ((complex H).Face n) s t := by
  constructor
  · intro he
    obtain ⟨⟨A,q⟩,rfl⟩ := (gradedFace_bijective H n).2 s
    obtain ⟨⟨B,r⟩,rfl⟩ := (gradedFace_bijective H n).2 t
    induction q using Quotient.inductionOn with | h g =>
    induction r using Quotient.inductionOn with | h h =>
    rw [quotientFaceMap_graded, quotientFaceMap_graded] at he
    have he' := (gradedFace_bijective (imageGroups H f) n).1 he
    have hAB : A = B := congrArg Sigma.fst he'
    subst B
    have hgh : (QuotientGroup.mk (f g) : Q ⧸ stabilizer (imageGroups H f) A.val) =
        QuotientGroup.mk (f h) := eq_of_heq (Sigma.mk.inj_iff.mp he').2
    have hm : (f g)⁻¹ * f h ∈ (stabilizer H A.val).map f := by
      rw [hinter]
      exact QuotientGroup.leftRel_apply.mp (Quotient.exact hgh)
    have hem : KernelCosetOrbits.cosetMap f (stabilizer H A.val) (QuotientGroup.mk g) =
        KernelCosetOrbits.cosetMap f (stabilizer H A.val) (QuotientGroup.mk h) :=
      Quotient.sound (QuotientGroup.leftRel_apply.mpr hm)
    obtain ⟨k,hk⟩ := MulAction.mem_orbit_iff.mp
      ((KernelCosetOrbits.cosetMap_eq_iff f (stabilizer H A.val) _ _).mp hem)
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨k,?_⟩
    rw [kernel_smul_graded]
    exact congrArg (fun c => gradedFace H n ⟨A,c⟩) hk
  · rintro ⟨k,hk⟩
    rw [← hk]
    exact quotientFaceMap_invariant H f n k t

end

section
open InfiniteChains CategoryTheory
attribute [local instance 1100] InfiniteChains.Complex.faceMulAction
variable {G Q I : Type} [Group G] [Group Q] [DecidableEq I]
variable (H : I → Subgroup G) (f : G →* Q)
variable (hf : Function.Surjective f)
variable (hinter : ∀ A : Finset I, (stabilizer H A).map f = stabilizer (imageGroups H f) A)

abbrev KernelCoinvariantChains (n : ℕ) := ((complex H).chainsRep (G := f.ker) n).ρ.Coinvariants

def quotientChainMap (n : ℕ) : (complex H).Chains n →ₗ[k] (complex (imageGroups H f)).Chains n :=
  Finsupp.lmapDomain k k (quotientFaceMap H f n)

@[simp] lemma quotientChainMap_single (n : ℕ) (s : (complex H).Face n) (r : k) :
    quotientChainMap H f n (Finsupp.single s r) = Finsupp.single (quotientFaceMap H f n s) r :=
  Finsupp.mapDomain_single

lemma quotientChainMap_invariant (n : ℕ) (g : f.ker) :
    (quotientChainMap H f n).comp (((complex H).chainsRep (G := f.ker) n).ρ g) =
      quotientChainMap H f n := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp [FinsuppPermutation.ρ_single, quotientFaceMap_invariant]

def toQuotient (n : ℕ) : KernelCoinvariantChains H f n →ₗ[k] (complex (imageGroups H f)).Chains n :=
  Representation.Coinvariants.lift _ (quotientChainMap H f n) (quotientChainMap_invariant H f n)

@[simp] lemma toQuotient_single (n : ℕ) (s : (complex H).Face n) (r : k) :
    toQuotient H f n (Representation.Coinvariants.mk
      (FinsuppPermutation.ρ k f.ker ((complex H).Face n)) (Finsupp.single s r)) =
      Finsupp.single (quotientFaceMap H f n s) r := quotientChainMap_single H f n s r

def liftFace (n : ℕ) (s : (complex (imageGroups H f)).Face n) : (complex H).Face n :=
  Classical.choose (quotientFaceMap_surjective H f hf n s)

@[simp] lemma quotient_liftFace (n : ℕ) (s : (complex (imageGroups H f)).Face n) :
    quotientFaceMap H f n (liftFace H f hf n s) = s :=
  Classical.choose_spec (quotientFaceMap_surjective H f hf n s)

def fromQuotient (n : ℕ) : (complex (imageGroups H f)).Chains n →ₗ[k] KernelCoinvariantChains H f n :=
  Finsupp.linearCombination k (fun s => Representation.Coinvariants.mk
    (FinsuppPermutation.ρ k f.ker ((complex H).Face n)) (Finsupp.single (liftFace H f hf n s) 1))

@[simp] lemma fromQuotient_single (n : ℕ) (s : (complex (imageGroups H f)).Face n) (r : k) :
    fromQuotient H f hf n (Finsupp.single s r) = Representation.Coinvariants.mk
      (FinsuppPermutation.ρ k f.ker ((complex H).Face n)) (Finsupp.single (liftFace H f hf n s) r) := by
  simp [fromQuotient, ← map_smul]

include hinter in
lemma fromQuotient_toQuotient (n : ℕ) :
    (fromQuotient H f hf n).comp (toQuotient H f n) = LinearMap.id := by
  apply Representation.Coinvariants.hom_ext
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  change fromQuotient H f hf n (quotientChainMap H f n (Finsupp.single s r)) =
    Representation.Coinvariants.mk (FinsuppPermutation.ρ k f.ker ((complex H).Face n))
      (Finsupp.single s r)
  rw [quotientChainMap_single, fromQuotient_single]
  obtain ⟨g,hg⟩ := MulAction.mem_orbit_iff.mp ((quotientFaceMap_eq_iff H f hinter n _ _).mp
    (quotient_liftFace H f hf n (quotientFaceMap H f n s)))
  have hh := Representation.Coinvariants.mk_self_apply
    (FinsuppPermutation.ρ k f.ker ((complex H).Face n)) g (Finsupp.single s r)
  simpa only [FinsuppPermutation.ρ_single, hg] using hh

lemma toQuotient_fromQuotient (n : ℕ) :
    (toQuotient H f n).comp (fromQuotient H f hf n) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  simp

def quotientChainsEquiv (n : ℕ) :
    KernelCoinvariantChains H f n ≃ₗ[k] (complex (imageGroups H f)).Chains n :=
  LinearEquiv.ofLinearMap (toQuotient H f n) (fromQuotient H f hf n)
    (toQuotient_fromQuotient H f hf n) (fromQuotient_toQuotient H f hf hinter n)

lemma image_erase_vertex (g : G) (A : Finset I) (i : I) :
    ((face H g A).erase (vertex H g i)).image (vertexMap H f) =
      (face (imageGroups H f) (f g) A).erase (vertex (imageGroups H f) (f g) i) := by
  rw [show (face H g A).erase (vertex H g i) = face H g (A.erase i) from
    (Finset.image_erase (vertex_injective H g) A i).symm]
  rw [image_face]
  exact Finset.image_erase (vertex_injective (imageGroups H f) (f g)) A i

lemma quotientChainMap_boundary (n : ℕ) :
    (quotientChainMap H f n).comp ((complex H).boundary n) =
      (complex (imageGroups H f)).boundary n ∘ₗ quotientChainMap H f (n+1) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro r
  apply (complex (imageGroups H f)).embed_injective n
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, CoboundaryExpanders.InfiniteChains.Complex.boundary_single,
    map_sum, quotientChainMap_single, CoboundaryExpanders.InfiniteChains.Complex.embed_single]
  change (∑ v : ↥s.val, Finsupp.single ((s.val.erase v.val).image (vertexMap H f)) r) =
    ∑ v : ↥(s.val.image (vertexMap H f)), Finsupp.single
      ((s.val.image (vertexMap H f)).erase v.val) r
  rw [Finset.sum_coe_sort s.val
    (fun v => Finsupp.single ((s.val.erase v).image (vertexMap H f)) r),
    Finset.sum_coe_sort (s.val.image (vertexMap H f))
    (fun v => Finsupp.single ((s.val.image (vertexMap H f)).erase v) r)]
  obtain ⟨g,A,hA⟩ := s.property.1
  rw [← hA, image_face]
  change (∑ v ∈ A.image (vertex H g), _) = ∑ v ∈ A.image (vertex (imageGroups H f) (f g)), _
  rw [Finset.sum_image, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [image_erase_vertex]
  · exact fun _ _ _ _ he => vertex_injective (imageGroups H f) (f g) he
  · exact fun _ _ _ _ he => vertex_injective H g he

def kernelCoinvariantBoundary (n : ℕ) :
    KernelCoinvariantChains H f (n+1) →ₗ[k] KernelCoinvariantChains H f n :=
  Representation.Coinvariants.map _ _ ((complex H).boundaryRep (G := f.ker) n).hom

lemma toQuotient_boundary (n : ℕ) :
    (toQuotient H f n).comp (kernelCoinvariantBoundary H f n) =
      (complex (imageGroups H f)).boundary n ∘ₗ toQuotient H f (n+1) := by
  apply Representation.Coinvariants.hom_ext
  exact quotientChainMap_boundary H f n

abbrev kernelCoinvariantComplex : ChainComplex (ModuleCat k) ℕ :=
  ((Rep.coinvariantsFunctor k f.ker).mapHomologicalComplex _).obj
    ((complex H).repComplex (G := f.ker))

def kernelCoinvariantQuotientIso :
    kernelCoinvariantComplex H f ≅ (complex (imageGroups H f)).chainComplex :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (quotientChainsEquiv H f hf hinter (j+1)).toModuleIso) (by
      intro i j hij
      have he : i=j+1 := by simpa using hij.symm
      subst i
      apply ModuleCat.hom_ext
      change ((complex (imageGroups H f)).chainComplex.d (j+1) j).hom.comp
        (toQuotient H f (j+2)) = _
      rw [CoboundaryExpanders.InfiniteChains.Complex.chainComplex_d]
      change (complex (imageGroups H f)).boundary (j+1) ∘ₗ toQuotient H f (j+2) =
        (toQuotient H f (j+1)).comp
          (Representation.Coinvariants.map _ _ (((complex H).repComplex (G := f.ker)).d (j+1) j).hom)
      rw [CoboundaryExpanders.InfiniteChains.Complex.repComplex_d]
      exact (toQuotient_boundary H f (j+1)).symm)

end

open InfiniteChains CategoryTheory
attribute [local instance 1100] InfiniteChains.Complex.faceMulAction
variable {G Q I : Type} [Group G] [Group Q] [DecidableEq I]
variable (H : I → Subgroup G) (f : G →* Q)

theorem kernel_face_stabilizer (hlocal : ∀ i, Set.InjOn f (H i))
    (n : ℕ) (s : (complex H).Face (n+1)) :
    MulAction.stabilizer f.ker s = ⊥ := by
  obtain ⟨⟨A,q⟩,rfl⟩ := (gradedFace_bijective H (n+1)).2 s
  induction q using Quotient.inductionOn with | h g =>
  obtain ⟨i,hi⟩ : A.val.Nonempty := Finset.card_pos.mp (by rw [A.property]; omega)
  have hi' : Set.InjOn f (stabilizer H A.val) := by
    intro a ha b hb hab
    exact hlocal i ((mem_stabilizer H A.val a).mp ha i hi)
      ((mem_stabilizer H A.val b).mp hb i hi) hab
  apply le_antisymm _ bot_le
  intro x hx
  have hfix : x • gradedFace H (n+1) ⟨A,QuotientGroup.mk g⟩ =
      gradedFace H (n+1) ⟨A,QuotientGroup.mk g⟩ := hx
  rw [kernel_smul_graded] at hfix
  have he := (gradedFace_bijective H (n+1)).1 hfix
  have hekk : x • (QuotientGroup.mk g : G ⧸ stabilizer H A.val) = QuotientGroup.mk g :=
    eq_of_heq (Sigma.mk.inj_iff.mp he).2
  have hx' : x ∈ MulAction.stabilizer f.ker (QuotientGroup.mk g : G ⧸ stabilizer H A.val) := hekk
  rw [KernelCosetOrbits.stabilizer_eq_bot f (stabilizer H A.val) hi'] at hx'
  exact hx'

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.PermutationProjectivity
open CategoryTheory
variable {k G X : Type} [Field k] [Group G] [MulAction G X]
abbrev Orbit := MulAction.orbitRel.Quotient G X
def orbitStabilizer : Orbit (G := G) (X := X) → Subgroup G :=
  fun q => MulAction.stabilizer G q.out

def orbitBasis : CosetSums.Basis (orbitStabilizer (G := G) (X := X)) ≃ X :=
  (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X).symm

lemma orbitBasis_apply (x : CosetSums.Basis (orbitStabilizer (G := G) (X := X))) :
    orbitBasis x = MulAction.ofQuotientStabilizer G x.1.out x.2 := rfl

lemma orbitBasis_smul (g : G) (x : CosetSums.Basis (orbitStabilizer (G := G) (X := X))) :
    orbitBasis (g • x) = g • orbitBasis x := by
  rw [orbitBasis_apply, orbitBasis_apply]
  exact MulAction.ofQuotientStabilizer_smul G x.1.out g x.2

def chainsIso :
    CosetSums.permutation (k := k) (orbitStabilizer (G := G) (X := X)) ≅
      FinsuppPermutation.rep k G X :=
  FinsuppPermutation.coeffIso _ _ _ ≪≫ Rep.mkIso {
    (Finsupp.domLCongr orbitBasis : _ ≃ₗ[k] _) with
    isIntertwining' := by
      intro g
      apply Finsupp.lhom_ext'
      intro x
      apply LinearMap.ext
      intro r
      change (Finsupp.domLCongr orbitBasis : _ ≃ₗ[k] _)
        (FinsuppPermutation.ρ k G _ g (Finsupp.single x r)) =
        FinsuppPermutation.ρ k G _ g
          ((Finsupp.domLCongr orbitBasis : _ ≃ₗ[k] _) (Finsupp.single x r))
      simp only [FinsuppPermutation.ρ_single, Finsupp.domLCongr_single]
      exact congrArg (fun s => Finsupp.single s r) (orbitBasis_smul g x) }

theorem projective_of_odd [∀ x : X, Finite (MulAction.stabilizer G x)]
    (hodd : ∀ x : X, Odd (Nat.card (MulAction.stabilizer G x))) :
    Projective (FinsuppPermutation.rep (ZMod 2) G X) := by
  let _ : ∀ q : Orbit (G := G) (X := X), Finite (orbitStabilizer q) :=
    fun q => (inferInstance : Finite (MulAction.stabilizer G q.out))
  have hP := CosetSums.projective_of_odd_order
    (orbitStabilizer (G := G) (X := X)) (fun q => hodd q.out)
  exact Projective.of_iso (chainsIso (k := ZMod 2) (G := G) (X := X)) hP

theorem projective_of_free (hfree : ∀ x : X, MulAction.stabilizer G x = ⊥) :
    Projective (FinsuppPermutation.rep (ZMod 2) G X) := by
  let _ : ∀ x : X, Finite (MulAction.stabilizer G x) := fun x => by
    rw [hfree x]
    infer_instance
  apply projective_of_odd
  intro x
  rw [hfree x]
  simp

end CoboundaryExpanders.PermutationProjectivity

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains CategoryTheory
attribute [local instance 1100] InfiniteChains.Complex.faceMulAction
variable {G Q I : Type} [Group G] [Group Q] [DecidableEq I] [Nonempty I]
variable (H : I → Subgroup G) (f : G →* Q)

omit [Nonempty I] in
lemma kernel_projective_chains (hlocal : ∀ i, Set.InjOn f (H i)) (n : ℕ) :
    Projective (((complex H).repComplex (G := f.ker)).X n) :=
  PermutationProjectivity.projective_of_free (kernel_face_stabilizer H f hlocal n)

def kernelHomologyQuotientIso (hf : Function.Surjective f)
    (hinter : ∀ A : Finset I, (stabilizer H A).map f = stabilizer (imageGroups H f) A)
    (hlocal : ∀ i, Set.InjOn f (H i)) (h : ℕ)
    (hexact : ∀ n, n < h → (complex H).chainComplex.ExactAt (n+1))
    (hzero : Function.Exact ((complex H).boundary 1) ((complex H).sumCoefficients 1))
    (j : ℕ) (hj : j ≤ h) :
    groupHomology (Rep.trivial k f.ker k) j ≅ (complex (imageGroups H f)).chainComplex.homology j := by
  classical
  let a : I := Classical.choice inferInstance
  let _ : Nonempty ((complex H).Face 1) :=
    ⟨⟨face H 1 {a}, ⟨1,{a},rfl⟩, by simp⟩⟩
  let ε : ((complex H).repComplex (G := f.ker)).X 0 ⟶ Rep.trivial k f.ker k :=
    (complex H).augmentationRep
  let _ : Epi ε := (complex H).augmentationRep_epi
  have hε : ((complex H).repComplex (G := f.ker)).d 1 0 ≫ ε = 0 := by
    change (complex H).boundaryRep 1 ≫ (complex H).augmentationRep = 0
    exact (complex H).augmentationRep_boundary
  have hz : (ShortComplex.mk (((complex H).repComplex (G := f.ker)).d 1 0)
      ε hε).Exact := by
    change (ShortComplex.mk ((complex H).boundaryRep 1)
      (complex H).augmentationRep _).Exact
    exact (complex H).augmentationRep_exact hzero
  exact CoinvariantHomology.homologyIso k f.ker ((complex H).repComplex (G := f.ker)) h
    ε hε
    (fun n _ => kernel_projective_chains H f hlocal n)
    (fun n hn => (complex H).repComplex_exactAt n (hexact n hn)) hz j hj ≪≫
      (HomologicalComplex.homologyFunctor _ _ j).mapIso (kernelCoinvariantQuotientIso H f hf hinter)

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
open CategoryTheory TypedCosetFaces
variable (p n : ℕ) [Fact p.Prime]

abbrev quotientProjection (m : ℕ) : U p (n+1) →* Gquot p (n+1) m :=
  QuotientGroup.mk' (uReduction p (n+1) m).ker

lemma quotientProjection_cross_injective (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (i j : Fin (n+1)) (a b : U p (n+1))
    (ha : a ∈ uLocalGroup p n hn i) (hb : b ∈ uLocalGroup p n hn j)
    (he : quotientProjection p n m a = quotientProjection p n m b) : a = b := by
  apply Subtype.ext
  apply localGroups_reduction_injective p n hn hm i j ⟨a.val,ha⟩ ⟨b.val,hb⟩
  exact congrArg (fun g : Gquot p (n+1) m =>
    (QuotientGroup.quotientKerEquivRange (uReduction p (n+1) m) g).val) he

lemma quotientProjection_intersections (hn : 1 ≤ n) {m : ℕ} (hm : 2 ≤ m)
    (A : Finset (Fin (n+1))) :
    (stabilizer (uLocalGroup p n hn) A).map (quotientProjection p n m) =
      stabilizer (reducedLocalGroup p n hn m) A := by
  classical
  apply le_antisymm
  · rintro g hg
    obtain ⟨a,ha,rfl⟩ := Subgroup.mem_map.mp hg
    apply (mem_stabilizer _ _ _).mpr
    intro i hi
    exact Subgroup.mem_map.mpr ⟨a, ((mem_stabilizer _ _ _).mp ha) i hi,rfl⟩
  · intro g hg
    by_cases hA : A.Nonempty
    · obtain ⟨i,hi⟩ := hA
      obtain ⟨a,ha,he⟩ := Subgroup.mem_map.mp (((mem_stabilizer _ _ _).mp hg) i hi)
      refine Subgroup.mem_map.mpr ⟨a, (mem_stabilizer _ _ _).mpr ?_,he⟩
      intro j hj
      obtain ⟨b,hb,hbe⟩ := Subgroup.mem_map.mp (((mem_stabilizer _ _ _).mp hg) j hj)
      have hab := quotientProjection_cross_injective p n hn hm i j a b ha hb (he.trans hbe.symm)
      exact hab.symm ▸ hb
    · have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
      subst A
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (uReduction p (n+1) m).ker g
      exact Subgroup.mem_map.mpr ⟨a,by simp,rfl⟩

abbrev quotientTypedComplex (hn : 1 ≤ n) (m : ℕ) :=
  TypedCosetFaces.complex (reducedLocalGroup p n hn m)

def gammaQuotientKernelEquiv (m : ℕ) (hm : 1 ≤ m) :
    Gamma p (n+1) m ≃* (quotientProjection p n m).ker :=
  (QuotientVanishing.gammaInU p (n+1) m hm).trans
    (MulEquiv.subgroupCongr (QuotientGroup.ker_mk' _).symm)

def matrixKernelHomologyIso (hn : 2 ≤ n) (m : ℕ) (hm : 2 ≤ m)
    (hL : OppositionAcyclic p n (by omega)) (j : ℕ) (hj : j < n-1) :
    groupHomology (Rep.trivial (ZMod 2) (quotientProjection p n m).ker (ZMod 2)) j ≅
      (quotientTypedComplex p n (by omega) m).chainComplex.homology j := by
  classical
  apply TypedCosetFaces.kernelHomologyQuotientIso (uLocalGroup p n (by omega))
    (quotientProjection p n m) (QuotientGroup.mk'_surjective _)
    (quotientProjection_intersections p n (by omega) hm)
    (fun i a ha b hb he => quotientProjection_cross_injective p n (by omega) hm i i a b ha hb he)
    (n-2)
  · intro r hr
    exact hL.2 (r+1) (by omega) (by omega)
  · exact hL.1
  · omega

theorem quotientTyped_homology_isZero (hn : 2 ≤ n) (hp : Odd p)
    (hL : OppositionAcyclic p n (by omega)) (m j : ℕ)
    (hm : 2 ≤ m) (hj : 0 < j) (hjn : j < n-1)
    (hz : CongruenceCokernels.ProZero p (n-1) j)
    (hz' : CongruenceCokernels.ProZero p n j) :
    Limits.IsZero ((quotientTypedComplex p n (by omega) m).chainComplex.homology j) := by
  classical
  have hΓ := gamma_isZero_of_opposition_and_proZero p n hn hp hL m j (by omega) hj hjn hz hz'
  let e := gammaQuotientKernelEquiv p n m (by omega)
  let f := Actions.induced (k := ZMod 2) e.toMonoidHom j
  have : Epi f := (ModuleCat.epi_iff_surjective f).mpr
    (Actions.induced_equiv_surjective (k := ZMod 2) e j)
  have hk := Limits.IsZero.of_epi f hΓ
  exact hk.of_iso (matrixKernelHomologyIso p n hn m hm hL j hjn).symm

end CoboundaryExpanders.Construction

end

end OAI
