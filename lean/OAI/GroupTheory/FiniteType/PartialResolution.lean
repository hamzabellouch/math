import Mathlib
import OAI.GroupTheory.FiniteType.ProductFiniteResolution

namespace OAI

noncomputable section
namespace PartialResolution
open CategoryTheory CategoryTheory.Limits
open ProductFiniteResolution
variable {k G : Type} [CommRing k] [Group G]
variable (C : ChainComplex (Rep k G) ℕ) (N : ℕ)
  (P : ProjectiveResolution (kerRep (C.d N (N-1))))

def obj (i : ℕ) : Rep k G := if i ≤ N then C.X i else P.complex.X (i-(N+1))

def headIso (i : ℕ) (h : i ≤ N) : obj C N P i ≅ C.X i :=
  eqToIso (by simp [obj,h])

def tailIso (i : ℕ) (h : N < i) : obj C N P i ≅ P.complex.X (i-(N+1)) :=
  eqToIso (by simp [obj,Nat.not_le.mpr h])

def seam : obj C N P (N+1) ⟶ obj C N P N :=
  (tailIso C N P (N+1) (by omega)).hom ≫
    eqToHom (by simp) ≫ P.π.f 0 ≫ kerι (C.d N (N-1)) ≫ (headIso C N P N le_rfl).inv

def d (i : ℕ) : obj C N P (i+1) ⟶ obj C N P i :=
  if h : i < N then
    (headIso C N P (i+1) (by omega)).hom ≫ C.d (i+1) i ≫ (headIso C N P i (by omega)).inv
  else if e : i = N then by subst i; exact seam C N P
  else (tailIso C N P (i+1) (by omega)).hom ≫
    P.complex.d ((i+1)-(N+1)) (i-(N+1)) ≫ (tailIso C N P i (by omega)).inv

lemma d_head (i : ℕ) (h : i < N) : d C N P i =
    (headIso C N P (i+1) (by omega)).hom ≫ C.d (i+1) i ≫ (headIso C N P i (by omega)).inv := by
  simp [d,h]

lemma d_seam : d C N P N = seam C N P := by simp [d]

lemma d_tail (i : ℕ) (h : N < i) : d C N P i =
    (tailIso C N P (i+1) (by omega)).hom ≫
      P.complex.d ((i+1)-(N+1)) (i-(N+1)) ≫ (tailIso C N P i h).inv := by
  simp [d,show ¬i<N by omega,show i≠N by omega]

lemma d_comp (hN : 0 < N) (i : ℕ) : d C N P (i+1) ≫ d C N P i = 0 := by
  by_cases h : i+1 < N
  · rw [d_head C N P (i+1) h,d_head C N P i (by omega)]
    simp only [Category.assoc,Iso.inv_hom_id_assoc,HomologicalComplex.d_comp_d_assoc,zero_comp,comp_zero]
  · by_cases e : i+1 = N
    · subst N
      rw [d_seam,d_head C (i+1) P i (by omega)]
      simp [seam,Category.assoc]
      erw [Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, kerι_comp_assoc,
        zero_comp, comp_zero]
    · by_cases e' : i = N
      · subst i
        rw [d_tail C N P (N+1) (by omega),d_seam]
        simp [seam,Category.assoc]
        rw [show N+1+1-(N+1)=1 by omega]
        erw [P.complex_d_comp_π_f_zero_assoc,zero_comp]
      · rw [d_tail C N P (i+1) (by omega),d_tail C N P i (by omega)]
        simp only [Category.assoc,Iso.inv_hom_id_assoc,HomologicalComplex.d_comp_d_assoc,zero_comp,comp_zero]

def complex (hN : 0 < N) : ChainComplex (Rep k G) ℕ :=
  ChainComplex.of (obj C N P) (d C N P) (d_comp C N P hN)

@[simp] lemma complex_X (hN : 0 < N) (i : ℕ) : (complex C N P hN).X i = obj C N P i := rfl
@[simp] lemma complex_d (hN : 0 < N) (i : ℕ) : (complex C N P hN).d (i+1) i = d C N P i := by
  simp [complex]

lemma exact_seam :
    (ShortComplex.mk (P.π.f 0 ≫ kerι (C.d N (N-1))) (C.d N (N-1))
      (by erw [Category.assoc, kerι_comp, comp_zero])).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y,hy⟩ := ((Rep.epi_iff_surjective (P.π.f 0)).mp inferInstance) ⟨x,hx⟩
  exact ⟨y,congrArg Subtype.val hy⟩

lemma exact_after_seam :
    (ShortComplex.mk (P.complex.d 1 0) (P.π.f 0 ≫ kerι (C.d N (N-1)))
      (by erw [P.complex_d_comp_π_f_zero_assoc, zero_comp])).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : (P.π.f 0).hom x = 0 := by
    apply Subtype.ext
    exact hx
  exact (ShortComplex.moduleCat_exact_iff _).mp
    (P.exact₀.map (forget₂ (Rep k G) (ModuleCat k))) x hx'

def startIso : obj C N P (N+1) ≅ P.complex.X 0 :=
  tailIso C N P (N+1) (by omega) ≪≫ eqToIso (by simp)

def nextIso : obj C N P (N+1+1) ≅ P.complex.X 1 :=
  tailIso C N P (N+1+1) (by omega) ≪≫ eqToIso (by congr 1; omega)

lemma exactAt_succ (hN : 0 < N)
    (hex : ∀ i, 0 < i → i < N → C.ExactAt i) (i : ℕ) :
    (complex C N P hN).ExactAt (i+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (i+1+1) (i+1) i (by simp) (by simp)]
  simp only [HomologicalComplex.sc',HomologicalComplex.shortComplexFunctor',complex,ChainComplex.of_d]
  change (ShortComplex.mk (d C N P (i+1)) (d C N P i) (d_comp C N P hN i)).Exact
  by_cases h : i+1 < N
  · have he := (HomologicalComplex.exactAt_iff' C (i+1+1) (i+1) i (by simp) (by simp)).mp
      (hex (i+1) (by omega) h)
    apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
      (headIso C N P (i+1+1) (by omega)) (headIso C N P (i+1) (by omega))
      (headIso C N P i (by omega)) ?_ ?_)).mpr he
    · simp [d_head C N P (i+1) h,Category.assoc]
      erw [Iso.inv_hom_id, Category.comp_id]
      rfl
    · simp [d_head C N P i (by omega : i<N),Category.assoc]
      erw [Iso.inv_hom_id, Category.comp_id]
      rfl
  · by_cases e : i+1 = N
    · subst N
      apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
        (startIso C (i+1) P) (headIso C (i+1) P (i+1) le_rfl)
        (headIso C (i+1) P i (by omega)) ?_ ?_)).mpr (exact_seam C (i+1) P)
      · simp [d_seam,seam,startIso,Category.assoc]
        erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      · simp [d_head C (i+1) P i (by omega),Category.assoc]
    · by_cases e' : i=N
      · subst i
        apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
          (nextIso C N P) (startIso C N P) (headIso C N P N le_rfl) ?_ ?_)).mpr
          (exact_after_seam C N P)
        · simp [d_tail C N P (N+1) (by omega),nextIso,startIso,Category.assoc]
        · simp [d_seam,seam,startIso,Category.assoc]
          erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
      · have ht : N < i := by omega
        have hp : P.complex.ExactAt (i+1-(N+1)) := by
          have eq : i+1-(N+1) = (i-(N+1))+1 := by omega
          rw [eq]
          exact P.complex_exactAt_succ _
        have he := (HomologicalComplex.exactAt_iff' P.complex
          ((i+1+1)-(N+1)) ((i+1)-(N+1)) (i-(N+1)) (by apply ComplexShape.prev_eq'; change _+1=_; omega)
          (by apply ComplexShape.next_eq'; change _+1=_; omega)).mp hp
        apply (ShortComplex.exact_iff_of_iso (ShortComplex.isoMk
          (tailIso C N P (i+1+1) (by omega)) (tailIso C N P (i+1) (by omega))
          (tailIso C N P i ht) ?_ ?_)).mpr he
        · simp [d_tail C N P (i+1) (by omega),Category.assoc]
          erw [Iso.inv_hom_id, Category.comp_id]
          rfl
        · simp [d_tail C N P i ht,Category.assoc]
          erw [Iso.inv_hom_id, Category.comp_id]
          rfl

instance obj_projective [∀ i, Projective (C.X i)] (i : ℕ) : Projective (obj C N P i) := by
  dsimp [obj]
  split <;> infer_instance

instance complex_projective [∀ i, Projective (C.X i)] (hN : 0<N) (i : ℕ) :
    Projective ((complex C N P hN).X i) := obj_projective C N P i

def augmentation {Z : Rep k G} (hN : 0<N) (ε : C.X 0 ⟶ Z) (hε : C.d 1 0 ≫ ε = 0) :
    complex C N P hN ⟶ (ChainComplex.single₀ (Rep k G)).obj Z :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨(headIso C N P 0 (by omega)).hom ≫ ε, by
    rw [complex_d,d_head C N P 0 hN]
    simp [Category.assoc,hε]
    rfl⟩

def resolution {Z : Rep k G} [∀ i, Projective (C.X i)]
    (hN : 0<N) (ε : C.X 0 ⟶ Z) [Epi ε] (hε : C.d 1 0 ≫ ε = 0)
    (he₀ : (ShortComplex.mk (C.d 1 0) ε hε).Exact)
    (hex : ∀ i, 0 < i → i < N → C.ExactAt i) : ProjectiveResolution Z where
  complex := complex C N P hN
  π := augmentation C N P hN ε hε
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
      · refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2 ⟨he₀,inferInstance⟩
        exact ShortComplex.isoMk (headIso C N P 1 (by omega))
          (headIso C N P 0 (by omega)) (Iso.refl _) (by
            simp [complex_d,d_head C N P 0 hN]
            erw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id])
          (by
            simp only [augmentation,Iso.refl_hom]
            erw [Category.comp_id]
            exact (ChainComplex.toSingle₀Equiv_symm_apply_f_zero
              (C := complex C N P hN) (X := Z) _ _).symm)
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact exactAt_succ C N P hN hex n
      · apply ChainComplex.exactAt_succ_single_obj⟩

lemma complex_head_d (hN : 0<N) (i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    (complex C N P hN).d i j ≫ (headIso C N P j hj).hom =
      (headIso C N P i hi).hom ≫ C.d i j := by
  by_cases h : j+1=i
  · subst i
    rw [complex_d,d_head C N P j (by omega)]
    simp
  · erw [(complex C N P hN).shape i j h,C.shape i j h,zero_comp,comp_zero]
    rfl

end PartialResolution

namespace ProductCriterion
open CategoryTheory CategoryTheory.Limits
open scoped MonoidAlgebra
variable {k G : Type} [CommRing k] [Group G]

@[simp] lemma moduleMap_comp {A B C : Rep k G} (f : A ⟶ B) (g : B ⟶ C) :
    moduleMap (f ≫ g) = (moduleMap g).comp (moduleMap f) := rfl
@[simp] lemma moduleMap_id (C : Rep k G) : moduleMap (𝟙 C) = LinearMap.id := rfl

def moduleIso {C D : Rep k G} (e : C ≅ D) : C.ρ.asModule ≃ₗ[k[G]] D.ρ.asModule :=
  LinearEquiv.ofLinearMap (moduleMap e.hom) (moduleMap e.inv) (by
    rw [← moduleMap_comp,e.inv_hom_id,moduleMap_id]) (by
    rw [← moduleMap_comp,e.hom_inv_id,moduleMap_id])

lemma kernel_fg_of_iso {B C D : Rep k G} (f : B ⟶ C) (g : C ⟶ D)
    (hfg : f ≫ g = 0) {α β : Type} [Finite α]
    (eC : C ≅ Rep.free k G α) (eD : D ≅ Rep.free k G β)
    (hex : ∀ I : Type, ((ShortComplex.mk f g hfg).map
      ((Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I))).Exact) :
    (moduleMap g).ker.FG := by
  let f' := f ≫ eC.hom
  let g' := eC.inv ≫ g ≫ eD.hom
  have hc : f' ≫ g' = 0 := by
    simp only [f',g',Category.assoc,eC.hom_inv_id_assoc]
    rw [← Category.assoc,hfg,zero_comp]
  have he (I : Type) : ((ShortComplex.mk f' g' hc).map
      ((Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I))).Exact := by
    let E : ShortComplex.mk f g hfg ≅ ShortComplex.mk f' g' hc :=
      ShortComplex.isoMk (Iso.refl _) eC eD (by simp [f'])
        (by simp [g'])
    exact (ShortComplex.exact_iff_of_iso
      ((((Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I)).mapShortComplex).mapIso E)).mp (hex I)
  have hfg' : (moduleMap g').ker.FG := kernel_fg_of_tensor_homology_zero B f' g' hc
    (fun I => (ShortComplex.exact_iff_isZero_homology _).mp (he I))
  have hmap : ((moduleMap g').ker).map (moduleMap eC.inv) = (moduleMap g).ker := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      have hy' : moduleMap eD.hom (moduleMap g (moduleMap eC.inv y)) = 0 := hy
      apply (moduleIso eD).injective
      change moduleMap eD.hom (moduleMap g (moduleMap eC.inv y)) = moduleMap eD.hom 0
      simpa using hy'
    · intro hx
      refine ⟨moduleMap eC.hom x,?_,?_⟩
      · change moduleMap eD.hom (moduleMap g (moduleMap eC.inv (moduleMap eC.hom x))) = 0
        have hi : moduleMap eC.inv (moduleMap eC.hom x) = x := (moduleIso eC).left_inv x
        rw [hi,show moduleMap g x = 0 from hx,map_zero]
      · exact (moduleIso eC).left_inv x
  rw [← hmap]
  exact hfg'.map _
end ProductCriterion

end

end OAI
