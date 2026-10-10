import Mathlib
import OAI.GroupTheory.FiniteType.PartialResolution

namespace OAI

noncomputable section

namespace PartialResolution
open CategoryTheory CategoryTheory.Limits ProductFiniteResolution ProductCriterion
open scoped MonoidAlgebra
variable {k G : Type} [CommRing k] [Group G]

lemma partial_cycles_fg (C : ChainComplex (Rep k G) ℕ) [∀ i, Projective (C.X i)]
    (N : ℕ) (hN : 0 < N) (ε : C.X 0 ⟶ Rep.trivial k G k) [Epi ε]
    (hε : C.d 1 0 ≫ ε = 0) (he₀ : (ShortComplex.mk (C.d 1 0) ε hε).Exact)
    (hex : ∀ i, 0 < i → i < N → C.ExactAt i)
    {α β : Type} [Finite α] (eC : C.X N ≅ Rep.free k G α)
    (eD : C.X (N-1) ≅ Rep.free k G β)
    (hzero : ∀ I : Type, IsZero (groupHomology (RegularProductR.rep k G I) N)) :
    (moduleMap (C.d N (N-1))).ker.FG := by
  let P := ProjectiveResolution.of (kerRep (C.d N (N-1)))
  let T := resolution C N P hN ε hε he₀ hex
  let f : T.complex.X (N+1) ⟶ C.X N :=
    T.complex.d (N+1) N ≫ (headIso C N P N le_rfl).hom
  have hc : f ≫ C.d N (N-1) = 0 := by
    change (complex C N P hN).d (N+1) N ≫
      (headIso C N P N le_rfl).hom ≫ C.d N (N-1) = 0
    erw [← complex_head_d C N P hN N (N-1) le_rfl (by omega),
      ← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]
  apply kernel_fg_of_iso f (C.d N (N-1)) hc eC eD
  intro I
  have he := product_resolution_exact T N hzero I
  rw [HomologicalComplex.exactAt_iff' _ (N+1) N (N-1)
    (by apply ComplexShape.prev_eq'; rfl)
    (by apply ComplexShape.next_eq'; change _+1=N; omega)] at he
  let E : ShortComplex.mk (T.complex.d (N+1) N) (T.complex.d N (N-1))
      (T.complex.d_comp_d _ _ _) ≅ ShortComplex.mk f (C.d N (N-1)) hc :=
    ShortComplex.isoMk (Iso.refl _) (headIso C N P N le_rfl)
      (headIso C N P (N-1) (by omega)) (by simp [f])
      (complex_head_d C N P hN N (N-1) le_rfl (by omega)).symm
  exact (ShortComplex.exact_iff_of_iso
    ((((Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I)).mapShortComplex).mapIso E)).mp he
end PartialResolution

namespace CWEquivariant
section
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular CategoryTheory HomologicalComplex ProductCriterion
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]
variable (hc : ∀ (g : G) n (i : RelCWComplex.cell (univ : Set X) n) (v : Disk n),
  g • RelCWComplex.map n i v = RelCWComplex.map n (g • i) v)

lemma cycles_fg [PathConnectedSpace (univ : Set X)] [∀ i, Projective (object (G:=G) (X:=X) i)]
    (n : ℕ) {α β : Type} [Finite α]
    (eC : object (G:=G) (X:=X) (n+1) ≅ Rep.free ℤ G α)
    (eD : object (G:=G) (X:=X) n ≅ Rep.free ℤ G β)
    (hex : ∀ j, 0 < j → j < n+1 →
      CategoryTheory.Limits.IsZero ((SingularChains.chains (univ : Set X)).homology j))
    (hzero : ∀ I : Type, CategoryTheory.Limits.IsZero
      (groupHomology (RegularProductR.rep ℤ G I) (n+1))) :
    (moduleBoundary hc n).ker.FG := by
  let : Epi (show (complex hc).X 0 ⟶ Rep.trivial ℤ G ℤ from aug hc) := aug_epi hc
  have : ∀ i, Projective ((complex hc).X i) := fun i => inferInstanceAs (Projective (object i))
  have h := PartialResolution.partial_cycles_fg (complex hc) (n+1) (by omega) (aug hc)
    (d_aug hc) (aug_exact hc) (fun i hi h => by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact complex_exactAt hc j (hex (j+1) hi h)) eC (by simpa only [Nat.add_sub_cancel_right,complex,ChainComplex.of_X] using eD) hzero
  rw [show (n+1)-1=n by omega] at h
  have hd : (complex hc).d (n+1) n = differential hc n := ChainComplex.of_d _ _ _
  rw [hd] at h
  exact h

def absoluteRep (m j : ℕ) : Rep ℤ G :=
  Rep.of ({ toFun := fun g => (homologyMap ((skeletal hc g).absoluteMap m) j).hom
            map_one' := by
              have he : (skeletal hc (1:G)).absoluteMap m = 𝟙 (absolute (C:=(univ : Set X)) m) := by
                unfold SkeletalMap.absoluteMap
                convert SingularChains.map_id using 2
                ext x
                simp [SkeletalMap.onSkel,skeletal]
              rw [he,homologyMap_id]
              rfl
            map_mul' := by
              intro g h
              have he : (skeletal hc (g*h)).absoluteMap m =
                  (skeletal hc h).absoluteMap m ≫ (skeletal hc g).absoluteMap m := by
                unfold SkeletalMap.absoluteMap
                rw [← SingularChains.map_comp]
                congr 1
                ext x
                simp [SkeletalMap.onSkel,skeletal,mul_smul]
              rw [he,homologyMap_comp]
              rfl } : Representation ℤ G ((absolute (C:=(univ : Set X)) m).homology j))

def qLinear (n : ℕ) : ((absoluteRep hc (n+1) n) : Type) →ₗ[ℤ]
    MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) n) :=
  (q n n ≫ (orientedIso n).inv).hom

lemma qLinear_smul (g : G) (n : ℕ) (x : absoluteRep hc (n+1) n) :
    qLinear hc n ((absoluteRep hc (n+1) n).ρ g x) = rep (G:=G) n g (qLinear hc n x) := by
  apply (orientedIso n).toLinearEquiv.injective
  change ((q n n ≫ (orientedIso n).inv) ≫ (orientedIso n).hom)
    ((homologyMap ((skeletal hc g).absoluteMap (n+1)) n) x) = _
  rw [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  change q n n ((homologyMap ((skeletal hc g).absoluteMap (n+1)) n) x) =
    (orientedIso n).hom (rep (G:=G) n g (qLinear hc n x))
  rw [← orientedIso_smul hc]
  change (homologyMap ((skeletal hc g).absoluteMap (n+1)) n ≫ q n n) x =
    ((q n n ≫ (orientedIso n).inv ≫ (orientedIso n).hom) ≫ (skeletal hc g).cellMap n) x
  rw [Iso.inv_hom_id,Category.comp_id,← (skeletal hc g).q_natural]
  rfl

def qRep (n : ℕ) : absoluteRep hc (n+1) n ⟶ object (G:=G) (X:=X) n :=
  Rep.ofHom ((qLinear hc n).intertwiningMap_of_isIntertwiningMap _ _
    (fun g x => qLinear_smul hc g n x))

lemma qRep_boundary (n : ℕ) : qRep hc (n+1) ≫ differential hc n = 0 := by
  apply Rep.Hom.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply (orientedIso n).toLinearEquiv.injective
  change (orientedIso n).hom (boundary n ((orientedIso (n+1)).inv (q (n+1) (n+1) x))) =
    (orientedIso n).hom 0
  rw [map_zero,oriented_boundary]
  change CWCellular.d n (((orientedIso (n+1)).inv ≫ (orientedIso (n+1)).hom) (q (n+1) (n+1) x)) = 0
  rw [Iso.inv_hom_id]
  exact congrArg (fun f => f x) (q_d (C:=(univ : Set X)) n)

def cyclesMap (n : ℕ) : (absoluteRep hc (n+2) (n+1)).ρ.asModule →ₗ[MonoidAlgebra ℤ G]
    (moduleBoundary hc n).ker :=
  (moduleMap (qRep hc (n+1))).codRestrict _ (fun x => by
    exact congrArg (fun f => moduleMap f x) (qRep_boundary hc n))

lemma cyclesMap_bijective (n : ℕ) : Function.Bijective (cyclesMap hc n) := by
  constructor
  · intro x y h
    apply top_injective (C:=(univ : Set X)) (n+1)
    have h' := congrArg (fun z => (orientedIso (n+1)).hom z) (congrArg Subtype.val h)
    change ((q (n+1) (n+1) ≫ (orientedIso (n+1)).inv) ≫ (orientedIso (n+1)).hom) x =
      ((q (n+1) (n+1) ≫ (orientedIso (n+1)).inv) ≫ (orientedIso (n+1)).hom) y at h'
    simpa only [Category.assoc,Iso.inv_hom_id,Category.comp_id] using h'
  · intro z
    have hz : CWCellular.d n ((orientedIso (n+1)).hom z.1) = 0 := by
      erw [← oriented_boundary]
      change (orientedIso n).hom (moduleBoundary hc n z.1) = 0
      erw [z.2,map_zero]
    obtain ⟨x,hx⟩ := (top_image (C:=(univ : Set X)) n _).mp hz
    refine ⟨x,Subtype.ext ?_⟩
    change (orientedIso (n+1)).inv (q (n+1) (n+1) x) = z.1
    rw [hx]
    exact congrArg (fun f => f z.1) (orientedIso (n+1)).hom_inv_id

def cyclesEquiv (n : ℕ) : (absoluteRep hc (n+2) (n+1)).ρ.asModule ≃ₗ[MonoidAlgebra ℤ G]
    (moduleBoundary hc n).ker := LinearEquiv.ofBijective (cyclesMap hc n) (cyclesMap_bijective hc n)

attribute [instance] AddCommGroup.toIntModule
end

attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular CategoryTheory HomologicalComplex ProductCriterion
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]
variable (hc : ∀ (g : G) n (i : RelCWComplex.cell (univ : Set X) n) (v : Disk n),
  g • RelCWComplex.map n i v = RelCWComplex.map n (g • i) v)

def wholeRep (j : ℕ) : Rep ℤ G :=
  Rep.of ({ toFun := fun g => (homologyMap (SingularChains.map (onSpace (X:=X) g)) j).hom
            map_one' := by
              have he : onSpace (X:=X) (1:G) = ContinuousMap.id _ := by
                ext x; simp [onSpace]
              rw [he,SingularChains.map_id,homologyMap_id]
              rfl
            map_mul' := by
              intro g h
              have he : onSpace (X:=X) (g*h) = (onSpace g).comp (onSpace h) := by
                ext x; simp [onSpace,mul_smul]
              rw [he,SingularChains.map_comp,homologyMap_comp]
              rfl } : Representation ℤ G ((SingularChains.chains (univ : Set X)).homology j))

def toWhole (m j : ℕ) : absoluteRep hc m j ⟶ wholeRep (G:=G) (X:=X) j :=
  Rep.ofHom ((homologyMap (SingularChains.map (skelToComplex (C:=(univ : Set X)) m)) j).hom.intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g x
    change ((homologyMap ((skeletal hc g).absoluteMap m) j ≫
      homologyMap (SingularChains.map (skelToComplex m)) j) x) =
      ((homologyMap (SingularChains.map (skelToComplex m)) j ≫
        homologyMap (SingularChains.map (onSpace g)) j) x)
    rw [← homologyMap_comp,← homologyMap_comp]
    congr 1
    unfold SkeletalMap.absoluteMap
    rw [← SingularChains.map_comp,← SingularChains.map_comp]
    rfl))

lemma toWhole_surjective (m j : ℕ) (hj : j < m) :
    Function.Surjective (moduleMap (toWhole hc m j)) :=
  homology_toComplex_surjective_top m j hj

include hc in

lemma homology_finite [PathConnectedSpace (univ : Set X)]
    [∀ i, Projective (object (G:=G) (X:=X) i)]
    (n : ℕ) {α β : Type} [Finite α]
    (eC : object (G:=G) (X:=X) (n+1) ≅ Rep.free ℤ G α)
    (eD : object (G:=G) (X:=X) n ≅ Rep.free ℤ G β)
    (hex : ∀ j, 0 < j → j < n+1 →
      CategoryTheory.Limits.IsZero ((SingularChains.chains (univ : Set X)).homology j))
    (hzero : ∀ I : Type, CategoryTheory.Limits.IsZero
      (groupHomology (RegularProductR.rep ℤ G I) (n+1))) :
    Module.Finite (MonoidAlgebra ℤ G) (wholeRep (G:=G) (X:=X) (n+1)).ρ.asModule := by
  have : Module.Finite (MonoidAlgebra ℤ G) (moduleBoundary hc n).ker :=
    Module.Finite.of_fg (cycles_fg hc n eC eD hex hzero)
  have : Module.Finite (MonoidAlgebra ℤ G) (absoluteRep hc (n+2) (n+1)).ρ.asModule :=
    Module.Finite.equiv (cyclesEquiv hc n).symm
  exact Module.Finite.of_surjective (moduleMap (toWhole hc (n+2) (n+1)))
    (toWhole_surjective hc _ _ (by omega))

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

end

end OAI
