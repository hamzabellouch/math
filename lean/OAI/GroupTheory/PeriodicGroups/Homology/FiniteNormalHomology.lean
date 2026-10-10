import Mathlib
import OAI.GroupTheory.PeriodicGroups.Homology.LocallyFiniteActions

namespace OAI

noncomputable section

namespace SourceBurnside.Stability
section
open Classical CategoryTheory CategoryTheory.Limits Representation Rep

namespace FiniteNormal
variable {G : Type} [Group G] (N : Subgroup G) [N.Normal] [Fintype N]

def averageEnd (A : Rep ℚ G) : A ⟶ A := Rep.ofHom
  { toLinearMap := FiniteAverage.average (A.ρ.comp N.subtype)
    isIntertwining' := by
      intro g
      ext x
      simp only [LinearMap.comp_apply, FiniteAverage.average_apply, map_smul, map_sum,
        MonoidHom.comp_apply]
      congr 1
      apply Fintype.sum_equiv (MulAut.conjNormal (H := N) g⁻¹).toEquiv
      intro n
      change A.ρ n.val (A.ρ g x) = A.ρ g (A.ρ ((MulAut.conjNormal g⁻¹) n).val x)
      simp only [← Module.End.mul_apply, ← map_mul, MulAut.conjNormal_apply]
      congr 2
      group }

lemma averageEnd_natural {A B : Rep ℚ G} (f : A ⟶ B) :
    averageEnd N A ≫ f = f ≫ averageEnd N B := by
  ext x
  exact FiniteAverage.intertwining _ _ (Rep.resMap N.subtype f).hom x

lemma averageEnd_trivial : averageEnd N (Rep.trivial ℚ G ℚ) = 𝟙 _ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change FiniteAverage.average _ x = x
  rw [FiniteAverage.average_apply]
  simp only [MonoidHom.comp_apply, Representation.trivial_apply,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀, one_smul]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

def averageChain (C : ChainComplex (Rep ℚ G) ℕ) : C ⟶ C where
  f n := averageEnd N (C.X n)
  comm' i j _ := averageEnd_natural N (C.d i j)

lemma averageChain_π (P : ProjectiveResolution (Rep.trivial ℚ G ℚ)) :
    averageChain N P.complex ≫ P.π = P.π := by
  apply HomologicalComplex.Hom.ext
  funext n
  change averageEnd N (P.complex.X n) ≫ P.π.f n = P.π.f n
  rw [averageEnd_natural]
  cases n with
  | zero => rw [show averageEnd N (((ChainComplex.single₀ (Rep ℚ G)).obj
      (Rep.trivial ℚ G ℚ)).X 0) = 𝟙 _ from averageEnd_trivial N, Category.comp_id]
  | succ n => exact (Limits.isZero_zero _).eq_of_tgt _ _

def averageHomotopy (P : ProjectiveResolution (Rep.trivial ℚ G ℚ)) :
    Homotopy (averageChain N P.complex) (𝟙 P.complex) :=
  ProjectiveResolution.liftHomotopy (𝟙 _) _ _
    (by simpa using averageChain_π N P) (by simp)

lemma averageBalanced (A B : Rep ℚ G) :
    ((Rep.coinvariantsTensor ℚ G).obj A).map (averageEnd N B) =
      ((Rep.coinvariantsTensor ℚ G).map (averageEnd N A)).app B := by
  apply Rep.coinvariantsTensor_hom_ext
  ext a b
  change Coinvariants.mk (A.ρ.tprod B.ρ)
      (a ⊗ₜ[ℚ] FiniteAverage.average (B.ρ.comp N.subtype) b) =
    Coinvariants.mk (A.ρ.tprod B.ρ)
      (FiniteAverage.average (A.ρ.comp N.subtype) a ⊗ₜ[ℚ] b)
  simp only [FiniteAverage.average_apply, TensorProduct.tmul_smul, TensorProduct.smul_tmul,
    TensorProduct.tmul_sum, TensorProduct.sum_tmul, map_smul, map_sum, MonoidHom.comp_apply]
  congr 1
  calc
    _ = ∑ n : N, Coinvariants.mk (A.ρ.tprod B.ρ) (A.ρ n.val⁻¹ a ⊗ₜ[ℚ] b) := by
      apply Finset.sum_congr rfl
      intro n _
      exact (Coinvariants.mk_inv_tmul A.ρ B.ρ a b n.val).symm
    _ = _ := Fintype.sum_equiv (Equiv.inv N) _ _ (fun n => rfl)

lemma averageTensor_zero (A B : Rep ℚ G) (hA : averageEnd N A = 0) :
    ((Rep.coinvariantsTensor ℚ G).obj A).map (averageEnd N B) = 0 := by
  rw [averageBalanced, hA]
  apply Rep.coinvariantsTensor_hom_ext
  ext a b
  simp [Rep.coinvariantsTensorMk]

theorem homology_isZero (A : Rep ℚ G) (hA : averageEnd N A = 0) (n : ℕ) :
    IsZero (groupHomology A n) := by
  let P := Rep.barResolution ℚ G
  let F := (Rep.coinvariantsTensor ℚ G).obj A
  have hz : (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (averageChain N P.complex) = 0 := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact averageTensor_zero N A _ hA
  have ht := (F.mapHomotopy (averageHomotopy N P)).homologyMap_eq n
  rw [hz, HomologicalComplex.homologyMap_zero, CategoryTheory.Functor.map_id,
    HomologicalComplex.homologyMap_id] at ht
  exact ((Limits.IsZero.iff_id_eq_zero _).mpr ht.symm).of_iso (groupHomologyIso A n P)

lemma averageEnd_zero_of_neg (A : Rep ℚ G) (t : N)
    (ht : ∀ a : A, A.ρ t.val a = -a) : averageEnd N A = 0 := by
  ext a
  change FiniteAverage.average (A.ρ.comp N.subtype) a = 0
  have h := FiniteAverage.average_action (A.ρ.comp N.subtype) t a
  change FiniteAverage.average (A.ρ.comp N.subtype) (A.ρ t.val a) = _ at h
  rw [ht, map_neg] at h
  have htwo : (2 : ℚ) • FiniteAverage.average (A.ρ.comp N.subtype) a = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp h.symm
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

end FiniteNormal
end

section
open Classical CategoryTheory CategoryTheory.Limits Rep

abbrev scalarRep {G : Type} [Group G] (χ : G →* ℚˣ) : Rep ℚ G :=
  Rep.of (k := ℚ) (X := ℚ)
    { toFun g := (χ g).val • LinearMap.id
      map_one' := by ext; simp
      map_mul' g h := by ext; simp [mul_smul,mul_comm] }

namespace SignHomology
variable {G H : Type} [Group G] [Group H]

lemma isZero_of_finite_normal (χ : G →* ℚˣ)
    (N : Subgroup G) [N.Normal] [Fintype N] (t : N) (ht : χ t.val = -1) (n : ℕ) :
    IsZero (groupHomology (scalarRep χ) n) := by
  apply FiniteNormal.homology_isZero N
  apply FiniteNormal.averageEnd_zero_of_neg N _ t
  intro a
  change (χ t.val).val • a = -a
  rw [ht]
  simp

lemma isZero_of_quotient (q : G →* H) (hq : Function.Surjective q)
    (hK : LocallyFinite q.ker) (χ : H →* ℚˣ)
    (N : Subgroup H) [N.Normal] [Fintype N] (t : N) (ht : χ t.val = -1) (n : ℕ) :
    IsZero (groupHomology (scalarRep (χ.comp q)) n) := by
  have := RelativeCoinvariants.surjective_map_isIso q hq hK (scalarRep χ) n
  exact (isZero_of_finite_normal χ N t ht n).of_iso
    (asIso (groupHomology.map q (𝟙 (Rep.res q (scalarRep χ))) n))

lemma product_isZero {P : Type} [Group P] [Fintype P] (χ : G × P →* ℚˣ)
    (p : P) (hp : χ (1,p) = -1) (n : ℕ) :
    IsZero (groupHomology (scalarRep χ) n) := by
  let N : Subgroup (G × P) := (MonoidHom.fst G P).ker
  let e : N ≃ P :=
    { toFun x := x.val.2
      invFun p := ⟨(1,p),rfl⟩
      left_inv x := Subtype.ext (Prod.ext x.property.symm rfl)
      right_inv p := rfl }
  let : Fintype N := Fintype.ofEquiv P e.symm
  exact isZero_of_finite_normal χ N ⟨(1,p),rfl⟩ hp n

end SignHomology
end

attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical CategoryTheory CategoryTheory.Limits Module MatrixK1 MatrixGenerators
open scoped Pointwise
namespace FrameStabilizer
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)
variable [LinearOrder (ColumnFrames.Vertex (ι := ι ⊕ κ) ε)]

abbrev V := ColumnFrames.Vertex (ι := ι ⊕ κ) ε
abbrev G := E (R := R) (ι := ι ⊕ κ)
abbrev rho := ColumnFrames.rho (ι := ι ⊕ κ) ε
omit [LinearOrder (ColumnFrames.Vertex (ι := ι ⊕ κ) ε)] in
lemma independent_action (g : G (R := R) (ι := ι) (κ := κ))
    (s : Set (V (ι := ι) (κ := κ) ε)) (hs : LinearIndepOn (ZMod 2) (rho ε) s) :
    LinearIndepOn (ZMod 2) (rho ε) ((g • ·) '' s) := ColumnFrames.independent_map ε g.val hs

abbrev index := Frames.Index (F := ZMod 2) (rho (ι := ι) (κ := κ) ε) (Fintype.card κ)
local instance : MulAction (G (R := R) (ι := ι) (κ := κ)) (index (ι := ι) (κ := κ) ε) :=
  Frames.indexAction (rho ε) (G (R := R) (ι := ι) (κ := κ)) (independent_action ε) (Fintype.card κ)

abbrev A := Frames.chainRep (G (R := R) (ι := ι) (κ := κ)) (ρ := rho (ι := ι) (κ := κ) ε)
  (independent_action ε) (Fintype.card κ)
abbrev b := Frames.frameBasis (F := ZMod 2) (rho (ι := ι) (κ := κ) ε) (Fintype.card κ)
abbrev right := UnorderedStabilizer.rightVertex (ι := ι) (κ := κ) ε

def base : index (ι := ι) (κ := κ) ε :=
  ⟨Finset.univ.image (right ε), by
    constructor
    · exact Finset.card_image_of_injective _ (UnorderedStabilizer.rightVertex_injective ε)
    · have hi := ColumnFrames.standard_independent (ι := ι ⊕ κ) ε (Set.range Sum.inr)
      simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ,←Set.range_comp,
        rho,right,UnorderedStabilizer.rightVertex,Function.comp_def] using hi⟩

lemma base_coe : ((base (ι := ι) (κ := κ) ε).val : Set (V (ι := ι) (κ := κ) ε)) = Set.range (right ε) := by
  simp [base]

lemma stabilizer_eq : MulAction.stabilizer (G (R := R) (ι := ι) (κ := κ)) (base (ι := ι) (κ := κ) ε) =
    UnorderedStabilizer.K (ι := ι) (κ := κ) ε := by
  ext g
  rw [MulAction.mem_stabilizer_iff,MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have hh := congrArg (fun x : index (ι := ι) (κ := κ) ε => (x.val : Set (V (ι := ι) (κ := κ) ε))) h
    simpa only [Frames.indexAction_val,Finset.coe_image,base_coe,Set.image_smul] using hh
  · intro h
    apply Subtype.ext
    apply Finset.coe_injective
    rw [Frames.indexAction_val,Finset.coe_image,base_coe,Set.image_smul]
    exact h

def stabilizerEquiv : MulAction.stabilizer (G (R := R) (ι := ι) (κ := κ)) (base (ι := ι) (κ := κ) ε) ≃*
    UnorderedStabilizer.K (ι := ι) (κ := κ) ε := MulEquiv.subgroupCongr (stabilizer_eq (ι := ι) (κ := κ) ε)

lemma monomial (g : G (R := R) (ι := ι) (κ := κ)) (x : index (ι := ι) (κ := κ) ε) :
    ∃c : ℚˣ, (A ε).ρ g (b ε x) = c.val • b ε (g • x) :=
  Frames.frame_action_monomial (rho ε) (G (R := R) (ι := ι) (κ := κ)) (independent_action ε) _ g x

abbrev characterS := MonomialInduction.character (base (ι := ι) (κ := κ) ε) (A ε) (b ε) (monomial ε)
def characterK : UnorderedStabilizer.K (ι := ι) (κ := κ) ε →* ℚˣ :=
  (characterS ε).comp (stabilizerEquiv (ι := ι) (κ := κ) ε).symm.toMonoidHom

lemma characterK_spec (s : UnorderedStabilizer.K (ι := ι) (κ := κ) ε) :
    Frames.labelMap (s.val • ·) (Frames.basis (base (ι := ι) (κ := κ) ε).val) =
      (characterK ε s).val • Frames.basis (base (ι := ι) (κ := κ) ε).val := by
  have h := MonomialInduction.character_spec (base (ι := ι) (κ := κ) ε) (A ε) (b ε) (monomial ε)
    ((stabilizerEquiv (ι := ι) (κ := κ) ε).symm s)
  have hh := congrArg Subtype.val h
  change Frames.labelMap (s.val • ·) (b ε (base (ι := ι) (κ := κ) ε)).val =
    (characterK ε s).val • (b ε (base (ι := ι) (κ := κ) ε)).val at hh
  simpa only [Frames.frameBasis_val] using hh

lemma perm_kernel_character : (UnorderedStabilizer.perm (ι := ι) (κ := κ) ε).ker ≤ (characterK ε).ker := by
  intro s hs
  apply MonoidHom.mem_ker.mpr
  apply Units.ext
  apply MonomialInduction.smul_basis_injective (base (ι := ι) (κ := κ) ε) (A ε) (b ε)
  dsimp only
  apply Subtype.ext
  change (characterK ε s).val • (b ε (base (ι := ι) (κ := κ) ε)).val = (1 : ℚ) • (b ε (base (ι := ι) (κ := κ) ε)).val
  rw [Frames.frameBasis_val,←characterK_spec,one_smul]
  apply Frames.labelMap_basis_fixed
  intro v hv
  obtain ⟨j,rfl⟩ := (base_coe (ι := ι) (κ := κ) ε ▸ (show v∈((base (ι := ι) (κ := κ) ε).val : Set (V (ι := ι) (κ := κ) ε)) from hv))
  have he := UnorderedStabilizer.perm_spec ε s j
  rw [MonoidHom.mem_ker.mp hs] at he
  exact he

variable (hI : MatrixNilKernel ε.toRingHom) (hι : 5 ≤ Fintype.card ι)

include hI hι in
lemma transitive (x : index (ι := ι) (κ := κ) ε) :
    ∃g : G (R := R) (ι := ι) (κ := κ), g • base (ι := ι) (κ := κ) ε = x := by
  let : Fintype x.val := Fintype.ofFinset x.val (fun _ => Iff.rfl)
  let e : κ ≃ x.val := Fintype.equivOfCardEq (by simpa using x.property.1.symm)
  let v : κ → V (ι := ι) (κ := κ) ε := fun j => (e j).val
  have hi : LinearIndependent (ZMod 2) (rho ε ∘ v) :=
    x.property.2.comp e e.injective
  obtain ⟨g,hg⟩ := MatrixK1.ordered_transitive ε hI hι v hi
  refine ⟨g,Subtype.ext ?_⟩
  apply Finset.coe_injective
  rw [Frames.indexAction_val,Finset.coe_image,base_coe,←Set.range_comp]
  change Set.range (fun j : κ => g • right ε j) = (x.val : Set (V (ι := ι) (κ := κ) ε))
  have he : (fun j : κ => g • right ε j) = v := funext hg
  rw [he]
  ext w
  constructor
  · rintro ⟨j,rfl⟩; exact (e j).property
  · intro hw
    use e.symm ⟨w,hw⟩
    change (e (e.symm ⟨w,hw⟩)).val = w
    rw [e.apply_symm_apply]

end FrameStabilizer
end SourceBurnside.Stability

namespace SourceBurnside.Stability.FrameStabilizer
attribute [-instance] Finset.Subtype.fintype Finset.fintypeCoeSort
open Classical CategoryTheory CategoryTheory.Limits Module MatrixK1 MatrixGenerators
open scoped Pointwise
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)
variable [LinearOrder (ColumnFrames.Vertex (ι := ι ⊕ κ) ε)]

local instance : MulAction (G (R := R) (ι := ι) (κ := κ)) (index (ι := ι) (κ := κ) ε) :=
  Frames.indexAction (rho ε) (G (R := R) (ι := ι) (κ := κ)) (independent_action ε) (Fintype.card κ)

def characterP : Equiv.Perm κ →* ℚˣ :=
  (UnorderedStabilizer.perm (ι := ι) (κ := κ) ε).liftOfRightInverseAux
    (UnorderedStabilizer.sectionElement ε 1)
    (UnorderedStabilizer.section_perm ε 1) (characterK ε) (perm_kernel_character ε)

lemma characterP_comp : (characterP (ι := ι) (κ := κ) ε).comp (UnorderedStabilizer.perm (ι := ι) ε) = characterK (ι := ι) (κ := κ) ε := by
  apply MonoidHom.ext
  intro s
  exact (UnorderedStabilizer.perm (ι := ι) (κ := κ) ε).liftOfRightInverseAux_comp_apply
    (UnorderedStabilizer.sectionElement ε 1) (UnorderedStabilizer.section_perm ε 1)
    (characterK ε) (perm_kernel_character ε) s

lemma characterP_swap (i j : κ) (hij : i≠j) :
    characterP (ι := ι) ε (Equiv.swap i j) = -1 := by
  let s := UnorderedStabilizer.sectionElement (ι := ι) ε 1 (Equiv.swap i j)
  change characterK ε s = -1
  apply Units.ext
  apply MonomialInduction.smul_basis_injective (base (ι := ι) (κ := κ) ε) (A ε) (b ε)
  dsimp only
  apply Subtype.ext
  change (characterK ε s).val • (b ε (base (ι := ι) (κ := κ) ε)).val =
    (-1 : ℚ) • (b ε (base (ι := ι) (κ := κ) ε)).val
  rw [Frames.frameBasis_val,←characterK_spec,neg_one_smul]
  apply Frames.labelMap_basis_transposition (s.val • ·) (base (ι := ι) (κ := κ) ε).val
    (right (ι := ι) (κ := κ) ε i) (right (ι := ι) (κ := κ) ε j)
  · change right (ι := ι) (κ := κ) ε i ∈ ((base (ι := ι) (κ := κ) ε).val : Set (V (ι := ι) (κ := κ) ε))
    rw [base_coe]; exact ⟨i,rfl⟩
  · change right (ι := ι) (κ := κ) ε j ∈ ((base (ι := ι) (κ := κ) ε).val : Set (V (ι := ι) (κ := κ) ε))
    rw [base_coe]; exact ⟨j,rfl⟩
  · exact (UnorderedStabilizer.rightVertex_injective ε).ne hij
  · change s.val.val • right (ι := ι) (κ := κ) ε i = right (ι := ι) (κ := κ) ε j
    simpa only [s,UnorderedStabilizer.section_perm,Equiv.swap_apply_left] using
      UnorderedStabilizer.perm_spec ε s i
  · change s.val.val • right (ι := ι) (κ := κ) ε j = right (ι := ι) (κ := κ) ε i
    simpa only [s,UnorderedStabilizer.section_perm,Equiv.swap_apply_right] using
      UnorderedStabilizer.perm_spec ε s j
  · intro v hv hvi hvj
    have hv' : v∈Set.range (right (ι := ι) (κ := κ) ε) := by
      rw [←base_coe]; exact hv
    obtain ⟨l,rfl⟩ := hv'
    have hli : l≠i := fun he => hvi (congrArg (right (ι := ι) (κ := κ) ε) he)
    have hlj : l≠j := fun he => hvj (congrArg (right (ι := ι) (κ := κ) ε) he)
    change s.val.val • right (ι := ι) (κ := κ) ε l = right (ι := ι) (κ := κ) ε l
    simpa only [s,UnorderedStabilizer.section_perm,Equiv.swap_apply_of_ne_of_ne hli hlj] using
      UnorderedStabilizer.perm_spec ε s l

variable (hI : MatrixNilKernel ε.toRingHom) (hι : 5≤Fintype.card ι)

include hI hι in
lemma characterK_homology_isZero (hκ : 2≤Fintype.card κ) (n : ℕ) :
    IsZero (groupHomology (scalarRep (characterK (ι := ι) (κ := κ) ε)) n) := by
  let q := UnorderedStabilizer.quotientMap (κ := κ) ε hI hι
  let χ : E (R := R) (ι := ι) × Equiv.Perm κ →* ℚˣ :=
    (characterP (ι := ι) ε).comp (MonoidHom.snd _ _)
  have he : characterK (ι := ι) (κ := κ) ε = χ.comp q := (characterP_comp ε).symm
  rw [he]
  have : Nontrivial κ := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i,j,hij⟩ := exists_pair_ne κ
  have hz := SignHomology.product_isZero χ (Equiv.swap i j) (characterP_swap ε i j hij) n
  have := RelativeCoinvariants.surjective_map_isIso q
    (UnorderedStabilizer.quotientMap_surjective ε hI hι)
    (UnorderedStabilizer.kernel_locallyFinite ε hI hι) (scalarRep χ) n
  exact hz.of_iso (asIso (groupHomology.map q (𝟙 (Rep.res q (scalarRep χ))) n))

include hI hι in
lemma characterS_homology_isZero (hκ : 2≤Fintype.card κ) (n : ℕ) :
    IsZero (groupHomology (scalarRep (characterS (ι := ι) (κ := κ) ε)) n) := by
  let e := stabilizerEquiv (ι := ι) (κ := κ) ε
  let j := groupHomology.mapIso (A := scalarRep (characterS ε)) (B := scalarRep (characterK ε))
    e (LinearEquiv.refl ℚ ℚ) (fun s => by
      apply LinearMap.ext
      intro a
      change (characterS ε s).val * a = (characterS ε (e.symm (e s))).val * a
      rw [e.symm_apply_apply]) n
  exact (characterK_homology_isZero ε hI hι hκ n).of_iso j

include hI hι in
lemma chains_homology_isZero (hκ : 2≤Fintype.card κ) (n : ℕ) :
    IsZero (groupHomology (A (ι := ι) (κ := κ) ε) n) := by
  let x := base (ι := ι) (κ := κ) ε
  let S := MulAction.stabilizer (G (R := R) (ι := ι) (κ := κ)) x
  let χ := characterS (ι := ι) (κ := κ) ε
  let f := MonomialInduction.induced x (A ε) (b ε) χ
    (MonomialInduction.character_spec x (A ε) (b ε) (monomial ε))
  have := MonomialInduction.induced_isIso x (A ε) (b ε) χ
    (MonomialInduction.character_spec x (A ε) (b ε) (monomial ε))
    (transitive ε hI hι) (monomial ε)
  have := ShapiroMap.map_isIso S (scalarRep χ) n
  let j := asIso (groupHomology.map S.subtype (ShapiroMap.unit S (scalarRep χ)) n)
  have hz : IsZero (groupHomology (Rep.ind S.subtype (scalarRep χ)) n) :=
    (characterS_homology_isZero ε hI hι hκ n).of_iso j.symm
  exact hz.of_iso (((groupHomology.functor ℚ (G (R := R) (ι := ι) (κ := κ)) n).mapIso (asIso f)).symm)

end SourceBurnside.Stability.FrameStabilizer

namespace SourceBurnside.Stability
open Classical CategoryTheory CategoryTheory.Limits MatrixK1
namespace H2FrameEdge
variable {R Ω : Type} [Ring R] [Algebra (ZMod 2) R] [Fintype Ω] [DecidableEq Ω]
variable (ε : R →ₐ[ZMod 2] ZMod 2) (hI : MatrixNilKernel ε.toRingHom)
variable [LinearOrder (ColumnFrames.Vertex (ι := Ω) ε)]

abbrev chains (k : ℕ) := Frames.chainRep (E (R := R) (ι := Ω)) (ρ := ColumnFrames.rho ε)
  (ColumnRelabel.independent_action ε) k

def augmentation : chains (Ω := Ω) ε 1 ⟶ Rep.trivial ℚ (E (R := R) (ι := Ω)) ℚ :=
  Frames.differentialRep (E (R := R)) (ColumnFrames.rho ε) (ColumnRelabel.independent_action ε) 0 ≫
    (Frames.degreeZeroIso (E (R := R)) (ColumnFrames.rho ε) (ColumnRelabel.independent_action ε)).hom

include hI in
lemma chains_acyclic (hΩ : 13≤Fintype.card Ω) (k : ℕ) (hk : 2≤k) (hk' : k≤4) (n : ℕ) :
    IsZero (groupHomology (chains (Ω := Ω) ε k) n) := by
  have hkn : k≤Fintype.card Ω := by omega
  let L := Fin (Fintype.card Ω-k)
  let K := Fin k
  let e : L ⊕ K ≃ Ω := Fintype.equivOfCardEq (by
    simp only [Fintype.card_sum,Fintype.card_fin,L,K]
    omega)
  let : LinearOrder (ColumnFrames.Vertex (ι := L ⊕ K) ε) := linearOrderOfSTO WellOrderingRel
  have hl : 5≤Fintype.card L := by simp only [L,Fintype.card_fin]; omega
  have hz := FrameStabilizer.chains_homology_isZero (ι := L) (κ := K) ε hI hl
    (by simpa only [K,Fintype.card_fin] using hk) n
  have hz' : IsZero (groupHomology (Frames.chainRep (E (R := R) (ι := L ⊕ K))
      (ρ := ColumnFrames.rho ε) (ColumnRelabel.independent_action ε) k) n) := by
    simpa only [FrameStabilizer.A,FrameStabilizer.rho,K,Fintype.card_fin] using hz
  exact hz'.of_iso (ColumnRelabel.homologyIso ε e k n).symm

include hI in
lemma augmentation_isIso (hΩ : 13≤Fintype.card Ω) :
    IsIso (groupHomology.map (B := Rep.trivial ℚ (E (R := R) (ι := Ω)) ℚ)
      (MonoidHom.id (E (R := R) (ι := Ω))) (augmentation ε) 2) := by
  let C := Frames.repComplex (E (R := R) (ι := Ω)) (ColumnFrames.rho ε) (ColumnRelabel.independent_action ε)
  have hrank : 10<Module.finrank (ZMod 2) (Ω → ZMod 2) := by simpa using (show 10<Fintype.card Ω by omega)
  have hepi : Epi (C.d 1 0) := by
    rw [Frames.repComplex_d]
    exact Frames.differentialRep_epi _ _ _ (ColumnFrames.rho_spanning ε) hrank
  have hex : ∀i : Fin 3, (C.sc' (i.val+2) (i.val+1) i.val).Exact :=
    fun i => Frames.repComplex_exact _ _ _ (ColumnFrames.rho_spanning ε) hrank i.val (by omega)
  have hacyc : ∀i : Fin 3, ∀q, IsZero (groupHomology (C.X (i.val+2)) q) :=
    fun i q => chains_acyclic ε hI hΩ (i.val+2) (by omega) (by omega) q
  have hi := HomologyEdge.isIso_H2_augmentation C hepi hex hacyc
  have : IsIso (groupHomology.map (B := chains (Ω := Ω) ε 0) (MonoidHom.id _) (Frames.differentialRep
      (E (R := R) (ι := Ω)) (ColumnFrames.rho ε) (ColumnRelabel.independent_action ε) 0) 2) := by
    simpa only [C,Frames.repComplex_d] using! hi
  have : IsIso (groupHomology.map (B := Rep.trivial ℚ (E (R := R) (ι := Ω)) ℚ)
      (MonoidHom.id _) (Frames.degreeZeroIso (E (R := R) (ι := Ω)) (ColumnFrames.rho ε)
        (ColumnRelabel.independent_action ε)).hom 2) := by
    change IsIso ((groupHomology.functor (k := ℚ) (G := E (R := R) (ι := Ω)) 2).map _)
    infer_instance
  rw [augmentation,groupHomology.map_id_comp]
  infer_instance

end H2FrameEdge
end SourceBurnside.Stability

namespace SourceBurnside.Stability.MonomialTrivial
open Classical CategoryTheory Representation Rep Module
variable {G X : Type} [Group G] [MulAction G X] (x₀ : X)
variable (A : Rep.{0} ℚ G) (b : Basis X ℚ A)
variable (h0 : ∀s : MulAction.stabilizer G x₀, A.ρ s.val (b x₀) = b x₀)

def scalarIso : MonomialInduction.charRep x₀ 1 ≅ Rep.trivial ℚ (MulAction.stabilizer G x₀) ℚ :=
  Rep.mkIso
    { __ := LinearEquiv.refl ℚ ℚ
      isIntertwining' := by intro s; ext; simp }

def seed : Rep.trivial ℚ (MulAction.stabilizer G x₀) ℚ ⟶
    Rep.res (MulAction.stabilizer G x₀).subtype A :=
  Rep.ofHom
    { toLinearMap := LinearMap.toSpanSingleton ℚ A (b x₀)
      isIntertwining' := by
        intro s
        apply LinearMap.ext
        intro a
        change a • b x₀ = A.ρ s.val (a • b x₀)
        rw [map_smul,h0] }

def induced : Rep.ind (MulAction.stabilizer G x₀).subtype (Rep.trivial ℚ (MulAction.stabilizer G x₀) ℚ) ⟶ A :=
  (Rep.indResHomEquiv (MulAction.stabilizer G x₀).subtype _ A).symm (seed x₀ A b h0)

lemma induced_mk (g : G) (a : ℚ) :
    (induced x₀ A b h0).hom (IndV.mk (MulAction.stabilizer G x₀).subtype
      (Rep.trivial ℚ (MulAction.stabilizer G x₀) ℚ).ρ g a) = a • A.ρ g⁻¹ (b x₀) := by
  simp [induced,Rep.indResHomEquiv,seed]

include h0 in
lemma scalar_property (s : MulAction.stabilizer G x₀) :
    A.ρ s.val (b x₀) = ((1 : MulAction.stabilizer G x₀ →* ℚˣ) s).val • b x₀ := by
  simpa using h0 s

lemma indMap_mk {H : Type} [Group H] (S : Subgroup H) {B C : Rep ℚ S} (f : B ⟶ C) (g : H) (a : B) :
    (Rep.indMap S.subtype f).hom (IndV.mk S.subtype B.ρ g a) = IndV.mk S.subtype C.ρ g (f.hom a) := by
  simp [Rep.indMap,IndV.mk]

lemma scalar_comp : (Rep.indFunctor ℚ (MulAction.stabilizer G x₀).subtype).map (scalarIso x₀).hom ≫
      induced x₀ A b h0 =
    MonomialInduction.induced x₀ A b 1 (scalar_property x₀ A b h0) := by
  apply Rep.hom_ext
  apply IntertwiningMap.ext
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro a
  change (induced x₀ A b h0).hom ((Rep.indMap (MulAction.stabilizer G x₀).subtype (scalarIso x₀).hom).hom
     (IndV.mk _ _ g a)) = _
  rw [indMap_mk,induced_mk]
  change a • A.ρ g⁻¹ (b x₀) =
    (MonomialInduction.induced x₀ A b 1 (scalar_property x₀ A b h0)).hom
      (IndV.mk (MulAction.stabilizer G x₀).subtype (MonomialInduction.charRep x₀ 1).ρ g a)
  exact (MonomialInduction.induced_mk x₀ A b 1 (scalar_property x₀ A b h0) g a).symm

variable (ht : ∀x : X, ∃g : G, g • x₀=x)
variable (hm : ∀(g : G) (x : X), ∃c : ℚˣ, A.ρ g (b x) = c.val • b (g • x))

include ht hm in
lemma induced_isIso : IsIso (induced x₀ A b h0) := by
  let i := (Rep.indFunctor ℚ (MulAction.stabilizer G x₀).subtype).mapIso (scalarIso x₀)
  have := MonomialInduction.induced_isIso x₀ A b 1 (scalar_property x₀ A b h0) ht hm
  have he : induced x₀ A b h0 = i.inv ≫ MonomialInduction.induced x₀ A b 1 (scalar_property x₀ A b h0) := by
    rw [←scalar_comp]
    change _ = i.inv ≫ i.hom ≫ induced x₀ A b h0
    rw [Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

include ht hm in
lemma seed_homology_isIso (n : ℕ) :
    IsIso (groupHomology.map (B := A) (MulAction.stabilizer G x₀).subtype (seed x₀ A b h0) n) := by
  let S := MulAction.stabilizer G x₀
  let T := Rep.trivial ℚ S ℚ
  let f := induced x₀ A b h0
  have : IsIso f := induced_isIso x₀ A b h0 ht hm
  have := ShapiroMap.map_isIso S T n
  have he : groupHomology.map S.subtype (seed x₀ A b h0) n =
      groupHomology.map S.subtype (ShapiroMap.unit S T) n ≫
        groupHomology.map (B := A) (MonoidHom.id G) f n := by
    rw [←groupHomology.map_comp]
    apply groupHomology.map_congr rfl
    apply LinearMap.ext
    intro a
    change a • b x₀ = f.hom (IndV.mk S.subtype T.ρ 1 a)
    rw [induced_mk]
    simp
  have : IsIso (groupHomology.map (B := A) (MonoidHom.id G) f n) := by
    change IsIso ((groupHomology.functor (k := ℚ) (G := G) n).map f)
    infer_instance
  rw [he]
  infer_instance

end SourceBurnside.Stability.MonomialTrivial

namespace SourceBurnside.Stability.UnorderedStabilizer
open Classical MatrixGenerators MatrixK1 CategoryTheory
variable {R ι κ : Type} [Ring R] [Algebra (ZMod 2) R]
variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (ε : R →ₐ[ZMod 2] ZMod 2)

def complementary : E (R := R) (ι := ι) →* K (ι := ι) (κ := κ) ε where
  toFun A := sectionElement ε A 1
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    change blockInclusion 1 * permRight 1 = 1
    simp
  map_mul' A B := by
    apply Subtype.ext
    apply Subtype.ext
    change blockInclusion (A.val*B.val) * permRight 1 =
      (blockInclusion A.val * permRight 1) * (blockInclusion B.val * permRight 1)
    simp

lemma complementary_val (A : E (R := R) (ι := ι)) :
    (complementary (ι := ι) (κ := κ) ε A).val.val = blockInclusion A.val := by
  change blockInclusion A.val * permRight 1 = _
  simp

variable (hI : MatrixNilKernel ε.toRingHom) (hι : 5≤Fintype.card ι)

lemma projection_complementary : (projection (κ := κ) ε hI hι).comp (complementary ε) = MonoidHom.id _ := by
  apply MonoidHom.ext
  intro A
  exact Subtype.ext (section_topBlock ε A 1)

lemma projection_surjective : Function.Surjective (projection (κ := κ) ε hI hι) := by
  intro A
  exact ⟨complementary ε A,congrArg (fun f : E (R := R) (ι := ι) →* E => f A)
    (projection_complementary ε hI hι)⟩

variable [Subsingleton κ]

lemma projection_kernel_eq : (projection (κ := κ) ε hI hι).ker = (quotientMap ε hI hι).ker := by
  ext s
  rw [MonoidHom.mem_ker,MonoidHom.mem_ker]
  change projection ε hI hι s=1 ↔ (projection ε hI hι s,perm ε s) = (1,1)
  simp only [Prod.mk.injEq,Subsingleton.elim (perm ε s) 1,and_true]

lemma projection_locallyFinite : LocallyFinite (projection (κ := κ) ε hI hι).ker := by
  rw [projection_kernel_eq]
  exact kernel_locallyFinite ε hI hι

include hI hι in
lemma complementary_homology_isIso (n : ℕ) :
    IsIso (RationalHomology.map (complementary (ι := ι) (κ := κ) ε) n) := by
  let i := RationalHomology.map (complementary (ι := ι) (κ := κ) ε) n
  let p := RationalHomology.map (projection (κ := κ) ε hI hι) n
  have : IsIso p := RationalHomology.surjective_isIso (projection ε hI hι)
    (projection_surjective ε hI hι) (projection_locallyFinite ε hI hι) n
  have he : i ≫ p = 𝟙 _ := by
    rw [←RationalHomology.map_comp,projection_complementary,RationalHomology.map_id]
  have hi : i = inv p := by
    rw [←Category.comp_id i,←IsIso.hom_inv_id p,←Category.assoc,he,Category.id_comp]
  change IsIso i
  rw [hi]
  infer_instance

end SourceBurnside.Stability.UnorderedStabilizer

namespace SourceBurnside.Stability
open Classical CategoryTheory MatrixGenerators MatrixK1 Representation
private lemma trivial_map_factorization {G₁ G₂ G₃ : Type} [Group G₁] [Group G₂] [Group G₃]
    (f : G₁ →* G₂) (g : G₂ →* G₃) (B : Rep ℚ G₃)
    (φ : Rep.trivial ℚ G₂ ℚ ⟶ Rep.res g B) (ψ : B ⟶ Rep.trivial ℚ G₃ ℚ)
    (h : ∀ a : ℚ, ψ.hom (φ.hom a) = a) (n : ℕ) :
    RationalHomology.map (g.comp f) n = RationalHomology.map f n ≫
      groupHomology.map g φ n ≫ groupHomology.map (MonoidHom.id G₃) ψ n := by
  have hRight := groupHomology.map_comp (A := Rep.trivial ℚ G₂ ℚ) (B := B)
    (C := Rep.trivial ℚ G₃ ℚ) g (MonoidHom.id G₃) φ ψ n
  have hBoth := groupHomology.map_comp (A := Rep.trivial ℚ G₁ ℚ)
    (B := Rep.trivial ℚ G₂ ℚ) (C := Rep.trivial ℚ G₃ ℚ) f ((MonoidHom.id G₃).comp g)
    (𝟙 (Rep.trivial ℚ G₁ ℚ)) (φ ≫ (Rep.resFunctor g).map ψ) n
  calc
    _ = groupHomology.map (A := Rep.trivial ℚ G₁ ℚ) (B := Rep.trivial ℚ G₃ ℚ)
        (((MonoidHom.id G₃).comp g).comp f)
        ((𝟙 (Rep.trivial ℚ G₁ ℚ)) ≫ (Rep.resFunctor f).map
          (φ ≫ (Rep.resFunctor g).map ψ)) n := by
      apply groupHomology.map_congr rfl
      apply LinearMap.ext
      intro a
      exact (h a).symm
    _ = _ := hBoth
    _ = _ := congrArg (fun m => RationalHomology.map f n ≫ m) hRight

namespace SingletonFrameEdge
variable {R ι : Type} [Ring R] [Algebra (ZMod 2) R] [Fintype ι] [DecidableEq ι]
variable (ε : R →ₐ[ZMod 2] ZMod 2)
variable [LinearOrder (ColumnFrames.Vertex (ι := ι ⊕ Fin 1) ε)]
local notation "G" => E (R := R) (ι := ι ⊕ Fin 1)
local notation "x₀" => FrameStabilizer.base (ι := ι) (κ := Fin 1) ε
local instance : MulAction G (FrameStabilizer.index (ι := ι) (κ := Fin 1) ε) :=
  Frames.indexAction (FrameStabilizer.rho ε) G (FrameStabilizer.independent_action ε) 1
local notation "S" => MulAction.stabilizer G x₀
local notation "A" => FrameStabilizer.A (ι := ι) (κ := Fin 1) ε
local notation "b" => FrameStabilizer.b (ι := ι) (κ := Fin 1) ε

lemma base_singleton : (x₀).val = {FrameStabilizer.right (ι := ι) ε (0 : Fin 1)} := by
  simp [FrameStabilizer.base,Finset.univ_unique]

lemma fixed (s : S) : (A).ρ s.val (b x₀) = b x₀ := by
  apply Subtype.ext
  change Frames.labelMap (s.val • ·) (b x₀).val = (b x₀).val
  rw [Frames.frameBasis_val]
  apply Frames.labelMap_basis_fixed
  intro v hv
  rw [base_singleton] at hv
  have he : v = FrameStabilizer.right (ι := ι) ε (0 : Fin 1) := Finset.mem_singleton.mp hv
  subst v
  let k := FrameStabilizer.stabilizerEquiv (ι := ι) (κ := Fin 1) ε s
  have h := UnorderedStabilizer.perm_spec ε k (0 : Fin 1)
  rw [Subsingleton.elim (UnorderedStabilizer.perm ε k 0) 0] at h
  simpa only [k,FrameStabilizer.stabilizerEquiv,MulEquiv.subgroupCongr_apply,
    FrameStabilizer.right,Subgroup.smul_def] using! h

abbrev seed := MonomialTrivial.seed x₀ A b (fixed (ι := ι) ε)

def lift : E (R := R) (ι := ι) →* S :=
  (FrameStabilizer.stabilizerEquiv (ι := ι) (κ := Fin 1) ε).symm.toMonoidHom.comp
    (UnorderedStabilizer.complementary ε)

def blockHom : E (R := R) (ι := ι) →* G := (S).subtype.comp (lift (ι := ι) ε)

lemma blockHom_val (g : E (R := R) (ι := ι)) : (blockHom (ι := ι) ε g).val = blockInclusion g.val :=
  UnorderedStabilizer.complementary_val ε g

lemma seed_augmentation (a : ℚ) :
    (H2FrameEdge.augmentation (Ω := ι ⊕ Fin 1) ε).hom ((seed (ι := ι) ε).hom a) = a := by
  change Frames.basis.repr (Frames.boundary _ (a • (b x₀).val)) ∅ = a
  rw [map_smul,Frames.frameBasis_val,base_singleton,Frames.basis_singleton,Frames.boundary_vertex]
  rw [←Frames.basis_empty,map_smul,Module.Basis.repr_self]
  simp

variable (hI : MatrixNilKernel ε.toRingHom) (hι : 12≤Fintype.card ι)

include hI hι in
lemma lift_homology_isIso (n : ℕ) : IsIso (RationalHomology.map (lift (ι := ι) ε) n) := by
  have hComplement := UnorderedStabilizer.complementary_homology_isIso (κ := Fin 1) ε hI (by omega : 5≤Fintype.card ι) n
  have hRelabel := RationalHomology.equiv_isIso (FrameStabilizer.stabilizerEquiv (ι := ι) (κ := Fin 1) ε).symm n
  erw [lift,RationalHomology.map_comp]
  exact IsIso.comp_isIso' hComplement hRelabel

include hI hι in
lemma seed_homology_isIso (n : ℕ) : IsIso (groupHomology.map (B := A) (S).subtype (seed (ι := ι) ε) n) :=
  MonomialTrivial.seed_homology_isIso x₀ A b (fixed (ι := ι) ε)
    (FrameStabilizer.transitive ε hI (by omega)) (FrameStabilizer.monomial ε) n

lemma composite (n : ℕ) : RationalHomology.map (blockHom (ι := ι) ε) n =
    RationalHomology.map (lift (ι := ι) ε) n ≫ groupHomology.map (B := A) (S).subtype (seed (ι := ι) ε) n ≫
      groupHomology.map (B := Rep.trivial ℚ G ℚ) (MonoidHom.id G) (H2FrameEdge.augmentation (Ω := ι ⊕ Fin 1) ε) n := by
  exact trivial_map_factorization (lift (ι := ι) ε) (S).subtype A (seed (ι := ι) ε)
    (H2FrameEdge.augmentation (Ω := ι ⊕ Fin 1) ε) (seed_augmentation ε) n

include hI hι in
lemma block_h2_isIso : IsIso (RationalHomology.map (blockHom (ι := ι) ε) 2) := by
  have hLift := lift_homology_isIso ε hI hι 2
  have hSeed := seed_homology_isIso ε hI hι 2
  have hAugmentation := H2FrameEdge.augmentation_isIso (Ω := ι ⊕ Fin 1) ε hI (by simpa using hι)
  rw [composite]
  exact IsIso.comp_isIso' hLift (IsIso.comp_isIso' hSeed hAugmentation)

end SingletonFrameEdge
end SourceBurnside.Stability

end

end OAI
