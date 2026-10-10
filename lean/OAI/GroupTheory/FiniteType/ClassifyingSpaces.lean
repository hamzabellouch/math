import Mathlib
import OAI.GroupTheory.FiniteType.AscendingTorus

namespace OAI

noncomputable section
namespace SimpleFInftyOvergroups
universe u
                                                                               
lemma HasTypeFInfty.of_equiv {G H : Type u} [Group G] [Group H]
    (e : G ≃* H) (hG : HasTypeFInfty G) : HasTypeFInfty H := by
  obtain ⟨X,t,cw,hT,hC,hFT,x,⟨eG⟩,E,tE,p,hp,hs,hE⟩ := hG
  exact ⟨X,t,cw,hT,hC,hFT,x,⟨e.symm.trans eG⟩,E,tE,p,hp,hs,hE⟩

theorem ascending_hnn_geometric
    {U P : Type} [Group U] [Group P] [Group.IsFinitelyPresented P]
    (a : U →* P) (b : P →* U) (hf : Function.Injective (b.comp a))
    (F₂ : ListChains.IdempotentSplittings U (ZMod 2) (b.comp a))
    (F₃ : ListChains.IdempotentSplittings U (ZMod 3) (b.comp a)) :
    HasTypeFInfty (AscendingHNN.Torus (b.comp a) hf) := by
  let := AscendingHNN.finitelyPresented_of_factorization (b.comp a) hf a b rfl
  have : Group.FG P := by
    obtain ⟨n,φ,hφ,_⟩ := (inferInstance : Group.IsFinitelyPresented P).out
    exact Group.fg_of_surjective hφ
  apply geometric_product_criterion
  intro I n hn
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 2 m]
  change CategoryTheory.Limits.IsZero
    (groupHomology (RegularProduct.rep (AscendingHNN.Torus (b.comp a) hf) I) (m+2))
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y => (AscendingHNN.regular_product_homology_vanishes a b hf F₂ F₃ I m x).trans
    (AscendingHNN.regular_product_homology_vanishes a b hf F₂ F₃ I m y).symm⟩

theorem ascending_torus_geometric
    {U P : Type} [Group U] [Group P] [Group.IsFinitelyPresented P]
    (f : U →* U) (hf : Function.Injective f)
    (a : U →* P) (b : P →* U) (heq : f = b.comp a)
    (F₂ : ListChains.IdempotentSplittings U (ZMod 2) f)
    (F₃ : ListChains.IdempotentSplittings U (ZMod 3) f) :
    HasTypeFInfty (AscendingTorus.Torus f) := by
  subst f
  exact HasTypeFInfty.of_equiv (AscendingHNN.presentationEquiv (b.comp a) hf)
    (ascending_hnn_geometric a b hf F₂ F₃)
end SimpleFInftyOvergroups

namespace FiniteExtension
universe u
variable {L : Type u} [Group L] (K : Subgroup L) [K.Normal]
abbrev Q := L ⧸ K
def pi : L →* Q K := QuotientGroup.mk' K

def sectionMap (c : Q K) : L := by
  classical
  exact if c = 1 then 1 else Classical.choose (QuotientGroup.mk'_surjective K c)
@[simp] lemma section_one : sectionMap K 1 = 1 := by simp [sectionMap]
@[simp] lemma pi_section (c : Q K) : pi K (sectionMap K c) = c := by
  by_cases h : c=1
  · simp [h]
  · simpa [sectionMap,h,pi] using Classical.choose_spec (QuotientGroup.mk'_surjective K c)
@[simp] lemma pi_coe (k : K) : pi K (k : L) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr k.property

def factor (x : L) : K := ⟨x * (sectionMap K (pi K x))⁻¹, by
  apply (QuotientGroup.eq_one_iff _).mp
  change pi K (x * (sectionMap K (pi K x))⁻¹)=1
  simp⟩
def twist (c : Q K) : K →* K :=
  ((MulAut.conj (sectionMap K c)).toMonoidHom.comp K.subtype).codRestrict K
    (fun k => (inferInstance : K.Normal).conj_mem k k.property (sectionMap K c))
def cocycle (c d : Q K) : K := factor K (sectionMap K c * sectionMap K d)
@[simp] lemma factor_one : factor K 1 = 1 := by ext; simp [factor]
@[simp] lemma factor_coe (k : K) : factor K (k : L) = k := by ext; simp [factor]
@[simp] lemma factor_section (c : Q K) : factor K (sectionMap K c) = 1 := by
  ext; simp [factor]
@[simp] lemma twist_coe (c : Q K) (k : K) :
    ((twist K c k : K) : L) = sectionMap K c * k * (sectionMap K c)⁻¹ := rfl
@[simp] lemma cocycle_coe (c d : Q K) :
    ((cocycle K c d : K) : L) =
      sectionMap K c * sectionMap K d * (sectionMap K (c*d))⁻¹ := by simp [cocycle,factor]
lemma factor_mul (x y : L) : factor K (x*y) =
    factor K x * twist K (pi K x) (factor K y) * cocycle K (pi K x) (pi K y) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul,twist_coe,cocycle_coe,factor,map_mul]
  group

abbrev Pre := Monoid.Coprod K (FreeGroup (Q K))
def inK : K →* Pre K := Monoid.Coprod.inl
def letter (c : Q K) : Pre K := Monoid.Coprod.inr (FreeGroup.of c)
def mulRel (c d : Q K) : Pre K :=
  letter K c * letter K d * (inK K (cocycle K c d) * letter K (c*d))⁻¹
def conjRel (c : Q K) (k : K) : Pre K :=
  letter K c * inK K k * (inK K (twist K c k) * letter K c)⁻¹

def rels (S : Set K) : Set (Pre K) := {letter K 1} ∪
    Set.range (fun p : Q K × Q K => mulRel K p.1 p.2) ∪
    (fun p : Q K × K => conjRel K p.1 p.2) '' (Set.univ ×ˢ S)
abbrev N (S : Set K) := Subgroup.normalClosure (rels K S)
abbrev Presented (S : Set K) := Pre K ⧸ N K S
def quot (S : Set K) : Pre K →* Presented K S := QuotientGroup.mk' (N K S)
def incl (S : Set K) : K →* Presented K S := (quot K S).comp (inK K)
def t (S : Set K) (c : Q K) : Presented K S := quot K S (letter K c)

lemma rel_eq_one (S : Set K) {r : Pre K} (hr : r ∈ rels K S) : quot K S r=1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure hr)
@[simp] lemma t_one (S : Set K) : t K S 1 = 1 :=
  rel_eq_one K S (Or.inl (Or.inl rfl))
lemma t_mul (S : Set K) (c d : Q K) :
    t K S c * t K S d = incl K S (cocycle K c d) * t K S (c*d) := by
  have h := rel_eq_one K S (Or.inl (Or.inr ⟨(c,d),rfl⟩))
  simpa only [mulRel,map_mul,map_inv,mul_inv_eq_one,t,incl,MonoidHom.comp_apply] using h
lemma t_conj_gen (S : Set K) (c : Q K) (k : K) (hk : k∈S) :
    t K S c * incl K S k = incl K S (twist K c k) * t K S c := by
  have h := rel_eq_one K S (Or.inr ⟨(c,k),⟨Set.mem_univ _,hk⟩,rfl⟩)
  simpa only [conjRel,map_mul,map_inv,mul_inv_eq_one,t,incl,MonoidHom.comp_apply] using h
lemma t_conj (S : Set K) (hS : Subgroup.closure S = ⊤) (c : Q K) (k : K) :
    t K S c * incl K S k = incl K S (twist K c k) * t K S c := by
  have h : (MulAut.conj (t K S c)).toMonoidHom.comp (incl K S) =
      (incl K S).comp (twist K c) := by
    apply MonoidHom.eq_of_eqOn_dense hS
    intro k hk
    change t K S c * incl K S k * (t K S c)⁻¹ = incl K S (twist K c k)
    rw [t_conj_gen K S c k hk,mul_inv_cancel_right]
  have hh := DFunLike.congr_fun h k
  change t K S c * incl K S k * (t K S c)⁻¹ = incl K S (twist K c k) at hh
  exact (mul_inv_eq_iff_eq_mul).mp hh

def retract (S : Set K) (hS : Subgroup.closure S = ⊤) : L →* Presented K S where
  toFun x := incl K S (factor K x) * t K S (pi K x)
  map_one' := by simp
  map_mul' x y := by
    simp only [factor_mul,map_mul]
    rw [show incl K S (factor K x) * t K S (pi K x) *
        (incl K S (factor K y) * t K S (pi K y)) =
      incl K S (factor K x) * (t K S (pi K x) * incl K S (factor K y)) *
        t K S (pi K y) by group]
    rw [t_conj K S hS]
    simp only [mul_assoc,← t_mul K S]

@[simp] lemma retract_coe (S : Set K) (hS : Subgroup.closure S = ⊤) (k : K) :
    retract K S hS (k : L) = incl K S k := by simp [retract]
@[simp] lemma retract_section (S : Set K) (hS : Subgroup.closure S = ⊤) (c : Q K) :
    retract K S hS (sectionMap K c) = t K S c := by simp [retract]

def evaluatePre : Pre K →* L := Monoid.Coprod.lift K.subtype (FreeGroup.lift (sectionMap K))
@[simp] lemma evaluatePre_inK (k : K) : evaluatePre K (inK K k) = k := by
  simp [evaluatePre,inK]
@[simp] lemma evaluatePre_letter (c : Q K) : evaluatePre K (letter K c) = sectionMap K c := by
  simp [evaluatePre,letter]
lemma rels_ker (S : Set K) : rels K S ⊆ (evaluatePre K).ker := by
  rintro x ((h|⟨⟨c,d⟩,rfl⟩)|⟨⟨c,k⟩,_,rfl⟩)
  · rcases h with rfl
    change evaluatePre K (letter K 1)=1
    simp
  · change evaluatePre K (mulRel K c d)=1
    simp only [mulRel,map_mul,map_inv,evaluatePre_letter,evaluatePre_inK,
      cocycle_coe]
    group
  · change evaluatePre K (conjRel K c k)=1
    simp only [conjRel,map_mul,map_inv,evaluatePre_letter,evaluatePre_inK,
      twist_coe]
    group

def evaluate (S : Set K) : Presented K S →* L :=
  QuotientGroup.lift (N K S) (evaluatePre K) (Subgroup.normalClosure_le_normal (rels_ker K S))
@[simp] lemma evaluate_quot (S : Set K) (x : Pre K) :
    evaluate K S (quot K S x) = evaluatePre K x := rfl
@[simp] lemma evaluate_incl (S : Set K) (k : K) : evaluate K S (incl K S k) = k := by
  change evaluatePre K (inK K k)=k
  simp
@[simp] lemma evaluate_t (S : Set K) (c : Q K) :
    evaluate K S (t K S c) = sectionMap K c := by
  change evaluatePre K (letter K c)=sectionMap K c
  simp
lemma evaluate_retract (S : Set K) (hS : Subgroup.closure S = ⊤) (x : L) :
    evaluate K S (retract K S hS x) = x := by simp [retract,factor]
lemma retract_evaluate (S : Set K) (hS : Subgroup.closure S = ⊤) (x : Presented K S) :
    retract K S hS (evaluate K S x) = x := by
  obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (N K S) x
  change ((retract K S hS).comp (evaluatePre K)) y = quot K S y
  have h : (retract K S hS).comp (evaluatePre K) = quot K S := by
    apply Monoid.Coprod.hom_ext
    · ext k
      change retract K S hS (evaluatePre K (inK K k)) = incl K S k
      simp
    · apply FreeGroup.ext_hom
      intro c
      change retract K S hS (evaluatePre K (letter K c)) = t K S c
      simp
  exact DFunLike.congr_fun h y

def presentationEquiv (S : Set K) (hS : Subgroup.closure S = ⊤) : Presented K S ≃* L :=
  { evaluate K S with
    invFun := retract K S hS
    left_inv := retract_evaluate K S hS
    right_inv := evaluate_retract K S hS }

lemma rels_finite [Finite (Q K)] (S : Set K) (hS : S.Finite) : (rels K S).Finite :=
  ((Set.finite_singleton _).union (Set.finite_range _)).union
    ((Set.finite_univ.prod hS).image _)

theorem finitelyPresented [Finite (Q K)] [Group.IsFinitelyPresented K] :
    Group.IsFinitelyPresented L := by
  obtain ⟨n,φ,hφ,_⟩ := (inferInstance : Group.IsFinitelyPresented K).out
  have : Group.FG K := Group.fg_of_surjective hφ
  obtain ⟨S,hS,hfin⟩ := Group.fg_iff.mp (inferInstance : Group.FG K)
  have : Group.IsFinitelyPresented (Presented K S) :=
    Group.IsFinitelyPresented.quotient (N K S) ⟨rels K S,rels_finite K S hfin,rfl⟩
  exact Group.IsFinitelyPresented.equiv (presentationEquiv K S hS)
end FiniteExtension

end

end OAI
