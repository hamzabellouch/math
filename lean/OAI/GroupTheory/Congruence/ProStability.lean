import OAI.Combinatorics.Coboundary.Realization
import OAI.GroupTheory.Congruence.Stabilization

namespace OAI

/-!
Positive exactness, coefficient change, Bockstein groups, integral pro-stability support, and F2 reductions.
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
open Filter

namespace CoboundaryExpanders.Construction
open Elementary
variable (p n : ℕ) [Fact p.Prime]

theorem U_constantCoeff (g : Matrix.SpecialLinearGroup (Fin (n+1)) (R p))
    (hg : g ∈ U p (n+1)) (i j : Fin (n+1)) (hji : j ≤ i) :
    (g i j).constantCoeff = if i=j then 1 else 0 := by
  change IsUpperUnitriangular _ (evalZero p (n+1) g) at hg
  have h := hg i j hji
  change Polynomial.eval 0 (g i j) = (1 : Matrix (Fin (n+1)) (Fin (n+1)) (ZMod p)) i j at h
  change (g i j).coeff 0 = _
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simpa only [Matrix.one_apply] using h

theorem cycleGenerated_eq_U (hn : 2 ≤ n) :
    cycleGenerated p n (by omega) = U p (n+1) := by
  apply le_antisymm (cycleGenerated_le_U p n (by omega))
  intro g hg
  apply polynomial_iwahori_mem_of_roots (U p (n+1)) (cycleGenerated p n (by omega))
    (cycleGenerated_le_U p n (by omega)) (U_constantCoeff p n) _ g hg
  intro i j hij c hc
  by_cases hlt : i < j
  · exact upper_polynomial_mem_generated p n hn hlt c
  · have hjlt : j < i := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)
    have hzero := hc hjlt
    have hx : Polynomial.X ∣ c := Polynomial.X_dvd_iff.mpr (by simpa using hzero)
    obtain ⟨f,rfl⟩ := hx
    exact X_polynomial_mem_generated p n hn hij f

theorem infinite_locals_generate (hn : 2 ≤ n) :
    Subgroup.closure (⋃ i, (uLocalGroup p n (by omega) i : Set (U p (n+1)))) = ⊤ := by
  let K : Subgroup (U p (n+1)) :=
    Subgroup.closure (⋃ i, (uLocalGroup p n (by omega) i : Set (U p (n+1))))
  have hgen : cycleGenerated p n (by omega) ≤ K.map (U p (n+1)).subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    obtain ⟨cut,hcut⟩ : ∃ cut : Fin (n+1), cut ≠ j := by
      by_cases hj : j=0
      · refine ⟨Fin.last n,?_⟩
        rw [hj]
        intro h
        have := congrArg Fin.val h
        simp only [Fin.val_last,Fin.val_zero] at this
        omega
      · exact ⟨0,fun h => hj h.symm⟩
    let u : U p (n+1) := ⟨cycleRoot p n (by omega) j,cycleRoot_mem_U p n (by omega) j⟩
    have hu : u ∈ uLocalGroup p n (by omega) cut :=
      Subgroup.subset_closure ⟨j,Ne.symm hcut,rfl⟩
    exact ⟨u,Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨cut,hu⟩),rfl⟩
  apply top_le_iff.mp
  intro u _
  have hu : u.val ∈ cycleGenerated p n (by omega) := by rw [cycleGenerated_eq_U p n hn]; exact u.property
  obtain ⟨v,hv,hvu⟩ := hgen hu
  have hvu' : v=u := Subtype.ext hvu
  exact hvu' ▸ hv

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders.TypedCosetFaces
open InfiniteChains
variable {G I : Type} [Group G] [DecidableEq I] (H : I → Subgroup G)

def singletonFace (g : G) (i : I) : (complex H).Face 1 :=
  ⟨{vertex H g i}, ⟨g,{i},by simp [face]⟩, Finset.card_singleton _⟩

def pairFace (g : G) (i j : I) (hij : i ≠ j) : (complex H).Face 2 :=
  ⟨{vertex H g i,vertex H g j}, ⟨g,{i,j},by simp [face]⟩, by
    have hv : vertex H g i ≠ vertex H g j := fun h => hij (vertex_injective H g h)
    simp [hv]⟩

lemma boundary_pair (g : G) (i j : I) (hij : i ≠ j) :
    (complex H).boundary 1 (Finsupp.single (pairFace H g i j hij) 1) =
      Finsupp.single (singletonFace H g i) 1 + Finsupp.single (singletonFace H g j) 1 := by
  apply (complex H).embed_injective 1
  change ((complex H).embed 1).comp ((complex H).boundary 1) _ = _
  rw [(complex H).embed_boundary]
  simp only [LinearMap.comp_apply, CoboundaryExpanders.InfiniteChains.Complex.embed_single, map_add, rawBoundary_single]
  have hv : vertex H g i ≠ vertex H g j := fun h => hij (vertex_injective H g h)
  simp [pairFace,singletonFace,hv,Finset.erase_insert_of_ne,add_comm]

abbrev Components := (complex H).Chains 1 ⧸ LinearMap.range ((complex H).boundary 1)

def component (g : G) (i : I) : Components H :=
  (LinearMap.range ((complex H).boundary 1)).mkQ (Finsupp.single (singletonFace H g i) 1)

lemma component_same_chamber (g : G) (i j : I) : component H g i = component H g j := by
  by_cases hij : i = j
  · subst j; rfl
  have hh : component H g i + component H g j = 0 := by
    rw [component,component,← map_add,← boundary_pair H g i j hij]
    exact Submodule.Quotient.mk_eq_zero _ |>.mpr ⟨_,rfl⟩
  have hc : component H g j + component H g j = 0 := by
    have htwo : (1:k) + 1 = 0 := rfl
    calc
      _ = ((1:k)+1) • component H g j := by rw [add_smul,one_smul]
      _ = 0 := by rw [htwo,zero_smul]
  calc
    component H g i = (component H g i + component H g j) + component H g j := by rw [add_assoc,hc,add_zero]
    _ = component H g j := by rw [hh,zero_add]

lemma component_mul_local (g h : G) (i : I) (hh : h ∈ H i) :
    component H g i = component H (g*h) i := by
  have hv : vertex H g i = vertex H (g*h) i := by
    apply congrArg (Sigma.mk i)
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    simpa using hh
  unfold component
  congr 2
  apply Subtype.ext
  exact congrArg (fun v => ({v} : Finset (Vertex H))) hv

lemma component_mul_closure (h : G)
    (hh : h ∈ Subgroup.closure (⋃ i, (H i : Set G))) :
    ∀ g i j, component H g i = component H (g*h) j := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp hx
    intro g i j
    exact (component_same_chamber H g i a).trans
      ((component_mul_local H g x a ha).trans (component_same_chamber H (g*x) a j))
  | one =>
    intro g i j
    simpa using component_same_chamber H g i j
  | mul a _ _ _ ia ib =>
    intro g i j
    exact (ia g i i).trans (by simpa [mul_assoc] using ib (g*a) i j)
  | inv a _ ia =>
    intro g i j
    simpa [mul_assoc] using (ia (g*a⁻¹) j i).symm

lemma component_constant (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤)
    (g h : G) (i j : I) : component H g i = component H h j := by
  have := component_mul_closure H (g⁻¹*h) (by rw [hgen]; trivial) g i j
  simpa using this

lemma singletonFace_surjective : Function.Surjective (fun gi : G × I => singletonFace H gi.1 gi.2) := by
  rintro ⟨s,⟨g,A,rfl⟩,hc⟩
  have hc' : A.card = 1 := by simpa using hc
  obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp hc'
  exact ⟨⟨g,i⟩,Subtype.ext (by simp [singletonFace,face])⟩

theorem augmentation_exact_of_generation [Nonempty I]
    (hgen : Subgroup.closure (⋃ i, (H i : Set G)) = ⊤) :
    Function.Exact ((complex H).boundary 1) ((complex H).sumCoefficients 1) := by
  let i : I := Classical.choice ‹Nonempty I›
  let π := (LinearMap.range ((complex H).boundary 1)).mkQ
  have hπ (c : (complex H).Chains 1) :
      π c = ((complex H).sumCoefficients 1 c) • component H 1 i := by
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add,hc,hd,add_smul]
    | single s r =>
      obtain ⟨⟨g,j⟩,rfl⟩ := singletonFace_surjective H s
      have hs : Finsupp.single (singletonFace H g j) r = r • Finsupp.single (singletonFace H g j) 1 := by simp
      rw [hs,map_smul]
      change r • component H g j = _
      rw [component_constant H hgen g 1 j i]
      simp
  intro c
  constructor
  · intro hc
    have hz : π c = 0 := by rw [hπ,hc,zero_smul]
    exact (Submodule.Quotient.mk_eq_zero _).mp hz
  · rintro ⟨b,rfl⟩
    exact LinearMap.congr_fun (complex H).augmentation_boundary b

end CoboundaryExpanders.TypedCosetFaces

namespace CoboundaryExpanders.Construction
variable (p n : ℕ) [Fact p.Prime]

theorem infinite_augmentation_exact (hn : 2 ≤ n) :
    Function.Exact ((infiniteCosetComplex p n (by omega)).boundary 1)
      ((infiniteCosetComplex p n (by omega)).sumCoefficients 1) :=
  TypedCosetFaces.augmentation_exact_of_generation _ (infinite_locals_generate p n hn)

theorem oppositionAcyclic_iff_positive (hn : 2 ≤ n) :
    OppositionAcyclic p n (by omega) ↔
      ∀ j : ℕ, 0 < j → j < n-1 →
        (infiniteCosetComplex p n (by omega)).chainComplex.ExactAt j := by
  exact ⟨And.right, fun h => ⟨infinite_augmentation_exact p n hn,h⟩⟩

end CoboundaryExpanders.Construction

namespace CoboundaryExpanders
open Construction

theorem reduction_to_positive_open_inputs
    (hinputs : ∀ d : ℕ, ∀ hd : 3 ≤ d, ∃ p : ℕ, ∃ hp : p.Prime, Odd p ∧
      letI : Fact p.Prime := ⟨hp⟩
      (∀ j : ℕ, 0 < j → j < 2*d-1 →
        (infiniteCosetComplex p (2*d) (by omega)).chainComplex.ExactAt j) ∧
      (∀ i : ℕ, 0 < i → i < d →
        CongruenceCokernels.ProZero p (2*d-1) i ∧ CongruenceCokernels.ProZero p (2*d) i) ∧
      UniformCosystolic p (2*d) (by omega)) : MainStatement := by
  apply reduction_to_three_open_inputs
  intro d hd
  obtain ⟨p,hp,ho,hL,hz,hq⟩ := hinputs d hd
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨p,hp,ho,(oppositionAcyclic_iff_positive p (2*d) (by omega)).mpr hL,hz,hq⟩

end CoboundaryExpanders

namespace CoboundaryExpanders.ProCoefficientChange

structure Tower where
  V : ℕ → Type
  ab : ∀ m, AddCommGroup (V m)
  mod : ∀ m, Module ℤ (V m)
  trans : ∀ m n, m ≤ n → V n →ₗ[ℤ] V m
  trans_self : ∀ m h, trans m m h = LinearMap.id
  trans_comp : ∀ m n r hmn hnr, (trans m n hmn).comp (trans n r hnr) = trans m r (hmn.trans hnr)
attribute [instance] Tower.ab Tower.mod

structure Map (A B : Tower) where
  f : ∀ m, A.V m →ₗ[ℤ] B.V m
  natural : ∀ m n h, (B.trans m n h).comp (f n) = (f m).comp (A.trans m n h)

namespace Map
variable {A B : Tower} (f : Map A B)

def ProSurjective : Prop := ∀ m, ∃ n, ∃ h : m ≤ n,
  ∀ y : B.V n, ∃ x : A.V m, f.f m x = B.trans m n h y

def ProInjective : Prop := ∀ m, ∃ n, ∃ h : m ≤ n,
  ∀ x : A.V n, f.f n x = 0 → A.trans m n h x = 0

lemma natural_apply (m n : ℕ) (h : m ≤ n) (x : A.V n) :
    B.trans m n h (f.f n x) = f.f m (A.trans m n h x) :=
  LinearMap.congr_fun (f.natural m n h) x
end Map

lemma Tower.trans_apply (A : Tower) (m n r : ℕ) (hmn : m ≤ n) (hnr : n ≤ r)
    (x : A.V r) : A.trans m n hmn (A.trans n r hnr x) = A.trans m r (hmn.trans hnr) x :=
  LinearMap.congr_fun (A.trans_comp m n r hmn hnr) x

structure Bockstein (I M J : Tower) where
  red : Map I M
  delta : Map M J
  exact_red : ∀ m, Function.Exact (red.f m) (delta.f m)
  exact_two : ∀ m, Function.Exact (delta.f m) (fun x : J.V m => x+x)

theorem proSurjective_of_bockstein
    {I₁ M₁ J₁ I₂ M₂ J₂ : Tower}
    (B₁ : Bockstein I₁ M₁ J₁) (B₂ : Bockstein I₂ M₂ J₂)
    (i : Map I₁ I₂) (f : Map M₁ M₂) (j : Map J₁ J₂)
    (hred : ∀ m, (f.f m).comp (B₁.red.f m) = (B₂.red.f m).comp (i.f m))
    (hdelta : ∀ m, (j.f m).comp (B₁.delta.f m) = (B₂.delta.f m).comp (f.f m))
    (hi : i.ProSurjective) (hj : j.ProSurjective) (hk : j.ProInjective) :
    f.ProSurjective := by
  have hδ (m : ℕ) (y : M₁.V m) : j.f m (B₁.delta.f m y) = B₂.delta.f m (f.f m y) :=
    LinearMap.congr_fun (hdelta m) y
  have hr (m : ℕ) (v : I₁.V m) : f.f m (B₁.red.f m v) = B₂.red.f m (i.f m v) :=
    LinearMap.congr_fun (hred m) v
  intro m
  obtain ⟨a,hma,ha⟩ := hi m
  obtain ⟨b,hab,hb⟩ := hk a
  obtain ⟨c,hbc,hc⟩ := hj b
  refine ⟨c,hma.trans (hab.trans hbc),?_⟩
  intro z
  obtain ⟨x,hx⟩ := hc (B₂.delta.f c z)
  have hx2 : j.f b (x+x) = 0 := by
    rw [map_add,hx,← map_add]
    have hz : B₂.delta.f c z + B₂.delta.f c z = 0 := (B₂.exact_two c _).2 ⟨z,rfl⟩
    rw [hz,map_zero]
  have hx2' : J₁.trans a b hab x + J₁.trans a b hab x = 0 := by
    rw [← map_add]
    exact hb _ hx2
  obtain ⟨y,hy⟩ := (B₁.exact_two a _).1 hx2'
  let za := M₂.trans a c (hab.trans hbc) z
  have he : B₂.delta.f a (za - f.f a y) = 0 := by
    rw [map_sub,sub_eq_zero]
    rw [← hδ a y]
    change B₂.delta.f a (M₂.trans a c (hab.trans hbc) z) = j.f a (B₁.delta.f a y)
    rw [hy,← j.natural_apply a b hab, hx]
    rw [J₂.trans_apply,← B₂.delta.natural_apply]
  obtain ⟨w,hw⟩ := (B₂.exact_red a _).1 he
  obtain ⟨v,hv⟩ := ha w
  refine ⟨M₁.trans m a hma y + B₁.red.f m v,?_⟩
  rw [map_add,hr m v,hv]
  rw [← f.natural_apply m a hma,← B₂.red.natural_apply m a hma,hw]
  rw [map_sub,add_sub_cancel]
  exact M₂.trans_apply m a c hma (hab.trans hbc) z

end CoboundaryExpanders.ProCoefficientChange

namespace CoboundaryExpanders.BocksteinGroups

section
variable (G : Type) [Group G]

attribute [local instance 2000] Rep.hV2

abbrev ZRep := Rep.trivial ℤ G ℤ
abbrev FRep := Rep.trivial ℤ G (ZMod 2)

def twice : ZRep G ⟶ ZRep G :=
  (Rep.trivialFunctor ℤ G).map (ModuleCat.ofHom (LinearMap.id + LinearMap.id : ℤ →ₗ[ℤ] ℤ))
def red : ZRep G ⟶ FRep G :=
  (Rep.trivialFunctor ℤ G).map (ModuleCat.ofHom (Int.castAddHom (ZMod 2)).toIntLinearMap)

def sequence : ShortComplex (Rep ℤ G) := ShortComplex.mk (twice G) (red G) (by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change ((x+x : ℤ) : ZMod 2) = 0
  simp [Int.cast_add,CharTwo.add_self_eq_zero])

lemma sequence_exact : (sequence G).ShortExact where
  exact := by
    apply ((sequence G).exact_map_iff_of_faithful (forget₂ (Rep ℤ G) (ModuleCat ℤ))).mp
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    change Function.Exact (fun x : ℤ => x+x) (fun x : ℤ => (x : ZMod 2))
    intro x
    change (x : ZMod 2) = 0 ↔ ∃ y : ℤ, y+y=x
    simpa only [even_iff_exists_two_mul, two_mul, eq_comm] using (ZMod.intCast_eq_zero_iff_even (n := x))
  mono_f := (Rep.mono_iff_injective _).mpr (by
    change Function.Injective (fun x : ℤ => x+x)
    intro x y h
    dsimp only at h
    omega)
  epi_g := (Rep.epi_iff_surjective _).mpr (by
    change Function.Surjective (fun x : ℤ => (x : ZMod 2))
    exact ZMod.intCast_surjective)

abbrev HZ (j : ℕ) := groupHomology (ZRep G) j
abbrev HF (j : ℕ) := groupHomology (FRep G) j

def reduce (j : ℕ) : HZ G j ⟶ HF G j := (groupHomology.functor ℤ G j).map (red G)
def delta (j : ℕ) : HF G (j+1) ⟶ HZ G j := groupHomology.δ (sequence_exact G) (j+1) j rfl

lemma exact_reduce_delta (j : ℕ) : Function.Exact (reduce G (j+1)) (delta G j) := by
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (groupHomology.mapShortComplex₃_exact (sequence_exact G) (i:=j+1) (j:=j) rfl)

lemma exact_delta_twice (j : ℕ) : Function.Exact (delta G j) (fun x : HZ G j => x+x) := by
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
    (groupHomology.mapShortComplex₁_exact (sequence_exact G) (i:=j+1) (j:=j) rfl)
  change Function.Exact (delta G j) ((groupHomology.functor ℤ G j).map (twice G)) at he
  have hc : groupHomology.chainsMap (MonoidHom.id G) (twice G) =
      𝟙 (groupHomology.inhomogeneousChains (ZRep G)) + 𝟙 _ := by
    apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext
    intro a
    simp only [LinearMap.coe_comp,Function.comp_apply,Finsupp.lsingle_apply]
    rw [groupHomology.chainsMap_f_single]
    change Finsupp.single x (a+a) = Finsupp.single x a + Finsupp.single x a
    exact Finsupp.single_add x a a
  have ht : (groupHomology.functor ℤ G j).map (twice G) = 𝟙 _ + 𝟙 _ := by
    change HomologicalComplex.homologyMap _ _ = _
    rw [hc,HomologicalComplex.homologyMap_add,HomologicalComplex.homologyMap_id]
    rfl
  rw [ht] at he
  exact he

end

attribute [local instance 2000] Rep.hV2
variable {G H K : Type} [Group G] [Group H] [Group K]
variable (A : Type) [AddCommGroup A] [Module ℤ A]

def coeff (f : G →* H) : Rep.trivial ℤ G A ⟶ Rep.res f (Rep.trivial ℤ H A) :=
  𝟙 (Rep.trivial ℤ G A)

def chainMap (f : G →* H) :
    groupHomology.inhomogeneousChains (Rep.trivial ℤ G A) ⟶
      groupHomology.inhomogeneousChains (Rep.trivial ℤ H A) :=
  groupHomology.chainsMap f (coeff A f)

def homMap (f : G →* H) (j : ℕ) :
    groupHomology (Rep.trivial ℤ G A) j ⟶ groupHomology (Rep.trivial ℤ H A) j :=
  groupHomology.map f (coeff A f) j

lemma homMap_id (j : ℕ) : homMap A (MonoidHom.id G) j = 𝟙 _ := groupHomology.map_id (A := Rep.trivial ℤ G A) j

lemma homMap_comp (f : G →* H) (g : H →* K) (j : ℕ) :
    homMap A (g.comp f) j = homMap A f j ≫ homMap A g j := by
  unfold homMap
  rw [← groupHomology.map_comp]
  exact groupHomology.map_congr rfl rfl j

variable {A} {B : Type} [AddCommGroup B] [Module ℤ B]

lemma chain_coeff_natural (f : G →* H) (c : A →ₗ[ℤ] B) :
    groupHomology.chainsMap (A := Rep.trivial ℤ G A) (B := Rep.trivial ℤ G B) (MonoidHom.id G)
        ((Rep.trivialFunctor ℤ G).map (ModuleCat.ofHom c)) ≫ chainMap B f =
      chainMap A f ≫ groupHomology.chainsMap (A := Rep.trivial ℤ H A) (B := Rep.trivial ℤ H B) (MonoidHom.id H)
        ((Rep.trivialFunctor ℤ H).map (ModuleCat.ofHom c)) := by
  unfold chainMap
  rw [← groupHomology.chainsMap_comp,← groupHomology.chainsMap_comp]
  exact groupHomology.chainsMap_congr rfl rfl

lemma hom_coeff_natural (f : G →* H) (c : A →ₗ[ℤ] B) (j : ℕ) :
    (groupHomology.functor ℤ G j).map ((Rep.trivialFunctor ℤ G).map (ModuleCat.ofHom c)) ≫ homMap B f j =
      homMap A f j ≫ (groupHomology.functor ℤ H j).map ((Rep.trivialFunctor ℤ H).map (ModuleCat.ofHom c)) := by
  have he := congrArg (fun t => HomologicalComplex.homologyMap t j) (chain_coeff_natural f c)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  exact he

def sequenceMap (f : G →* H) :
    (sequence G).map (groupHomology.chainsFunctor ℤ G) ⟶
      (sequence H).map (groupHomology.chainsFunctor ℤ H) where
  τ₁ := chainMap ℤ f
  τ₂ := chainMap ℤ f
  τ₃ := chainMap (ZMod 2) f
  comm₁₂ := by
    change chainMap ℤ f ≫ groupHomology.chainsMap (MonoidHom.id H) (twice H) =
      groupHomology.chainsMap (MonoidHom.id G) (twice G) ≫ chainMap ℤ f
    exact (chain_coeff_natural f (LinearMap.id+LinearMap.id : ℤ →ₗ[ℤ] ℤ)).symm
  comm₂₃ := by
    change chainMap ℤ f ≫ groupHomology.chainsMap (MonoidHom.id H) (red H) =
      groupHomology.chainsMap (MonoidHom.id G) (red G) ≫ chainMap (ZMod 2) f
    exact (chain_coeff_natural f (Int.castAddHom (ZMod 2)).toIntLinearMap).symm

lemma delta_natural (f : G →* H) (j : ℕ) :
    delta G j ≫ homMap ℤ f j = homMap (ZMod 2) f (j+1) ≫ delta H j :=
  HomologicalComplex.HomologySequence.δ_naturality (sequenceMap f)
    (groupHomology.map_chainsFunctor_shortExact (sequence_exact G))
    (groupHomology.map_chainsFunctor_shortExact (sequence_exact H)) (j+1) j rfl

lemma reduce_natural (f : G →* H) (j : ℕ) :
    reduce G j ≫ homMap (ZMod 2) f j = homMap ℤ f j ≫ reduce H j :=
  hom_coeff_natural f (Int.castAddHom (ZMod 2)).toIntLinearMap j

end CoboundaryExpanders.BocksteinGroups

namespace CoboundaryExpanders.GroupProStability
open ProCoefficientChange BocksteinGroups
attribute [local instance 2000] Rep.hV2
attribute [local instance 3000] ModuleCat.isModule

structure Groups where
  G : ℕ → Type
  grp : ∀ m, Group (G m)
  trans : ∀ m n, m ≤ n → G n →* G m
  trans_self : ∀ m h, trans m m h = MonoidHom.id _
  trans_comp : ∀ m n r hmn hnr, (trans m n hmn).comp (trans n r hnr) = trans m r (hmn.trans hnr)
attribute [instance] Groups.grp

structure Hom (G H : Groups) where
  f : ∀ m, G.G m →* H.G m
  natural : ∀ m n h, (H.trans m n h).comp (f n) = (f m).comp (G.trans m n h)

variable (A : Type) [AddCommGroup A] [Module ℤ A]

def tower (G : Groups) (j : ℕ) : Tower where
  V m := groupHomology (Rep.trivial ℤ (G.G m) A) j
  ab _ := inferInstance
  mod _ := inferInstance
  trans m n h := (homMap A (G.trans m n h) j).hom
  trans_self m h := by rw [G.trans_self,homMap_id]; rfl
  trans_comp m n r hmn hnr := by
    rw [← ModuleCat.hom_comp, ← homMap_comp,G.trans_comp]

variable {G H : Groups}

def map (f : Hom G H) (j : ℕ) : Map (tower A G j) (tower A H j) where
  f m := (homMap A (f.f m) j).hom
  natural m n h := by
    change (homMap A (H.trans m n h) j).hom.comp (homMap A (f.f n) j).hom =
      (homMap A (f.f m) j).hom.comp (homMap A (G.trans m n h) j).hom
    rw [← ModuleCat.hom_comp,← ModuleCat.hom_comp,← homMap_comp,← homMap_comp,f.natural]

def redMap (G : Groups) (j : ℕ) : Map (tower ℤ G j) (tower (ZMod 2) G j) where
  f m := (reduce (G.G m) j).hom
  natural m n h := congrArg ModuleCat.Hom.hom (reduce_natural (G.trans m n h) j)

def deltaMap (G : Groups) (j : ℕ) : Map (tower (ZMod 2) G (j+1)) (tower ℤ G j) where
  f m := (delta (G.G m) j).hom
  natural m n h := congrArg ModuleCat.Hom.hom (delta_natural (G.trans m n h) j)

def bockstein (G : Groups) (j : ℕ) :
    Bockstein (tower ℤ G (j+1)) (tower (ZMod 2) G (j+1)) (tower ℤ G j) where
  red := redMap G (j+1)
  delta := deltaMap G j
  exact_red m := exact_reduce_delta (G.G m) j
  exact_two m := exact_delta_twice (G.G m) j

theorem modTwo_proSurjective (f : Hom G H) (j : ℕ)
    (hi : (map ℤ f (j+1)).ProSurjective)
    (hj : (map ℤ f j).ProSurjective) (hk : (map ℤ f j).ProInjective) :
    (map (ZMod 2) f (j+1)).ProSurjective := by
  apply proSurjective_of_bockstein (bockstein G j) (bockstein H j)
    (map ℤ f (j+1)) (map (ZMod 2) f (j+1)) (map ℤ f j) _ _ hi hj hk
  · intro m
    exact congrArg ModuleCat.Hom.hom (reduce_natural (f.f m) (j+1))
  · intro m
    exact congrArg ModuleCat.Hom.hom (delta_natural (f.f m) j)

end CoboundaryExpanders.GroupProStability

namespace CoboundaryExpanders.IntegralProStability
open Construction Blocks GroupProStability ProCoefficientChange
attribute [local instance 2000] Rep.hV2
attribute [local instance 3000] ModuleCat.isModule

def groups (p a : ℕ) : Groups where
  G m := Gamma p a (m+1)
  grp _ := inferInstance
  trans m n h := Subgroup.inclusion (gamma_antitone p a (Nat.add_le_add_right h 1))
  trans_self m h := by ext x; rfl
  trans_comp m n r hmn hnr := by ext x; rfl

def stabilization (p a : ℕ) : Hom (groups p a) (groups p (a+1)) where
  f m := gammaStabilization p a 1 (m+1)
  natural m n h := CongruenceCokernels.group_natural p a (m+1) (n+1) (Nat.add_le_add_right h 1)

def ProIso (p a j : ℕ) : Prop :=
  (GroupProStability.map ℤ (stabilization p a) j).ProSurjective ∧
  (GroupProStability.map ℤ (stabilization p a) j).ProInjective

def IntegralStability (p : ℕ) : Prop :=
  ∀ j a : ℕ, 2*j+1 ≤ a → ProIso p a j

theorem modTwo_proSurjective (p a j : ℕ)
    (hj : ProIso p a j) (hs : ProIso p a (j+1)) :
    (GroupProStability.map (ZMod 2) (stabilization p a) (j+1)).ProSurjective :=
  GroupProStability.modTwo_proSurjective (stabilization p a) j hs.1 hj.1 hj.2

end CoboundaryExpanders.IntegralProStability

namespace CoboundaryExpanders.HomologyScalars
variable (G : Type) [Group G]
attribute [local instance 2000] Rep.hV2
attribute [local instance 3000] ModuleCat.isModule
abbrev SC := ModuleCat.restrictScalars (Int.castRingHom (ZMod 2))
abbrev ZC := groupHomology.inhomogeneousChains (Rep.trivial ℤ G (ZMod 2))
abbrev FC := groupHomology.inhomogeneousChains (Rep.trivial (ZMod 2) G (ZMod 2))
abbrev RC := (SC.mapHomologicalComplex (ComplexShape.down ℕ)).obj (FC G)

def degreeAddEquiv (i : ℕ) : (ZC G).X i ≃+ (RC G).X i where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl

def degreeIso (i : ℕ) : (ZC G).X i ≅ (RC G).X i :=
  (degreeAddEquiv G i).toIntLinearEquiv.toModuleIso

lemma single_compare (j : ℕ) (x : Fin (j+1) → G) (a : ZMod 2) :
    groupHomology.inhomogeneousChains.d (Rep.trivial (ZMod 2) G (ZMod 2)) j (Finsupp.single x a) =
    groupHomology.inhomogeneousChains.d (Rep.trivial ℤ G (ZMod 2)) j (Finsupp.single x a) := by
  calc
    _ = Finsupp.single (fun i : Fin j => x i.succ) a +
        ∑ i : Fin (j+1), (-1 : ZMod 2) ^ (i.val+1) •
          (Finsupp.single (Fin.contractNth i (· * ·) x) a : (Fin j → G) →₀ ZMod 2) :=
      groupHomology.inhomogeneousChains.d_single (A := Rep.trivial (ZMod 2) G (ZMod 2)) j x a
    _ = Finsupp.single (fun i : Fin j => x i.succ) a +
        ∑ i : Fin (j+1), (-1 : ℤ) ^ (i.val+1) •
          (Finsupp.single (Fin.contractNth i (· * ·) x) a : (Fin j → G) →₀ ZMod 2) := by
      apply congrArg (fun z : (Fin j → G) →₀ ZMod 2 => Finsupp.single (fun i : Fin j => x i.succ) a + z)
      apply Finset.sum_congr rfl
      intro i _
      rw [← Int.cast_smul_eq_zsmul (ZMod 2)]
      simp
    _ = _ := (groupHomology.inhomogeneousChains.d_single (A := Rep.trivial ℤ G (ZMod 2)) j x a).symm

lemma differential (j : ℕ) :
    (degreeIso G (j+1)).hom ≫ (RC G).d (j+1) j =
      (ZC G).d (j+1) j ≫ (degreeIso G j).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (FC G).d (j+1) j z = (ZC G).d (j+1) j z
  rw [groupHomology.inhomogeneousChains.d_def,groupHomology.inhomogeneousChains.d_def]
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | single x a => exact single_compare G j x a

def chainIso : ZC G ≅ RC G :=
  HomologicalComplex.Hom.isoOfComponents (degreeIso G) (by
    intro i j hij
    have he : j+1=i := hij
    subst i
    exact differential G j)

def homologyIso (j : ℕ) :
    groupHomology (Rep.trivial ℤ G (ZMod 2)) j ≅
      SC.obj (groupHomology (Rep.trivial (ZMod 2) G (ZMod 2)) j) :=
  (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) j).mapIso (chainIso G) ≪≫
    ((FC G).sc j).mapHomologyIso SC

variable {G} {H : Type} [Group H]

def coeffZ (f : G →* H) : Rep.trivial ℤ G (ZMod 2) ⟶ Rep.res f (Rep.trivial ℤ H (ZMod 2)) := 𝟙 _
def coeffF (f : G →* H) : Rep.trivial (ZMod 2) G (ZMod 2) ⟶ Rep.res f (Rep.trivial (ZMod 2) H (ZMod 2)) := 𝟙 _
def mapZ (f : G →* H) : ZC G ⟶ ZC H := groupHomology.chainsMap f (coeffZ f)
def mapF (f : G →* H) : FC G ⟶ FC H := groupHomology.chainsMap f (coeffF f)

lemma chain_natural (f : G →* H) :
    mapZ f ≫ (chainIso H).hom = (chainIso G).hom ≫
      (SC.mapHomologicalComplex (ComplexShape.down ℕ)).map (mapF f) := by
  apply HomologicalComplex.Hom.ext
  funext i
  change (mapZ f).f i ≫ (degreeIso H i).hom =
    (degreeIso G i).hom ≫ SC.map ((mapF f).f i)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using Finsupp.induction_linear with
  | zero =>
    change (mapZ f).f i 0 = (mapF f).f i 0
    exact (ModuleCat.Hom.hom ((mapZ f).f i)).map_zero.trans
      (ModuleCat.Hom.hom ((mapF f).f i)).map_zero.symm
  | add x y hx hy => simp only [map_add,hx,hy]
  | single x a =>
    change (groupHomology.chainsMap f (coeffZ f)).f i (Finsupp.single x a) =
      (groupHomology.chainsMap f (coeffF f)).f i (Finsupp.single x a)
    rfl

lemma homology_natural (f : G →* H) (j : ℕ) :
    groupHomology.map f (coeffZ f) j ≫ (homologyIso H j).hom =
      (homologyIso G j).hom ≫ SC.map (groupHomology.map f (coeffF f) j) := by
  let eG : (RC G).homology j ≅
      SC.obj (groupHomology (Rep.trivial (ZMod 2) G (ZMod 2)) j) :=
    ((FC G).sc j).mapHomologyIso SC
  let eH : (RC H).homology j ≅
      SC.obj (groupHomology (Rep.trivial (ZMod 2) H (ZMod 2)) j) :=
    ((FC H).sc j).mapHomologyIso SC
  change HomologicalComplex.homologyMap (mapZ f) j ≫
      (HomologicalComplex.homologyMap (chainIso H).hom j ≫ eH.hom) =
    (HomologicalComplex.homologyMap (chainIso G).hom j ≫ eG.hom) ≫ _
  rw [← Category.assoc,← HomologicalComplex.homologyMap_comp,chain_natural,
    HomologicalComplex.homologyMap_comp,Category.assoc,Category.assoc]
  congr 1
  exact ShortComplex.mapHomologyIso_hom_naturality ((HomologicalComplex.shortComplexFunctor (ModuleCat (ZMod 2)) (ComplexShape.down ℕ) j).map (mapF f)) SC

end CoboundaryExpanders.HomologyScalars

namespace CoboundaryExpanders.IntegralProStability
open CategoryTheory Construction Blocks
attribute [local instance 2000] Rep.hV2
attribute [local instance 3000] ModuleCat.isModule

private lemma natural_apply {G H : Type} [Group G] [Group H]
    (f : G →* H) (j : ℕ)
    (x : groupHomology (Rep.trivial ℤ G (ZMod 2)) j) :
    (HomologyScalars.homologyIso H j).hom (BocksteinGroups.homMap (ZMod 2) f j x) =
      Actions.induced (k := ZMod 2) f j ((HomologyScalars.homologyIso G j).hom x) := by
  exact congrArg (fun g => g x) (HomologyScalars.homology_natural f j)

private lemma moduleIso_right_inv {X Y : ModuleCat ℤ} (e : X ≅ Y) (y : Y) :
    e.hom (e.inv y) = y :=
  congrArg (fun f : Y ⟶ Y => f y) e.inv_hom_id

private lemma natural_lift {A B D : Type} [Group A] [Group B] [Group D]
    (f : A →* B) (g : D →* B) (j : ℕ)
    (x : groupHomology (Rep.trivial ℤ A (ZMod 2)) j)
    (z : groupHomology (Rep.trivial (ZMod 2) D (ZMod 2)) j)
    (hx : BocksteinGroups.homMap (ZMod 2) f j x =
      BocksteinGroups.homMap (ZMod 2) g j ((HomologyScalars.homologyIso D j).inv z)) :
    Actions.induced (k := ZMod 2) f j ((HomologyScalars.homologyIso A j).hom x) =
      Actions.induced (k := ZMod 2) g j z := by
  refine (natural_apply f j x).symm.trans ?_
  refine (congrArg (fun y : groupHomology (Rep.trivial ℤ B (ZMod 2)) j =>
    (HomologyScalars.homologyIso B j).hom y) hx).trans ?_
  refine (natural_apply g j _).trans ?_
  exact congrArg (fun y : groupHomology (Rep.trivial (ZMod 2) D (ZMod 2)) j =>
    Actions.induced (k := ZMod 2) g j y)
    (moduleIso_right_inv (HomologyScalars.homologyIso D j) z)

theorem proZero_of_integral (p a j : ℕ)
    (hj : ProIso p a j) (hs : ProIso p a (j+1)) :
    CongruenceCokernels.ProZero p a (j+1) := by
  intro m hm
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show m ≠ 0 by omega)
  obtain ⟨n,hmn,h⟩ := modTwo_proSurjective p a j hj hs m
  refine ⟨n+1, Nat.add_le_add_right hmn 1, ?_⟩
  apply LinearMap.ext
  intro q
  obtain ⟨z,rfl⟩ := Submodule.Quotient.mk_surjective _ q
  change Submodule.Quotient.mk (CongruenceCokernels.transition p (a+1) (m+1) (n+1) (j+1) _ z) = 0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  obtain ⟨x,hx⟩ := h ((HomologyScalars.homologyIso (Gamma p (a+1) (n+1)) (j+1)).inv z)
  refine ⟨(HomologyScalars.homologyIso (Gamma p a (m+1)) (j+1)).hom x, ?_⟩
  exact natural_lift (gammaStabilization p a 1 (m+1))
    (Subgroup.inclusion (gamma_antitone p (a+1) (Nat.add_le_add_right hmn 1)))
    (j+1) x z hx


theorem proZero_of_stability (p a i : ℕ) (hi : 0 < i) (ha : 2*i+1 ≤ a)
    (hst : IntegralStability p) : CongruenceCokernels.ProZero p a i := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show i ≠ 0 by omega)
  exact proZero_of_integral p a j (hst j a (by omega)) (hst (j+1) a ha)

end CoboundaryExpanders.IntegralProStability

namespace CoboundaryExpanders
open Construction

theorem reduction_to_opposition_integral_stability_and_OVB
    (hinputs : ∀ d : ℕ, ∀ hd : 3 ≤ d, ∃ p : ℕ, ∃ hp : p.Prime, Odd p ∧
      letI : Fact p.Prime := ⟨hp⟩
      (∀ j : ℕ, 0 < j → j < 2*d-1 →
        (infiniteCosetComplex p (2*d) (by omega)).chainComplex.ExactAt j) ∧
      IntegralProStability.IntegralStability p ∧
      UniformCosystolic p (2*d) (by omega)) :
    MainStatement := by
  apply reduction_to_positive_open_inputs
  intro d hd
  obtain ⟨p,hp,ho,hL,hs,hq⟩ := hinputs d hd
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨p,hp,ho,hL,?_,hq⟩
  intro i hi hid
  exact ⟨IntegralProStability.proZero_of_stability p (2*d-1) i hi (by omega) hs,
    IntegralProStability.proZero_of_stability p (2*d) i hi (by omega) hs⟩

end CoboundaryExpanders

namespace CoboundaryExpanders.BocksteinGroups
open CategoryTheory
attribute [local instance 2000] Rep.hV2
attribute [local instance 3000] ModuleCat.isModule
variable {G H : Type} [Group G] [Group H]

lemma homMap_zero_eq (f : G →* H) :
    homMap ℤ f 0 = (groupHomology.H0IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).hom ≫
      (groupHomology.H0IsoOfIsTrivial (Rep.trivial ℤ H ℤ)).inv := by
  rw [← cancel_epi (groupHomology.H0IsoOfIsTrivial (Rep.trivial ℤ G ℤ)).inv]
  rw [Iso.inv_hom_id_assoc]
  simp only [groupHomology.H0IsoOfIsTrivial_inv_eq_π,
    homMap, groupHomology.H0π_comp_map]
  rfl

lemma homMap_zero_bijective (f : G →* H) : Function.Bijective (homMap ℤ f 0) := by
  rw [homMap_zero_eq]
  exact ConcreteCategory.bijective_of_isIso _

end CoboundaryExpanders.BocksteinGroups

namespace CoboundaryExpanders.IntegralProStability
open CategoryTheory
attribute [local instance 2000] Rep.hV2
attribute [local instance 3000] ModuleCat.isModule

theorem proIso_zero (p a : ℕ) : ProIso p a 0 := by
  constructor
  · intro m
    refine ⟨m,le_rfl,?_⟩
    intro y
    obtain ⟨x,hx⟩ := (BocksteinGroups.homMap_zero_bijective
      (Blocks.gammaStabilization p a 1 (m+1))).surjective y
    refine ⟨x,?_⟩
    rw [ProCoefficientChange.Tower.trans_self]
    exact hx
  · intro m
    refine ⟨m,le_rfl,?_⟩
    intro x hx
    have he : x = 0 := (BocksteinGroups.homMap_zero_bijective
      (Blocks.gammaStabilization p a 1 (m+1))).injective (hx.trans (map_zero _).symm)
    rw [he,map_zero]

theorem integralStability_iff_positive (p : ℕ) : IntegralStability p ↔
    ∀ j a : ℕ, 0 < j → 2*j+1 ≤ a → ProIso p a j := by
  constructor
  · intro h j a _ ha
    exact h j a ha
  · intro h j a ha
    cases j with
    | zero => exact proIso_zero p a
    | succ j => exact h (j+1) a (by omega) ha

end CoboundaryExpanders.IntegralProStability

namespace CoboundaryExpanders
open Construction

theorem reduction_to_positive_literature_inputs
    (hinputs : ∀ d : ℕ, ∀ hd : 3 ≤ d, ∃ p : ℕ, ∃ hp : p.Prime, Odd p ∧
      letI : Fact p.Prime := ⟨hp⟩
      (∀ j : ℕ, 0 < j → j < 2*d-1 →
        (infiniteCosetComplex p (2*d) (by omega)).chainComplex.ExactAt j) ∧
      (∀ j a : ℕ, 0 < j → 2*j+1 ≤ a → IntegralProStability.ProIso p a j) ∧
      UniformCosystolic p (2*d) (by omega)) : MainStatement := by
  apply reduction_to_opposition_integral_stability_and_OVB
  intro d hd
  obtain ⟨p,hp,ho,hL,hs,hq⟩ := hinputs d hd
  let : Fact p.Prime := ⟨hp⟩
  exact ⟨p,hp,ho,hL,(IntegralProStability.integralStability_iff_positive p).mpr hs,hq⟩

end CoboundaryExpanders

end

end OAI
