import Mathlib
import OAI.CategoryTheory.Thomason.StrictCategories

namespace OAI

/-! Directed Prisms. -/

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex

variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}}

structure PositiveAntihomotopy (F G : Hom K L) where
  map (p : ℕ) : K.Chain p →+ L.Chain (p+1)
  positive (p : ℕ) (x : K.Chain p) : x ∈ K.positive p → map p x ∈ L.positive (p+1)
  boundary_zero (x : K.Chain 0) : L.d 0 (map 0 x) = G.map 0 x - F.map 0 x
  boundary_succ (p : ℕ) (x : K.Chain (p+1)) :
    L.d (p+1) (map (p+1) x) = map p (K.d p x) +
      ((-1 : ℤ)^(p+1)) • (G.map (p+1) x - F.map (p+1) x)

namespace PositiveAntihomotopy

variable {F G : Hom K L} (h : PositiveAntihomotopy F G)

def cylinderMap : (p : ℕ) → K.cylinder.Chain p →+ L.Chain p
  | 0 =>
    { toFun := fun x => F.map 0 x.1 + G.map 0 x.2
      map_zero' := by simp
      map_add' := by intro x y; simp; abel }
  | p+1 =>
    { toFun := fun x => F.map (p+1) x.1 + G.map (p+1) x.2.1 + h.map p x.2.2
      map_zero' := by simp
      map_add' := by intro x y; simp; abel }

def cylinderHom : Hom K.cylinder L where
  map := h.cylinderMap
  map_d p x := by
    cases p with
    | zero =>
      dsimp [cylinder, cylinderMap, cylinderDifferential]
      simp only [map_add, map_sub, F.map_d, G.map_d, h.boundary_zero]
      abel
    | succ p =>
      dsimp [cylinder, cylinderMap, cylinderDifferential]
      simp only [map_add, map_sub, map_zsmul, smul_sub, F.map_d, G.map_d,
        h.boundary_succ]
      abel
  map_augmentation x := by
    dsimp [cylinderMap, cylinder]
    simp only [map_add, F.map_augmentation, G.map_augmentation]
  map_positive p x hx := by
    cases p with
    | zero =>
      exact (L.positive 0).add_mem
        (F.map_positive 0 _ hx.1) (G.map_positive 0 _ hx.2)
    | succ p =>
      exact (L.positive (p+1)).add_mem
        ((L.positive (p+1)).add_mem
          (F.map_positive (p+1) _ hx.1) (G.map_positive (p+1) _ hx.2.1))
        (h.positive p _ hx.2.2)

lemma cylinderHom_endpoint_false :
    Hom.comp (K.cylinderEndpoint false) h.cylinderHom = F := by
  ext p x
  cases p <;>
    dsimp [Hom.comp, cylinderEndpoint, cylinderEndpointMap, cylinderHom, cylinderMap] <;> simp

lemma cylinderHom_endpoint_true :
    Hom.comp (K.cylinderEndpoint true) h.cylinderHom = G := by
  ext p x
  cases p <;>
    dsimp [Hom.comp, cylinderEndpoint, cylinderEndpointMap, cylinderHom, cylinderMap] <;> simp

end PositiveAntihomotopy
end Thomason.DirectedComplex

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E]

lemma degreeSign_of_grade {k : ℕ} {c : Chains E} (hc : c ∈ grade (k+1)) :
    degreeSign c = ((-1 : ℤ)^k) • c := by
  classical
  rw [degreeSign, Finsupp.linearCombination_apply]
  change (∑ w ∈ c.support, c w • (((-1 : ℤ)^(w.val.length-1)) • bracket w.val)) = _
  calc
    _ = ∑ w ∈ c.support, ((-1 : ℤ)^k) • Finsupp.single w (c w) := by
      apply Finset.sum_congr rfl
      intro w hw
      have hl := (mem_grade_iff (k+1) c).mp hc w (Finsupp.mem_support_iff.mp hw)
      rw [hl, Nat.add_sub_cancel, bracket_of_pairwise w.property, smul_comm]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    _ = ((-1 : ℤ)^k) • c := by
      rw [← Finset.smul_sum]
      congr 1
      exact Finsupp.sum_single c

lemma prism_of_grade_zero {D : Type v} [PartialOrder D] (f g : E → D)
    {c : Chains E} (hc : c ∈ grade 0) : prism f g c = 0 := by
  classical
  rw [prism, Finsupp.linearCombination_apply, Finsupp.sum]
  apply Finset.sum_eq_zero
  intro w hw
  have hl := (mem_grade_iff 0 c).mp hc w (Finsupp.mem_support_iff.mp hw)
  have ht : w.val = [] := List.length_eq_zero_iff.mp hl
  simp [ht]

def gradedPrism {D : Type v} [PartialOrder D] (f g : E → D) (p : ℕ) :
    (complex E).Chain p →+ (complex D).Chain (p+1) where
  toFun c := ⟨prism f g c.val, prism_mem_grade f g c.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _x _y := Subtype.ext (map_add _ _ _)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.RelativePrismData

open NormalizedChains DirectedComplex

variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)

def antihomotopy : PositiveAntihomotopy (complexMap d.f) (complexMap d.g) where
  map := gradedPrism d.f d.g
  positive p x hx := prism_positive d.f d.g hx
  boundary_zero x := by
    apply Subtype.ext
    change boundary (prism d.f d.g x.val) = map d.g x.val - map d.f x.val
    rw [d.boundary_prism, degreeSign_of_grade x.property,
      prism_of_grade_zero d.f d.g (boundary_mem_grade x.property)]
    simp
  boundary_succ p x := by
    apply Subtype.ext
    change boundary (prism d.f d.g x.val) = prism d.f d.g (boundary x.val) +
      ((-1 : ℤ)^(p+1)) • (map d.g x.val - map d.f x.val)
    rw [d.boundary_prism, degreeSign_of_grade x.property]
    simp only [map_smul, smul_sub]
    abel

def cylinderChainMap : Hom (complex E).cylinder (complex E) :=
  d.antihomotopy.cylinderHom

lemma cylinderChainMap_endpoint_false :
    Hom.comp ((complex E).cylinderEndpoint false) d.cylinderChainMap = complexMap d.f :=
  d.antihomotopy.cylinderHom_endpoint_false

lemma cylinderChainMap_endpoint_true :
    Hom.comp ((complex E).cylinderEndpoint true) d.cylinderChainMap = complexMap d.g :=
  d.antihomotopy.cylinderHom_endpoint_true

def tableCylinder : OmegaCategory.Functor (complex E).cylinder.nu (complex E).nu :=
  d.cylinderChainMap.nu

end Thomason.RelativePrismData

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.Hom

variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {M : DirectedComplex.{w}}

def cylinderMap (F : Hom K L) : (p : ℕ) → K.cylinder.Chain p →+ L.cylinder.Chain p
  | 0 =>
    { toFun := fun x => (F.map 0 x.1, F.map 0 x.2)
      map_zero' := by simp
      map_add' := by intro x y; simp }
  | p+1 =>
    { toFun := fun x => (F.map (p+1) x.1, F.map (p+1) x.2.1, F.map p x.2.2)
      map_zero' := by simp
      map_add' := by intro x y; simp }

def cylinder (F : Hom K L) : Hom K.cylinder L.cylinder where
  map := F.cylinderMap
  map_d p x := by
    cases p <;> dsimp [cylinderMap, DirectedComplex.cylinder, cylinderDifferential] <;>
      simp only [map_add, map_sub, map_zsmul, F.map_d]
  map_augmentation x := by
    dsimp [cylinderMap, DirectedComplex.cylinder]
    rw [F.map_augmentation, F.map_augmentation]
  map_positive p x hx := by
    cases p with
    | zero => exact ⟨F.map_positive 0 _ hx.1, F.map_positive 0 _ hx.2⟩
    | succ p => exact ⟨F.map_positive (p+1) _ hx.1,
        F.map_positive (p+1) _ hx.2.1, F.map_positive p _ hx.2.2⟩

@[simp] lemma cylinder_id : (id K).cylinder = id K.cylinder := by
  ext p x
  cases p <;> rfl

lemma cylinder_comp (F : Hom K L) (G : Hom L M) :
    (comp F G).cylinder = comp F.cylinder G.cylinder := by
  ext p x
  cases p <;> rfl

lemma cylinder_endpoint (F : Hom K L) (b : Bool) :
    comp (K.cylinderEndpoint b) F.cylinder = comp F (L.cylinderEndpoint b) := by
  ext p x
  cases p <;> cases b <;>
    dsimp [comp, DirectedComplex.cylinderEndpoint, cylinderEndpointMap,
      cylinder, cylinderMap] <;> simp

lemma cylinder_projection (F : Hom K L) :
    comp F.cylinder L.cylinderProjection = comp K.cylinderProjection F := by
  ext p x
  cases p <;>
    dsimp [comp, DirectedComplex.cylinderProjection, cylinderProjectionMap,
      cylinder, cylinderMap] <;> simp

end Thomason.DirectedComplex.Hom

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

lemma map_prism {B : Type w} [PartialOrder B] (f g : E →o D)
    (hfg : ∀ e, f e ≤ g e) (a : D →o B) (c : Chains E) :
    map a (prism f g c) = prism (a ∘ f) (a ∘ g) c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih]
    congr 1
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul]
    congr 1
    have hl := l.property.imp fun h => le_of_lt h
    rw [prism_bracket _ _ hl, prism_bracket _ _ hl]
    rcases l with ⟨l, hs⟩
    dsimp at *
    cases l using List.reverseRecOn with
    | nil => simp [prismWord]
    | append_singleton l b =>
      rw [prismWord_append, prismWord_append]
      have hh : (l.map f ++ [f b, g b]).Pairwise (· ≤ ·) := by
        rw [List.pairwise_append]
        refine ⟨?_, by simpa using hfg b, ?_⟩
        · exact List.pairwise_map.mpr ((List.pairwise_append.mp hl).1.imp fun h => f.monotone h)
        · intro x hx y hy
          obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx
          have hwb : w ≤ b := (List.pairwise_append.mp hl).2.2 w hw b (by simp)
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl | rfl
          · exact f.monotone hwb
          · exact (f.monotone hwb).trans (hfg b)
      rw [map_bracket a hh]
      simp only [List.map_append, List.map_cons, List.map_nil, List.map_map,
        Function.comp_apply]

lemma prism_stationary_map {A : Set D} (d : RelativePrismData D A)
    (a : E →o D) (ha : ∀ e, a e ∈ A) (c : Chains E) :
    prism d.f d.g (map a c) = 0 := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, ih, add_zero]
    have hz : Finsupp.single l z = z • bracket l.val := by
      rw [bracket_of_pairwise l.property]
      simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hz]
    simp only [map_smul]
    have hl := l.property.imp fun h => le_of_lt h
    rw [map_bracket _ hl,
      prism_bracket _ _ (List.pairwise_map.mpr (hl.imp fun h => a.monotone h)),
      d.prism_stationary]
    · simp
    · intro x hx
      obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
      exact ha e

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.RelativePrismData

open DirectedComplex NormalizedChains

variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)

lemma cylinderChainMap_stationary {B : Type v} [PartialOrder B]
    (a : B →o E) (ha : ∀ b, a b ∈ A) :
    Hom.comp (complexMap a).cylinder d.cylinderChainMap =
      Hom.comp (complex B).cylinderProjection (complexMap (d.f.comp a)) := by
  have hag : d.g.comp a = d.f.comp a := by
    ext b
    exact (d.agree (a b) (ha b)).symm
  have hm (p : ℕ) (x : (complex B).Chain p) :
      (complexMap d.g).map p ((complexMap a).map p x) =
        (complexMap d.f).map p ((complexMap a).map p x) := by
    have he : Hom.comp (complexMap a) (complexMap d.g) =
        Hom.comp (complexMap a) (complexMap d.f) := by
      rw [← complexMap_comp, ← complexMap_comp, hag]
    exact congrArg (fun h => h.map p x) he
  have hf (p : ℕ) (x : (complex B).Chain p) :
      (complexMap (d.f.comp a)).map p x =
        (complexMap d.f).map p ((complexMap a).map p x) := by
    exact congrArg (fun h => h.map p x) (complexMap_comp a d.f)
  ext p x
  cases p with
  | zero =>
    change (complexMap d.f).map 0 ((complexMap a).map 0 x.1) +
      (complexMap d.g).map 0 ((complexMap a).map 0 x.2) =
      (complexMap (d.f.comp a)).map 0 (x.1 + x.2)
    rw [map_add, hf, hf, hm]
  | succ p =>
    change (complexMap d.f).map (p+1) ((complexMap a).map (p+1) x.1) +
      (complexMap d.g).map (p+1) ((complexMap a).map (p+1) x.2.1) +
      gradedPrism d.f d.g p ((complexMap a).map p x.2.2) =
      (complexMap (d.f.comp a)).map (p+1) (x.1 + x.2.1)
    have hh : gradedPrism d.f d.g p ((complexMap a).map p x.2.2) = 0 := by
      apply Subtype.ext
      exact prism_stationary_map d a ha x.2.2.val
    rw [hh, add_zero, map_add, hf, hf, hm]

lemma tableCylinder_stationary {B : Type v} [PartialOrder B]
    (a : B →o E) (ha : ∀ b, a b ∈ A) :
    OmegaCategory.Functor.comp (complexMap a).cylinder.nu d.tableCylinder =
      OmegaCategory.Functor.comp (complex B).cylinderProjection.nu
        (complexMap (d.f.comp a)).nu := by
  exact congrArg Hom.nu (d.cylinderChainMap_stationary a ha)

end Thomason.RelativePrismData

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.PositiveAntihomotopy

variable {J : DirectedComplex.{u}} {K : DirectedComplex.{v}} {L : DirectedComplex.{w}}

def precomp (a : Hom J K) {F G : Hom K L} (h : PositiveAntihomotopy F G) :
    PositiveAntihomotopy (Hom.comp a F) (Hom.comp a G) where
  map p := (h.map p).comp (a.map p)
  positive p x hx := h.positive p _ (a.map_positive p x hx)
  boundary_zero x := h.boundary_zero _
  boundary_succ p x := by
    dsimp [Hom.comp]
    rw [h.boundary_succ, ← a.map_d]

def postcomp {F G : Hom J K} (h : PositiveAntihomotopy F G) (a : Hom K L) :
    PositiveAntihomotopy (Hom.comp F a) (Hom.comp G a) where
  map p := (a.map (p+1)).comp (h.map p)
  positive p x hx := a.map_positive (p+1) _ (h.positive p x hx)
  boundary_zero x := by
    dsimp [Hom.comp]
    rw [← a.map_d, h.boundary_zero, map_sub]
  boundary_succ p x := by
    dsimp [Hom.comp]
    rw [← a.map_d, h.boundary_succ, map_add, map_zsmul, map_sub]

lemma precomp_cylinderHom (a : Hom J K) {F G : Hom K L}
    (h : PositiveAntihomotopy F G) :
    (h.precomp a).cylinderHom = Hom.comp a.cylinder h.cylinderHom := by
  ext p x
  cases p <;> rfl

lemma postcomp_cylinderHom {F G : Hom J K} (h : PositiveAntihomotopy F G)
    (a : Hom K L) :
    (h.postcomp a).cylinderHom = Hom.comp h.cylinderHom a := by
  ext p x
  cases p <;> dsimp [Hom.comp, cylinderHom, cylinderMap, postcomp] <;>
    simp only [map_add]

end Thomason.DirectedComplex.PositiveAntihomotopy

end

noncomputable section
universe u v w z


namespace Thomason.RelativePrismData

variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)

def simplexImage {m : ℕ} (σ : Fin (m+1) →o E) : Set E :=
  Set.range (d.f ∘ σ) ∪ Set.range (d.g ∘ σ)

lemma simplexImage_finite {m : ℕ} (σ : Fin (m+1) →o E) :
    (d.simplexImage σ).Finite :=
  (Set.finite_range _).union (Set.finite_range _)

lemma simplexImage_shape {m : ℕ} (σ : Fin (m+1) →o E) :
    d.simplexImage σ = Set.range (d.f ∘ σ) ∪ {d.g (σ (Fin.last m))} := by
  ext e
  refine ⟨?_, ?_⟩
  · rintro (he | ⟨i, rfl⟩)
    · exact Or.inl he
    · by_cases hi : σ i ∈ A
      · exact Or.inl ⟨i, d.agree (σ i) hi⟩
      · exact Or.inr (d.constant (σ i) hi (σ (Fin.last m)) (fun hh =>
          hi (d.lowerSet (σ.monotone (Fin.le_last i)) hh)))
  · rintro (he | he)
    · exact Or.inl he
    · exact Or.inr ⟨Fin.last m, he.symm⟩

lemma simplexImage_bounded {m : ℕ} (σ : Fin (m+1) →o E)
    {e : E} (he : e ∈ d.simplexImage σ) : e ≤ d.g (σ (Fin.last m)) := by
  rw [d.simplexImage_shape] at he
  rcases he with ⟨i, rfl⟩ | he
  · exact (d.f.monotone (σ.monotone (Fin.le_last i))).trans (d.below _)
  · exact le_of_eq he

lemma simplexImage_total {m : ℕ} (σ : Fin (m+1) →o E)
    {e e' : E} (he : e ∈ d.simplexImage σ) (he' : e' ∈ d.simplexImage σ) :
    e ≤ e' ∨ e' ≤ e := by
  rw [d.simplexImage_shape] at he he'
  rcases he with ⟨i, rfl⟩ | he
  · rcases he' with ⟨j, rfl⟩ | he'
    · exact (le_total i j).imp
        (fun h => d.f.monotone (σ.monotone h))
        (fun h => d.f.monotone (σ.monotone h))
    · exact Or.inl (he' ▸ (d.f.monotone (σ.monotone (Fin.le_last i))).trans (d.below _))
  · exact Or.inr (he ▸ d.simplexImage_bounded σ (by rw [d.simplexImage_shape]; exact he'))

noncomputable abbrev simplexImageLinearOrder {m : ℕ} (σ : Fin (m+1) →o E) :
    LinearOrder (d.simplexImage σ) := by
  classical
  exact {
    toPartialOrder := inferInstance
    le_total := fun x y => d.simplexImage_total σ x.property y.property
    toDecidableLE := Classical.decRel _ }

def simplexImageLeft {m : ℕ} (σ : Fin (m+1) →o E) : Fin (m+1) →o d.simplexImage σ where
  toFun i := ⟨d.f (σ i), Or.inl ⟨i, rfl⟩⟩
  monotone' _ _ h := d.f.monotone (σ.monotone h)

def simplexImageRight {m : ℕ} (σ : Fin (m+1) →o E) : Fin (m+1) →o d.simplexImage σ where
  toFun i := ⟨d.g (σ i), Or.inr ⟨i, rfl⟩⟩
  monotone' _ _ h := d.g.monotone (σ.monotone h)

def simplexImageMap {m q : ℕ} (σ : Fin (m+1) →o E) (α : Fin (q+1) →o Fin (m+1)) :
    d.simplexImage (σ.comp α) ↪o d.simplexImage σ where
  toFun x := ⟨x.val, by
    rcases x.property with ⟨i, hi⟩ | ⟨i, hi⟩
    · exact Or.inl ⟨α i, hi⟩
    · exact Or.inr ⟨α i, hi⟩⟩
  inj' _ _ h := Subtype.ext (congrArg (fun y : d.simplexImage σ => y.val) h)
  map_rel_iff' := Iff.rfl

end Thomason.RelativePrismData

end

noncomputable section
universe u v w z


namespace Thomason.NormalizedChains

variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]

def wordEmbedding (f : E ↪o D) : Word E ↪ Word D where
  toFun w := ⟨w.val.map f, List.pairwise_map.mpr (w.property.imp fun h => f.strictMono h)⟩
  inj' x y h := by
    apply Subtype.ext
    exact List.map_injective_iff.mpr f.injective (congrArg Subtype.val h)

lemma map_orderEmbedding (f : E ↪o D) (c : Chains E) :
    map f.toOrderHom c = Finsupp.mapDomain (wordEmbedding f) c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | @single_add l z c _ _ ih =>
    simp only [map_add, Finsupp.mapDomain_add, ih]
    congr 1
    rw [map, Finsupp.linearCombination_single, Finsupp.mapDomain_single]
    change z • bracket (wordEmbedding f l).val = Finsupp.single (wordEmbedding f l) z
    rw [bracket_of_pairwise (wordEmbedding f l).property]
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

lemma map_orderEmbedding_injective (f : E ↪o D) :
    Function.Injective (map f.toOrderHom) := by
  intro x y h
  apply Finsupp.mapDomain_injective (wordEmbedding f).injective
  simpa only [← map_orderEmbedding] using h

lemma complexMap_orderEmbedding_injective (f : E ↪o D) (p : ℕ) :
    Function.Injective ((complexMap f.toOrderHom).map p) := by
  intro x y h
  apply Subtype.ext
  exact map_orderEmbedding_injective f (congrArg Subtype.val h)

end Thomason.NormalizedChains

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.PositiveAntihomotopy

variable {J : DirectedComplex.{u}} {K : DirectedComplex.{v}} {L : DirectedComplex.{w}}

def lift (F G : Hom J K) (a : Hom K L)
    (ha : ∀ p, Function.Injective (a.map p)) {F' G' : Hom J L}
    (h : PositiveAntihomotopy F' G')
    (hf : ∀ p x, a.map p (F.map p x) = F'.map p x)
    (hg : ∀ p x, a.map p (G.map p x) = G'.map p x)
    (H : (p : ℕ) → J.Chain p →+ K.Chain (p+1))
    (Hpos : ∀ p x, x ∈ J.positive p → H p x ∈ K.positive (p+1))
    (Hmap : ∀ p x, a.map (p+1) (H p x) = h.map p x) :
    PositiveAntihomotopy F G where
  map := H
  positive := Hpos
  boundary_zero x := by
    apply ha 0
    rw [a.map_d, Hmap, h.boundary_zero, map_sub, hf, hg]
  boundary_succ p x := by
    apply ha (p+1)
    rw [a.map_d, Hmap, h.boundary_succ, map_add, Hmap, map_zsmul, map_sub, hf, hg]

end Thomason.DirectedComplex.PositiveAntihomotopy

end

noncomputable section
universe u v w z


namespace Thomason.RelativePrismData

open NormalizedChains DirectedComplex

variable {E : Type u} [PartialOrder E] {A : Set E} (d : RelativePrismData E A)

def simplexImageInclusion {m : ℕ} (σ : Fin (m+1) →o E) : d.simplexImage σ ↪o E :=
  OrderEmbedding.subtype _

def simplexAntihomotopy {m : ℕ} (σ : Fin (m+1) →o E) :
    PositiveAntihomotopy (complexMap (d.simplexImageLeft σ))
      (complexMap (d.simplexImageRight σ)) :=
  PositiveAntihomotopy.lift _ _ (complexMap (d.simplexImageInclusion σ).toOrderHom)
    (complexMap_orderEmbedding_injective (d.simplexImageInclusion σ))
    (d.antihomotopy.precomp (complexMap σ))
    (fun p x => by
      apply Subtype.ext
      change map (d.simplexImageInclusion σ).toOrderHom
        (map (d.simplexImageLeft σ) x.val) = map d.f (map σ x.val)
      simp only [← map_comp]
      rfl)
    (fun p x => by
      apply Subtype.ext
      change map (d.simplexImageInclusion σ).toOrderHom
        (map (d.simplexImageRight σ) x.val) = map d.g (map σ x.val)
      simp only [← map_comp]
      rfl)
    (gradedPrism (d.simplexImageLeft σ) (d.simplexImageRight σ))
    (fun _ _ hx => prism_positive _ _ hx)
    (fun p x => by
      apply Subtype.ext
      change map (d.simplexImageInclusion σ).toOrderHom
        (prism (d.simplexImageLeft σ) (d.simplexImageRight σ) x.val) =
        prism d.f d.g (map σ x.val)
      rw [map_prism _ _ (fun i => d.below (σ i)), prism_map]
      rfl)

def simplexCylinderChainMap {m : ℕ} (σ : Fin (m+1) →o E) :
    Hom (complex (Fin (m+1))).cylinder (complex (d.simplexImage σ)) :=
  (d.simplexAntihomotopy σ).cylinderHom

lemma simplexCylinderChainMap_inclusion {m : ℕ} (σ : Fin (m+1) →o E) :
    Hom.comp (d.simplexCylinderChainMap σ)
      (complexMap (d.simplexImageInclusion σ).toOrderHom) =
      Hom.comp (complexMap σ).cylinder d.cylinderChainMap := by
  ext p x
  cases p with
  | zero =>
    apply Subtype.ext
    change map _ (map _ x.1.val + map _ x.2.val) =
      map _ (map _ x.1.val) + map _ (map _ x.2.val)
    simp only [map_add, ← map_comp]
    rfl
  | succ p =>
    apply Subtype.ext
    change map _ (map _ x.1.val + map _ x.2.1.val + prism _ _ x.2.2.val) =
      map _ (map _ x.1.val) + map _ (map _ x.2.1.val) + prism _ _ (map _ x.2.2.val)
    simp only [map_add, ← map_comp]
    rw [map_prism _ _ (fun i => d.below (σ i)), prism_map]
    rfl

lemma simplexCylinderChainMap_naturality {m q : ℕ} (σ : Fin (m+1) →o E)
    (α : Fin (q+1) →o Fin (m+1)) :
    Hom.comp (d.simplexCylinderChainMap (σ.comp α))
      (complexMap (d.simplexImageMap σ α).toOrderHom) =
      Hom.comp (complexMap α).cylinder (d.simplexCylinderChainMap σ) := by
  ext p x
  apply complexMap_orderEmbedding_injective (d.simplexImageInclusion σ) p
  have hl := congrArg (fun h => h.map p x)
    (d.simplexCylinderChainMap_inclusion (σ.comp α))
  have hr := congrArg (fun h => h.map p ((complexMap α).cylinder.map p x))
    (d.simplexCylinderChainMap_inclusion σ)
  have he : Hom.comp (complexMap (d.simplexImageMap σ α).toOrderHom)
      (complexMap (d.simplexImageInclusion σ).toOrderHom) =
      complexMap (d.simplexImageInclusion (σ.comp α)).toOrderHom := by
    rw [← complexMap_comp]
    rfl
  have hc : Hom.comp (complexMap α).cylinder (complexMap σ).cylinder =
      (complexMap (σ.comp α)).cylinder := by
    rw [complexMap_comp, Hom.cylinder_comp]
  change (Hom.comp (complexMap (d.simplexImageMap σ α).toOrderHom)
      (complexMap (d.simplexImageInclusion σ).toOrderHom)).map p
        ((d.simplexCylinderChainMap (σ.comp α)).map p x) = _
  rw [he]
  dsimp only [Hom.comp, AddMonoidHom.comp_apply] at hl hr ⊢
  rw [hl, hr]
  exact congrArg (fun h => d.cylinderChainMap.map p (h.map p x)) hc.symm

end Thomason.RelativePrismData

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory

@[ext]
structure ThinCell (S : Type u) (r : S → S → Prop) where
  left : S
  right : S
  related : r left right

namespace ThinCell

variable {S : Type u} {r : S → S → Prop}
variable (hr : ∀ s, r s s) (ht : ∀ {s t v}, r s t → r t v → r s v)

def vertex (s : S) : ThinCell S r := ⟨s, s, hr s⟩

def source : ℕ → ThinCell S r → ThinCell S r
  | 0, x => vertex hr x.left
  | _+1, x => x

def target : ℕ → ThinCell S r → ThinCell S r
  | 0, x => vertex hr x.right
  | _+1, x => x

def comp : (k : ℕ) → (x y : ThinCell S r) → target hr k x = source hr k y → ThinCell S r
  | 0, x, y, h => ⟨x.left, y.right, ht x.related (by
      have he : x.right = y.left := congrArg ThinCell.left h
      exact he ▸ y.related)⟩
  | _+1, x, _, _ => x

@[simp] lemma source_zero (x : ThinCell S r) : source hr 0 x = vertex hr x.left := rfl
@[simp] lemma source_succ (k : ℕ) (x : ThinCell S r) : source hr (k+1) x = x := rfl
@[simp] lemma target_zero (x : ThinCell S r) : target hr 0 x = vertex hr x.right := rfl
@[simp] lemma target_succ (k : ℕ) (x : ThinCell S r) : target hr (k+1) x = x := rfl
@[simp] lemma vertex_left (s : S) : (vertex hr s).left = s := rfl
@[simp] lemma vertex_right (s : S) : (vertex hr s).right = s := rfl
@[simp] lemma comp_zero_left (x y : ThinCell S r) (h) : (comp hr ht 0 x y h).left = x.left := rfl
@[simp] lemma comp_zero_right (x y : ThinCell S r) (h) : (comp hr ht 0 x y h).right = y.right := rfl
@[simp] lemma comp_succ (k : ℕ) (x y : ThinCell S r) (h) : comp hr ht (k+1) x y h = x := rfl

end ThinCell

def thin {S : Type u} (r : S → S → Prop)
    (hr : ∀ s, r s s) (ht : ∀ {s t v}, r s t → r t v → r s v) : OmegaCategory.{u} where
  Cell := ThinCell S r
  source := ThinCell.source hr
  target := ThinCell.target hr
  source_source i j x := by
    cases i <;> cases j <;> simp [ThinCell.source, ThinCell.vertex]
  target_target i j x := by
    cases i <;> cases j <;> simp [ThinCell.target, ThinCell.vertex]
  source_target i j x := by
    cases i <;> cases j <;> simp [ThinCell.source, ThinCell.target, ThinCell.vertex]
  target_source i j x := by
    cases i <;> cases j <;> simp [ThinCell.source, ThinCell.target, ThinCell.vertex]
  comp := ThinCell.comp hr ht
  source_comp_le i k hik x y h := by
    cases k with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      rfl
    | succ k => rfl
  target_comp_le i k hik x y h := by
    cases k with
    | zero =>
      have hi : i = 0 := by omega
      subst i
      rfl
    | succ k => exact congrArg (ThinCell.target hr i) h
  source_comp_gt i k hki x y h hs := by
    cases i with
    | zero => omega
    | succ i => rfl
  target_comp_gt i k hki x y h hs := by
    cases i with
    | zero => omega
    | succ i => rfl
  unit_left k x h := by
    cases k with
    | zero => ext <;> rfl
    | succ k => rfl
  unit_right k x h := by
    cases k with
    | zero => ext <;> rfl
    | succ k => rfl
  assoc k x y z hxy hyz hxy_z hx_yz := by
    cases k with
    | zero => ext <;> rfl
    | succ k => rfl
  interchange k l hkl a b c d hab hcd hac hbd hab_cd hac_bd := by
    cases l with
    | zero => omega
    | succ l => rfl
  finite_dimension x := ⟨1, rfl⟩

def interval : OmegaCategory.{u} := thin (fun a b : ULift.{u} (Fin 2) => a.down ≤ b.down)
  (fun _ => le_rfl) (fun h h' => h.trans h')

def chaotic (S : Type u) : OmegaCategory.{u} := thin (fun _ _ : S => True)
  (fun _ => True.intro) (fun _ _ => True.intro)

lemma thin_truncated {S : Type u} (r : S → S → Prop)
    (hr : ∀ s, r s s) (ht : ∀ {s t v}, r s t → r t v → r s v) :
    (thin r hr ht).IsTruncated 1 := fun _ => rfl

end Thomason.OmegaCategory

end

end OAI
