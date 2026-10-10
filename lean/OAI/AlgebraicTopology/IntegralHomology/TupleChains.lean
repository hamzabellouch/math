import OAI.AlgebraicTopology.IntegralHomology.SmallChains
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI

noncomputable section

namespace Kaplansky

/-! Tuple chains, subdivision, chain maps, and support control. -/

section
open CategoryTheory Limits AlgebraicTopology Simplicial

section

/-- Ordered tuples, with deletion and repetition of vertices. -/
def tupleSSet (E : Type) : SSet.{0} where
  obj n := Fin (n.unop.len + 1) → E
  map f := ↾fun v => v ∘ f.unop.toOrderHom

abbrev tupleChains (E : Type) := (tupleSSet E).chainComplex (ModuleCat.of ℤ ℤ)
abbrev tupleGen {E : Type} {n : ℕ} (v : Fin (n+1) → E) :
    ModuleCat.of ℤ ℤ ⟶ (tupleChains E).X n := (tupleSSet E).ιChainComplex v

/-- Maps from tuple chains are determined by their values on tuple generators. -/
theorem tupleChains_hom_ext {E : Type} {n : ℕ} {T : ModuleCat.{0} ℤ}
    {f g : (tupleChains E).X n ⟶ T}
    (h : ∀ v : Fin (n+1) → E, tupleGen v ≫ f = tupleGen v ≫ g) : f = g :=
  SSet.chainComplex_hom_ext h

@[reassoc]
theorem tupleGen_d {E : Type} {n : ℕ} (v : Fin (n+2) → E) :
    tupleGen v ≫ (tupleChains E).d (n+1) n =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • tupleGen (v ∘ i.succAbove) := by
  exact SSet.ιChainComplex_d (tupleSSet E) (ModuleCat.of ℤ ℤ) v

/-- Prepending a fixed vertex, extended linearly on actual free chains. -/
def tupleCone {E : Type} (p : E) (n : ℕ) :
    (tupleChains E).X n ⟶ (tupleChains E).X (n+1) :=
  Sigma.desc (fun v => tupleGen (Fin.cons p v))

@[reassoc (attr := simp)]
theorem tupleGen_cone {E : Type} (p : E) {n : ℕ} (v : Fin (n+1) → E) :
    tupleGen v ≫ tupleCone p n = tupleGen (Fin.cons p v) := by
  exact Sigma.ι_comp_desc _ _

/-- Augmentation of zero-chains. -/
def tupleAugmentation (E : Type) : (tupleChains E).X 0 ⟶ ModuleCat.of ℤ ℤ :=
  Sigma.desc (fun _ => 𝟙 _)

@[reassoc (attr := simp)]
theorem tupleGen_augmentation {E : Type} (v : Fin 1 → E) :
    tupleGen v ≫ tupleAugmentation E = 𝟙 _ := by
  exact Sigma.ι_comp_desc _ _

@[reassoc (attr := simp)]
theorem tuple_d_augmentation (E : Type) :
    (tupleChains E).d 1 0 ≫ tupleAugmentation E = 0 := by
  apply tupleChains_hom_ext
  intro v
  rw [← Category.assoc, tupleGen_d]
  simp [Fin.sum_univ_two]

@[reassoc]
theorem tupleCone_d_zero {E : Type} (p : E) :
    tupleCone p 0 ≫ (tupleChains E).d 1 0 =
      𝟙 _ - tupleAugmentation E ≫ tupleGen (fun _ : Fin 1 => p) := by
  apply tupleChains_hom_ext
  intro v
  rw [← Category.assoc, tupleGen_cone, tupleGen_d]
  have hzero : Fin.cons p v ∘ (0 : Fin 2).succAbove = v := by ext i; simp
  have hone : Fin.cons p v ∘ (1 : Fin 2).succAbove = (fun _ : Fin 1 => p) := by
    ext i
    fin_cases i
    rfl
  change (∑ i : Fin 2, (-1 : ℤ)^i.val • tupleGen (Fin.cons p v ∘ i.succAbove)) = tupleGen v ≫ _
  simp only [Fin.sum_univ_two, hzero, hone, Fin.val_zero, pow_zero, one_smul,
    Fin.val_one, pow_one, neg_smul, Category.comp_id,
    tupleGen_augmentation_assoc, sub_eq_add_neg, Preadditive.comp_add, Preadditive.comp_neg]

/-- The cone boundary identity in positive degree. -/
@[reassoc]
theorem tupleCone_d {E : Type} (p : E) (n : ℕ) :
    tupleCone p (n+1) ≫ (tupleChains E).d (n+2) (n+1) =
      𝟙 _ - (tupleChains E).d (n+1) n ≫ tupleCone p n := by
  apply tupleChains_hom_ext
  intro v
  rw [← Category.assoc, tupleGen_cone, tupleGen_d]
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, tupleGen_d]
  rw [Fin.sum_univ_succ]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, tupleGen_cone,
    Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ]
  have hzero : Fin.cons p v ∘ (0 : Fin (n+3)).succAbove = v := by
    ext i
    simp
  have hsucc (i : Fin (n+2)) :
      Fin.cons p v ∘ i.succ.succAbove = Fin.cons p (v ∘ i.succAbove) := by
    ext j
    cases j using Fin.cases <;> simp [Function.comp_def]
  simp only [hzero, hsucc, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
    sub_eq_add_neg]

variable {E : Type}

/-- A center is chosen for each positive-dimensional tuple. The chain
identity does not require a metric; barycenters will supply mesh control. -/
def tupleSubdivisionMap (b : ∀ n : ℕ, (Fin (n+2) → E) → E) :
    ∀ n, (tupleChains E).X n ⟶ (tupleChains E).X n := fun n => match n with
  | 0 => 𝟙 _
  | n+1 => Sigma.desc (fun v => tupleGen v ≫ (tupleChains E).d (n+1) n ≫
      tupleSubdivisionMap b n ≫ tupleCone (b n v) n)

@[simp]
theorem tupleSubdivisionMap_zero (b : ∀ n : ℕ, (Fin (n+2) → E) → E) :
    tupleSubdivisionMap b 0 = 𝟙 _ := rfl

@[reassoc (attr := simp)]
theorem tupleGen_subdivision_succ (b : ∀ n : ℕ, (Fin (n+2) → E) → E)
    {n : ℕ} (v : Fin (n+2) → E) :
    tupleGen v ≫ tupleSubdivisionMap b (n+1) =
      tupleGen v ≫ (tupleChains E).d (n+1) n ≫
      tupleSubdivisionMap b n ≫ tupleCone (b n v) n := by
  exact Sigma.ι_comp_desc _ _

/-- Subdivision commutes with the actual alternating boundary. -/
@[reassoc]
theorem tupleSubdivisionMap_d (b : ∀ n : ℕ, (Fin (n+2) → E) → E) (n : ℕ) :
    tupleSubdivisionMap b (n+1) ≫ (tupleChains E).d (n+1) n =
      (tupleChains E).d (n+1) n ≫ tupleSubdivisionMap b n := by
  induction n with
  | zero =>
    apply tupleChains_hom_ext
    intro v
    rw [← Category.assoc, tupleGen_subdivision_succ]
    simp only [tupleSubdivisionMap_zero, Category.id_comp, Category.comp_id, Category.assoc]
    rw [tupleCone_d_zero]
    simp [Preadditive.comp_sub, ← Category.assoc]
  | succ n ih =>
    apply tupleChains_hom_ext
    intro v
    rw [← Category.assoc, tupleGen_subdivision_succ]
    simp only [Category.assoc, tupleCone_d, Preadditive.comp_sub, Category.comp_id]
    rw [← Category.assoc (tupleSubdivisionMap b (n+1)), ih]
    simp [← Category.assoc]

/-- A constructed chain endomorphism, for any supplied centers. -/
def tupleSubdivision (b : ∀ n : ℕ, (Fin (n+2) → E) → E) :
    tupleChains E ⟶ tupleChains E :=
  ChainComplex.ofHom (tupleSubdivisionMap b) (tupleSubdivisionMap_d b)

/-- The prism is filled by a cone after subtracting its prescribed boundary.
This recursion constructs the homotopy; it is not a homotopy premise. -/
def tupleSubdivisionPrism (b : ∀ n : ℕ, (Fin (n+2) → E) → E) :
    ∀ n, (tupleChains E).X n ⟶ (tupleChains E).X (n+1) := fun n => match n with
  | 0 => 0
  | n+1 => Sigma.desc (fun v =>
      (tupleGen v - tupleGen v ≫ tupleSubdivisionMap b (n+1) -
        tupleGen v ≫ (tupleChains E).d (n+1) n ≫ tupleSubdivisionPrism b n) ≫
      tupleCone (b n v) (n+1))

@[simp]
theorem tupleSubdivisionPrism_zero (b : ∀ n : ℕ, (Fin (n+2) → E) → E) :
    tupleSubdivisionPrism b 0 = 0 := rfl

@[reassoc (attr := simp)]
theorem tupleGen_prism_succ (b : ∀ n : ℕ, (Fin (n+2) → E) → E)
    {n : ℕ} (v : Fin (n+2) → E) :
    tupleGen v ≫ tupleSubdivisionPrism b (n+1) =
      (tupleGen v - tupleGen v ≫ tupleSubdivisionMap b (n+1) -
        tupleGen v ≫ (tupleChains E).d (n+1) n ≫ tupleSubdivisionPrism b n) ≫
      tupleCone (b n v) (n+1) := by
  exact Sigma.ι_comp_desc _ _

/-- A cone fills every positive-dimensional cycle in tuple chains. -/
theorem tupleCone_cycle (p : E) (n : ℕ) {A : ModuleCat.{0} ℤ}
    (z : A ⟶ (tupleChains E).X (n+1))
    (hz : z ≫ (tupleChains E).d (n+1) n = 0) :
    z ≫ tupleCone p (n+1) ≫ (tupleChains E).d (n+2) (n+1) = z := by
  rw [tupleCone_d, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hz]
  simp only [zero_comp, sub_zero]

/-- The full positive-degree chain-homotopy equation. -/
theorem tupleSubdivisionPrism_equation (b : ∀ n : ℕ, (Fin (n+2) → E) → E) (n : ℕ) :
    tupleSubdivisionPrism b (n+1) ≫ (tupleChains E).d (n+2) (n+1) =
      𝟙 _ - tupleSubdivisionMap b (n+1) -
      (tupleChains E).d (n+1) n ≫ tupleSubdivisionPrism b n := by
  induction n with
  | zero =>
    have hcycle : (𝟙 _ - tupleSubdivisionMap b 1 -
        (tupleChains E).d 1 0 ≫ tupleSubdivisionPrism b 0) ≫
        (tupleChains E).d 1 0 = 0 := by
      rw [tupleSubdivisionPrism_zero, comp_zero, sub_zero, Preadditive.sub_comp,
        Category.id_comp, tupleSubdivisionMap_d, tupleSubdivisionMap_zero, Category.comp_id]
      exact sub_self _
    apply tupleChains_hom_ext
    intro v
    rw [← Category.assoc, tupleGen_prism_succ, Category.assoc]
    change (tupleGen v - tupleGen v ≫ tupleSubdivisionMap b 1 -
      tupleGen v ≫ (tupleChains E).d 1 0 ≫ tupleSubdivisionPrism b 0) ≫ _ = _
    rw [show tupleGen v - tupleGen v ≫ tupleSubdivisionMap b 1 -
        tupleGen v ≫ (tupleChains E).d 1 0 ≫ tupleSubdivisionPrism b 0 =
        tupleGen v ≫ (𝟙 _ - tupleSubdivisionMap b 1 -
          (tupleChains E).d 1 0 ≫ tupleSubdivisionPrism b 0) by
      simp only [Preadditive.comp_sub, Category.comp_id]]
    exact tupleCone_cycle _ 0 _ (by rw [Category.assoc, hcycle, comp_zero])
  | succ n ih =>
    have hcycle :
        (𝟙 _ - tupleSubdivisionMap b (n+2) -
          (tupleChains E).d (n+2) (n+1) ≫ tupleSubdivisionPrism b (n+1)) ≫
          (tupleChains E).d (n+2) (n+1) = 0 := by
      simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
        tupleSubdivisionMap_d, ih, Preadditive.comp_sub, Category.comp_id,
        HomologicalComplex.d_comp_d_assoc, zero_comp]
      abel
    apply tupleChains_hom_ext
    intro v
    rw [← Category.assoc, tupleGen_prism_succ, Category.assoc]
    rw [show tupleGen v - tupleGen v ≫ tupleSubdivisionMap b (n+2) -
        tupleGen v ≫ (tupleChains E).d (n+2) (n+1) ≫ tupleSubdivisionPrism b (n+1) =
        tupleGen v ≫ (𝟙 _ - tupleSubdivisionMap b (n+2) -
          (tupleChains E).d (n+2) (n+1) ≫ tupleSubdivisionPrism b (n+1)) by
      simp only [Preadditive.comp_sub, Category.comp_id]]
    exact tupleCone_cycle _ (n+1) _ (by rw [Category.assoc, hcycle, comp_zero])

def chainHomotopyOfComponents {P Q : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (f g : P ⟶ Q) (h : ∀ n, P.X n ⟶ Q.X (n+1))
    (hzero : f.f 0 = h 0 ≫ Q.d 1 0 + g.f 0)
    (hsucc : ∀ n, f.f (n+1) = P.d (n+1) n ≫ h n +
      h (n+1) ≫ Q.d (n+2) (n+1) + g.f (n+1)) : Homotopy f g where
  hom i j := if e : i+1 = j then h i ≫ eqToHom (congrArg Q.X e) else 0
  zero i j h' := by simp_all [ComplexShape.down_Rel]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simpa only [dite_true, eqToHom_refl, Category.comp_id, zero_add] using hzero
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simpa only [dite_true, eqToHom_refl, Category.comp_id] using hsucc n

/-- Subdivision is chain homotopic to the identity. -/
def tupleSubdivisionHomotopy (b : ∀ n : ℕ, (Fin (n+2) → E) → E) :
    Homotopy (𝟙 (tupleChains E)) (tupleSubdivision b) :=
  chainHomotopyOfComponents _ _ (tupleSubdivisionPrism b)
    (by simp [tupleSubdivision]) (fun n => by
      change 𝟙 _ = _ + _ + tupleSubdivisionMap b (n+1)
      rw [tupleSubdivisionPrism_equation]
      abel)

end

variable {E F : Type}

/-- Applying a function to each vertex defines a simplicial map. -/
def tupleSSetMap (f : E → F) : tupleSSet E ⟶ tupleSSet F where
  app _ := ↾fun v => f ∘ v

abbrev tupleChainMap (f : E → F) : tupleChains E ⟶ tupleChains F :=
  SSet.chainComplexMap (tupleSSetMap f) (ModuleCat.of ℤ ℤ)

@[reassoc (attr := simp)]
theorem tupleGen_map (f : E → F) {n : ℕ} (v : Fin (n+1) → E) :
    tupleGen v ≫ (tupleChainMap f).f n = tupleGen (f ∘ v) := by
  exact SSet.ι_chainComplexMap_f (X := tupleSSet E) (Y := tupleSSet F)
    (f := tupleSSetMap f) (R := ModuleCat.of ℤ ℤ) (x := v)

@[reassoc]
theorem tupleCone_map (f : E → F) (p : E) (n : ℕ) :
    tupleCone p n ≫ (tupleChainMap f).f (n+1) =
      (tupleChainMap f).f n ≫ tupleCone (f p) n := by
  apply tupleChains_hom_ext
  intro v
  simp only [← Category.assoc, tupleGen_cone, tupleGen_map, Fin.comp_cons]

/-- Naturality of subdivision for center-preserving vertex maps. -/
@[reassoc]
theorem tupleSubdivisionMap_naturality
    (b : ∀ n : ℕ, (Fin (n+2) → E) → E)
    (c : ∀ n : ℕ, (Fin (n+2) → F) → F)
    (f : E → F) (hb : ∀ n v, f (b n v) = c n (f ∘ v)) (n : ℕ) :
    tupleSubdivisionMap b n ≫ (tupleChainMap f).f n =
      (tupleChainMap f).f n ≫ tupleSubdivisionMap c n := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply tupleChains_hom_ext
    intro v
    rw [← Category.assoc, tupleGen_subdivision_succ]
    simp only [Category.assoc, tupleCone_map, hb]
    rw [← Category.assoc (tupleSubdivisionMap b n), ih]
    simp only [Category.assoc, ← (tupleChainMap f).comm_assoc (n+1) n]
    simp only [tupleGen_map_assoc, tupleGen_subdivision_succ]

/-- The explicit subdivision homotopy has the same naturality. -/
@[reassoc]
theorem tupleSubdivisionPrism_naturality
    (b : ∀ n : ℕ, (Fin (n+2) → E) → E)
    (c : ∀ n : ℕ, (Fin (n+2) → F) → F)
    (f : E → F) (hb : ∀ n v, f (b n v) = c n (f ∘ v)) (n : ℕ) :
    tupleSubdivisionPrism b n ≫ (tupleChainMap f).f (n+1) =
      (tupleChainMap f).f n ≫ tupleSubdivisionPrism c n := by
  induction n with
  | zero => simp
  | succ n ih =>
    apply tupleChains_hom_ext
    intro v
    rw [← Category.assoc, tupleGen_prism_succ, Category.assoc, tupleCone_map, hb]
    rw [← Category.assoc]
    simp only [Preadditive.sub_comp, Category.assoc,
      tupleSubdivisionMap_naturality b c f hb, ih]
    simp only [← (tupleChainMap f).comm_assoc (n+1) n]
    simp only [tupleGen_map_assoc, tupleGen_subdivision_succ, tupleGen_subdivision_succ_assoc, Category.assoc, tupleGen_prism_succ,
      Preadditive.sub_comp, Category.assoc]

end

open CategoryTheory Limits AlgebraicTopology Simplicial
section
variable {E F : Type}

/-- Integral chains spanned by tuples satisfying a specified support condition. -/
def tupleChainSpan {n : ℕ} (P : (Fin (n+1) → E) → Prop) :
    Submodule ℤ ((tupleChains E).X n) :=
  Submodule.span ℤ {c | ∃ v, P v ∧ c = tupleGen v (1 : ℤ)}

theorem tupleGen_mem_span {n : ℕ} {P : (Fin (n+1) → E) → Prop}
    (v : Fin (n+1) → E) (hv : P v) : tupleGen v (1 : ℤ) ∈ tupleChainSpan P :=
  Submodule.subset_span ⟨v, hv, rfl⟩

/-- To control a linear operator on supported chains, it suffices to control
each supported generator. -/
theorem tupleChainSpan_map {n m : ℕ} {P : (Fin (n+1) → E) → Prop}
    {Q : (Fin (m+1) → F) → Prop}
    (L : (tupleChains E).X n ⟶ (tupleChains F).X m)
    (hL : ∀ v, P v → L (tupleGen v (1 : ℤ)) ∈ tupleChainSpan Q)
    {c : (tupleChains E).X n} (hc : c ∈ tupleChainSpan P) : L c ∈ tupleChainSpan Q := by
  have h : tupleChainSpan P ≤ (tupleChainSpan Q).comap L.hom := by
    apply Submodule.span_le.mpr
    rintro c ⟨v, hv, rfl⟩
    exact hL v hv
  exact h hc

theorem tupleChainSpan_mono {n : ℕ} {P Q : (Fin (n+1) → E) → Prop}
    (h : ∀ v, P v → Q v) : tupleChainSpan P ≤ tupleChainSpan Q := by
  apply Submodule.span_le.mpr
  rintro c ⟨v, hv, rfl⟩
  exact tupleGen_mem_span v (h v hv)

/-- Coning preserves the support condition exactly when prepending its
vertex preserves the generator condition. -/
theorem tupleCone_mem_span {n : ℕ} (p : E)
    {P : (Fin (n+1) → E) → Prop} {Q : (Fin (n+2) → E) → Prop}
    (h : ∀ v, P v → Q (Fin.cons p v))
    {c : (tupleChains E).X n} (hc : c ∈ tupleChainSpan P) :
    tupleCone p n c ∈ tupleChainSpan Q := by
  apply tupleChainSpan_map (tupleCone p n) (fun v hv => ?_) hc
  change (tupleGen v ≫ tupleCone p n) (1 : ℤ) ∈ _
  rw [tupleGen_cone]
  exact tupleGen_mem_span _ (h v hv)

/-- The recursive subdivision formula evaluated as an actual chain. -/
theorem tupleSubdivision_gen_value (b : ∀ n : ℕ, (Fin (n+2) → E) → E)
    {n : ℕ} (v : Fin (n+2) → E) :
    tupleSubdivisionMap b (n+1) (tupleGen v (1 : ℤ)) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        tupleCone (b n v) n (tupleSubdivisionMap b n (tupleGen (v ∘ i.succAbove) (1 : ℤ))) := by
  change (tupleGen v ≫ tupleSubdivisionMap b (n+1)) (1 : ℤ) = _
  rw [tupleGen_subdivision_succ, ← Category.assoc, ← Category.assoc, tupleGen_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
  change ((∑ i : Fin (n+2), (-1 : ℤ)^i.val •
    (tupleGen (v ∘ i.succAbove) ≫ tupleSubdivisionMap b n ≫ tupleCone (b n v) n)).hom) (1 : ℤ) = _
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    ModuleCat.hom_comp]

  apply Finset.sum_congr rfl
  intro i hi
  rfl

end

end Kaplansky

end

end OAI
