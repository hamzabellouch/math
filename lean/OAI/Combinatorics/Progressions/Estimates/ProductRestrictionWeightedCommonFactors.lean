import OAI.Combinatorics.Progressions.Estimates.CommonRefilteredMappedOrbitFactors
import OAI.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration

variable {ι κ α β σ : Type*} [Fintype ι] [Fintype κ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (r : κ → ι)
  (e : Basis α ℚ (∀ i, L i)) (ω : α → ℕ)
  (hF : ∀ j, (pi D).filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (f : Basis β ℚ (∀ j, L (r j))) (ν : β → ℕ)
  (hG : ∀ j, (pi (fun j => D (r j))).filtration.layer j =
    Submodule.span ℚ (f '' {i | j ≤ ν i}))
  (w : σ → ℕ)

theorem productRestriction_jointOrbitSymbol
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w) :
    (pi D).filtration.realSymbolProjection (pi (fun j => D (r j))).filtration
      (liePiMap (fun j => liePiEval (R := ℚ) (r j))) (productRestriction_layers D r) w
      ((pi D).filtration.realPolynomialSymbolHom e ω hF w
        ⟨⟨(piRealOrbit (fun i => (D i).filtration) g).log,
          (piRealOrbit (fun i => (D i).filtration) g).property⟩⟩) =
      (pi (fun j => D (r j))).filtration.realPolynomialSymbolHom f ν hG w
        ⟨⟨(piRealOrbit (fun j => (D (r j)).filtration) (fun j => g (r j))).log,
          (piRealOrbit (fun j => (D (r j)).filtration) (fun j => g (r j))).property⟩⟩ := by
  apply NilpotentLieBCHGroup.ext
  have h := (pi D).filtration.realFilteredPolynomialSymbolMap_polynomial
    (pi (fun j => D (r j))).filtration
    (liePiMap (fun j => liePiEval (R := ℚ) (r j))) (productRestriction_layers D r)
    e ω hF f ν hG w
    ⟨(piRealOrbit (fun i => (D i).filtration) g).log,
      (piRealOrbit (fun i => (D i).filtration) g).property⟩
  change _ = (pi (fun j => D (r j))).filtration.realSymbolOfPolynomial f ν hG w
    (piRealOrbit (fun j => (D (r j)).filtration) (fun j => g (r j))).log
  exact h.trans (congrArg
    ((pi (fun j => D (r j))).filtration.realSymbolOfPolynomial f ν hG w)
    (productRestriction_piRealOrbit_log D r g))

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped BigOperators

variable {ι κ : Type*} [Fintype κ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

noncomputable def productRestrictionSectionLinear (f : κ → ι) :
    (∀ j, L (f j)) →ₗ[ℚ] (∀ i, L i) := by
  classical
  exact ∑ j, (LinearMap.single ℚ L (f j)).comp (LinearMap.proj j)

theorem productRestrictionSectionLinear_apply (f : κ → ι) (hf : Function.Injective f)
    (x : ∀ j, L (f j)) (j : κ) :
    productRestrictionSectionLinear f x (f j) = x j := by
  classical
  simp only [productRestrictionSectionLinear, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.single_apply, LinearMap.proj_apply, Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · exact Pi.single_eq_same _ _
  · intro k _ hkj
    exact Pi.single_eq_of_ne (fun h => hkj (hf h.symm)) _
  · simp

theorem productRestrictionSectionLinear_apply_of_not_mem (f : κ → ι)
    (x : ∀ j, L (f j)) (i : ι) (hi : i ∉ Set.range f) :
    productRestrictionSectionLinear f x i = 0 := by
  classical
  simp only [productRestrictionSectionLinear, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.single_apply, LinearMap.proj_apply, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j _
  exact Pi.single_eq_of_ne (fun h => hi ⟨j, h.symm⟩) _

noncomputable def productRestrictionSection (f : κ → ι) (hf : Function.Injective f) :
    (∀ j, L (f j)) →ₗ⁅ℚ⁆ (∀ i, L i) where
  toLinearMap := productRestrictionSectionLinear f
  map_lie' {x y} := by
    ext i
    change productRestrictionSectionLinear f ⁅x, y⁆ i =
      ⁅productRestrictionSectionLinear f x i, productRestrictionSectionLinear f y i⁆
    by_cases hi : i ∈ Set.range f
    · obtain ⟨j, rfl⟩ := hi
      simp only [productRestrictionSectionLinear_apply f hf, lie_pi_apply]
    · simp only [productRestrictionSectionLinear_apply_of_not_mem f _ i hi, lie_zero]

@[simp] theorem productRestrictionSection_apply (f : κ → ι) (hf : Function.Injective f)
    (x : ∀ j, L (f j)) (j : κ) :
    productRestrictionSection f hf x (f j) = x j :=
  productRestrictionSectionLinear_apply f hf x j

theorem productRestrictionSection_apply_of_not_mem (f : κ → ι) (hf : Function.Injective f)
    (x : ∀ j, L (f j)) (i : ι) (hi : i ∉ Set.range f) :
    productRestrictionSection f hf x i = 0 :=
  productRestrictionSectionLinear_apply_of_not_mem f x i hi

@[simp] theorem productRestrictionSection_rightInverse (f : κ → ι) (hf : Function.Injective f)
    (x : ∀ j, L (f j)) :
    liePiMap (fun j => liePiEval (R := ℚ) (f j))
      (productRestrictionSection f hf x) = x := by
  funext j
  exact productRestrictionSection_apply f hf x j

variable [Fintype ι] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  (f : κ → ι) (hf : Function.Injective f)

theorem productRestrictionSection_layers (n : ℕ) (x : ∀ j, L (f j))
    (hx : x ∈ (pi (fun j => D (f j))).filtration.layer n) :
    productRestrictionSection f hf x ∈ (pi D).filtration.layer n := by
  apply (NilpotentLieFiltration.mem_pi_layer (fun i => (D i).filtration) n _).mpr
  intro i
  by_cases hi : i ∈ Set.range f
  · obtain ⟨j, rfl⟩ := hi
    rw [productRestrictionSection_apply]
    exact (NilpotentLieFiltration.mem_pi_layer (fun j => (D (f j)).filtration) n x).mp hx j
  · rw [productRestrictionSection_apply_of_not_mem f hf x i hi]
    exact Submodule.zero_mem _

theorem productRestrictionSection_coordinates (x : ∀ j, L (f j))
    (k : Fin (Fintype.card (Σ j : κ, Fin (d (f j))))) :
    (pi D).basis.repr (productRestrictionSection f hf x)
        (productRestrictionIndex (d := d) f k) =
      (pi (fun j => D (f j))).basis.repr x k := by
  rw [← productRestriction_coordinates D f, productRestrictionSection_rightInverse]

theorem productRestrictionSection_coordinates_of_not_mem (x : ∀ j, L (f j))
    (i : ι) (hi : i ∉ Set.range f) (k : Fin (d i)) :
    (pi D).basis.repr (productRestrictionSection f hf x)
      (Fintype.equivFin (Σ i, Fin (d i)) ⟨i, k⟩) = 0 := by
  rw [← productFinBasis_repr_component D,
    productRestrictionSection_apply_of_not_mem f hf x i hi, map_zero, Finsupp.zero_apply]

include hf in

theorem productRestriction_layer_surjective (n : ℕ) (x : ∀ j, L (f j))
    (hx : x ∈ (pi (fun j => D (f j))).filtration.layer n) :
    ∃ y ∈ (pi D).filtration.layer n,
      liePiMap (fun j => liePiEval (R := ℚ) (f j)) y = x :=
  ⟨productRestrictionSection f hf x, productRestrictionSection_layers D f hf n x hx,
    productRestrictionSection_rightInverse f hf x⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem productRestriction_matrix_height
    {ι κ : Type*} [Fintype ι] [Fintype κ] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (r : κ → ι)
    (i : Fin (Fintype.card (Σ j : κ, Fin (d (r j)))))
    (j : Fin (Fintype.card (Σ k, Fin (d k)))) :
    RationalHeightLE ((pi (fun k => D (r k))).basis.repr
      (liePiMap (fun k => liePiEval (R := ℚ) (r k)) ((pi D).basis j)) i) 1 := by
  classical
  rw [productRestriction_coordinates D r, Basis.repr_self, Finsupp.single_apply]
  split_ifs
  · exact rationalHeightLE_one le_rfl
  · exact rationalHeightLE_zero le_rfl

theorem productRestriction_adapted_matrix_logHeight
    {ι κ α β : Type*} [Fintype ι] [Fintype κ] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i)) (r : κ → ι)
    (e : Basis α ℚ (∀ i, L i)) (c : Basis β ℚ (∀ j, L (r j)))
    {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card (Σ j : κ, Fin (d (r j))) : ℝ) ≤ p)
    (hs : ∀ i j, rationalLogHeight ((pi D).basis.repr (e i) j) ≤ p)
    (htInv : ∀ i j, rationalLogHeight (c.repr ((pi (fun k => D (r k))).basis i) j) ≤ p)
    (i : α) (j : β) :
    rationalLogHeight (c.repr
      (liePiMap (fun k => liePiEval (R := ℚ) (r k)) (e i)) j) ≤ (p + 2) ^ 4 := by
  apply linearMap_coordinate_logHeight (pi (fun k => D (r k))).basis c LinearMap.id hp
    (by simpa only [Fintype.card_fin] using hdim) htInv
  intro k
  exact (congrArg rationalLogHeight (productRestriction_coordinates D r (e i) k)).trans_le
    (hs i _)

variable {ι κ α β σ : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β]
    {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {s : ℕ} {d : ι → ℕ}
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (r : κ → ι) (hr : Function.Injective r)
    (e : Basis α ℚ (∀ i, L i)) (ω : α → ℕ)
    (hF : ∀ j, (pi D).filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (c : Basis β ℚ (∀ j, L (r j))) (ν : β → ℕ)
    (hG : ∀ j, (pi (fun k => D (r k))).filtration.layer j =
      Submodule.span ℚ (c '' {i | j ≤ ν i}))
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ν)]

include hr in

theorem productRestriction_controlledSymbolFactorizationAtFast
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE
      (c.repr (liePiMap (fun k => liePiEval (R := ℚ) (r k)) (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hα : (Fintype.card α : ℝ) ≤ p)
    (hβ : (Fintype.card β : ℝ) ≤ p)
    (hrows : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω ⊕
      SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ p)
    (hcols : ((Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) *
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : (pi D).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (η : (∀ j, L (r j)) →ₗ[ℚ] ℚ)
    (U : LieSubalgebra ℚ (pi (fun j => D (r j))).filtration.AssociatedGraded)
    (hfactor : (pi (fun j => D (r j))).filtration.ControlledSymbolFactorizationAtFast
      c ν hG η T ((pi D).filtration.realSymbolProjection (pi (fun j => D (r j))).filtration
        (liePiMap (fun j => liePiEval (R := ℚ) (r j))) (productRestriction_layers D r)
        (fun _ => 1) X) p U) :
    (pi D).filtration.ControlledSymbolFactorizationAtFast e ω hF
      (η.comp (liePiMap (fun j => liePiEval (R := ℚ) (r j))).toLinearMap) T X
      (controlledProjectionBudget p)
      (U.comap ((pi D).filtration.associatedGradedMap (pi (fun j => D (r j))).filtration
        (liePiMap (fun j => liePiEval (R := ℚ) (r j))) (productRestriction_layers D r))) := by
  exact (pi D).filtration.controlledSymbolFactorizationAtFast_projection_pullback
    (pi (fun j => D (r j))).filtration e ω hF c ν hG
    (liePiMap (fun j => liePiEval (R := ℚ) (r j))) (productRestriction_layers D r)
    (productRestriction_layer_surjective D r hr) hH hentries hp hα hβ hrows hcols hHp T hT X η U hfactor

include hr in

theorem productRestriction_controlledSymbolFactorization
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE
      (c.repr (liePiMap (fun k => liePiEval (R := ℚ) (r k)) (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hα : (Fintype.card α : ℝ) ≤ p)
    (hβ : (Fintype.card β : ℝ) ≤ p)
    (hrows : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω ⊕
      SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ p)
    (hcols : ((Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) *
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (X : (pi D).filtration.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (η : (∀ j, L (r j)) →ₗ[ℚ] ℚ)
    (hfactor : (pi (fun j => D (r j))).filtration.ControlledSymbolFactorization
      c ν hG η T ((pi D).filtration.realSymbolProjection (pi (fun j => D (r j))).filtration
        (liePiMap (fun j => liePiEval (R := ℚ) (r j))) (productRestriction_layers D r)
        (fun _ => 1) X) p) :
    (pi D).filtration.ControlledSymbolFactorization e ω hF
      (η.comp (liePiMap (fun j => liePiEval (R := ℚ) (r j))).toLinearMap) T X
      (controlledProjectionBudget p) := by
  exact (pi D).filtration.controlledSymbolFactorization_projection_pullback
    (pi (fun j => D (r j))).filtration e ω hF c ν hG
    (liePiMap (fun j => liePiEval (R := ℚ) (r j))) (productRestriction_layers D r)
    (productRestriction_layer_surjective D r hr) hH hentries hp hα hβ hrows hcols hHp T hT X η hfactor

include hr in

theorem productRestriction_jointOrbit_controlledSymbolFactorization
    {H : ℕ} (hH : 1 ≤ H)
    (hentries : ∀ i j, RationalHeightLE
      (c.repr (liePiMap (fun k => liePiEval (R := ℚ) (r k)) (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hα : (Fintype.card α : ℝ) ≤ p)
    (hβ : (Fintype.card β : ℝ) ≤ p)
    (hrows : (Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω ⊕
      SymbolBasisIndex (fun _ : σ => 1) ν) : ℝ) ≤ p)
    (hcols : ((Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) *
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (η : (∀ j, L (r j)) →ₗ[ℚ] ℚ)
    (hfactor : (pi (fun j => D (r j))).filtration.ControlledSymbolFactorization
      c ν hG η T
      ((pi (fun j => D (r j))).filtration.realPolynomialSymbolHom c ν hG (fun _ => 1)
        ⟨⟨(piRealOrbit (fun j => (D (r j)).filtration) (fun j => g (r j))).log,
          (piRealOrbit (fun j => (D (r j)).filtration) (fun j => g (r j))).property⟩⟩) p) :
    (pi D).filtration.ControlledSymbolFactorization e ω hF
      (η.comp (liePiMap (fun j => liePiEval (R := ℚ) (r j))).toLinearMap) T
      ((pi D).filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
        ⟨⟨(piRealOrbit (fun i => (D i).filtration) g).log,
          (piRealOrbit (fun i => (D i).filtration) g).property⟩⟩)
      (controlledProjectionBudget p) := by
  apply productRestriction_controlledSymbolFactorization D r hr e ω hF c ν hG
    hH hentries hp hα hβ hrows hcols hHp T hT _ η
  rw [productRestriction_jointOrbitSymbol D r e ω hF c ν hG]
  exact hfactor

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem exists_productRestriction_jointOrbit_controlledSymbolFactorizationAtFast (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {ι κ α β σ : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β] [Fintype σ]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (r : κ → ι), Function.Injective r →
    ∀ (e : Basis α ℚ (∀ i, L i)) (ω : α → ℕ)
      (hF : ∀ j, (pi D).filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (c : Basis β ℚ (∀ j, L (r j))) (ν : β → ℕ)
      (hG : ∀ j, (pi (fun k => D (r k))).filtration.layer j =
        Submodule.span ℚ (c '' {i | j ≤ ν i}))
      {H : ℕ}, 1 ≤ H →
      (∀ i j, RationalHeightLE
        (c.repr (liePiMap (fun k => liePiEval (R := ℚ) (r k)) (e j)) i) H) →
    ∀ {p : ℝ}, 0 ≤ p → (Fintype.card α : ℝ) ≤ p → (Fintype.card β : ℝ) ≤ p →
      (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
    ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
    ∀ (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
      (η : (∀ j, L (r j)) →ₗ[ℚ] ℚ)
      (U : LieSubalgebra ℚ (pi (fun j => D (r j))).filtration.AssociatedGraded),
      (pi (fun j => D (r j))).filtration.ControlledSymbolFactorizationAtFast
        c ν hG η T
        ((pi (fun j => D (r j))).filtration.realPolynomialSymbolHom c ν hG (fun _ => 1)
          ⟨⟨(piRealOrbit (fun j => (D (r j)).filtration) (fun j => g (r j))).log,
            (piRealOrbit (fun j => (D (r j)).filtration) (fun j => g (r j))).property⟩⟩) p U →
      (pi D).filtration.ControlledSymbolFactorizationAtFast e ω hF
        (η.comp (liePiMap (fun j => liePiEval (R := ℚ) (r j))).toLinearMap) T
        ((pi D).filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
          ⟨⟨(piRealOrbit (fun i => (D i).filtration) g).log,
            (piRealOrbit (fun i => (D i).filtration) g).property⟩⟩)
        ((p + C) ^ C)
        (U.comap ((pi D).filtration.associatedGradedMap (pi (fun j => D (r j))).filtration
          (liePiMap (fun j => liePiEval (R := ℚ) (r j))) (productRestriction_layers D r))) := by
  obtain ⟨C, hC, hbudget⟩ := exists_controlledProjectionUniformBudget_power s
  refine ⟨C, hC, ?_⟩
  intro ι κ α β σ _ _ _ _ _ L _ _ d D r hr e ω hF c ν hG H hH hentries
    p hp hα hβ hσ hHp T hT g η U hfactor
  apply ControlledSymbolFactorizationAtFast.mono (pi D).filtration e ω hF
    (q := (p + C) ^ C) (hpq := hbudget p hp) (hT := hT)
  apply (pi D).filtration.controlledSymbolFactorizationAtFast_projection_of_dimensions e ω hF
    (pi (fun j => D (r j))).filtration c ν hG
    (liePiMap (fun j => liePiEval (R := ℚ) (r j))) (productRestriction_layers D r)
    (productRestriction_layer_surjective D r hr) hH hentries hp hα hβ hσ hHp T hT
  rw [productRestriction_jointOrbitSymbol D r e ω hF c ν hG]
  exact hfactor

theorem exists_productRestriction_jointOrbit_controlledSymbolFactorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {ι κ α β σ : Type*} [Fintype ι] [Fintype κ] [Fintype α] [Fintype β] [Fintype σ]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (r : κ → ι), Function.Injective r →
    ∀ (e : Basis α ℚ (∀ i, L i)) (ω : α → ℕ)
      (hF : ∀ j, (pi D).filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (c : Basis β ℚ (∀ j, L (r j))) (ν : β → ℕ)
      (hG : ∀ j, (pi (fun k => D (r k))).filtration.layer j =
        Submodule.span ℚ (c '' {i | j ≤ ν i}))
      {H : ℕ}, 1 ≤ H →
      (∀ i j, RationalHeightLE
        (c.repr (liePiMap (fun k => liePiEval (R := ℚ) (r k)) (e j)) i) H) →
    ∀ {p : ℝ}, 0 ≤ p → (Fintype.card α : ℝ) ≤ p → (Fintype.card β : ℝ) ≤ p →
      (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
    ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
    ∀ (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
      (η : (∀ j, L (r j)) →ₗ[ℚ] ℚ),
      (pi (fun j => D (r j))).filtration.ControlledSymbolFactorization c ν hG η T
        ((pi (fun j => D (r j))).filtration.realPolynomialSymbolHom c ν hG (fun _ => 1)
          ⟨⟨(piRealOrbit (fun j => (D (r j)).filtration) (fun j => g (r j))).log,
            (piRealOrbit (fun j => (D (r j)).filtration) (fun j => g (r j))).property⟩⟩) p →
      (pi D).filtration.ControlledSymbolFactorization e ω hF
        (η.comp (liePiMap (fun j => liePiEval (R := ℚ) (r j))).toLinearMap) T
        ((pi D).filtration.realPolynomialSymbolHom e ω hF (fun _ => 1)
          ⟨⟨(piRealOrbit (fun i => (D i).filtration) g).log,
            (piRealOrbit (fun i => (D i).filtration) g).property⟩⟩)
        ((p + C) ^ C) := by
  obtain ⟨C, hC, hlift⟩ := exists_productRestriction_jointOrbit_controlledSymbolFactorizationAtFast s
  refine ⟨C, hC, ?_⟩
  intro ι κ α β σ _ _ _ _ _ L _ _ d D r hr e ω hF c ν hG H hH hentries
    p hp hα hβ hσ hHp T hT g η hfactor
  obtain ⟨U, hU⟩ := hfactor.exists_fastWitness (pi (fun j => D (r j))).filtration c ν hG
  obtain ⟨m, E, P, R, v, hdata⟩ :=
    hlift D r hr e ω hF c ν hG hH hentries hp hα hβ hσ hHp T hT g η U hU
  exact ⟨m, E, P, R, _, v, hdata⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

theorem exists_productRestriction_weighted_common_orbit_factors (s : ℕ) :
    ∃ C A : ℕ, 2 ≤ C ∧ 2 ≤ A ∧
    ∀ {ι α σ J Ω : Type*} [Fintype ι] [Fintype α] [Fintype σ]
      [Fintype J] [Fintype Ω]
      {κ β : J → Type*} [∀ j, Fintype (κ j)] [∀ j, Fintype (β j)]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
      {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (r : ∀ j, κ j → ι), (∀ j, Function.Injective (r j)) →
    ∀ (e : Basis α ℚ (∀ i, L i)) (ω : α → ℕ)
      (hF : ∀ k, (pi D).filtration.layer k = Submodule.span ℚ (e '' {i | k ≤ ω i}))
      (b : ∀ j, Basis (β j) ℚ (∀ k, L (r j k))) (ν : ∀ j, β j → ℕ)
      (hG : ∀ j k, (pi (fun i => D (r j i))).filtration.layer k =
        Submodule.span ℚ (b j '' {i | k ≤ ν j i}))
      {height : ℕ}, 1 ≤ height →
      (∀ j i k, RationalHeightLE
        ((b j).repr (liePiMap (fun i => liePiEval (R := ℚ) (r j i)) (e k)) i) height) →
    ∀ {p : ℝ}, 0 ≤ p → (Fintype.card α : ℝ) ≤ p →
      (∀ j, (Fintype.card (β j) : ℝ) ≤ p) →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (height : ℝ) ≤ Real.exp p →
      (∀ i j k, rationalLogHeight (e.repr ⁅e i, e j⁆ k) ≤ p) →
      let P := p + (p + C) ^ C
      ∀ side : σ → ℝ, (∀ i, Real.exp ((P + 2) ^ A) ≤ side i) →
      ∀ (outer : FiniteProbabilityWeights Ω) (H : Finset Ω), 0 < outer.mass H →
      ∀ (g : Ω → ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1))
        (η : ∀ j, (∀ i, L (r j i)) →ₗ[ℚ] ℚ),
        (∀ a ∈ H, ∀ j,
          (pi (fun i => D (r j i))).filtration.ControlledSymbolFactorization
            (b j) (ν j) (hG j) (η j) side
            ((pi (fun i => D (r j i))).filtration.realPolynomialSymbolHom
              (b j) (ν j) (hG j) (fun _ => 1)
              ⟨⟨(piRealOrbit (fun i => (D (r j i)).filtration)
                (fun i => g a (r j i))).log,
                (piRealOrbit (fun i => (D (r j i)).filtration)
                  (fun i => g a (r j i))).property⟩⟩) p) →
        let q := (P + 2) ^ A + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
        ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
          (v : Fin (Fintype.card α) → (pi D).filtration.AssociatedGraded)
          (m : ℕ) (H' : Finset Ω),
          H' ⊆ H ∧ 0 < outer.mass H' ∧
          Real.exp (-((q + 2) ^ 5 + q)) * outer.mass H ≤ outer.mass H' ∧
          Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
          BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis e ω hF)
            ω W.toSubmodule ∧
          (∀ i k, rationalLogHeight
            (((pi D).filtration.associatedGradedBasis e ω hF).repr (v i) k) ≤ q) ∧
          (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s →
            realifyFunctional ((η j).comp
              (liePiMap (fun i => liePiEval (R := ℚ) (r j i))).toLinearMap) x = 0) ∧
          0 < m ∧ (m : ℝ) ≤ Real.exp q ∧
          ∀ a ∈ H', (pi D).filtration.HasCommonRefilteredOrbitFactors e ω hF side q m W
            ⟨⟨(piRealOrbit (fun i => (D i).filtration) (g a)).log,
              (piRealOrbit (fun i => (D i).filtration) (g a)).property⟩⟩ := by
  obtain ⟨C, hC, hlift⟩ := exists_productRestriction_jointOrbit_controlledSymbolFactorization s
  obtain ⟨A, hA, hcommon⟩ := exists_weighted_common_refiltered_orbit_factors s
  refine ⟨C, A, hC, hA, ?_⟩
  intro ι α σ J Ω _ _ _ _ _ κ β _ _ L _ _ d D r hr e ω hF b ν hG
    height hheight hentries p hp hα hβ hσ hJ hheightp hstructure P side hside
    outer H hH g η hfactor
  have hpP : p ≤ P := by
    dsimp only [P]
    exact le_add_of_nonneg_right (by positivity)
  have hliftP : (p + C) ^ C ≤ P := by
    dsimp only [P]
    exact le_add_of_nonneg_left hp
  have hsidepos (i) : 0 < side i := (Real.exp_pos _).trans_le (hside i)
  apply hcommon (pi D).filtration e ω hF
    (fun j => (η j).comp (liePiMap (fun i => liePiEval (R := ℚ) (r j i))).toLinearMap)
    (hp.trans hpP) (hα.trans hpP) (hσ.trans hpP) (hJ.trans hpP)
    (fun i j k => (hstructure i j k).trans hpP) side hside outer H hH
    (fun a => ⟨⟨(piRealOrbit (fun i => (D i).filtration) (g a)).log,
      (piRealOrbit (fun i => (D i).filtration) (g a)).property⟩⟩)
  intro a ha j
  exact (hlift D (r j) (hr j) e ω hF (b j) (ν j) (hG j)
    hheight (hentries j) hp hα (hβ j) hσ hheightp side hsidepos
    (g a) (η j) (hfactor a ha j)).mono (pi D).filtration e ω hF hliftP hsidepos

end Erdos3.RationalFilteredNilmanifold

end

end OAI
