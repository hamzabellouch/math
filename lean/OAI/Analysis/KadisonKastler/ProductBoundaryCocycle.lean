import OAI.Analysis.KadisonKastler.StandardTracialPosition
import OAI.Analysis.KadisonKastler.CommonRightProjection
import OAI.Analysis.KadisonKastler.NonsingularBoundary

namespace OAI

/-! # The two-sided product boundary cocycle

Standard tracial conjugation turns the second copy into a commuting right
action. The resulting product cocycle is close to the product representation
with the explicit error `2 * δ + 2 * κ`.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
@[simp]
theorem conjugationOperator_one (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) :
    conjugationOperator J (1 : H →L[ℂ] H) = 1 := by
  ext ξ
  exact hJ ξ

omit [CompleteSpace H] in
theorem conjugationOperator_mul (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (a b : H →L[ℂ] H) :
    conjugationOperator J (a * b) = conjugationOperator J a * conjugationOperator J b := by
  ext ξ
  change J (a (b (J ξ))) = J (a (J (J (b (J ξ)))))
  rw [hJ (b (J ξ))]

omit [CompleteSpace H] in
theorem conjugationOperator_sub (J : H ≃ₗᵢ⋆[ℂ] H) (a b : H →L[ℂ] H) :
    conjugationOperator J (a - b) = conjugationOperator J a - conjugationOperator J b := by
  ext ξ
  exact map_sub J _ _

/-- The right-action operation is a homomorphism on the unitary group. -/
def conjugationUnitaryHom (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J) :
    unitary (H →L[ℂ] H) →* unitary (H →L[ℂ] H) where
  toFun := conjugationUnitary J hJ
  map_one' := by
    apply Subtype.ext
    exact conjugationOperator_one J hJ
  map_mul' a b := by
    apply Subtype.ext
    exact conjugationOperator_mul J hJ a b

omit [CompleteSpace H] in
/-- Conjugation by a conjugate-linear isometry preserves the operator norm. -/
theorem norm_conjugationOperator (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (a : H →L[ℂ] H) : ‖conjugationOperator J a‖ = ‖a‖ := by
  have hle (b : H →L[ℂ] H) : ‖conjugationOperator J b‖ ≤ ‖b‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro ξ
    change ‖J (b (J ξ))‖ ≤ ‖b‖ * ‖ξ‖
    rw [J.norm_map]
    simpa only [J.norm_map] using b.le_opNorm (J ξ)
  have hback := hle (conjugationOperator J a)
  rw [conjugationOperator_twice J hJ] at hback
  exact le_antisymm (hle a) hback

omit [CompleteSpace H] in
theorem norm_conjugationOperator_sub (J : H ≃ₗᵢ⋆[ℂ] H)
    (hJ : Function.Involutive J) (a b : H →L[ℂ] H) :
    ‖conjugationOperator J a - conjugationOperator J b‖ = ‖a - b‖ := by
  rw [← conjugationOperator_sub, norm_conjugationOperator J hJ]

omit [CompleteSpace H] in
/-- Moving the two conjugations costs at most twice their distance. -/
theorem norm_conjugationOperator_change_le (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H)
    (a : H →L[ℂ] H) :
    ‖conjugationOperator J₁ a - conjugationOperator J₂ a‖ ≤
      2 * ‖(J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)‖ * ‖a‖ := by
  let d : H →L⋆[ℂ] H := (J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  change ‖J₁ (a (J₁ ξ)) - J₂ (a (J₂ ξ))‖ ≤ _
  calc
    _ ≤ ‖J₁ (a (J₁ ξ)) - J₂ (a (J₁ ξ))‖ +
        ‖J₂ (a (J₁ ξ)) - J₂ (a (J₂ ξ))‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ = ‖d (a (J₁ ξ))‖ + ‖a (J₁ ξ - J₂ ξ)‖ := by
      rw [← map_sub J₂, J₂.norm_map, map_sub]
      rfl
    _ ≤ ‖d‖ * (‖a‖ * ‖ξ‖) + ‖a‖ * (‖d‖ * ‖ξ‖) := by
      apply add_le_add
      · exact (d.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (by simpa only [J₁.norm_map] using a.le_opNorm (J₁ ξ)) (norm_nonneg d))
      · exact (a.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (d.le_opNorm ξ) (norm_nonneg a))
    _ = _ := by dsimp only [d]; ring

namespace StandardTracialPosition

variable {N : VonNeumannAlgebra H} (p : StandardTracialPosition N)

/-- Left multiplication commutes with every tracial right multiplier. -/
theorem commute_conjugationOperator (a b : H →L[ℂ] H) (ha : a ∈ N) (hb : b ∈ N) :
    Commute a (conjugationOperator p.conjugation b) := by
  exact VonNeumannAlgebra.mem_commutant_iff.mp
    (conjugationOperator_mem_commutant N p.conjugation p.vector
      p.conjugation_algebraVector p.cyclic (⟨b, hb⟩ : Algebra N)) a ha

end StandardTracialPosition

variable {G D : Type*} [Group G]

/-- The pointwise product of the left cocycle and its tracial right copy. -/
def productBoundaryValue {N : VonNeumannAlgebra H} (p : StandardTracialPosition N)
    (W : G → D → unitary (H →L[ℂ] H)) (g : G × G) (x : D × D) :
    unitary (H →L[ℂ] H) :=
  W g.1 x.1 * conjugationUnitary p.conjugation p.conjugation_involutive (W g.2 x.2)

omit [Group G] in
@[simp]
theorem productBoundaryValue_coe {N : VonNeumannAlgebra H} (p : StandardTracialPosition N)
    (W : G → D → unitary (H →L[ℂ] H)) (g : G × G) (x : D × D) :
    (productBoundaryValue p W g x : H →L[ℂ] H) =
      (W g.1 x.1 : H →L[ℂ] H) *
        conjugationOperator p.conjugation (W g.2 x.2) := rfl

/-- The two-sided field satisfies the product-action cocycle law. -/
theorem productBoundaryValue_cocycle {N : VonNeumannAlgebra H}
    (p : StandardTracialPosition N) (α : G →* Equiv.Perm D)
    (W : G → D → unitary (H →L[ℂ] H))
    (hmem : ∀ g x, (W g x : H →L[ℂ] H) ∈ N)
    (hcoc : ∀ g h x, (W (g * h) x : H →L[ℂ] H) =
      (W g x : H →L[ℂ] H) * (W h (α g⁻¹ x) : H →L[ℂ] H))
    (g h : G × G) (x : D × D) :
    (productBoundaryValue p W (g * h) x : H →L[ℂ] H) =
      (productBoundaryValue p W g x : H →L[ℂ] H) *
        (productBoundaryValue p W h (α g.1⁻¹ x.1, α g.2⁻¹ x.2) : H →L[ℂ] H) := by
  simp only [productBoundaryValue_coe, Prod.fst_mul, Prod.snd_mul]
  rw [hcoc, hcoc, conjugationOperator_mul p.conjugation p.conjugation_involutive]
  have hc := p.commute_conjugationOperator (W h.1 (α g.1⁻¹ x.1)) (W g.2 x.2)
    (hmem _ _) (hmem _ _)
  calc
    _ = (W g.1 x.1 : H →L[ℂ] H) *
        ((W h.1 (α g.1⁻¹ x.1) : H →L[ℂ] H) *
          conjugationOperator p.conjugation (W g.2 x.2)) *
        conjugationOperator p.conjugation (W h.2 (α g.2⁻¹ x.2)) := by noncomm_ring
    _ = _ := by rw [hc.eq]; noncomm_ring

/-- The commuting left and right copies form an actual representation. -/
def productBoundaryRepresentation {M : VonNeumannAlgebra H}
    (p : StandardTracialPosition M) (U : G →* unitary (Algebra M)) :
    (G × G) →* unitary (H →L[ℂ] H) where
  toFun g :=
    Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) (U g.1) *
      conjugationUnitary p.conjugation p.conjugation_involutive
        (Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) (U g.2))
  map_one' := by
    apply Subtype.ext
    change (U 1 : Algebra M).val *
      conjugationOperator p.conjugation (U 1 : Algebra M).val = 1
    rw [map_one]
    change 1 * conjugationOperator p.conjugation 1 = 1
    rw [conjugationOperator_one p.conjugation p.conjugation_involutive, mul_one]
  map_mul' g h := by
    apply Subtype.ext
    change (((U (g.1 * h.1) : Algebra M).val) *
      conjugationOperator p.conjugation (U (g.2 * h.2) : Algebra M).val) = _
    simp only [map_mul, MulMemClass.coe_mul,
      conjugationOperator_mul p.conjugation p.conjugation_involutive]
    have hc := p.commute_conjugationOperator (U h.1 : Algebra M).val
      (U g.2 : Algebra M).val (U h.1).val.property (U g.2).val.property
    change ((U g.1 : Algebra M).val * (U h.1 : Algebra M).val) *
        (conjugationOperator p.conjugation (U g.2 : Algebra M).val *
          conjugationOperator p.conjugation (U h.2 : Algebra M).val) =
      ((U g.1 : Algebra M).val * conjugationOperator p.conjugation (U g.2 : Algebra M).val) *
        ((U h.1 : Algebra M).val * conjugationOperator p.conjugation (U h.2 : Algebra M).val)
    calc
      _ = (U g.1 : Algebra M).val *
          ((U h.1 : Algebra M).val * conjugationOperator p.conjugation (U g.2 : Algebra M).val) *
          conjugationOperator p.conjugation (U h.2 : Algebra M).val := by noncomm_ring
      _ = _ := by rw [hc.eq]; noncomm_ring

@[simp]
theorem productBoundaryRepresentation_coe {M : VonNeumannAlgebra H}
    (p : StandardTracialPosition M) (U : G →* unitary (Algebra M)) (g : G × G) :
    (productBoundaryRepresentation p U g : H →L[ℂ] H) =
      (U g.1 : Algebra M).val * conjugationOperator p.conjugation (U g.2 : Algebra M).val := rfl

/-- Perturbing two unitary factors and the conjugation has an additive bound. -/
theorem norm_product_conjugation_sub_le
    (J₁ J₂ : H ≃ₗᵢ⋆[ℂ] H) (hJ₂ : Function.Involutive J₂)
    (a b c d : unitary (H →L[ℂ] H))
    {δ κ : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hab : ‖(a : H →L[ℂ] H) - b‖ ≤ δ)
    (hcd : ‖(c : H →L[ℂ] H) - d‖ ≤ δ)
    (hJ : ‖(J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)‖ ≤ κ) :
    ‖(a : H →L[ℂ] H) * conjugationOperator J₂ c -
      (b : H →L[ℂ] H) * conjugationOperator J₁ d‖ ≤ 2 * δ + 2 * κ := by
  have hC : ‖conjugationOperator J₂ c‖ ≤ 1 := by
    rw [norm_conjugationOperator J₂ hJ₂]
    exact norm_unitary_le_one c
  have hCC : ‖conjugationOperator J₂ c - conjugationOperator J₁ d‖ ≤ δ + 2 * κ := by
    calc
      _ ≤ ‖conjugationOperator J₂ c - conjugationOperator J₂ d‖ +
          ‖conjugationOperator J₂ d - conjugationOperator J₁ d‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ δ + 2 * κ := by
        apply add_le_add
        · exact (norm_conjugationOperator_sub J₂ hJ₂ c d).le.trans hcd
        · calc
            _ = ‖conjugationOperator J₁ d - conjugationOperator J₂ d‖ := norm_sub_rev _ _
            _ ≤ 2 * ‖(J₁ : H →L⋆[ℂ] H) - (J₂ : H →L⋆[ℂ] H)‖ * ‖(d : H →L[ℂ] H)‖ :=
              norm_conjugationOperator_change_le _ _ _
            _ ≤ 2 * κ * 1 := mul_le_mul
              (mul_le_mul_of_nonneg_left hJ (by positivity)) (norm_unitary_le_one d)
              (norm_nonneg _) (by positivity)
            _ = _ := mul_one _
  calc
    _ = ‖((a : H →L[ℂ] H) - b) * conjugationOperator J₂ c +
        (b : H →L[ℂ] H) * (conjugationOperator J₂ c - conjugationOperator J₁ d)‖ := by
      congr 1
      noncomm_ring
    _ ≤ ‖((a : H →L[ℂ] H) - b) * conjugationOperator J₂ c‖ +
        ‖(b : H →L[ℂ] H) * (conjugationOperator J₂ c - conjugationOperator J₁ d)‖ := norm_add_le _ _
    _ ≤ (δ * 1) + (1 * (δ + 2 * κ)) := by
      apply add_le_add
      · exact (norm_mul_le _ _).trans (mul_le_mul hab hC (norm_nonneg _) hδ)
      · exact (norm_mul_le _ _).trans
          (mul_le_mul (norm_unitary_le_one b) hCC (norm_nonneg _) (by norm_num))
    _ = _ := by ring

/-- Pointwise perturbation of a two-sided boundary field. -/
theorem productBoundaryValue_close {M N : VonNeumannAlgebra H}
    (pM : StandardTracialPosition M) (pN : StandardTracialPosition N)
    (U : G →* unitary (Algebra M)) (W : G → D → unitary (H →L[ℂ] H))
    {δ κ : ℝ} (hδ : 0 ≤ δ) (hκ : 0 ≤ κ)
    (hclose : ∀ g x, ‖(W g x : H →L[ℂ] H) - (U g : Algebra M).val‖ ≤ δ)
    (hJ : ‖(pM.conjugation : H →L⋆[ℂ] H) - (pN.conjugation : H →L⋆[ℂ] H)‖ ≤ κ)
    (g : G × G) (x : D × D) :
    ‖(productBoundaryValue pN W g x : H →L[ℂ] H) -
      (productBoundaryRepresentation pM U g : H →L[ℂ] H)‖ ≤ 2 * δ + 2 * κ := by
  exact norm_product_conjugation_sub_le pM.conjugation pN.conjugation
    pN.conjugation_involutive (W g.1 x.1)
    (Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) (U g.1))
    (W g.2 x.2) (Unitary.map (StarMonoidHom.ofClass M.toStarSubalgebra.subtype) (U g.2))
    hδ hκ (hclose _ _) (hclose _ _) hJ

end

end KadisonKastler

end OAI
