import OAI.Dynamics.MultipleMixing.Entropy

namespace OAI

noncomputable section

namespace Rokhlin

section

open scoped InnerProductSpace CStarAlgebra
open ContinuousLinearMap

open MeasureTheory Filter
open scoped BigOperators Topology


variable {Ω : Type*} [MeasurableSpace Ω]

def timeMap (T : Ω ≃ᵐ Ω) (n : ℤ) : Ω → Ω :=
  ⇑((T.toEquiv : Equiv.Perm Ω) ^ n)

def IsMixing (μ : Measure Ω) (T : Ω ≃ᵐ Ω) : Prop :=
  ∀ A B : Set Ω, MeasurableSet A → MeasurableSet B →
    Tendsto (fun n : ℤ => μ (A ∩ timeMap T n ⁻¹' B))
      (comap Int.natAbs atTop) (𝓝 (μ A * μ B))

def layoutTime {k : ℕ} (gaps : Fin (k - 1) → ℕ+) (i : Fin k) : ℕ :=
  ∑ j : Fin (k - 1), if j.val < i.val then (gaps j : ℕ) else 0

def MixingOfOrder (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (k : ℕ) : Prop :=
  ∀ A : Fin k → Set Ω, (∀ i, MeasurableSet (A i)) →
    Tendsto
      (fun gaps : Fin (k - 1) → ℕ+ =>
        μ (⋂ i : Fin k, timeMap T (layoutTime gaps i : ℤ) ⁻¹' A i))
      atTop (𝓝 (∏ i : Fin k, μ (A i)))

section Rectangle

variable {H₁ H₂ H₃ H₄ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄]

open ContinuousLinearMap

theorem rectangle_square_identities
    (F : H₂ →L[ℂ] H₁) (G : H₄ →L[ℂ] H₃)
    (K : H₃ →L[ℂ] H₁) (N : H₄ →L[ℂ] H₂)
    (h₁ : F ∘L N = K ∘L G) (h₂ : F.adjoint ∘L K = N ∘L G.adjoint) :
    (K ∘L K.adjoint) ∘L F = F ∘L (N ∘L N.adjoint) ∧
    (K.adjoint ∘L K) ∘L G = G ∘L (N.adjoint ∘L N) ∧
    (F.adjoint ∘L F) ∘L N = N ∘L (G.adjoint ∘L G) ∧
    (F ∘L F.adjoint) ∘L K = K ∘L (G ∘L G.adjoint) := by
  have h₂' : K.adjoint ∘L F = G ∘L N.adjoint := by
    simpa only [adjoint_comp, adjoint_adjoint] using congrArg adjoint h₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (K ∘L K.adjoint) ∘L F = K ∘L (K.adjoint ∘L F) := comp_assoc _ _ _
      _ = K ∘L (G ∘L N.adjoint) := congrArg (K ∘L ·) h₂'
      _ = (K ∘L G) ∘L N.adjoint := (comp_assoc _ _ _).symm
      _ = (F ∘L N) ∘L N.adjoint := congrArg (· ∘L N.adjoint) h₁.symm
      _ = F ∘L (N ∘L N.adjoint) := comp_assoc _ _ _
  · calc
      (K.adjoint ∘L K) ∘L G = K.adjoint ∘L (K ∘L G) := comp_assoc _ _ _
      _ = K.adjoint ∘L (F ∘L N) := congrArg (K.adjoint ∘L ·) h₁.symm
      _ = (K.adjoint ∘L F) ∘L N := (comp_assoc _ _ _).symm
      _ = (G ∘L N.adjoint) ∘L N := congrArg (· ∘L N) h₂'
      _ = G ∘L (N.adjoint ∘L N) := comp_assoc _ _ _
  · calc
      (F.adjoint ∘L F) ∘L N = F.adjoint ∘L (F ∘L N) := comp_assoc _ _ _
      _ = F.adjoint ∘L (K ∘L G) := congrArg (F.adjoint ∘L ·) h₁
      _ = (F.adjoint ∘L K) ∘L G := (comp_assoc _ _ _).symm
      _ = (N ∘L G.adjoint) ∘L G := congrArg (· ∘L G) h₂
      _ = N ∘L (G.adjoint ∘L G) := comp_assoc _ _ _
  · calc
      (F ∘L F.adjoint) ∘L K = F ∘L (F.adjoint ∘L K) := comp_assoc _ _ _
      _ = F ∘L (N ∘L G.adjoint) := congrArg (F ∘L ·) h₂
      _ = (F ∘L N) ∘L G.adjoint := (comp_assoc _ _ _).symm
      _ = (K ∘L G) ∘L G.adjoint := congrArg (· ∘L G.adjoint) h₁
      _ = K ∘L (G ∘L G.adjoint) := comp_assoc _ _ _

end Rectangle

section EssentialRanges

variable {X E H J : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [NormedSpace ℂ H]
  [NormedAddCommGroup J] [NormedSpace ℂ J]

def HasEssentialTotalRange (μ : Measure X) (F : X → E →L[ℂ] H) : Prop :=
  ∀ p : Submodule ℂ H, IsClosed (p : Set H) →
    (∀ᵐ x ∂μ, LinearMap.range (F x).toLinearMap ≤ p) → p = ⊤

theorem HasEssentialTotalRange.cancel_left {μ : Measure X}
    {F : X → E →L[ℂ] H} (hF : HasEssentialTotalRange μ F)
    {A B : H →L[ℂ] J} (h : ∀ᵐ x ∂μ, A ∘L F x = B ∘L F x) : A = B := by
  have hker : (A - B).ker = ⊤ := by
    apply hF (A - B).ker (A - B).isClosed_ker
    filter_upwards [h] with x hx
    rintro y ⟨v, rfl⟩
    change A (F x v) - B (F x v) = 0
    exact sub_eq_zero.mpr (DFunLike.congr_fun hx v)
  apply sub_eq_zero.mp
  ext v
  have hv : v ∈ (A - B).ker := by rw [hker]; trivial
  exact hv

theorem essentially_constant_of_intertwining
    {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (μC : Measure C) (μX : Measure X) (μD : Measure D)
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μX] [IsProbabilityMeasure μD]
    (F : X → E →L[ℂ] H) (A : C → H →L[ℂ] H) (B : D → E →L[ℂ] E)
    (hF : HasEssentialTotalRange μX F)
    (h : ∀ᵐ p ∂μC.prod (μX.prod μD),
      A p.1 ∘L F p.2.1 = F p.2.1 ∘L B p.2.2) :
    ∃ Q : H →L[ℂ] H, ∀ᵐ c ∂μC, A c = Q := by
  have h' : ∀ᵐ c ∂μC, ∀ᵐ x ∂μX, ∀ᵐ d ∂μD,
      A c ∘L F x = F x ∘L B d :=
    (Measure.ae_ae_of_ae_prod h).mono fun _ hc => Measure.ae_ae_of_ae_prod hc
  obtain ⟨c₀, hc₀⟩ := h'.exists
  refine ⟨A c₀, h'.mono fun c hc => ?_⟩
  apply hF.cancel_left
  filter_upwards [hc, hc₀] with x hx hx₀
  obtain ⟨d, hd, hd₀⟩ := (hx.and hx₀).exists
  exact hd.trans hd₀.symm

end EssentialRanges

section HilbertEssentialRanges

variable {X E H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem HasEssentialTotalRange.eq_zero_of_adjoint_ae_eq_zero
    {μ : Measure X} {F : X → E →L[ℂ] H} (hF : HasEssentialTotalRange μ F)
    {v : H} (hv : ∀ᵐ x ∂μ, (F x).adjoint v = 0) : v = 0 := by
  have hh : innerSL ℂ v = (0 : H →L[ℂ] ℂ) := by
    apply hF.cancel_left
    filter_upwards [hv] with x hx
    ext w
    change inner ℂ v (F x w) = 0
    rw [← ContinuousLinearMap.adjoint_inner_left, hx, inner_zero_left]
  exact inner_self_eq_zero.mp (DFunLike.congr_fun hh v)

theorem fixed_source_square_injective {μ : Measure X} (F : X → E →L[ℂ] H)
    (hF : HasEssentialTotalRange μ (fun x => (F x).adjoint))
    (Q : E →L[ℂ] E) (hQ : ∀ᵐ x ∂μ, (F x).adjoint ∘L F x = Q) :
    Function.Injective Q := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  apply hF.eq_zero_of_adjoint_ae_eq_zero
  filter_upwards [hQ] with x hx
  rw [ContinuousLinearMap.adjoint_adjoint]
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hz : (F x).adjoint (F x v) = 0 := by
    change ((F x).adjoint ∘L F x) v = 0
    rw [hx]
    exact hv
  rw [hz, inner_zero_right]

theorem essentially_constant_right_of_intertwining
    {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (μC : Measure C) (μX : Measure X) (μD : Measure D)
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μX] [IsProbabilityMeasure μD]
    (F : X → E →L[ℂ] H) (A : C → H →L[ℂ] H) (B : D → E →L[ℂ] E)
    (hF : HasEssentialTotalRange μX (fun x => (F x).adjoint))
    (h : ∀ᵐ p ∂μC.prod (μX.prod μD),
      A p.1 ∘L F p.2.1 = F p.2.1 ∘L B p.2.2) :
    ∃ Q : E →L[ℂ] E, ∀ᵐ d ∂μD, B d = Q := by
  obtain ⟨c₀, hc₀⟩ := (Measure.ae_ae_of_ae_prod h).exists
  have hh : ∀ᵐ p ∂μD.prod μX, A c₀ ∘L F p.2 = F p.2 ∘L B p.1 := by
    have hh' : ∀ᵐ p ∂(μD.prod μX).map Prod.swap,
        A c₀ ∘L F p.1 = F p.1 ∘L B p.2 := by
      rw [Measure.prod_swap]
      exact hc₀
    exact ae_of_ae_map measurable_swap.aemeasurable hh'
  have h' := Measure.ae_ae_of_ae_prod hh
  obtain ⟨d₀, hd₀⟩ := h'.exists
  refine ⟨B d₀, h'.mono fun d hd => ?_⟩
  have heq : (B d).adjoint = (B d₀).adjoint := by
    apply hF.cancel_left
    filter_upwards [hd, hd₀] with x hx hx₀
    have hh := congrArg adjoint (hx.symm.trans hx₀)
    simpa only [adjoint_comp] using hh
  simpa only [adjoint_adjoint] using congrArg adjoint heq

theorem fixed_ends_of_product_intertwining
    {C D : Type*} [MeasurableSpace C] [MeasurableSpace D]
    (μC : Measure C) (μX : Measure X) (μD : Measure D)
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μX] [IsProbabilityMeasure μD]
    (F : X → E →L[ℂ] H) (A : C → H →L[ℂ] H) (B : D → E →L[ℂ] E)
    (hF : HasEssentialTotalRange μX F)
    (hF' : HasEssentialTotalRange μX (fun x => (F x).adjoint))
    (h : ∀ᵐ p ∂μC.prod (μX.prod μD),
      A p.1 ∘L F p.2.1 = F p.2.1 ∘L B p.2.2) :
    (∃ Q : H →L[ℂ] H, ∀ᵐ c ∂μC, A c = Q) ∧
      (∃ Q : E →L[ℂ] E, ∀ᵐ d ∂μD, B d = Q) :=
  ⟨essentially_constant_of_intertwining μC μX μD F A B hF h,
    essentially_constant_right_of_intertwining μC μX μD F A B hF' h⟩

end HilbertEssentialRanges

section Polar
variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem denseRange_iff_adjoint_injective (T : E →L[ℂ] H) :
    DenseRange T ↔ Function.Injective T.adjoint := by
  change Dense (LinearMap.range T.toLinearMap : Set H) ↔ _
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, T.orthogonal_range, LinearMap.ker_eq_bot]
  rfl

theorem exists_unitary_of_selfAdjoint_square
    (T : E →L[ℂ] H) (A : E →L[ℂ] E)
    (hA : IsSelfAdjoint A) (hAi : Function.Injective A)
    (hT : DenseRange T) (hAT : A ∘L A = T.adjoint ∘L T) :
    ∃ U : E ≃ₗᵢ[ℂ] H, ∀ x, U (A x) = T x := by
  have hAd : DenseRange A := (denseRange_iff_adjoint_injective A).mpr (by
    rw [hA.adjoint_eq]; exact hAi)
  have hn : ∀ x, ‖T x‖ = ‖A x‖ := by
    intro x
    have hsq : ‖T x‖ ^ 2 = ‖A x‖ ^ 2 := by
      rw [T.apply_norm_sq_eq_inner_adjoint_right, A.apply_norm_sq_eq_inner_adjoint_right,
        hA.adjoint_eq, hAT]
    nlinarith [norm_nonneg (T x), norm_nonneg (A x)]
  refine ⟨(LinearEquiv.refl ℂ E).extendOfIsometry A.toLinearMap T.toLinearMap hAd hT hn, ?_⟩
  intro x
  exact LinearEquiv.extendOfIsometry_eq _ _ _ hAd hT hn x

noncomputable def operatorAbs (T : E →L[ℂ] H) : E →L[ℂ] E :=
  CFC.sqrt (T.adjoint ∘L T)

theorem operatorAbs_nonneg (T : E →L[ℂ] H) : 0 ≤ operatorAbs T :=
  CFC.sqrt_nonneg _

theorem operatorAbs_sq (T : E →L[ℂ] H) :
    operatorAbs T ∘L operatorAbs T = T.adjoint ∘L T := by
  exact CFC.sqrt_mul_sqrt_self _ ((nonneg_iff_isPositive).mpr
    (isPositive_adjoint_comp_self T))

theorem operatorAbs_injective (T : E →L[ℂ] H) (hT : Function.Injective T) :
    Function.Injective (operatorAbs T) := by
  have hTT : Function.Injective (T.adjoint ∘L T) :=
    T.adjoint_comp_self_injective_iff.mpr hT
  rw [← operatorAbs_sq] at hTT
  intro x y hxy
  exact hTT (congrArg (operatorAbs T) hxy)

theorem exists_unitary_polar (T : E →L[ℂ] H)
    (hTi : Function.Injective T) (hTd : DenseRange T) :
    ∃ U : E ≃ₗᵢ[ℂ] H, ∀ x, U (operatorAbs T x) = T x := by
  exact exists_unitary_of_selfAdjoint_square T (operatorAbs T)
    (IsSelfAdjoint.of_nonneg (operatorAbs_nonneg T))
    (operatorAbs_injective T hTi) hTd (operatorAbs_sq T)

end Polar

section
variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def intertwinerAlgebra (N : E →L[ℂ] H) :
    StarSubalgebra ℝ ((H →L[ℂ] H) × (E →L[ℂ] E)) where
  carrier := {p | p.1 ∘L N = N ∘L p.2 ∧ star p.1 ∘L N = N ∘L star p.2}
  add_mem' := by
    rintro ⟨A,B⟩ ⟨C,D⟩ ⟨h₁,h₂⟩ ⟨h₃,h₄⟩
    change (A+C) ∘L N = N ∘L (B+D) ∧ star (A+C) ∘L N = N ∘L star (B+D)
    simp only [add_comp, comp_add, star_add, h₁, h₂, h₃, h₄, and_self]
  mul_mem' := by
    rintro ⟨A,B⟩ ⟨C,D⟩ ⟨h₁,h₂⟩ ⟨h₃,h₄⟩
    change (A ∘L C) ∘L N = N ∘L (B ∘L D) ∧
      star (A*C) ∘L N = N ∘L star (B*D)
    constructor
    · rw [comp_assoc, h₃, ← comp_assoc, h₁, comp_assoc]
    · simp only [star_mul]
      change (star C ∘L star A) ∘L N = N ∘L (star D ∘L star B)
      rw [comp_assoc, h₂, ← comp_assoc, h₄, comp_assoc]
  algebraMap_mem' := by
    intro r
    constructor <;> ext x <;> simp [← algebraMap_star_comm]
  star_mem' := by
    rintro ⟨A,B⟩ ⟨h₁,h₂⟩
    exact ⟨h₂, by simpa using h₁⟩

instance intertwinerAlgebra_isClosed (N : E →L[ℂ] H) :
    IsClosed (intertwinerAlgebra N : Set ((H →L[ℂ] H) × (E →L[ℂ] E))) := by
  change IsClosed {p : (H →L[ℂ] H) × (E →L[ℂ] E) |
    p.1 ∘L N = N ∘L p.2 ∧ star p.1 ∘L N = N ∘L star p.2}
  apply IsClosed.inter
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · exact isClosed_eq (by fun_prop) (by fun_prop)

theorem sqrt_intertwines (A : H →L[ℂ] H) (B : E →L[ℂ] E) (N : E →L[ℂ] H)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h : A ∘L N = N ∘L B) :
    CFC.sqrt A ∘L N = N ∘L CFC.sqrt B := by
  have hm : (A,B) ∈ intertwinerAlgebra N := by
    refine ⟨h, ?_⟩
    rw [(IsSelfAdjoint.of_nonneg hA).star_eq, (IsSelfAdjoint.of_nonneg hB).star_eq]
    exact h
  have hh := cfcₙ_mem (p := IsSelfAdjoint) (𝕜 := ℝ) (𝕜' := ℝ) (s := intertwinerAlgebra N)
    (fun x : ℝ => Real.sqrt x) hm
  rw [← CFC.sqrt_eq_real_sqrt (A,B) (show 0 ≤ (A,B) from ⟨hA,hB⟩),
    CFC.sqrt_map_prod hA hB] at hh
  exact hh.1
end

section PolarRectangle
variable {H₁ H₂ H₃ H₄ : Type*}
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄]

omit [CompleteSpace H₁] [CompleteSpace H₂] [CompleteSpace H₃] in
theorem eq_of_comp_eq_of_denseRange (A B : H₂ →L[ℂ] H₁) (C : H₃ →L[ℂ] H₂)
    (hC : DenseRange C) (h : A ∘L C = B ∘L C) : A = B := by
  apply DFunLike.coe_injective
  exact hC.equalizer A.continuous B.continuous (by
    funext x
    exact congrArg (fun S : H₃ →L[ℂ] H₁ => S x) h)

theorem operatorAbs_denseRange (T : H₂ →L[ℂ] H₁) (hT : Function.Injective T) :
    DenseRange (operatorAbs T) := by
  apply (denseRange_iff_adjoint_injective _).mpr
  rw [(IsSelfAdjoint.of_nonneg (operatorAbs_nonneg T)).adjoint_eq]
  exact operatorAbs_injective T hT

theorem polar_rectangle
    (F : H₂ →L[ℂ] H₁) (G : H₄ →L[ℂ] H₃)
    (K : H₃ →L[ℂ] H₁) (N : H₄ →L[ℂ] H₂)
    (h₁ : F ∘L N = K ∘L G) (h₂ : F.adjoint ∘L K = N ∘L G.adjoint)
    (hGi : Function.Injective G) (hNi : Function.Injective N)
    (UF : H₂ ≃ₗᵢ[ℂ] H₁) (UG : H₄ ≃ₗᵢ[ℂ] H₃)
    (UK : H₃ ≃ₗᵢ[ℂ] H₁) (UN : H₄ ≃ₗᵢ[ℂ] H₂)
    (hF : (UF : H₂ →L[ℂ] H₁) ∘L operatorAbs F = F)
    (hG : (UG : H₄ →L[ℂ] H₃) ∘L operatorAbs G = G)
    (hK : (UK : H₃ →L[ℂ] H₁) ∘L operatorAbs K = K)
    (hN : (UN : H₄ →L[ℂ] H₂) ∘L operatorAbs N = N) :
    (UF : H₂ →L[ℂ] H₁) ∘L (UN : H₄ →L[ℂ] H₂) =
      (UK : H₃ →L[ℂ] H₁) ∘L (UG : H₄ →L[ℂ] H₃) := by
  have hsq := (rectangle_square_identities F G K N h₁ h₂).2.2.1
  have hroot : operatorAbs F ∘L N = N ∘L operatorAbs G :=
    sqrt_intertwines _ _ N
      ((nonneg_iff_isPositive).mpr (isPositive_adjoint_comp_self F))
      ((nonneg_iff_isPositive).mpr (isPositive_adjoint_comp_self G)) hsq
  have hmid : (UF : H₂ →L[ℂ] H₁) ∘L N = K ∘L (UG : H₄ →L[ℂ] H₃) := by
    apply eq_of_comp_eq_of_denseRange _ _ (operatorAbs G) (operatorAbs_denseRange G hGi)
    calc
      ((UF : H₂ →L[ℂ] H₁) ∘L N) ∘L operatorAbs G =
        (UF : H₂ →L[ℂ] H₁) ∘L (operatorAbs F ∘L N) := by
          rw [comp_assoc, hroot]
      _ = F ∘L N := by rw [← comp_assoc, hF]
      _ = K ∘L G := h₁
      _ = (K ∘L (UG : H₄ →L[ℂ] H₃)) ∘L operatorAbs G := by rw [comp_assoc, hG]
  have hss : N.adjoint ∘L N =
      (UG.symm : H₃ →L[ℂ] H₄) ∘L (K.adjoint ∘L K) ∘L (UG : H₄ →L[ℂ] H₃) := by
    have hh := congrArg (fun S : H₄ →L[ℂ] H₁ => S.adjoint ∘L S) hmid
    ext x
    simpa [adjoint_comp] using congrArg (fun S : H₄ →L[ℂ] H₄ => S x) hh
  have hsq' : (K.adjoint ∘L K) ∘L (UG : H₄ →L[ℂ] H₃) =
      (UG : H₄ →L[ℂ] H₃) ∘L (N.adjoint ∘L N) := by
    rw [hss]
    ext x
    simp
  have hroot' : operatorAbs K ∘L (UG : H₄ →L[ℂ] H₃) =
      (UG : H₄ →L[ℂ] H₃) ∘L operatorAbs N :=
    sqrt_intertwines _ _ (UG : H₄ →L[ℂ] H₃)
      ((nonneg_iff_isPositive).mpr (isPositive_adjoint_comp_self K))
      ((nonneg_iff_isPositive).mpr (isPositive_adjoint_comp_self N)) hsq'
  apply eq_of_comp_eq_of_denseRange _ _ (operatorAbs N) (operatorAbs_denseRange N hNi)
  calc
    ((UF : H₂ →L[ℂ] H₁) ∘L (UN : H₄ →L[ℂ] H₂)) ∘L operatorAbs N =
      (UF : H₂ →L[ℂ] H₁) ∘L N := by rw [comp_assoc, hN]
    _ = K ∘L (UG : H₄ →L[ℂ] H₃) := hmid
    _ = (UK : H₃ →L[ℂ] H₁) ∘L (operatorAbs K ∘L (UG : H₄ →L[ℂ] H₃)) := by
      rw [← comp_assoc, hK]
    _ = ((UK : H₃ →L[ℂ] H₁) ∘L (UG : H₄ →L[ℂ] H₃)) ∘L operatorAbs N := by
      rw [hroot', comp_assoc]
end PolarRectangle

variable {X Y C D H₁ H₂ H₃ H₄ : Type*}
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace C] [MeasurableSpace D]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
  [NormedAddCommGroup H₃] [InnerProductSpace ℂ H₃] [CompleteSpace H₃]
  [NormedAddCommGroup H₄] [InnerProductSpace ℂ H₄] [CompleteSpace H₄]

def HasFixedInjectiveSquares (μ : Measure X) (F : X → H₂ →L[ℂ] H₁) : Prop :=
  ∃ P : H₂ →L[ℂ] H₂, ∃ Q : H₁ →L[ℂ] H₁,
    Function.Injective P ∧ Function.Injective Q ∧
    (∀ᵐ x ∂μ, (F x).adjoint ∘L F x = P) ∧
    (∀ᵐ x ∂μ, F x ∘L (F x).adjoint = Q)

theorem hasFixedInjectiveSquares_of_fixed
    (μ : Measure X) (F : X → H₂ →L[ℂ] H₁)
    (hF : HasEssentialTotalRange μ F)
    (hFa : HasEssentialTotalRange μ (fun x => (F x).adjoint))
    (hP : ∃ P, ∀ᵐ x ∂μ, (F x).adjoint ∘L F x = P)
    (hQ : ∃ Q, ∀ᵐ x ∂μ, F x ∘L (F x).adjoint = Q) :
    HasFixedInjectiveSquares μ F := by
  obtain ⟨P, hP⟩ := hP
  obtain ⟨Q, hQ⟩ := hQ
  refine ⟨P, Q, fixed_source_square_injective F hFa P hP, ?_, hP, hQ⟩
  apply fixed_source_square_injective (fun x => (F x).adjoint) (by simpa using hF) Q
  simpa using hQ

theorem fixed_squares_of_product_identities
    (μX : Measure X) (μY : Measure Y) (μC : Measure C) (μD : Measure D)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsProbabilityMeasure μC] [IsProbabilityMeasure μD]
    (F : X → H₂ →L[ℂ] H₁) (G : Y → H₄ →L[ℂ] H₃)
    (K : C → H₃ →L[ℂ] H₁) (N : D → H₄ →L[ℂ] H₂)
    (hF : HasEssentialTotalRange μX F)
    (hFa : HasEssentialTotalRange μX (fun x => (F x).adjoint))
    (hG : HasEssentialTotalRange μY G)
    (hGa : HasEssentialTotalRange μY (fun y => (G y).adjoint))
    (hK : HasEssentialTotalRange μC K)
    (hKa : HasEssentialTotalRange μC (fun c => (K c).adjoint))
    (hN : HasEssentialTotalRange μD N)
    (hNa : HasEssentialTotalRange μD (fun d => (N d).adjoint))
    (h₁ : ∀ᵐ p ∂μC.prod (μX.prod μD),
      (K p.1 ∘L (K p.1).adjoint) ∘L F p.2.1 =
        F p.2.1 ∘L (N p.2.2 ∘L (N p.2.2).adjoint))
    (h₂ : ∀ᵐ p ∂μC.prod (μY.prod μD),
      ((K p.1).adjoint ∘L K p.1) ∘L G p.2.1 =
        G p.2.1 ∘L ((N p.2.2).adjoint ∘L N p.2.2))
    (h₃ : ∀ᵐ p ∂μX.prod (μD.prod μY),
      ((F p.1).adjoint ∘L F p.1) ∘L N p.2.1 =
        N p.2.1 ∘L ((G p.2.2).adjoint ∘L G p.2.2))
    (h₄ : ∀ᵐ p ∂μX.prod (μC.prod μY),
      (F p.1 ∘L (F p.1).adjoint) ∘L K p.2.1 =
        K p.2.1 ∘L (G p.2.2 ∘L (G p.2.2).adjoint)) :
    HasFixedInjectiveSquares μX F ∧ HasFixedInjectiveSquares μY G ∧
    HasFixedInjectiveSquares μC K ∧ HasFixedInjectiveSquares μD N := by
  have hKK := essentially_constant_of_intertwining μC μX μD F
    (fun c => K c ∘L (K c).adjoint) (fun d => N d ∘L (N d).adjoint) hF h₁
  have hNN := essentially_constant_right_of_intertwining μC μX μD F
    (fun c => K c ∘L (K c).adjoint) (fun d => N d ∘L (N d).adjoint) hFa h₁
  have hKK' := essentially_constant_of_intertwining μC μY μD G
    (fun c => (K c).adjoint ∘L K c) (fun d => (N d).adjoint ∘L N d) hG h₂
  have hNN' := essentially_constant_right_of_intertwining μC μY μD G
    (fun c => (K c).adjoint ∘L K c) (fun d => (N d).adjoint ∘L N d) hGa h₂
  have hFF' := essentially_constant_of_intertwining μX μD μY N
    (fun x => (F x).adjoint ∘L F x) (fun y => (G y).adjoint ∘L G y) hN h₃
  have hGG' := essentially_constant_right_of_intertwining μX μD μY N
    (fun x => (F x).adjoint ∘L F x) (fun y => (G y).adjoint ∘L G y) hNa h₃
  have hFF := essentially_constant_of_intertwining μX μC μY K
    (fun x => F x ∘L (F x).adjoint) (fun y => G y ∘L (G y).adjoint) hK h₄
  have hGG := essentially_constant_right_of_intertwining μX μC μY K
    (fun x => F x ∘L (F x).adjoint) (fun y => G y ∘L (G y).adjoint) hKa h₄
  exact ⟨hasFixedInjectiveSquares_of_fixed μX F hF hFa hFF' hFF,
    hasFixedInjectiveSquares_of_fixed μY G hG hGa hGG' hGG,
    hasFixedInjectiveSquares_of_fixed μC K hK hKa hKK' hKK,
    hasFixedInjectiveSquares_of_fixed μD N hN hNa hNN' hNN⟩

end

section
open MeasureTheory Filter
variable {Ω : Type*} [MeasurableSpace Ω]
lemma timeMap_zero (T : Ω ≃ᵐ Ω) : timeMap T 0 = id := by
  simp [timeMap]
lemma timeMap_add (T : Ω ≃ᵐ Ω) (m n : ℤ) : timeMap T (m+n) = timeMap T m ∘ timeMap T n := by
  simp only [timeMap,zpow_add,Equiv.Perm.coe_mul]
lemma timeMap_nat (T : Ω ≃ᵐ Ω) (n : ℕ) : timeMap T n = (T : Ω → Ω)^[n] := by
  simp only [timeMap,zpow_natCast,Equiv.Perm.coe_pow,MeasurableEquiv.coe_toEquiv]
lemma timeMap_neg_nat (T : Ω ≃ᵐ Ω) (n : ℕ) : timeMap T (-(n:ℤ)) = (T.symm : Ω → Ω)^[n] := by
  simp only [timeMap,zpow_neg,zpow_natCast,←inv_pow,Equiv.Perm.coe_pow]
  rfl
lemma timeMap_preserving (μ : Measure Ω) (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ) (n : ℤ) :
    MeasurePreserving (timeMap T n) μ μ := by
  induction n using Int.negInduction with
  | nat n => rw [timeMap_nat]; exact hT.iterate n
  | neg _ n => rw [timeMap_neg_nat]; exact (hT.symm T).iterate n
lemma timeMap_measurable (T : Ω ≃ᵐ Ω) (n : ℤ) : Measurable (timeMap T n) := by
  induction n using Int.negInduction with
  | nat n => rw [timeMap_nat]; exact T.measurable.iterate n
  | neg _ n => rw [timeMap_neg_nat]; exact T.symm.measurable.iterate n
lemma timeMap_comm (T : Ω ≃ᵐ Ω) (m n : ℤ) (x : Ω) :
    timeMap T m (timeMap T n x) = timeMap T n (timeMap T m x) := by
  change (timeMap T m ∘ timeMap T n) x = (timeMap T n ∘ timeMap T m) x
  rw [←timeMap_add,←timeMap_add,add_comm]
lemma timeMap_inv_apply (T : Ω ≃ᵐ Ω) (n : ℤ) (x : Ω) : timeMap T (-n) (timeMap T n x) = x := by
  change (timeMap T (-n) ∘ timeMap T n) x = x
  rw [←timeMap_add,neg_add_cancel,timeMap_zero]
  rfl
end

section
open MeasureTheory Filter
open scoped Topology RealInnerProductSpace
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] (μ : Measure Ω) [retained6 : IsProbabilityMeasure μ]

include retained6 in
lemma reverse_tail_pairing_along (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) (c : ℕ → ℕ) (hc : Tendsto c atTop atTop)
    (f : Lp ℝ 2 μ) (g : ℕ → Lp ℝ 2 μ)
    (hg : ∀ n, AEStronglyMeasurable[m (c n)] (g n) μ) (hb : ∀ n, ‖g n‖ ≤ 1) :
    Tendsto (fun n => ⟪f - (condExpL2 ℝ ℝ
      (show (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ from
        (iInf_le _ 0).trans (completedFactor_le μ (m 0))) f : Lp ℝ 2 μ), g n⟫)
      atTop (𝓝 0) := by
  let _ := retained6
  let ft : Lp ℝ 2 μ := condExpL2 ℝ ℝ
    (show (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ from
      (iInf_le _ 0).trans (completedFactor_le μ (m 0))) f
  have he n : ⟪f-ft,g n⟫ = ⟪(condExpL2 ℝ ℝ (hm (c n)) f : Lp ℝ 2 μ)-ft,g n⟫ := by
    simp only [inner_sub_left,inner_condExpL2_eq_inner_fun (hm (c n)) f (g n) (hg n)]
  have hbound n : |⟪f-ft,g n⟫| ≤ ‖(condExpL2 ℝ ℝ (hm (c n)) f : Lp ℝ 2 μ)-ft‖ := by
    rw [he]
    exact (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg ((condExpL2 ℝ ℝ (hm (c n)) f : Lp ℝ 2 μ)-ft),hb n])
  have ht := (reverse_conditional_L2 μ m hm hanti f).comp hc
  have ht' : Tendsto (fun n => ‖(condExpL2 ℝ ℝ (hm (c n)) f : Lp ℝ 2 μ)-ft‖) atTop (𝓝 0) := by
    simpa only [ft,sub_self,norm_zero,Function.comp_apply] using (ht.sub (tendsto_const_nhds (x := ft))).norm
  exact squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using hbound n) ht'

lemma integral_tail_replacement (m : ℕ → MeasurableSpace Ω) (hm : ∀ n, m n ≤ m₀)
    (hanti : Antitone m) (c : ℕ → ℕ) (hc : Tendsto c atTop atTop)
    (f : Ω → ℝ) (hf : MemLp f 2 μ) (g : ℕ → Ω → ℝ)
    (hg : ∀ n, Measurable[m (c n)] (g n)) (hb : ∀ n x, |g n x| ≤ 1) :
    Tendsto (fun n => ∫ x, (f x-μ[f | ⨅ n, completedFactor (m₀ := m₀) μ (m n)] x)*g n x ∂μ)
      atTop (𝓝 0) := by
  have hgm n : MemLp (g n) 2 μ := MemLp.of_bound
    ((hg n).mono (hm (c n)) le_rfl).aestronglyMeasurable 1
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb n x)
  let G n : Lp ℝ 2 μ := (hgm n).toLp (g n)
  let ht : (⨅ n, completedFactor (m₀ := m₀) μ (m n)) ≤ m₀ :=
    (iInf_le _ 0).trans (completedFactor_le μ (m 0))
  let F : Lp ℝ 2 μ := hf.toLp f
  let FT : Lp ℝ 2 μ := condExpL2 ℝ ℝ ht F
  have hG n : AEStronglyMeasurable[m (c n)] (G n) μ :=
    (hg n).stronglyMeasurable.aestronglyMeasurable.congr (hgm n).coeFn_toLp.symm
  have hGb n : ‖G n‖ ≤ 1 := by
    have hb' : ∀ᵐ x ∂μ, ‖G n x‖ ≤ (1:ℝ) := by
      filter_upwards [(hgm n).coeFn_toLp] with x hx
      simpa only [G,hx,Real.norm_eq_abs] using hb n x
    simpa only [measureUnivNNReal,measure_univ,ENNReal.toNNReal_one,NNReal.coe_one,Real.one_rpow,one_mul]
      using Lp.norm_le_of_ae_bound (f := G n) (by norm_num : (0:ℝ) ≤ 1) hb'
  have hh := reverse_tail_pairing_along μ m hm hanti c hc F G hG hGb
  change Tendsto (fun n => ⟪F-FT,G n⟫) atTop (𝓝 0) at hh
  convert hh using 1
  funext n
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,(hgm n).coeFn_toLp,
    hf.condExpL2_ae_eq_condExp (𝕜 := ℝ) ht,Lp.coeFn_sub F FT] with x hx hy hz hw
  change F x = f x at hx
  change G n x = g n x at hy
  change FT x = μ[f | ⨅ n, completedFactor (m₀ := m₀) μ (m n)] x at hz
  rw [hw,Pi.sub_apply,hx,hy,hz]
  simp [mul_comm]
end

section
open MeasureTheory MeasurableSpace
open scoped ENNReal
variable {Y : Type*} [m : MeasurableSpace Y] [CountablyGenerated Y]
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

def hilbertTestAlgebra : Set (Set Y) := generateSetAlgebra (Set.range (natGeneratingSequence Y))

lemma hilbertTestAlgebra_algebra : IsSetAlgebra (hilbertTestAlgebra (Y := Y)) :=
  isSetAlgebra_generateSetAlgebra

lemma hilbertTestAlgebra_countable : (hilbertTestAlgebra (Y := Y)).Countable :=
  countable_generateSetAlgebra (Set.countable_range _)

lemma hilbertTestAlgebra_generates : m = generateFrom (hilbertTestAlgebra (Y := Y)) := by
  rw [hilbertTestAlgebra,generateFrom_generateSetAlgebra_eq,generateFrom_natGeneratingSequence]

lemma hilbertTestAlgebra_measurable {s : Set Y} (hs : s ∈ hilbertTestAlgebra) : MeasurableSet s := by
  rw [hilbertTestAlgebra_generates (Y := Y)]
  exact measurableSet_generateFrom hs

lemma hilbertTestAlgebra_dense (μ : Measure Y) [IsFiniteMeasure μ] :
    (Submodule.span ℂ (Set.range (fun s : hilbertTestAlgebra (Y := Y) =>
      indicatorConstLp 2 (hilbertTestAlgebra_measurable s.property) (measure_ne_top μ s) (1 : ℂ)))).topologicalClosure = ⊤ := by
  let D := (Submodule.span ℂ (Set.range (fun s : hilbertTestAlgebra (Y := Y) =>
      indicatorConstLp 2 (hilbertTestAlgebra_measurable s.property) (measure_ne_top μ s) (1 : ℂ)))).topologicalClosure
  have hd := Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ hilbertTestAlgebra_algebra hilbertTestAlgebra_generates
  have hunit (s : Set Y) (hs : s ∈ hilbertTestAlgebra) (hμs : μ s ≠ ∞) (c : ℂ) :
      indicatorConstLp 2 (hd.measurable s hs) hμs c ∈ D := by
    have he : indicatorConstLp 2 (hd.measurable s hs) hμs c =
        c • indicatorConstLp 2 (hilbertTestAlgebra_measurable hs) (measure_ne_top μ s) (1 : ℂ) := by
      apply Lp.ext
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hd.measurable s hs) (hμs := hμs) (c := c),
        Lp.coeFn_smul c (indicatorConstLp 2 (hilbertTestAlgebra_measurable hs) (measure_ne_top μ s) (1 : ℂ)),
        indicatorConstLp_coeFn (p := 2) (hs := hilbertTestAlgebra_measurable hs) (hμs := measure_ne_top μ s) (c := (1 : ℂ))] with y hy hsm h1
      rw [hy,hsm]
      change s.indicator (fun _ => c) y = c • indicatorConstLp 2 (hilbertTestAlgebra_measurable hs) (measure_ne_top μ s) (1 : ℂ) y
      rw [h1]
      by_cases hys : y ∈ s <;> simp [hys]
    rw [he]
    exact D.smul_mem c (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨s,hs⟩,rfl⟩))
  apply top_unique
  intro v _
  change v ∈ D
  apply Lp.induction (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (fun v => v ∈ D)
  · intro c s hs hμs
    have hm := hd.indicatorConstLp_subset_closure (p := 2) c ⟨s,hs,hμs.ne,rfl⟩
    exact (closure_minimal (by rintro _ ⟨s,hs,hμs,rfl⟩; exact hunit s hs hμs c) (Submodule.isClosed_topologicalClosure _)) hm
  · intro f g hf hg hfg hF hG
    exact D.add_mem hF hG
  · exact (Submodule.isClosed_topologicalClosure _)

end

section
open MeasureTheory MeasurableSpace Topology
open scoped ENNReal
variable {Y : Type*} [MeasurableSpace Y] [CountablyGenerated Y]
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

abbrev HilbertTestKey (Y : Type*) [MeasurableSpace Y] [CountablyGenerated Y] :=
  List ((ℚ × ℚ) × hilbertTestAlgebra (Y := Y))

instance : Countable (HilbertTestKey Y) := by
  have : Countable (hilbertTestAlgebra (Y := Y)) := hilbertTestAlgebra_countable.to_subtype
  infer_instance

def hilbertTestFunction (t : HilbertTestKey Y) : Y → ℂ :=
  fun y => (t.map (fun p => ((p.1.1 : ℂ) + p.1.2 * Complex.I) *
    (p.2.val.indicator (fun _ => (1 : ℂ))) y)).sum

lemma hilbertTestFunction_measurable (t : HilbertTestKey Y) : Measurable (hilbertTestFunction t) := by
  induction t with
  | nil =>
    change Measurable (fun _ : Y => (0 : ℂ))
    exact measurable_const
  | cons p t ih =>
    change Measurable (fun y => ((p.1.1 : ℂ) + p.1.2 * Complex.I) *
      (p.2.val.indicator (fun _ => (1 : ℂ))) y + hilbertTestFunction t y)
    exact (measurable_const.mul (measurable_const.indicator (hilbertTestAlgebra_measurable p.2.property))).add ih

def hilbertTestVector (μ : Measure Y) [IsFiniteMeasure μ] (t : HilbertTestKey Y) : Lp ℂ 2 μ :=
  (t.map (fun p => ((p.1.1 : ℂ) + p.1.2 * Complex.I) •
    indicatorConstLp 2 (hilbertTestAlgebra_measurable p.2.property) (measure_ne_top μ p.2.val) (1 : ℂ))).sum

lemma hilbertTestVector_append (μ : Measure Y) [IsFiniteMeasure μ] (s t : HilbertTestKey Y) :
    hilbertTestVector μ (s ++ t) = hilbertTestVector μ s + hilbertTestVector μ t := by
  simp [hilbertTestVector]

lemma rationalComplex_dense : DenseRange (fun p : ℚ × ℚ => (p.1 : ℂ) + p.2 * Complex.I) := by
  have h := Rat.denseRange_cast (𝕜 := ℝ)
  have hh := h.prodMap h
  have hsurj : Function.Surjective (fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * Complex.I) := by
    intro z
    exact ⟨(z.re,z.im),Complex.re_add_im z⟩
  convert hsurj.denseRange.comp hh (by fun_prop) using 1
  ext p
  simp

lemma hilbertTestVector_dense (μ : Measure Y) [IsFiniteMeasure μ] :
    DenseRange (hilbertTestVector μ) := by
  let S : AddSubmonoid (Lp ℂ 2 μ) := {
    carrier := Set.range (hilbertTestVector μ)
    zero_mem' := ⟨[],by simp [hilbertTestVector]⟩
    add_mem' := by
      rintro _ _ ⟨s,rfl⟩ ⟨t,rfl⟩
      exact ⟨s ++ t,hilbertTestVector_append μ s t⟩ }
  let D := S.topologicalClosure
  have hd : IsClosed (D : Set (Lp ℂ 2 μ)) := AddSubmonoid.isClosed_topologicalClosure S
  have hsingle (t : hilbertTestAlgebra (Y := Y)) (c : ℂ) :
      c • indicatorConstLp 2 (hilbertTestAlgebra_measurable t.property)
        (measure_ne_top μ t.val) (1 : ℂ) ∈ D := by
    refine rationalComplex_dense.induction_on c
      (hd.preimage (continuous_id.smul continuous_const)) ?_
    intro q
    apply (show (S : Set (Lp ℂ 2 μ)) ⊆ D from subset_closure)
    exact ⟨[(q,t)],by simp [hilbertTestVector]⟩
  have hspan : (Submodule.span ℂ (Set.range (fun t : hilbertTestAlgebra (Y := Y) =>
      indicatorConstLp 2 (hilbertTestAlgebra_measurable t.property)
        (measure_ne_top μ t.val) (1 : ℂ))) : Set (Lp ℂ 2 μ)) ⊆ D := by
    intro v hv
    have h : ∀ c : ℂ, c • v ∈ D := by
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨t,rfl⟩ := hx
        exact hsingle t
      | zero => intro c; simp only [smul_zero]; exact D.zero_mem
      | add x y hx hy ihx ihy =>
        intro c
        simpa only [smul_add] using D.add_mem (ihx c) (ihy c)
      | smul a x hx ih => intro c; simpa only [smul_smul] using ih (c*a)
    simpa using h 1
  intro v
  have hall : (Submodule.span ℂ (Set.range (fun t : hilbertTestAlgebra (Y := Y) =>
      indicatorConstLp 2 (hilbertTestAlgebra_measurable t.property)
        (measure_ne_top μ t.val) (1 : ℂ)))).topologicalClosure = ⊤ := hilbertTestAlgebra_dense μ
  have hv : v ∈ (Submodule.span ℂ (Set.range (fun t : hilbertTestAlgebra (Y := Y) =>
      indicatorConstLp 2 (hilbertTestAlgebra_measurable t.property)
        (measure_ne_top μ t.val) (1 : ℂ)))).topologicalClosure := by rw [hall]; trivial
  exact closure_minimal hspan hd hv
end

section
open Filter Topology MeasureTheory

def IsDistanceCode (d : ℕ → ℕ → ℝ) (z : ℕ → ℝ) : Prop :=
  (∀ n, 0 ≤ z n) ∧ (∀ n m, z n ≤ d n m + z m) ∧
    (∀ n m, d n m ≤ z n + z m) ∧ ∀ m : ℕ, ∃ n, z n < (1/2 : ℝ)^m

variable {H : Type*} [MetricSpace H] [CompleteSpace H]
omit [CompleteSpace H] in
lemma distance_isCode {a : ℕ → H} (ha : DenseRange a) (v : H) :
    IsDistanceCode (fun n m => dist (a n) (a m)) (fun n => dist v (a n)) := by
  refine ⟨fun n => dist_nonneg, ?_, ?_, ?_⟩
  · intro n m
    simpa [dist_comm,add_comm] using dist_triangle v (a m) (a n)
  · intro n m
    simpa [dist_comm] using dist_triangle (a n) v (a m)
  · intro m
    exact ha.exists_dist_lt v (by positivity : 0 < (1/2 : ℝ)^m)

lemma IsDistanceCode.exists_eq {a : ℕ → H} {z : ℕ → ℝ}
    (hz : IsDistanceCode (fun n m => dist (a n) (a m)) z) :
    ∃ v : H, ∀ n, dist v (a n) = z n := by
  choose b hb using hz.2.2.2
  have ht : Tendsto (fun m => z (b m)) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => hz.1 _)
      (Eventually.of_forall fun m => (hb m).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  have hc : CauchySeq (fun m => a (b m)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨N, fun m hm n hn => ?_⟩
    have h := hz.2.2.1 (b m) (b n)
    have := hN m hm
    have := hN n hn
    linarith
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨v,fun n => le_antisymm ?_ ?_⟩
  · have h := le_of_tendsto_of_tendsto (hv.dist tendsto_const_nhds)
      (ht.add_const (z n)) (Eventually.of_forall fun m => hz.2.2.1 (b m) n)
    simpa using h
  · have h := le_of_tendsto_of_tendsto tendsto_const_nhds
      ((tendsto_const_nhds.dist hv).add ht)
      (Eventually.of_forall fun m => hz.2.1 n (b m))
    simpa [dist_comm] using h

omit [CompleteSpace H] in
lemma distance_code_injective {a : ℕ → H} (ha : DenseRange a) :
    Function.Injective (fun v : H => fun n => dist v (a n)) := by
  intro v w he
  have hh : ∀ b : H, dist v b = dist w b := fun b => ha.induction_on b
    (isClosed_eq (continuous_const.dist continuous_id) (continuous_const.dist continuous_id))
    (fun n => congrFun he n)
  simpa [dist_comm] using (hh v).symm

lemma isDistanceCode_iff {a : ℕ → H} (ha : DenseRange a) {z : ℕ → ℝ} :
    IsDistanceCode (fun n m => dist (a n) (a m)) z ↔
      ∃! v : H, ∀ n, dist v (a n) = z n := by
  constructor
  · intro hz
    obtain ⟨v,hv⟩ := hz.exists_eq
    exact ⟨v,hv,fun w hw => distance_code_injective ha (funext fun n => (hw n).trans (hv n).symm)⟩
  · rintro ⟨v,hv,_⟩
    have he : (fun n => dist v (a n)) = z := funext hv
    rw [←he]
    exact distance_isCode ha v

variable {U : Type*} [MeasurableSpace U]
lemma measurableSet_distanceCode (d : U → ℕ → ℕ → ℝ)
    (hd : ∀ n m, Measurable (fun u => d u n m)) :
    MeasurableSet {p : U × (ℕ → ℝ) | IsDistanceCode (d p.1) p.2} := by
  have hz (n : ℕ) : Measurable (fun p : U × (ℕ → ℝ) => p.2 n) :=
    (measurable_pi_apply n).comp measurable_snd
  have hd' (n m : ℕ) : Measurable (fun p : U × (ℕ → ℝ) => d p.1 n m) :=
    (hd n m).comp measurable_fst
  simp only [IsDistanceCode, Set.ofPred_and, Set.ofPred_forall, Set.ofPred_exists]
  exact (MeasurableSet.iInter fun n => measurableSet_le measurable_const (hz n)).inter
    ((MeasurableSet.iInter fun n => MeasurableSet.iInter fun m =>
      measurableSet_le (hz n) ((hd' n m).add (hz m))).inter
    ((MeasurableSet.iInter fun n => MeasurableSet.iInter fun m =>
      measurableSet_le (hd' n m) ((hz n).add (hz m))).inter
    (MeasurableSet.iInter fun m : ℕ => MeasurableSet.iUnion fun n : ℕ =>
      measurableSet_lt (hz n) measurable_const)))
end

section
open MeasureTheory MeasurableSpace ProbabilityTheory
open scoped ENNReal InnerProductSpace
variable {Y : Type*} [MeasurableSpace Y] [CountablyGenerated Y]
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

lemma hilbertTestVector_coe (μ : Measure Y) [IsFiniteMeasure μ] (t : HilbertTestKey Y) :
    ↑(hilbertTestVector μ t) =ᵐ[μ] hilbertTestFunction t := by
  induction t with
  | nil => exact Lp.coeFn_zero _ _ _
  | cons p t ih =>
    let c : ℂ := (p.1.1 : ℂ) + p.1.2 * Complex.I
    let f := indicatorConstLp 2 (hilbertTestAlgebra_measurable p.2.property)
      (measure_ne_top μ p.2.val) (1 : ℂ)
    change ↑(c • f + hilbertTestVector μ t) =ᵐ[μ] _
    filter_upwards [Lp.coeFn_add (c • f) (hilbertTestVector μ t),Lp.coeFn_smul c f,
      indicatorConstLp_coeFn (p := 2) (hs := hilbertTestAlgebra_measurable p.2.property)
        (hμs := measure_ne_top μ p.2.val) (c := (1 : ℂ)),ih] with y hadd hsm hf ht
    change (c • f + hilbertTestVector μ t) y = c * _ + hilbertTestFunction t y
    rw [hadd]
    change (c • f) y + hilbertTestVector μ t y = _
    rw [hsm]
    change c * f y + hilbertTestVector μ t y = _
    rw [hf,ht]

def hilbertTestKeys : ℕ → HilbertTestKey Y := Classical.choose (exists_surjective_nat (HilbertTestKey Y))
lemma hilbertTestKeys_surjective : Function.Surjective (hilbertTestKeys (Y := Y)) :=
  Classical.choose_spec (exists_surjective_nat (HilbertTestKey Y))

def hilbertTests (μ : Measure Y) [IsFiniteMeasure μ] (n : ℕ) : Lp ℂ 2 μ :=
  hilbertTestVector μ (hilbertTestKeys n)
lemma hilbertTests_dense (μ : Measure Y) [IsFiniteMeasure μ] : DenseRange (hilbertTests μ) :=
  by
    have hr : Set.range (hilbertTests μ) = Set.range (hilbertTestVector μ) := by
      ext v
      constructor
      · rintro ⟨n,rfl⟩
        exact ⟨hilbertTestKeys n,rfl⟩
      · rintro ⟨t,rfl⟩
        obtain ⟨n,rfl⟩ := hilbertTestKeys_surjective t
        exact ⟨n,rfl⟩
    intro v
    simpa only [hr] using hilbertTestVector_dense μ v

lemma hilbertTestVector_dist (μ : Measure Y) [IsFiniteMeasure μ] (s t : HilbertTestKey Y) :
    dist (hilbertTestVector μ s) (hilbertTestVector μ t) =
      Real.sqrt (Complex.re (∫ y, inner ℂ (hilbertTestFunction s y - hilbertTestFunction t y)
        (hilbertTestFunction s y - hilbertTestFunction t y) ∂μ)) := by
  rw [dist_eq_norm]
  have he : (∫ y, inner ℂ ((hilbertTestVector μ s - hilbertTestVector μ t) y)
      ((hilbertTestVector μ s - hilbertTestVector μ t) y) ∂μ) =
      ∫ y, inner ℂ (hilbertTestFunction s y - hilbertTestFunction t y)
        (hilbertTestFunction s y - hilbertTestFunction t y) ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (hilbertTestVector μ s) (hilbertTestVector μ t),
      hilbertTestVector_coe μ s,hilbertTestVector_coe μ t] with y hd hs ht
    rw [hd]
    change inner ℂ (hilbertTestVector μ s y - hilbertTestVector μ t y)
      (hilbertTestVector μ s y - hilbertTestVector μ t y) = _
    rw [hs,ht]
  rw [←he,←L2.inner_def]
  exact norm_eq_sqrt_re_inner (𝕜 := ℂ) _

variable {U : Type*} [MeasurableSpace U]
lemma hilbertTests_dist_measurable (κ : Kernel U Y) [IsMarkovKernel κ] (n m : ℕ) :
    Measurable (fun u => dist (hilbertTests (κ u) n) (hilbertTests (κ u) m)) := by
  simp only [hilbertTests,hilbertTestVector_dist]
  apply Real.continuous_sqrt.measurable.comp
  apply Complex.continuous_re.measurable.comp
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.integral_kernel
  exact ((hilbertTestFunction_measurable _).sub (hilbertTestFunction_measurable _)).stronglyMeasurable.inner
    ((hilbertTestFunction_measurable _).sub (hilbertTestFunction_measurable _)).stronglyMeasurable

end

section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  (κ : Kernel U Y) [IsMarkovKernel κ]
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

def HilbertCode := {p : U × (ℕ → ℝ) //
  IsDistanceCode (fun n m => dist (hilbertTests (κ p.1) n) (hilbertTests (κ p.1) m)) p.2}

instance : MeasurableSpace (HilbertCode κ) := inferInstanceAs (MeasurableSpace (Subtype _))
instance [StandardBorelSpace U] : StandardBorelSpace (HilbertCode κ) := by
  apply MeasurableSet.standardBorel
  exact measurableSet_distanceCode _ (hilbertTests_dist_measurable κ)

namespace HilbertCode
variable {κ}
def base (p : HilbertCode κ) : U := p.val.1
def code (p : HilbertCode κ) : ℕ → ℝ := p.val.2
lemma measurable_base : Measurable (base (κ := κ)) := measurable_fst.comp measurable_subtype_coe
lemma measurable_code (n : ℕ) : Measurable (fun p : HilbertCode κ => p.code n) :=
  ((measurable_pi_apply n).comp measurable_snd).comp measurable_subtype_coe

def decode (p : HilbertCode κ) : Lp ℂ 2 (κ p.base) := p.property.exists_eq.choose
lemma decode_dist (p : HilbertCode κ) (n : ℕ) :
    dist p.decode (hilbertTests (κ p.base) n) = p.code n := p.property.exists_eq.choose_spec n

def encode (u : U) (v : Lp ℂ 2 (κ u)) : HilbertCode κ :=
  ⟨(u,fun n => dist v (hilbertTests (κ u) n)),distance_isCode (hilbertTests_dense (κ u)) v⟩
lemma decode_encode (u : U) (v : Lp ℂ 2 (κ u)) : (encode u v).decode = v := by
  apply distance_code_injective (hilbertTests_dense (κ u))
  funext n
  exact (encode u v).decode_dist n

lemma encode_decode (p : HilbertCode κ) : encode p.base p.decode = p := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  funext n
  exact p.decode_dist n

def approxIndex (p : HilbertCode κ) (m : ℕ) : ℕ := Nat.find (p.property.2.2.2 m)
lemma approxIndex_spec (p : HilbertCode κ) (m : ℕ) :
    dist (hilbertTests (κ p.base) (approxIndex p m)) p.decode < (1/2 : ℝ)^m := by
  rw [dist_comm,decode_dist]
  exact Nat.find_spec (p.property.2.2.2 m)

lemma measurable_approxIndex (m : ℕ) : Measurable (fun p : HilbertCode κ => approxIndex p m) := by
  exact Measurable.find (f := fun n (_ : HilbertCode κ) => n) (fun _ => measurable_const)
    (fun n => measurableSet_lt (measurable_code (κ := κ) n) measurable_const)
    (fun p => p.property.2.2.2 m)

def approximant (m : ℕ) (p : HilbertCode κ × Y) : ℂ :=
  hilbertTestFunction (hilbertTestKeys (approxIndex p.1 m)) p.2

lemma measurable_approximant (m : ℕ) : Measurable (approximant (κ := κ) m) := by
  have hm : Measurable (fun p : ℕ × Y => hilbertTestFunction (hilbertTestKeys p.1) p.2) :=
    measurable_from_prod_countable_right fun n => hilbertTestFunction_measurable (hilbertTestKeys n)
  exact hm.comp (((measurable_approxIndex m).comp measurable_fst).prodMk measurable_snd)

def representative (p : HilbertCode κ × Y) : ℂ :=
  limUnder atTop (fun m => approximant m p)
lemma measurable_representative : Measurable (representative (κ := κ)) := by
  exact (StronglyMeasurable.limUnder fun m => (measurable_approximant m).stronglyMeasurable).measurable

lemma representative_eq_decode (p : HilbertCode κ) :
    (fun y => representative (p,y)) =ᵐ[κ p.base] (p.decode : Y → ℂ) := by
  let v (m : ℕ) : Lp ℂ 2 (κ p.base) :=
    hilbertTests (κ p.base) (approxIndex p m) - p.decode
  have hvnorm (m) : ‖v m‖ ≤ (1/2 : ℝ)^m := by
    simpa only [v,←dist_eq_norm] using (approxIndex_spec p m).le
  have hsum : Summable (fun m => ‖v m‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hvnorm summable_geometric_two
  have hfinite : ∑' m, eLpNorm (v m : Y → ℂ) 2 (κ p.base) ≠ ⊤ := by
    have he (m) : eLpNorm (v m : Y → ℂ) 2 (κ p.base) = (‖v m‖₊ : ℝ≥0∞) := by
      rw [Lp.nnnorm_def,ENNReal.coe_toNNReal (Lp.eLpNorm_ne_top _)]
    simp only [he]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr (NNReal.summable_coe.mp hsum)
  have hae := summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    hfinite
  have heq : ∀ᵐ y ∂κ p.base, ∀ m, v m y = approximant m (p,y) - p.decode y := by
    rw [ae_all_iff]
    intro m
    filter_upwards [Lp.coeFn_sub (hilbertTests (κ p.base) (approxIndex p m)) p.decode,
      hilbertTestVector_coe (κ p.base) (hilbertTestKeys (approxIndex p m))] with y hd hf
    change (hilbertTests (κ p.base) (approxIndex p m) - p.decode) y = _
    rw [hd]
    change hilbertTestVector (κ p.base) (hilbertTestKeys (approxIndex p m)) y - p.decode y = _
    rw [hf]
    rfl
  filter_upwards [hae,heq] with y hy he
  apply Tendsto.limUnder_eq
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := hy.tendsto_atTop_zero
  simpa only [he] using ht

end HilbertCode
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  {κ : Kernel U Y} [IsMarkovKernel κ]
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩

omit [MeasurableSpace.CountablyGenerated Y] in
lemma lp_dist_of_representatives {μ : Measure Y} (v w : Lp ℂ 2 μ)
    (f g : Y → ℂ) (hf : (v : Y → ℂ) =ᵐ[μ] f) (hg : (w : Y → ℂ) =ᵐ[μ] g) :
    dist v w = Real.sqrt (Complex.re (∫ y, inner ℂ (f y - g y) (f y - g y) ∂μ)) := by
  rw [dist_eq_norm]
  have he : (∫ y, inner ℂ ((v-w) y) ((v-w) y) ∂μ) =
      ∫ y, inner ℂ (f y-g y) (f y-g y) ∂μ := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub v w,hf,hg] with y hd hv hw
    rw [hd]
    change inner ℂ (v y-w y) (v y-w y) = _
    rw [hv,hw]
  rw [←he,←L2.inner_def]
  exact norm_eq_sqrt_re_inner (𝕜 := ℂ) _

namespace HilbertCode

def distance (p q : HilbertCode κ) : ℝ := Real.sqrt (Complex.re (∫ y,
  inner ℂ (representative (p,y) - representative (q,y))
    (representative (p,y) - representative (q,y)) ∂κ p.base))

lemma distance_encode (u : U) (v w : Lp ℂ 2 (κ u)) :
    distance (encode u v) (encode u w) = dist v w := by
  have hv := representative_eq_decode (encode u v)
  have hw := representative_eq_decode (encode u w)
  simp only [decode_encode] at hv hw
  exact (lp_dist_of_representatives v w _ _ hv.symm hw.symm).symm

lemma measurable_distance : Measurable (fun p : HilbertCode κ × HilbertCode κ => distance p.1 p.2) := by
  let ξ : Kernel (HilbertCode κ × HilbertCode κ) Y := κ.comap (fun p : HilbertCode κ × HilbertCode κ => p.1.base)
    (measurable_base.comp measurable_fst)
  have hf : StronglyMeasurable (fun p : (HilbertCode κ × HilbertCode κ) × Y =>
      inner ℂ (representative (p.1.1,p.2)-representative (p.1.2,p.2))
        (representative (p.1.1,p.2)-representative (p.1.2,p.2))) := by
    have h₁ : Measurable (fun p : (HilbertCode κ × HilbertCode κ) × Y => representative (p.1.1,p.2)) := (measurable_representative (κ := κ)).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h₂ : Measurable (fun p : (HilbertCode κ × HilbertCode κ) × Y => representative (p.1.2,p.2)) := (measurable_representative (κ := κ)).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    exact (h₁.sub h₂).stronglyMeasurable.inner (h₁.sub h₂).stronglyMeasurable
  exact Real.continuous_sqrt.measurable.comp
    (Complex.continuous_re.measurable.comp (hf.integral_kernel_prod_right (κ := ξ) (f := fun p y =>
      inner ℂ (representative (p.1,y)-representative (p.2,y))
        (representative (p.1,y)-representative (p.2,y)))).measurable)
end HilbertCode

lemma measurable_hilbert_encode {V : Type*} [MeasurableSpace V]
    (u : V → U) (hu : Measurable u) (s : ∀ v, Lp ℂ 2 (κ (u v)))
    (f : V × Y → ℂ) (hf : Measurable f)
    (he : ∀ v, (s v : Y → ℂ) =ᵐ[κ (u v)] (fun y => f (v,y))) :
    Measurable (fun v => HilbertCode.encode (u v) (s v)) := by
  apply Measurable.subtype_mk
  apply hu.prodMk
  apply Measurable.of_eval
  intro n
  have hdist : (fun v => dist (s v) (hilbertTests (κ (u v)) n)) =
      fun v => Real.sqrt (Complex.re (∫ y,
        inner ℂ (f (v,y)-hilbertTestFunction (hilbertTestKeys n) y)
          (f (v,y)-hilbertTestFunction (hilbertTestKeys n) y) ∂κ (u v))) := by
    funext v
    exact lp_dist_of_representatives _ _ _ _ (he v) (hilbertTestVector_coe _ _)
  change Measurable (fun v => dist (s v) (hilbertTests (κ (u v)) n))
  rw [hdist]
  have hh := hf.sub ((hilbertTestFunction_measurable (hilbertTestKeys n)).comp measurable_snd)
  exact Real.continuous_sqrt.measurable.comp
    (Complex.continuous_re.measurable.comp
      ((hh.stronglyMeasurable.inner hh.stronglyMeasurable).integral_kernel_prod_right
        (κ := κ.comap u hu)).measurable)
end

section
open scoped InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def RayCanonical (t : ℕ → H) (v : H) : Prop :=
  ∃ n, (∀ m < n, inner ℂ (t m) v = 0) ∧
    0 < (inner ℂ (t n) v).re ∧ (inner ℂ (t n) v).im = 0

lemma exists_inner_ne_zero_of_dense (t : ℕ → H) (ht : DenseRange t) {v : H} (hv : v ≠ 0) :
    ∃ n, inner ℂ (t n) v ≠ 0 := by
  by_contra! h
  have he : ∀ w, inner ℂ w v = 0 := by
    intro w
    exact ht.induction_on w (isClosed_eq (continuous_id.inner continuous_const) continuous_const) h
  exact hv ((inner_self_eq_zero (𝕜 := ℂ)).mp (he v))

lemma exists_rayCanonical (t : ℕ → H) (ht : DenseRange t) {v : H} (hv : v ≠ 0) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ RayCanonical t (a • v) := by
  have hex := exists_inner_ne_zero_of_dense t ht hv
  let n := Nat.find hex
  let z := inner ℂ (t n) v
  have hz : z ≠ 0 := Nat.find_spec hex
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let a : ℂ := (‖z‖ : ℂ) / z
  have han : ‖a‖ = 1 := by
    dsimp [a]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hnz,div_self hnz.ne']
  refine ⟨a,han,n,?_,?_,?_⟩
  · intro m hm
    rw [inner_smul_right,not_ne_iff.mp (Nat.find_min hex hm),mul_zero]
  · have he : inner ℂ (t n) (a • v) = (‖z‖ : ℂ) := by
      rw [inner_smul_right]
      exact div_mul_cancel₀ _ hz
    rw [he,Complex.ofReal_re]
    exact hnz
  · have he : inner ℂ (t n) (a • v) = (‖z‖ : ℂ) := by
      rw [inner_smul_right]
      exact div_mul_cancel₀ _ hz
    rw [he,Complex.ofReal_im]

lemma rayCanonical_unique {t : ℕ → H} {v w : H}
    (hv : RayCanonical t v) (hw : RayCanonical t w)
    {a : ℂ} (ha : ‖a‖ = 1) (he : v = a • w) : v = w := by
  obtain ⟨n,hn,hpn,hin⟩ := hv
  obtain ⟨m,hm,hpm,him⟩ := hw
  have hne : inner ℂ (t n) v ≠ 0 := by
    intro h; rw [h] at hpn; simp at hpn
  have hme : inner ℂ (t m) w ≠ 0 := by
    intro h; rw [h] at hpm; simp at hpm
  have han : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hnm : n = m := by
    rcases lt_trichotomy n m with h | h | h
    · have hh := hm n h
      rw [he,inner_smul_right,hh,mul_zero] at hne
      exact (hne rfl).elim
    · exact h
    · have hh := hn m h
      rw [he,inner_smul_right] at hh
      exact (mul_ne_zero han hme hh).elim
  subst m
  have hev : inner ℂ (t n) v = ((inner ℂ (t n) v).re : ℂ) := by
    apply Complex.ext <;> simp [hin]
  have hew : inner ℂ (t n) w = ((inner ℂ (t n) w).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hnorm : ‖inner ℂ (t n) v‖ = ‖inner ℂ (t n) w‖ := by
    rw [he,inner_smul_right,norm_mul,ha,one_mul]
  have hcoeff : inner ℂ (t n) v = inner ℂ (t n) w := by
    rw [hev,hew] at hnorm ⊢
    have hh : (inner ℂ (t n) v).re = (inner ℂ (t n) w).re := by
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpn,abs_of_pos hpm] using hnorm
    rw [hh]
  have ha1 : a = 1 := by
    apply (mul_right_cancel₀ hme)
    simpa only [one_mul,←inner_smul_right,←he,one_smul] using hcoeff
  simpa [ha1] using he
end

section
open MeasureTheory MeasurableSpace Set
variable {P T : Type*} [MeasurableSpace P] [CountablySeparated P]
  [MeasurableSpace T] [StandardBorelSpace T]

lemma borel_injective_cover_branches (p : T → P) (hp : Measurable p)
    (U : ℕ → Set T) (hU : ∀ n, MeasurableSet (U n))
    (hcover : (⋃ n, U n) = Set.univ)
    (hinj : ∀ n, Set.InjOn p (U n)) :
    ∃ C : ℕ → Set T, (∀ n, MeasurableSet (C n)) ∧
      (⋃ n, C n) = Set.univ ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (∀ n, MeasurableEmbedding (fun x : C n => p x)) := by
  refine ⟨disjointed U, fun n => MeasurableSet.disjointed hU n, ?_, disjoint_disjointed U, ?_⟩
  · rwa [iUnion_disjointed]
  · intro n
    let : StandardBorelSpace ↥(disjointed U n) := MeasurableSet.standardBorel (MeasurableSet.disjointed hU n)
    apply (hp.comp measurable_subtype_coe).measurableEmbedding
    intro x y hxy
    apply Subtype.ext
    exact hinj n (disjointed_subset U n x.property) (disjointed_subset U n y.property) hxy
end

namespace HilbertCode
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]

def coefficient (p : HilbertCode κ) (n : ℕ) : ℂ :=
  ∫ y, inner ℂ (hilbertTestFunction (hilbertTestKeys n) y) (representative (p,y)) ∂κ p.base

lemma coefficient_eq (p : HilbertCode κ) (n : ℕ) :
    coefficient p n = inner ℂ (hilbertTests (κ p.base) n) p.decode := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hilbertTestVector_coe (κ p.base) (hilbertTestKeys n),representative_eq_decode p]
    with y ht hv
  rw [hv]
  change inner ℂ _ _ = inner ℂ (hilbertTestVector _ _ y) _
  rw [ht]

lemma measurable_coefficient (n : ℕ) : Measurable (fun p : HilbertCode κ => coefficient p n) := by
  have hh : StronglyMeasurable (fun p : HilbertCode κ × Y =>
      inner ℂ (hilbertTestFunction (hilbertTestKeys n) p.2) (representative p)) :=
    ((hilbertTestFunction_measurable _).comp measurable_snd).stronglyMeasurable.inner
      measurable_representative.stronglyMeasurable
  exact (hh.integral_kernel_prod_right (κ := κ.comap base measurable_base)
    (f := fun p y => inner ℂ (hilbertTestFunction (hilbertTestKeys n) y) (representative (p,y)))).measurable

def IsCanonical (p : HilbertCode κ) : Prop := RayCanonical (hilbertTests (κ p.base)) p.decode

lemma measurableSet_isCanonical : MeasurableSet {p : HilbertCode κ | IsCanonical p} := by
  simp only [IsCanonical,RayCanonical,←coefficient_eq,Set.ofPred_exists,Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun m => MeasurableSet.iInter fun _ =>
      measurableSet_eq_fun (measurable_coefficient m) measurable_const
  · exact (measurableSet_lt measurable_const (Complex.continuous_re.measurable.comp (measurable_coefficient n))).inter
      (measurableSet_eq_fun (Complex.continuous_im.measurable.comp (measurable_coefficient n)) measurable_const)

def IsUnimodular (p : HilbertCode κ) : Prop :=
  ∀ᵐ y ∂κ p.base, ‖representative (p,y)‖ = 1

lemma measurableSet_isUnimodular : MeasurableSet {p : HilbertCode κ | IsUnimodular p} := by
  have ht : MeasurableSet {p : HilbertCode κ × Y | ‖representative p‖ ≠ 1} :=
    (measurableSet_eq_fun measurable_representative.norm measurable_const).compl
  have hm := Kernel.measurable_kernel_prodMk_left (κ := κ.comap base measurable_base) ht
  exact measurableSet_eq_fun hm measurable_const

lemma norm_decode_eq_one {p : HilbertCode κ} (hp : IsUnimodular p) : ‖p.decode‖ = 1 := by
  have hn : ∀ᵐ y ∂κ p.base, ‖p.decode y‖ = ‖(1 : ℂ)‖ := by
    filter_upwards [hp,representative_eq_decode p] with y hy he
    simpa only [norm_one,he] using hy
  rw [Lp.norm_def,eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable p.decode) aestronglyMeasurable_const hn,eLpNorm_const (1 : ℂ) (by norm_num) (IsProbabilityMeasure.ne_zero (κ p.base))]
  simp

lemma distance_le_codes (p q : HilbertCode κ) (he : p.base = q.base) (n : ℕ) :
    distance p q ≤ p.code n + q.code n := by
  rcases p with ⟨⟨u,a⟩,ha⟩
  rcases q with ⟨⟨v,b⟩,hb⟩
  change u = v at he
  subst v
  let p : HilbertCode κ := ⟨(u,a),ha⟩
  let q : HilbertCode κ := ⟨(u,b),hb⟩
  change distance p q ≤ p.code n + q.code n
  have hp : encode u p.decode = p := encode_decode p
  have hq : encode u q.decode = q := encode_decode q
  have hd : distance p q = dist p.decode q.decode := by
    exact (congrArg₂ distance hp hq).symm.trans (distance_encode u
      (show Lp ℂ 2 (κ u) from p.decode) (show Lp ℂ 2 (κ u) from q.decode))
  rw [hd]
  rw [←decode_dist p n,←decode_dist q n]
  exact (dist_triangle _ (hilbertTests (κ u) n) _).trans_eq (by rw [dist_comm (hilbertTests (κ u) n) q.decode]; rfl)
end HilbertCode

section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ComplexConjugate


theorem exact_mean_dichotomy {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hk : 3 ≤ Fintype.card ι) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (heq : ∀ i, a i = ∏ j ∈ Finset.univ.erase i, a j) :
    (∀ i, a i = 0) ∨ (∀ i, a i = 1) := by
  classical
  by_cases hz : ∃ i, a i = 0
  · obtain ⟨i, hi⟩ := hz
    left
    intro j
    by_cases hij : i = j
    · simpa [← hij] using hi
    · rw [heq j]
      exact Finset.prod_eq_zero (by simp [hij]) hi
  · have hn (i) : a i ≠ 0 := fun hi => hz ⟨i, hi⟩
    have hp (i) : 0 < a i := lt_of_le_of_ne (ha i) (hn i).symm
    have hl (i) : 2 * Real.log (a i) = ∑ j, Real.log (a j) := by
      have hh := congrArg Real.log (heq i)
      rw [Real.log_prod (fun j _ => hn j)] at hh
      have hs := Finset.sum_erase_add (s := Finset.univ)
        (fun j => Real.log (a j)) (Finset.mem_univ i)
      linarith
    have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ)
      rfl (fun i _ => hl i)
    simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hc : (3 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hk
    have hsum : ∑ j, Real.log (a j) = 0 := by nlinarith
    right
    intro i
    have hi : Real.log (a i) = 0 := by simpa [hsum] using hl i
    rw [← Real.exp_log (hp i), hi, Real.exp_zero]

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in

theorem exact_tuple_mean_equations
    (f : ι → Ω → ℂ) (hm : ∀ i, AEStronglyMeasurable (f i) μ)
    (hn : ∀ i, ∀ᵐ ω ∂μ, ‖f i ω‖ = 1)
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset ι) => f j) μ)
    (c : ℂ) (hc : ‖c‖ = 1) (hprod : ∀ᵐ ω ∂μ, ∏ i, f i ω = c) :
    ∀ i, ‖∫ ω, f i ω ∂μ‖ = ∏ j ∈ Finset.univ.erase i, ‖∫ ω, f j ω ∂μ‖ := by
  intro i
  have hi : (fun ω => ∏ j ∈ Finset.univ.erase i, f j ω) =ᵐ[μ]
      (fun ω => c * conj (f i ω)) := by
    filter_upwards [hprod, hn i] with ω hω hnω
    rw [← Complex.inv_eq_conj hnω, ← hω]
    rw [← Finset.prod_erase_mul Finset.univ (fun j => f j ω) (Finset.mem_univ i)]
    have hne : f i ω ≠ 0 := by intro hh; simp [hh] at hnω
    rw [mul_assoc, mul_inv_cancel₀ hne, mul_one]
  have hp : ∫ ω, ∏ j ∈ Finset.univ.erase i, f j ω ∂μ =
      ∏ j ∈ Finset.univ.erase i, ∫ ω, f j ω ∂μ := by
    have h := (hind i).integral_fun_prod_eq_prod_integral (fun j => hm j)
    have hh (g : ι → ℂ) : ∏ j : (Finset.univ.erase i : Finset ι), g j =
        ∏ j ∈ Finset.univ.erase i, g j := Finset.prod_coe_sort _ _
    refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => (hh (fun j => f j ω)).symm)).trans ?_
    exact h.trans (hh (fun j => ∫ ω, f j ω ∂μ))
  have hh : ∏ j ∈ Finset.univ.erase i, ∫ ω, f j ω ∂μ =
      c * conj (∫ ω, f i ω ∂μ) := by
    rw [← hp, integral_congr_ae hi, integral_const_mul, integral_conj]
  have hw := congrArg norm hh
  simpa only [norm_prod, norm_mul, hc, Complex.norm_conj, one_mul] using hw.symm

theorem ae_eq_mean_of_norm_mean_eq_one (f : Ω → ℂ)
    (hn : ∀ᵐ ω ∂μ, ‖f ω‖ = 1) (hi : ‖∫ ω, f ω ∂μ‖ = 1) :
    f =ᵐ[μ] (fun _ => ∫ ω, f ω ∂μ) := by
  rcases ae_eq_const_or_norm_integral_lt_of_norm_le_const (hn.mono fun _ h => h.le)
      with h | h
  · simpa only [average_eq_integral, Function.const_def] using h
  · simp [hi] at h

theorem exact_tuple_dichotomy
    (hk : 3 ≤ Fintype.card ι)
    (f : ι → Ω → ℂ) (hm : ∀ i, AEStronglyMeasurable (f i) μ)
    (hn : ∀ i, ∀ᵐ ω ∂μ, ‖f i ω‖ = 1)
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset ι) => f j) μ)
    (c : ℂ) (hc : ‖c‖ = 1) (hprod : ∀ᵐ ω ∂μ, ∏ i, f i ω = c) :
    (∀ i, ∫ ω, f i ω ∂μ = 0) ∨
      (∀ i, f i =ᵐ[μ] (fun _ => ∫ ω, f i ω ∂μ) ∧ ‖∫ ω, f i ω ∂μ‖ = 1) := by
  rcases exact_mean_dichotomy hk (fun i => ‖∫ ω, f i ω ∂μ‖)
      (fun _ => norm_nonneg _) (exact_tuple_mean_equations f hm hn hind c hc hprod)
      with h | h
  · exact Or.inl fun i => norm_eq_zero.mp (h i)
  · exact Or.inr fun i => ⟨ae_eq_mean_of_norm_mean_eq_one (f i) (hn i) (h i), h i⟩

theorem exact_quotient_dichotomy
    {S : ι → Type*} [∀ i, MeasurableSpace (S i)]
    (hk : 3 ≤ Fintype.card ι) (X : ∀ i, Ω → S i)
    (hX : ∀ i, AEMeasurable (X i) μ)
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset ι) => X j) μ)
    (f g : ∀ i, S i → ℂ) (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hnf : ∀ i, ∀ᵐ ω ∂μ, ‖f i (X i ω)‖ = 1)
    (hng : ∀ i, ∀ᵐ ω ∂μ, ‖g i (X i ω)‖ = 1)
    (c d : ℂ) (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (hpf : ∀ᵐ ω ∂μ, ∏ i, f i (X i ω) = c)
    (hpg : ∀ᵐ ω ∂μ, ∏ i, g i (X i ω) = d) :
    (∀ i, ∫ ω, f i (X i ω) * conj (g i (X i ω)) ∂μ = 0) ∨
    (∀ i, ∃ a : ℂ, ‖a‖ = 1 ∧
      (fun ω => f i (X i ω)) =ᵐ[μ] (fun ω => a * g i (X i ω))) := by
  let q (i : ι) (ω : Ω) := f i (X i ω) * conj (g i (X i ω))
  have hqm (i) : AEStronglyMeasurable (q i) μ :=
    ((hf i).comp_aemeasurable (hX i)).aestronglyMeasurable.mul
      (((hg i).comp_aemeasurable (hX i)).aestronglyMeasurable.star)
  have hqn (i) : ∀ᵐ ω ∂μ, ‖q i ω‖ = 1 := by
    filter_upwards [hnf i, hng i] with ω hfω hgω
    simp [q, hfω, hgω]
  have hqi (i) : iIndepFun (fun j : (Finset.univ.erase i : Finset ι) => q j) μ := by
    exact (hind i).comp (fun j y => f j y * conj (g j y))
      (fun j => (hf j).mul (Complex.continuous_conj.measurable.comp (hg j)))
  have hqp : ∀ᵐ ω ∂μ, ∏ i, q i ω = c * conj d := by
    filter_upwards [hpf, hpg] with ω hfω hgω
    simp only [q, Finset.prod_mul_distrib, ← map_prod, hfω, hgω]
  have hcd : ‖c * conj d‖ = 1 := by simp [hc, hd]
  rcases exact_tuple_dichotomy hk q hqm hqn hqi (c * conj d) hcd hqp with h | h
  · exact Or.inl h
  · right
    intro i
    refine ⟨∫ ω, q i ω ∂μ, (h i).2, ?_⟩
    filter_upwards [(h i).1, hng i] with ω hh hn
    rw [← hh]
    change f i (X i ω) = (f i (X i ω) * conj (g i (X i ω))) * g i (X i ω)
    rw [← Complex.inv_eq_conj hn, mul_assoc, inv_mul_cancel₀, mul_one]
    intro hz
    simp [hz] at hn

end

namespace HilbertCode

open MeasureTheory ProbabilityTheory Set
open scoped InnerProductSpace ComplexConjugate

section DecodingInnerProducts
variable {U Y I : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]
  [Fintype I] [DecidableEq I]

lemma inner_decode (p q : HilbertCode κ) (he : p.base = q.base) :
    ∫ y, representative (p,y) * conj (representative (q,y)) ∂κ p.base =
      inner ℂ (he ▸ q.decode) p.decode := by
  cases p with | mk p hp =>
    cases q with | mk q hq =>
      rcases p with ⟨u,a⟩
      rcases q with ⟨v,b⟩
      change u = v at he
      subst v
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [representative_eq_decode (⟨(u,a),hp⟩ : HilbertCode κ),
        representative_eq_decode (⟨(u,b),hq⟩ : HilbertCode κ)] with y hy hz
      rw [hy,hz]
      exact (RCLike.inner_apply _ _).symm

lemma eq_of_decode_smul {p q : HilbertCode κ} (he : p.base = q.base)
    (hp : IsCanonical p) (hq : IsCanonical q) {a : ℂ} (ha : ‖a‖ = 1)
    (hv : (fun y => representative (p,y)) =ᵐ[κ p.base]
      (fun y => a * representative (q,y))) : p = q := by
  rcases p with ⟨⟨u,f⟩,hf⟩
  rcases q with ⟨⟨v,g⟩,hg⟩
  change u = v at he
  subst v
  let p : HilbertCode κ := ⟨(u,f),hf⟩
  let q : HilbertCode κ := ⟨(u,g),hg⟩
  have hs : (p.decode : Lp ℂ 2 (κ u)) = a • (q.decode : Lp ℂ 2 (κ u)) := by
    apply Lp.ext
    change (fun y => (p.decode : Lp ℂ 2 (κ u)) y) =ᵐ[κ u]
      (fun y => (a • (q.decode : Lp ℂ 2 (κ u)) : Lp ℂ 2 (κ u)) y)
    filter_upwards [hv,representative_eq_decode p,representative_eq_decode q,
      Lp.coeFn_smul a (q.decode : Lp ℂ 2 (κ u))] with y hy hpy hqy hs
    exact hpy.symm.trans ((hy.trans (congrArg (a*·) hqy)).trans hs.symm)
  have hvv : (p.decode : Lp ℂ 2 (κ u)) = (q.decode : Lp ℂ 2 (κ u)) :=
    rayCanonical_unique hp hq ha hs
  exact (encode_decode p).symm.trans ((congrArg (encode u) hvv).trans (encode_decode q))

lemma distance_ge_one_of_orthogonal {p q : HilbertCode κ} (he : p.base = q.base)
    (hp : IsUnimodular p) (hq : IsUnimodular q)
    (hz : ∫ y, representative (p,y) * conj (representative (q,y)) ∂κ p.base = 0) :
    1 ≤ distance p q := by
  rcases p with ⟨⟨u,a⟩,ha⟩
  rcases q with ⟨⟨t,b⟩,hb⟩
  change u = t at he
  subst t
  let p : HilbertCode κ := ⟨(u,a),ha⟩
  let q : HilbertCode κ := ⟨(u,b),hb⟩
  let v : Lp ℂ 2 (κ u) := p.decode
  let w : Lp ℂ 2 (κ u) := q.decode
  have hid : inner ℂ w v = 0 := (inner_decode p q rfl).symm.trans hz
  have hn1 : ‖v‖ = 1 := norm_decode_eq_one hp
  have hn2 : ‖w‖ = 1 := norm_decode_eq_one hq
  have hn := norm_sub_sq (𝕜 := ℂ) w v
  rw [hid,hn1,hn2] at hn
  have hd : distance p q = dist v w :=
    (congrArg₂ distance (encode_decode p) (encode_decode q)).symm.trans
      (distance_encode u v w)
  change 1 ≤ distance p q
  rw [hd,dist_comm,dist_eq_norm]
  norm_num at hn
  have hh := norm_nonneg (w-v)
  nlinarith

omit [Fintype I] [DecidableEq I] in
lemma ae_norm_representative_comp (μ : Measure (I → Y)) (p q : HilbertCode κ)
    (he : p.base = q.base) (hq : IsUnimodular q) (i : I)
    (hm : MeasurePreserving (fun y : I → Y => y i) μ (κ p.base)) :
    ∀ᵐ y ∂μ, ‖representative (q,y i)‖ = 1 := by
  have h : ∀ᵐ y ∂κ p.base, ‖representative (q,y)‖ = 1 := by rw [he]; exact hq
  exact hm.quasiMeasurePreserving.ae h

omit [DecidableEq I] in
lemma ae_norm_prod_representative (μ : Measure (I → Y)) (p : I → HilbertCode κ)
    (hn : ∀ i, ∀ᵐ y ∂μ, ‖representative (p i,y i)‖ = 1) :
    ∀ᵐ y ∂μ, ‖∏ i, representative (p i,y i)‖ = 1 := by
  filter_upwards [ae_all_iff.mpr hn] with y hy
  simp only [norm_prod,hy,Finset.prod_const_one]

lemma code_tuple_quotient (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ]
    (p q : I → HilbertCode κ) (he : ∀ i, (p i).base = (q i).base)
    (hp : ∀ i, IsUnimodular (p i))
    (hq : ∀ i, IsUnimodular (q i))
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (κ (p i).base))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ)
    (hpe : ‖∫ y, ∏ i, representative (p i,y i) ∂μ‖ = 1)
    (hqe : ‖∫ y, ∏ i, representative (q i,y i) ∂μ‖ = 1) :
    (∀ i, ∫ y, representative (p i,y i) * conj (representative (q i,y i)) ∂μ = 0) ∨
    (∀ i, ∃ a : ℂ, ‖a‖ = 1 ∧ (fun y : I → Y => representative (p i,y i)) =ᵐ[μ]
       (fun y => a * representative (q i,y i))) := by
  have hpm (i) : Measurable (fun y => representative (p i,y)) :=
    measurable_representative.comp measurable_prodMk_left
  have hqm (i) : Measurable (fun y => representative (q i,y)) :=
    measurable_representative.comp measurable_prodMk_left
  have hpn (i) := (hm i).quasiMeasurePreserving.ae (hp i)
  have hqn (i) := ae_norm_representative_comp μ (p i) (q i) (he i) (hq i) i (hm i)
  have hpProd := ae_norm_prod_representative μ p hpn
  have hqProd := ae_norm_prod_representative μ q hqn
  exact exact_quotient_dichotomy (μ := μ) (S := fun _ : I => Y) hk (fun i y => y i) (fun i => (hm i).measurable.aemeasurable)
    hind (fun i y => representative (p i,y)) (fun i y => representative (q i,y))
    hpm hqm hpn hqn _ _ hpe hqe
    (ae_eq_mean_of_norm_mean_eq_one _ hpProd hpe)
    (ae_eq_mean_of_norm_mean_eq_one _ hqProd hqe)

lemma exact_codes_dichotomy (hk : 3 ≤ Fintype.card I)
    (μ : Measure (I → Y)) [IsProbabilityMeasure μ]
    (p q : I → HilbertCode κ) (he : ∀ i, (p i).base = (q i).base)
    (hp : ∀ i, IsCanonical (p i) ∧ IsUnimodular (p i))
    (hq : ∀ i, IsCanonical (q i) ∧ IsUnimodular (q i))
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) μ (κ (p i).base))
    (hind : ∀ i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) μ)
    (hpe : ‖∫ y, ∏ i, representative (p i,y i) ∂μ‖ = 1)
    (hqe : ‖∫ y, ∏ i, representative (q i,y i) ∂μ‖ = 1) :
    p = q ∨ ∀ i, 1 ≤ distance (p i) (q i) := by
  have hpm (i) : Measurable (fun y => representative (p i,y)) :=
    measurable_representative.comp measurable_prodMk_left
  have hqm (i) : Measurable (fun y => representative (q i,y)) :=
    measurable_representative.comp measurable_prodMk_left
  rcases code_tuple_quotient hk μ p q he (fun i => (hp i).2) (fun i => (hq i).2)
    hm hind hpe hqe with hz | hs
  · right
    intro i
    have hz' : ∫ y, representative (p i,y) * conj (representative (q i,y)) ∂κ (p i).base = 0 := by
      rw [←(hm i).map_eq]
      have hf : Measurable (fun y => representative (p i,y) * conj (representative (q i,y))) :=
        (hpm i).mul (Complex.continuous_conj.measurable.comp (hqm i))
      exact (integral_map (hm i).measurable.aemeasurable hf.aestronglyMeasurable).trans (hz i)
    exact distance_ge_one_of_orthogonal (he i) (hp i).2 (hq i).2 hz'
  · left
    funext i
    obtain ⟨a,ha,hv⟩ := hs i
    apply eq_of_decode_smul (he i) (hp i).1 (hq i).1 ha
    rw [←(hm i).map_eq]
    apply (ae_map_iff (hm i).measurable.aemeasurable
      (measurableSet_eq_fun (hpm i) (measurable_const.mul (hqm i)))).mpr
    exact hv
end DecodingInnerProducts


variable {U Y P T : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]
  [MeasurableSpace P] [MeasurableSpace.CountablySeparated P]
  [MeasurableSpace T] [StandardBorelSpace T]

lemma separated_branches (p : T → P) (hp : Measurable p)
    (v : T → HilbertCode κ) (hv : Measurable v)
    (hb : ∀ x y, p x = p y → (v x).base = (v y).base)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x y, p x = p y → x ≠ y → δ ≤ distance (v x) (v y)) :
    ∃ C : ℕ → Set T, (∀ n, MeasurableSet (C n)) ∧
      (⋃ n, C n) = Set.univ ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (∀ n, MeasurableEmbedding (fun x : C n => p x)) := by
  let B : ℕ → Set T := fun n => {x | (v x).code n < δ / 3}
  apply borel_injective_cover_branches p hp B
  · intro n
    exact measurableSet_lt ((measurable_code n).comp hv) measurable_const
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n,hn⟩ := (hilbertTests_dense (κ (v x).base)).exists_dist_lt (v x).decode
      (by positivity : 0 < δ/3)
    apply Set.mem_iUnion.mpr
    refine ⟨n,?_⟩
    change (v x).code n < δ/3
    rw [←decode_dist]
    exact hn
  · intro n x hx y hy hxy
    by_contra hne
    have h := hsep x y hxy hne
    have ht := distance_le_codes (v x) (v y) (hb x y hxy) n
    change (v x).code n < δ/3 at hx
    change (v y).code n < δ/3 at hy
    linarith
end HilbertCode

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
variable {P U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

def exactCodeMean (t : P × (I → HilbertCode κ)) : ℂ :=
  ∫ y, ∏ i, HilbertCode.representative (t.2 i,y i) ∂Λ t.1

omit [StandardBorelSpace P] [StandardBorelSpace U] [DecidableEq I] in
lemma measurable_exactCodeMean : Measurable (exactCodeMean κ Λ) := by
  have hh : StronglyMeasurable (fun t : (P × (I → HilbertCode κ)) × (I → Y) =>
      ∏ i, HilbertCode.representative (t.1.2 i,t.2 i)) := by
    apply Measurable.stronglyMeasurable
    apply Finset.measurable_prod
    intro i _
    exact HilbertCode.measurable_representative.comp
      (((measurable_pi_apply i).comp measurable_fst.snd).prodMk
        ((measurable_pi_apply i).comp measurable_snd))
  exact (hh.integral_kernel_prod_right (κ := Λ.comap Prod.fst measurable_fst)
    (f := fun (t : P × (I → HilbertCode κ)) (y : I → Y) =>
      ∏ i, HilbertCode.representative (t.2 i,y i))).measurable

def exactCodeSet : Set (P × (I → HilbertCode κ)) :=
  {t | (∀ i, (t.2 i).base = u t.1 i) ∧
    (∀ i, HilbertCode.IsCanonical (t.2 i) ∧ HilbertCode.IsUnimodular (t.2 i)) ∧
    ‖exactCodeMean κ Λ t‖ = 1}

omit [DecidableEq I] in
omit [StandardBorelSpace P] in
lemma measurableSet_exactCodeSet (hu : Measurable u) : MeasurableSet (exactCodeSet κ Λ u) := by
  have hbase (i : I) : MeasurableSet {t : P × (I → HilbertCode κ) | (t.2 i).base = u t.1 i} :=
    measurableSet_eq_fun
      ((HilbertCode.measurable_base (κ := κ)).comp ((measurable_pi_apply i).comp measurable_snd))
      (((measurable_pi_apply i).comp hu).comp measurable_fst)
  have hcan (i : I) : MeasurableSet {t : P × (I → HilbertCode κ) |
      HilbertCode.IsCanonical (t.2 i) ∧ HilbertCode.IsUnimodular (t.2 i)} :=
    (HilbertCode.measurableSet_isCanonical.inter HilbertCode.measurableSet_isUnimodular).preimage
      ((measurable_pi_apply i).comp measurable_snd)
  have hb : MeasurableSet {t : P × (I → HilbertCode κ) | ∀ i, (t.2 i).base = u t.1 i} := by
    convert MeasurableSet.iInter hbase using 1
    ext t
    simp
  have hc : MeasurableSet {t : P × (I → HilbertCode κ) |
      ∀ i, HilbertCode.IsCanonical (t.2 i) ∧ HilbertCode.IsUnimodular (t.2 i)} := by
    convert MeasurableSet.iInter hcan using 1
    ext t
    simp
  exact hb.inter (hc.inter (measurableSet_eq_fun (measurable_exactCodeMean κ Λ).norm measurable_const))

abbrev ExactCodeTuple := exactCodeSet κ Λ u

lemma exactCodeTuple_branches (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) :
    ∃ C : ℕ → Set (ExactCodeTuple κ Λ u), (∀ n, MeasurableSet (C n)) ∧
      (⋃ n, C n) = Set.univ ∧ Pairwise (fun i j => Disjoint (C i) (C j)) ∧
      (∀ n, MeasurableEmbedding (fun x : C n => x.1.1.1)) := by
  let : StandardBorelSpace (ExactCodeTuple κ Λ u) :=
    (measurableSet_exactCodeSet κ Λ u hu).standardBorel
  obtain ⟨i₀⟩ : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  refine HilbertCode.separated_branches (fun t : ExactCodeTuple κ Λ u => t.1.1)
    measurable_subtype_coe.fst (fun t => t.1.2 i₀)
    ((measurable_pi_apply i₀).comp measurable_subtype_coe.snd) ?_ 1 zero_lt_one ?_
  · intro x y hxy
    exact (x.property.1 i₀).trans ((congrArg (fun p => u p i₀) hxy).trans (y.property.1 i₀).symm)
  · intro x y hxy hne
    have hb i : (x.1.2 i).base = (y.1.2 i).base :=
      (x.property.1 i).trans ((congrArg (fun p => u p i) hxy).trans (y.property.1 i).symm)
    have hmp i : MeasurePreserving (fun z : I → Y => z i) (Λ x.1.1) (κ (x.1.2 i).base) := by
      rw [x.property.1 i]
      exact hm x.1.1 i
    have hymean : ‖exactCodeMean κ Λ (x.1.1,y.1.2)‖ = 1 := by
      rw [show (x.1.1,y.1.2) = y.1 from Prod.ext hxy rfl]
      exact y.property.2.2
    rcases HilbertCode.exact_codes_dichotomy hk (Λ x.1.1) x.1.2 y.1.2 hb
      x.property.2.1 y.property.2.1 hmp (hind x.1.1) x.property.2.2 hymean with he | hd
    · exact (hne (Subtype.ext (Prod.ext hxy he))).elim
    · exact hd i₀
end

section
open MeasureTheory Set Function
variable {P T Z : Type*} [MeasurableSpace P] [MeasurableSpace T] [MeasurableSpace Z]

lemma measurable_branch_sections (f : T → P) (g : T → Z) (hg : Measurable g)
    (d : P → Z) (hd : Measurable d) (C : ℕ → Set T)
    (hcover : (⋃ n, C n) = Set.univ)
    (hemb : ∀ n, MeasurableEmbedding (fun x : C n => f x)) :
    ∃ (D : ℕ → Set P) (s : ℕ → P → Z),
      (∀ n, MeasurableSet (D n)) ∧ (∀ n, Measurable (s n)) ∧
      (∀ n p, p ∉ D n → s n p = d p) ∧
      (∀ n p, p ∈ D n → ∃ t, f t = p ∧ s n p = g t) ∧
      (∀ t, ∃ n, f t ∈ D n ∧ s n (f t) = g t) := by
  let F (n : ℕ) : C n → P := fun x => f x
  let D (n : ℕ) : Set P := Set.range (F n)
  let s (n : ℕ) := Function.extend (F n) (fun t => g t) d
  refine ⟨D,s,fun n => (hemb n).measurableSet_range,?_,?_,?_,?_⟩
  · intro n
    exact (hemb n).measurable_extend (hg.comp measurable_subtype_coe) hd
  · intro n p hp
    exact Function.extend_apply' _ _ p hp
  · intro n p hp
    obtain ⟨t,rfl⟩ := hp
    exact ⟨t,rfl,(hemb n).injective.extend_apply _ _ t⟩
  · intro t
    have ht : t ∈ ⋃ n, C n := by rw [hcover]; trivial
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp ht
    exact ⟨n,⟨⟨t,hn⟩,rfl⟩,(hemb n).injective.extend_apply _ _ ⟨t,hn⟩⟩

lemma measurableSet_branched_relation [MeasurableEq Z]
    (f : T → P) (g : T → Z) (hg : Measurable g)
    (d : P → Z) (hd : Measurable d) (C : ℕ → Set T)
    (hcover : (⋃ n, C n) = Set.univ)
    (hemb : ∀ n, MeasurableEmbedding (fun x : C n => f x)) :
    MeasurableSet {pz : P × Z | ∃ t, f t = pz.1 ∧ g t = pz.2} := by
  obtain ⟨D,s,hD,hs,_,hhas,hevery⟩ := measurable_branch_sections f g hg d hd C hcover hemb
  have he : {pz : P × Z | ∃ t, f t = pz.1 ∧ g t = pz.2} =
      ⋃ n, {pz : P × Z | pz.1 ∈ D n ∧ s n pz.1 = pz.2} := by
    ext pz
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨t,hf,hg⟩
      obtain ⟨n,hn,he⟩ := hevery t
      exact ⟨n,hf ▸ hn,by rw [←hf,he,hg]⟩
    · rintro ⟨n,hn,he⟩
      obtain ⟨t,hf,hg⟩ := hhas n pz.1 hn
      exact ⟨t,hf,hg.symm.trans he⟩
  rw [he]
  exact MeasurableSet.iUnion fun n => (hD n).preimage measurable_fst |>.inter
    (measurableSet_eq_fun ((hs n).comp measurable_fst) measurable_snd)
end

section
open MeasureTheory ProbabilityTheory Set Topology
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
abbrev RationalSpanKey := List ((ℚ × ℚ) × ℕ)
def rationalSpanTest (v : ℕ → H) (t : RationalSpanKey) : H :=
  (t.map (fun p => ((p.1.1 : ℂ) + p.1.2 * Complex.I) • v p.2)).sum

lemma rationalSpanTest_append (v : ℕ → H) (s t : RationalSpanKey) :
    rationalSpanTest v (s ++ t) = rationalSpanTest v s + rationalSpanTest v t := by
  simp [rationalSpanTest]

lemma closure_rationalSpanTest (v : ℕ → H) :
    closure (Set.range (rationalSpanTest v)) =
      ((Submodule.span ℂ (Set.range v)).topologicalClosure : Set H) := by
  let S : AddSubmonoid H := {
    carrier := Set.range (rationalSpanTest v)
    zero_mem' := ⟨[],by simp [rationalSpanTest]⟩
    add_mem' := by
      rintro _ _ ⟨s,rfl⟩ ⟨t,rfl⟩
      exact ⟨s ++ t,rationalSpanTest_append v s t⟩ }
  let D := S.topologicalClosure
  have hd : IsClosed (D : Set H) := AddSubmonoid.isClosed_topologicalClosure S
  apply Set.Subset.antisymm
  · apply closure_minimal _ (Submodule.isClosed_topologicalClosure _)
    rintro _ ⟨t,rfl⟩
    apply Submodule.le_topologicalClosure
    induction t with
    | nil => exact Submodule.zero_mem _
    | cons p t ih =>
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨p.2,rfl⟩)) ih
  · have hsingle (n : ℕ) (c : ℂ) : c • v n ∈ D := by
      refine rationalComplex_dense.induction_on c
        (hd.preimage (continuous_id.smul continuous_const)) ?_
      intro q
      apply (show (S : Set H) ⊆ D from subset_closure)
      exact ⟨[(q,n)],by simp [rationalSpanTest]⟩
    apply closure_minimal _ hd
    intro w hw
    have h : ∀ c : ℂ, c • w ∈ D := by
      induction hw using Submodule.span_induction with
      | mem x hx => obtain ⟨n,rfl⟩ := hx; exact hsingle n
      | zero => intro c; simp only [smul_zero]; exact D.zero_mem
      | add x y hx hy ihx ihy =>
        intro c
        simpa only [smul_add] using D.add_mem (ihx c) (ihy c)
      | smul a x hx ih => intro c; simpa only [smul_smul] using ih (c*a)
    simpa using h 1

variable {P U Y : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]
  {u : P → U}

namespace HilbertCode

def atBase (q : HilbertCode κ) (a : U) (h : q.base = a) : Lp ℂ 2 (κ a) := h ▸ q.decode
lemma encode_atBase (q : HilbertCode κ) (a : U) (h : q.base = a) :
    encode a (atBase q a h) = q := by
  subst a
  exact encode_decode q
end HilbertCode

def MeasurableSection (v : ∀ p, Lp ℂ 2 (κ (u p))) : Prop :=
  Measurable (fun p => HilbertCode.encode (u p) (v p))

lemma MeasurableSection.zero (hu : Measurable u) :
    MeasurableSection (κ := κ) (u := u) (fun _ => 0) := by
  exact measurable_hilbert_encode u hu _ (fun _ => 0) measurable_const
    (fun _ => Lp.coeFn_zero _ _ _)

lemma MeasurableSection.add {v w : ∀ p, Lp ℂ 2 (κ (u p))}
    (hv : MeasurableSection v) (hw : MeasurableSection w) :
    MeasurableSection (fun p => v p + w p) := by
  have hu : Measurable u := HilbertCode.measurable_base.comp hv
  let f : P × Y → ℂ := fun py => HilbertCode.representative (HilbertCode.encode (u py.1) (v py.1),py.2)
  let g : P × Y → ℂ := fun py => HilbertCode.representative (HilbertCode.encode (u py.1) (w py.1),py.2)
  have hf : Measurable f := HilbertCode.measurable_representative.comp ((hv.comp measurable_fst).prodMk measurable_snd)
  have hg : Measurable g := HilbertCode.measurable_representative.comp ((hw.comp measurable_fst).prodMk measurable_snd)
  refine measurable_hilbert_encode u hu _ (f+g) (hf.add hg) ?_
  intro p
  filter_upwards [Lp.coeFn_add (v p) (w p),
    HilbertCode.representative_eq_decode (HilbertCode.encode (u p) (v p)),
    HilbertCode.representative_eq_decode (HilbertCode.encode (u p) (w p))] with y ha hv hw
  simp only [HilbertCode.decode_encode] at hv hw
  rw [ha]
  change (v p) y + (w p) y = _
  exact congrArg₂ (fun a b : ℂ => a+b) hv.symm hw.symm

lemma MeasurableSection.smul {v : ∀ p, Lp ℂ 2 (κ (u p))}
    (hv : MeasurableSection v) (c : ℂ) : MeasurableSection (fun p => c • v p) := by
  have hu : Measurable u := HilbertCode.measurable_base.comp hv
  let f : P × Y → ℂ := fun py => c * HilbertCode.representative (HilbertCode.encode (u py.1) (v py.1),py.2)
  have hf : Measurable f := measurable_const.mul (HilbertCode.measurable_representative.comp
    ((hv.comp measurable_fst).prodMk measurable_snd))
  refine measurable_hilbert_encode u hu _ f hf ?_
  intro p
  filter_upwards [Lp.coeFn_smul c (v p),
    HilbertCode.representative_eq_decode (HilbertCode.encode (u p) (v p))] with y ha hv
  simp only [HilbertCode.decode_encode] at hv
  rw [ha]
  change c * (v p) y = _
  exact congrArg (c * ·) hv.symm

lemma MeasurableSection.rationalSpanTest (hu : Measurable u)
    {s : ℕ → ∀ p, Lp ℂ 2 (κ (u p))} (hs : ∀ n, MeasurableSection (s n))
    (t : RationalSpanKey) : MeasurableSection (fun p => rationalSpanTest (fun n => s n p) t) := by
  induction t with
  | nil => exact MeasurableSection.zero hu
  | cons p t ih => exact ((hs p.2).smul _).add ih

lemma measurableSet_section_mem_span (hu : Measurable u)
    {s : ℕ → ∀ p, Lp ℂ 2 (κ (u p))} (hs : ∀ n, MeasurableSection (s n))
    {v : ∀ p, Lp ℂ 2 (κ (u p))} (hv : MeasurableSection v) :
    MeasurableSet {p | v p ∈ (Submodule.span ℂ (Set.range (fun n => s n p))).topologicalClosure} := by
  have he (p) : v p ∈ (Submodule.span ℂ (Set.range (fun n => s n p))).topologicalClosure ↔
      ∀ m : ℕ, ∃ t : RationalSpanKey,
        dist (v p) (rationalSpanTest (fun n => s n p) t) < (1 : ℝ) / (m+1) := by
    change v p ∈ ((Submodule.span ℂ (Set.range (fun n => s n p))).topologicalClosure : Set _) ↔ _
    rw [←closure_rationalSpanTest (fun n => s n p)]
    exact Metric.mem_closure_range_iff_nat
  simp_rw [he,Set.ofPred_forall,Set.ofPred_exists]
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iUnion
  intro t
  have hd := HilbertCode.measurable_distance.comp (hv.prodMk (MeasurableSection.rationalSpanTest hu hs t))
  have hd' : Measurable (fun p => dist (v p) (rationalSpanTest (fun n => s n p) t)) := by
    convert hd using 1
    funext p
    exact (HilbertCode.distance_encode (u p) (v p) (rationalSpanTest (fun n => s n p) t)).symm
  exact measurableSet_lt hd' measurable_const
end

section
open MeasureTheory ProbabilityTheory Set
variable {P U Y I : Type*} [MeasurableSpace P] [StandardBorelSpace P]
  [MeasurableSpace U] [StandardBorelSpace U]
  [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated Y]
  [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

lemma exactCode_sections (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) :
    ∃ (D : ℕ → Set P) (s : ℕ → P → I → HilbertCode κ),
      (∀ n, MeasurableSet (D n)) ∧ (∀ n, Measurable (s n)) ∧
      (∀ n p i, (s n p i).base = u p i) ∧
      (∀ n p, p ∈ D n → (p,s n p) ∈ exactCodeSet κ Λ u) ∧
      (∀ n p, p ∉ D n → s n p = fun i => HilbertCode.encode (u p i) 0) ∧
      (∀ t ∈ exactCodeSet κ Λ u, ∃ n, t.1 ∈ D n ∧ s n t.1 = t.2) := by
  let T := ExactCodeTuple κ Λ u
  obtain ⟨C,_,hcover,_,hemb⟩ := exactCodeTuple_branches κ Λ u hu hk hm hind
  let d : P → I → HilbertCode κ := fun p i => HilbertCode.encode (u p i) 0
  have hd : Measurable d := by
    apply Measurable.of_eval
    intro i
    exact MeasurableSection.zero ((measurable_pi_apply i).comp hu)
  obtain ⟨D,s,hD,hs,hzero,hhas,hevery⟩ := measurable_branch_sections
    (fun t : T => t.1.1) (fun t : T => t.1.2) measurable_subtype_coe.snd d hd C hcover hemb
  have hmem (n) (p) (hp : p ∈ D n) : (p,s n p) ∈ exactCodeSet κ Λ u := by
    obtain ⟨t,ht,hs⟩ := hhas n p hp
    rw [hs,←ht]
    exact t.property
  refine ⟨D,s,hD,hs,?_,hmem,hzero,?_⟩
  · intro n p i
    by_cases hp : p ∈ D n
    · exact (hmem n p hp).1 i
    · rw [hzero n p hp]
      rfl
  · intro t ht
    exact hevery ⟨t,ht⟩

lemma measurableSet_exactCodeSlot (hu : Measurable u) (hk : 3 ≤ Fintype.card I)
    (hm : ∀ p i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (hind : ∀ p i, iIndepFun (fun j : (Finset.univ.erase i : Finset I) =>
      fun y : I → Y => y j) (Λ p)) (i : I) :
    MeasurableSet {pz : P × HilbertCode κ | ∃ a : I → HilbertCode κ,
      (pz.1,a) ∈ exactCodeSet κ Λ u ∧ a i = pz.2} := by
  obtain ⟨C,_,hcover,_,hemb⟩ := exactCodeTuple_branches κ Λ u hu hk hm hind
  have hd : Measurable (fun p : P => HilbertCode.encode (u p i) (0 : Lp ℂ 2 (κ (u p i)))) :=
    MeasurableSection.zero ((measurable_pi_apply i).comp hu)
  have h := measurableSet_branched_relation
    (fun t : ExactCodeTuple κ Λ u => t.1.1) (fun t : ExactCodeTuple κ Λ u => t.1.2 i)
    ((measurable_pi_apply i).comp measurable_subtype_coe.snd) _ hd C hcover hemb
  convert h using 1
  ext pz
  constructor
  · rintro ⟨a,ha,he⟩
    exact ⟨⟨(pz.1,a),ha⟩,rfl,he⟩
  · rintro ⟨t,ht,he⟩
    exact ⟨t.1.2,by rw [←ht]; exact t.property,he⟩
end

section
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
local instance instMeasurableSpaceCircle_circleLp : MeasurableSpace Circle := inferInstanceAs (MeasurableSpace (Submonoid.unitSphere ℂ))
local instance instBorelSpaceCircle_circleLp : BorelSpace Circle := inferInstanceAs (BorelSpace (Submonoid.unitSphere ℂ))
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]

lemma circle_memLp (f : X → Circle) (hf : Measurable f) :
    MemLp (fun x => (f x : ℂ)) 2 μ :=
  MemLp.of_bound (measurable_subtype_coe.comp hf).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => (Circle.norm_coe (f x)).le)

def circleLp (f : X → Circle) (hf : Measurable f) : Lp ℂ 2 μ :=
  (circle_memLp μ f hf).toLp (fun x => (f x : ℂ))

lemma circleLp_coe (f : X → Circle) (hf : Measurable f) :
    circleLp μ f hf =ᵐ[μ] (fun x => (f x : ℂ)) := MemLp.coeFn_toLp _

lemma circleLp_congr {f g : X → Circle} (hf : Measurable f) (hg : Measurable g)
    (he : f =ᵐ[μ] g) : circleLp μ f hf = circleLp μ g hg := by
  apply Lp.ext
  filter_upwards [circleLp_coe μ f hf, circleLp_coe μ g hg,he] with x h1 h2 h3
  rw [h1,h2,h3]

lemma circleLp_norm [IsProbabilityMeasure μ] (f : X → Circle) (hf : Measurable f) :
    ‖circleLp μ f hf‖ = 1 := by
  have hn : ∀ᵐ x ∂μ, ‖circleLp μ f hf x‖ = ‖(1 : ℂ)‖ := by
    filter_upwards [circleLp_coe μ f hf] with x hx
    rw [hx,Circle.norm_coe,norm_one]
  rw [Lp.norm_def,eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable (circleLp μ f hf)) aestronglyMeasurable_const hn,eLpNorm_const (1 : ℂ) (by norm_num) (IsProbabilityMeasure.ne_zero μ)]
  simp

lemma circleLp_ne_zero [IsProbabilityMeasure μ] (f : X → Circle) (hf : Measurable f) :
    circleLp μ f hf ≠ 0 := by
  intro h
  have hn := circleLp_norm μ f hf
  simp only [h,norm_zero,zero_ne_one] at hn

lemma circleLp_inner (f g : X → Circle) (hf : Measurable f) (hg : Measurable g) :
    inner ℂ (circleLp μ f hf) (circleLp μ g hg) =
      ∫ x, conj (f x : ℂ) * (g x : ℂ) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [circleLp_coe μ f hf,circleLp_coe μ g hg] with x h1 h2
  rw [h1,h2]
  simp only [RCLike.inner_apply,starRingEnd_apply]
  ring

lemma circleLp_phase (c : Circle) (f : X → Circle) (hf : Measurable f) :
    circleLp μ (fun x => c*f x) (measurable_const.mul hf) = (c : ℂ) • circleLp μ f hf := by
  apply Lp.ext
  filter_upwards [circleLp_coe μ (fun x => c*f x) (measurable_const.mul hf),
    circleLp_coe μ f hf,Lp.coeFn_smul (c : ℂ) (circleLp μ f hf)] with x h1 h2 h3
  rw [h1,h3]
  change (c : ℂ) * (f x : ℂ) = (c : ℂ) * (circleLp μ f hf x)
  rw [h2]
end

section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

omit [DecidableEq I] in
lemma normalized_exact_codes (p : P)
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (f : I → Y → Circle) (hf : ∀ i, Measurable (f i)) (c : Circle)
    (he : ∀ᵐ y ∂Λ p, ∏ i, f i (y i) = c) :
    ∃ (a : I → HilbertCode κ) (d : I → ℂ), (p,a) ∈ exactCodeSet κ Λ u ∧
      ∀ i, ‖d i‖ = 1 ∧ a i = HilbertCode.encode (u p i)
        (d i • circleLp (κ (u p i)) (f i) (hf i)) := by
  have hc (i) := exists_rayCanonical (hilbertTests (κ (u p i)))
    (hilbertTests_dense (κ (u p i))) (circleLp_ne_zero (κ (u p i)) (f i) (hf i))
  choose d hd hdcan using hc
  let a : I → HilbertCode κ := fun i => HilbertCode.encode (u p i)
    (d i • circleLp (κ (u p i)) (f i) (hf i))
  have hrepr (i) : (fun y => HilbertCode.representative (a i,y)) =ᵐ[κ (u p i)]
      (fun y => d i * (f i y : ℂ)) := by
    filter_upwards [HilbertCode.representative_eq_decode (a i),
      Lp.coeFn_smul (d i) (circleLp (κ (u p i)) (f i) (hf i)),
      circleLp_coe (κ (u p i)) (f i) (hf i)] with y h1 h2 h3
    change HilbertCode.representative (a i,y) =
      (HilbertCode.decode (HilbertCode.encode (u p i) (d i • circleLp (κ (u p i)) (f i) (hf i))) : Lp ℂ 2 (κ (u p i))) y at h1
    rw [HilbertCode.decode_encode] at h1
    exact h1.trans (h2.trans (congrArg (d i * ·) h3))
  have heprod : (fun y => ∏ i, HilbertCode.representative (a i,y i)) =ᵐ[Λ p]
      (fun _ => (∏ i, d i) * (c : ℂ)) := by
    filter_upwards [ae_all_iff.mpr (fun i => (hm i).quasiMeasurePreserving.ae_eq_comp (hrepr i)),he]
      with y hy he
    have hcoe : (∏ i, (f i (y i) : ℂ)) = (c : ℂ) :=
      (map_prod Circle.coeHom (fun i => f i (y i)) Finset.univ).symm.trans
        (congrArg (fun z : Circle => (z : ℂ)) he)
    calc
      (∏ i, HilbertCode.representative (a i,y i)) = ∏ i, d i * (f i (y i) : ℂ) :=
        Finset.prod_congr rfl (fun i _ => hy i)
      _ = (∏ i, d i) * (∏ i, (f i (y i) : ℂ)) := Finset.prod_mul_distrib
      _ = (∏ i, d i) * (c : ℂ) := congrArg ((∏ i, d i) * ·) hcoe
  refine ⟨a,d,⟨fun _ => rfl,?_,?_⟩,fun i => ⟨hd i,rfl⟩⟩
  · intro i
    constructor
    · change RayCanonical (hilbertTests (κ (u p i)))
        (HilbertCode.decode (HilbertCode.encode (u p i) (d i • circleLp (κ (u p i)) (f i) (hf i))))
      rw [HilbertCode.decode_encode]
      exact hdcan i
    · change ∀ᵐ y ∂κ (u p i), ‖HilbertCode.representative (a i,y)‖ = 1
      filter_upwards [hrepr i] with y hy
      rw [hy,norm_mul,hd i,Circle.norm_coe,one_mul]
  · change ‖∫ y, ∏ i, HilbertCode.representative (a i,y i) ∂Λ p‖ = 1
    rw [integral_congr_ae heprod,integral_const]
    simp only [probReal_univ,one_smul,norm_mul,norm_prod,hd,Finset.prod_const_one,
      Circle.norm_coe,one_mul]
end

section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
attribute [local instance] Rokhlin.instMeasurableSpaceCircle_circleLp Rokhlin.instBorelSpaceCircle_circleLp

def circleOfValue (z : ℂ) : Circle := by
  classical
  exact ⟨if ‖z‖ = 1 then z else 1, by
    split_ifs with h
    · exact mem_sphere_zero_iff_norm.mpr h
    · exact mem_sphere_zero_iff_norm.mpr (norm_one : ‖(1 : ℂ)‖ = 1)⟩
lemma circleOfValue_coe {z : ℂ} (h : ‖z‖ = 1) : (circleOfValue z : ℂ) = z := by
  classical
  change (if ‖z‖ = 1 then z else (1 : ℂ)) = z
  exact ite_eq_left h
lemma measurable_circleOfValue : Measurable circleOfValue := by
  classical
  apply Measurable.subtype_mk
  exact measurable_id.ite (measurableSet_eq_fun measurable_norm measurable_const) measurable_const

variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I] [DecidableEq I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

namespace HilbertCode
variable {κ}
def circleRep (q : HilbertCode κ) (y : Y) : Circle := circleOfValue (representative (κ := κ) (q,y))
lemma circleRep_coe (q : HilbertCode κ) (y : Y)
    (h : ‖representative (κ := κ) (q,y)‖ = 1) :
    (circleRep (κ := κ) q y : ℂ) = representative (κ := κ) (q,y) :=
  circleOfValue_coe (z := representative (κ := κ) (q,y)) h
lemma measurable_circleRep : Measurable (fun qy : HilbertCode κ × Y => circleRep qy.1 qy.2) :=
  measurable_circleOfValue.comp measurable_representative
lemma measurable_circleRep_fixed (q : HilbertCode κ) : Measurable (circleRep (κ := κ) q) := by
  have h : Measurable (fun y : Y => (q,y)) := measurable_const.prodMk measurable_id
  have hh : Measurable (fun y : Y => representative (κ := κ) (q,y)) :=
    (measurable_representative (κ := κ)).comp h
  exact measurable_circleOfValue.comp hh
lemma circleRep_ae (q : HilbertCode κ) (hq : IsUnimodular q) :
    (fun y => (circleRep (κ := κ) q y : ℂ)) =ᵐ[κ q.base] (fun y => representative (κ := κ) (q,y)) :=
  hq.mono fun _ h => circleOfValue_coe h
lemma circleLp_circleRep (q : HilbertCode κ) (hq : IsUnimodular q) :
    circleLp (κ q.base) (circleRep (κ := κ) q) (measurable_circleRep_fixed (κ := κ) q) = q.decode := by
  apply Lp.ext
  exact (circleLp_coe (κ q.base) (circleRep (κ := κ) q) (measurable_circleRep_fixed (κ := κ) q)).trans
    ((circleRep_ae (κ := κ) q hq).trans (representative_eq_decode q))
end HilbertCode

omit [DecidableEq I] in
lemma exactCode_circle_tuple {p : P} {a : I → HilbertCode κ}
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (ha : (p,a) ∈ exactCodeSet κ Λ u) :
    ∃ c : Circle, ∀ᵐ y ∂Λ p, ∏ i, HilbertCode.circleRep (κ := κ) (a i) (y i) = c := by
  let c : Circle := ⟨exactCodeMean κ Λ (p,a),mem_sphere_zero_iff_norm.mpr ha.2.2⟩
  have hn (i) : ∀ᵐ y ∂Λ p, ‖HilbertCode.representative (κ := κ) (a i,y i)‖ = 1 := by
    have h : ∀ᵐ y ∂κ (u p i), ‖HilbertCode.representative (κ := κ) (a i,y)‖ = 1 := by
      rw [←ha.1 i]
      exact (ha.2.1 i).2
    exact (hm i).quasiMeasurePreserving.ae h
  have hnp : ∀ᵐ y ∂Λ p, ‖∏ i, HilbertCode.representative (κ := κ) (a i,y i)‖ = 1 :=
    HilbertCode.ae_norm_prod_representative (κ := κ) (Λ p) a hn
  have hmean : ‖∫ y, ∏ i, HilbertCode.representative (κ := κ) (a i,y i) ∂Λ p‖ = 1 := ha.2.2
  have he : (fun y => ∏ i, HilbertCode.representative (κ := κ) (a i,y i)) =ᵐ[Λ p]
      (fun _ => exactCodeMean κ Λ (p,a)) :=
    ae_eq_mean_of_norm_mean_eq_one (μ := Λ p) _ hnp hmean
  refine ⟨c,?_⟩
  filter_upwards [he,ae_all_iff.mpr hn] with y hy hn
  apply Circle.coe_injective
  change ((∏ i, HilbertCode.circleRep (κ := κ) (a i) (y i) : Circle) : ℂ) = exactCodeMean κ Λ (p,a)
  change Circle.coeHom (∏ i, HilbertCode.circleRep (κ := κ) (a i) (y i)) = _
  rw [map_prod]
  exact (Finset.prod_congr rfl (fun i _ => HilbertCode.circleRep_coe (κ := κ) (a i) (y i) (hn i))).trans hy
end

namespace HilbertCode

open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace
attribute [local instance] instMeasurableSpaceCircle_circleLp instBorelSpaceCircle_circleLp
variable {U Y : Type*} [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] {κ : Kernel U Y} [IsMarkovKernel κ]

abbrev UnitCode (κ : Kernel U Y) [IsMarkovKernel κ] := {q : HilbertCode κ // q.IsUnimodular}

lemma unitCode_exists_coefficient (q : UnitCode κ) : ∃ n, coefficient q.val n ≠ 0 := by
  have hne : q.val.decode ≠ 0 := norm_ne_zero_iff.mp (by rw [norm_decode_eq_one q.property]; norm_num)
  simpa only [coefficient_eq] using exists_inner_ne_zero_of_dense
    (hilbertTests (κ q.val.base)) (hilbertTests_dense _) hne

def firstCoefficient (q : UnitCode κ) : ℕ := Nat.find (unitCode_exists_coefficient q)
lemma measurable_firstCoefficient : Measurable (firstCoefficient (κ := κ)) :=
  measurable_find unitCode_exists_coefficient (fun n =>
    (measurableSet_eq_fun ((measurable_coefficient n).comp measurable_subtype_coe) measurable_const).compl)

def unitPhase (q : UnitCode κ) : ℂ :=
  (‖coefficient q.val (firstCoefficient q)‖ : ℂ) / coefficient q.val (firstCoefficient q)
lemma measurable_unitPhase : Measurable (unitPhase (κ := κ)) := by
  have hm : Measurable (fun q : UnitCode κ => coefficient q.val (firstCoefficient q)) :=
    Measurable.find (fun n => (measurable_coefficient n).comp measurable_subtype_coe)
      (fun n => (measurableSet_eq_fun ((measurable_coefficient n).comp measurable_subtype_coe)
        measurable_const).compl) unitCode_exists_coefficient
  exact (Complex.continuous_ofReal.measurable.comp hm.norm).div hm

lemma unitPhase_norm (q : UnitCode κ) : ‖unitPhase q‖ = 1 := by
  have hz : coefficient q.val (firstCoefficient q) ≠ 0 := Nat.find_spec (unitCode_exists_coefficient q)
  simp only [unitPhase,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_norm]
  exact div_self (norm_ne_zero_iff.mpr hz)

lemma unitPhase_canonical (q : UnitCode κ) :
    RayCanonical (hilbertTests (κ q.val.base)) (unitPhase q • q.val.decode) := by
  have hz : coefficient q.val (firstCoefficient q) ≠ 0 := Nat.find_spec (unitCode_exists_coefficient q)
  refine ⟨firstCoefficient q,?_,?_,?_⟩
  · intro n hn
    rw [inner_smul_right,←coefficient_eq]
    rw [not_ne_iff.mp (Nat.find_min (unitCode_exists_coefficient q) hn),mul_zero]
  · rw [inner_smul_right,←coefficient_eq]
    unfold unitPhase
    rw [div_mul_cancel₀ _ hz,Complex.ofReal_re]
    exact norm_pos_iff.mpr hz
  · rw [inner_smul_right,←coefficient_eq]
    unfold unitPhase
    rw [div_mul_cancel₀ _ hz,Complex.ofReal_im]

def normalizeUnit (q : UnitCode κ) : HilbertCode κ := encode q.val.base (unitPhase q • q.val.decode)

lemma normalizeUnit_base (q : UnitCode κ) : (normalizeUnit q).base = q.val.base := rfl
lemma normalizeUnit_canonical (q : UnitCode κ) : (normalizeUnit q).IsCanonical := by
  change RayCanonical _ (decode (encode _ _))
  rw [decode_encode]
  exact unitPhase_canonical q

lemma normalizeUnit_representative (q : UnitCode κ) :
    (fun y => representative (normalizeUnit q,y)) =ᵐ[κ q.val.base]
      fun y => unitPhase q * representative (q.val,y) := by
  have hr := representative_eq_decode (normalizeUnit q)
  change (fun y => representative (normalizeUnit q,y)) =ᵐ[κ q.val.base]
    fun y => (decode (encode _ (unitPhase q • q.val.decode)) : Lp ℂ 2 (κ q.val.base)) y at hr
  rw [decode_encode] at hr
  filter_upwards [hr,Lp.coeFn_smul (unitPhase q) q.val.decode,representative_eq_decode q.val]
    with y h1 h2 h3
  exact h1.trans (h2.trans (congrArg (unitPhase q * ·) h3.symm))

lemma normalizeUnit_unimodular (q : UnitCode κ) : (normalizeUnit q).IsUnimodular := by
  filter_upwards [normalizeUnit_representative q,q.property] with y h1 h2
  rw [h1,norm_mul,unitPhase_norm,h2,mul_one]

lemma measurable_normalizeUnit : Measurable (normalizeUnit (κ := κ)) := by
  apply measurable_hilbert_encode (fun q : UnitCode κ => q.val.base)
    (measurable_base.comp measurable_subtype_coe) _
    (fun qy => unitPhase qy.1 * representative (qy.1.val,qy.2))
  · exact (measurable_unitPhase.comp measurable_fst).mul
      (measurable_representative.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd))
  · intro q
    filter_upwards [Lp.coeFn_smul (unitPhase q) q.val.decode,representative_eq_decode q.val]
      with y h1 h2
    exact h1.trans (congrArg (unitPhase q * ·) h2.symm)

def transportRaw (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) : HilbertCode κ :=
  encode (F q.base) (circleLp (κ (F q.base)) (circleRep (κ := κ) q ∘ E.symm)
    ((measurable_circleRep_fixed q).comp E.symm.measurable))

lemma transportRaw_base (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) :
    (transportRaw F E q).base = F q.base := rfl

lemma transportRaw_representative (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) :
    (fun y => representative (transportRaw F E q,y)) =ᵐ[κ (F q.base)]
      (fun y => (circleRep (κ := κ) q (E.symm y) : ℂ)) := by
  have h := representative_eq_decode (transportRaw F E q)
  change (fun y => representative (transportRaw F E q,y)) =ᵐ[κ (F q.base)]
    (decode (encode _ _) : Y → ℂ) at h
  rw [decode_encode] at h
  exact h.trans (circleLp_coe _ _ _)

lemma transportRaw_unimodular (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) :
    (transportRaw F E q).IsUnimodular := by
  filter_upwards [transportRaw_representative F E q] with y hy
  rw [hy,Circle.norm_coe]

lemma measurable_circleRep_comp (E : Y ≃ᵐ Y) :
    Measurable (fun qy : HilbertCode κ × Y => circleRep (κ := κ) qy.1 (E.symm qy.2)) := by
  have hm : Measurable (fun qy : HilbertCode κ × Y => (qy.1,E.symm qy.2)) :=
    measurable_fst.prodMk (E.symm.measurable.comp measurable_snd)
  have hr : Measurable (fun qy : HilbertCode κ × Y => representative (κ := κ) (qy.1,E.symm qy.2)) :=
    (measurable_representative (κ := κ)).comp hm
  exact measurable_circleOfValue.comp hr

lemma measurable_transportRaw (F : U → U) (hF : Measurable F) (E : Y ≃ᵐ Y) :
    Measurable (transportRaw (κ := κ) F E) := by
  unfold transportRaw
  apply measurable_hilbert_encode (κ := κ) (fun q : HilbertCode κ => F q.base)
    (hF.comp (measurable_base (κ := κ)))
    (fun q => circleLp (κ (F q.base)) (circleRep (κ := κ) q ∘ E.symm)
      ((measurable_circleRep_fixed q).comp E.symm.measurable))
    (fun qy : HilbertCode κ × Y => (circleRep (κ := κ) qy.1 (E.symm qy.2) : ℂ))
  · exact measurable_subtype_coe.comp (measurable_circleRep_comp (κ := κ) E)
  · intro q
    exact circleLp_coe _ _ _

def transport (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) : HilbertCode κ :=
  normalizeUnit ⟨transportRaw F E q,transportRaw_unimodular F E q⟩

lemma transport_base (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) :
    (transport F E q).base = F q.base := rfl
lemma transport_canonical (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) :
    (transport F E q).IsCanonical := normalizeUnit_canonical _
lemma transport_unimodular (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ) :
    (transport F E q).IsUnimodular := normalizeUnit_unimodular _
lemma measurable_transport (F : U → U) (hF : Measurable F) (E : Y ≃ᵐ Y) :
    Measurable (transport (κ := κ) F E) :=
  measurable_normalizeUnit.comp (Measurable.subtype_mk (measurable_transportRaw F hF E))

lemma transport_representative (F : U → U) (E : Y ≃ᵐ Y) (q : HilbertCode κ)
    (hq : q.IsUnimodular)
    (hE : MeasurePreserving E (κ q.base) (κ (F q.base))) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ (fun y => representative (transport F E q,y)) =ᵐ[κ (F q.base)]
      (fun y => c * representative (q,E.symm y)) := by
  let r : UnitCode κ := ⟨transportRaw F E q,transportRaw_unimodular F E q⟩
  refine ⟨unitPhase r,unitPhase_norm r,?_⟩
  have hinv := MeasurePreserving.symm E hE
  have hrep := hinv.quasiMeasurePreserving.ae (circleRep_ae q hq)
  filter_upwards [normalizeUnit_representative r,transportRaw_representative F E q,hrep]
    with y h1 h2 h3
  exact h1.trans (congrArg (unitPhase r * ·) (h2.trans h3))

lemma transport_inverse (F : U ≃ᵐ U) (E : Y ≃ᵐ Y) (q : HilbertCode κ)
    (hq : q.IsUnimodular) (hc : q.IsCanonical)
    (hE : MeasurePreserving E (κ q.base) (κ (F q.base))) :
    transport F.symm E.symm (transport F E q) = q := by
  have hinv : MeasurePreserving E.symm (κ (transport F E q).base)
      (κ (F.symm (transport F E q).base)) := by
    simpa only [transport_base,F.symm_apply_apply] using MeasurePreserving.symm E hE
  obtain ⟨c,hc1,hr⟩ := transport_representative F E q hq hE
  obtain ⟨d,hd1,hs⟩ := transport_representative F.symm E.symm (transport F E q)
    (transport_unimodular F E q) hinv
  have hs' : (fun y => representative (transport F.symm E.symm (transport F E q),y)) =ᵐ[κ q.base]
      (fun y => d * representative (transport F E q,E y)) := by
    simpa only [transport_base,F.symm_apply_apply,MeasurableEquiv.symm_symm] using hs
  apply eq_of_decode_smul (by simp only [transport_base,F.symm_apply_apply])
    (transport_canonical _ _ _) hc (a := d*c) (by rw [norm_mul,hd1,hc1,mul_one])
  simp only [transport_base,F.symm_apply_apply]
  filter_upwards [hs',hE.quasiMeasurePreserving.ae hr] with y h1 h2
  rw [h1,h2,E.symm_apply_apply,mul_assoc]
end HilbertCode

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
variable {P U Y I : Type*} [MeasurableSpace P] [MeasurableSpace U] [MeasurableSpace Y]
  [MeasurableSpace.CountablyGenerated Y] [Fintype I]
  (κ : Kernel U Y) [IsMarkovKernel κ] (Λ : Kernel P (I → Y)) [IsMarkovKernel Λ]
  (u : P → I → U)

omit [IsMarkovKernel Λ] in

lemma exactCode_transport (F : U → U) (E : Y ≃ᵐ Y) (p p' : P)
    (hu : ∀ i, u p' i = F (u p i))
    (hκ : ∀ i, MeasurePreserving E (κ (u p i)) (κ (F (u p i))))
    (hΛ : MeasurePreserving (fun y : I → Y => fun i => E (y i)) (Λ p) (Λ p'))
    (hm : ∀ i, MeasurePreserving (fun y : I → Y => y i) (Λ p) (κ (u p i)))
    (q : I → HilbertCode κ) (hq : (p,q) ∈ exactCodeSet κ Λ u) :
    (p',fun i => HilbertCode.transport F E (q i)) ∈ exactCodeSet κ Λ u := by
  classical
  have hkq (i) : MeasurePreserving E (κ (q i).base) (κ (F (q i).base)) := by
    rw [hq.1 i]; exact hκ i
  choose c hc hrep using fun i => HilbertCode.transport_representative F E (q i) (hq.2.1 i).2 (hkq i)
  refine ⟨fun i => by rw [HilbertCode.transport_base,hq.1 i,hu i],
    fun i => ⟨HilbertCode.transport_canonical _ _ _,HilbertCode.transport_unimodular _ _ _⟩,?_⟩
  have hr (i) : ∀ᵐ y ∂Λ p,
      HilbertCode.representative (HilbertCode.transport F E (q i),E (y i)) =
      c i * HilbertCode.representative (q i,y i) := by
    have hh := (hkq i).quasiMeasurePreserving.ae (hrep i)
    have hh' : ∀ᵐ y ∂κ (u p i),
        HilbertCode.representative (HilbertCode.transport F E (q i),E y) =
          c i * HilbertCode.representative (q i,y) := by
      rw [←hq.1 i]
      simpa only [E.symm_apply_apply] using hh
    exact (hm i).quasiMeasurePreserving.ae hh'
  have he : (fun y : I → Y => ∏ i, HilbertCode.representative
      (HilbertCode.transport F E (q i),E (y i))) =ᵐ[Λ p]
      (fun y => (∏ i, c i) * ∏ i, HilbertCode.representative (q i,y i)) := by
    filter_upwards [ae_all_iff.mpr hr] with y hy
    rw [←Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => hy i)
  have hmeas : AEStronglyMeasurable (fun y : I → Y => ∏ i,
      HilbertCode.representative (HilbertCode.transport F E (q i),y i)) (Λ p') := by
    apply Measurable.aestronglyMeasurable
    apply Finset.measurable_prod
    intro i _
    exact HilbertCode.measurable_representative.comp (measurable_const.prodMk (measurable_pi_apply i))
  change ‖∫ y, ∏ i, HilbertCode.representative (HilbertCode.transport F E (q i),y i) ∂Λ p'‖ = 1
  rw [←hΛ.hasLaw.integral_comp hmeas]
  simp only [Function.comp_def]
  rw [integral_congr_ae he,integral_const_mul,norm_mul]
  have hn : ‖∏ i, c i‖ = 1 := by rw [norm_prod]; simp only [hc,Finset.prod_const_one]
  rw [hn,one_mul]
  exact hq.2.2

end Rokhlin

end

end OAI
