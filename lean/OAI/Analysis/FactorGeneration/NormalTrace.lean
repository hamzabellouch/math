import OAI.Analysis.FactorGeneration.FunctionalLimits
import OAI.Analysis.FactorGeneration.LocalizedStates

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! A genuine linear state with exact equality of real quadratic values,
constructed from the original finite factor predicates by scalar compactness. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance quadraticStateCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance quadraticStateOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance quadraticStatePreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance quadraticStateLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance quadraticStateStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hdiff hfinite in
theorem exists_real_quadratic_state (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    ∃ φ : M.toStarSubalgebra →L[ℂ] ℂ,
      ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re) ∧
      ∀ x : M.toStarSubalgebra, (φ (star x*x)).re=(φ (x*star x)).re := by
  have hex (n : ℕ) := exists_approximately_tracial_state hfactor hdiff hfinite hunit
    (1/((n : ℝ)+1)) (by positivity)
  choose f hf hfone hfpos hfquad using hex
  let ω := Ultrafilter.of (atTop : Filter ℕ)
  obtain ⟨φ,hφ,ht⟩ := exists_bounded_functional_ultralimit ω f 1 (by norm_num) hf
  have hε : Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) (ω : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left (Ultrafilter.of_le _)
  have hre (x : M.toStarSubalgebra) := (Complex.continuous_re.tendsto (φ x)).comp (ht x)
  have hle (x : M.toStarSubalgebra) : (φ (star x*x)).re ≤ (φ (x*star x)).re := by
    have hr := (hε.const_add 1).mul (hre (x*star x))
    have h := le_of_tendsto_of_tendsto (hre (star x*x)) hr
      (Eventually.of_forall (fun n => hfquad n x))
    simpa only [add_zero,one_mul] using h
  refine ⟨φ,hφ,?_,?_,?_⟩
  · apply tendsto_nhds_unique (ht 1)
    simpa only [hfone] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) (ω : Filter ℕ) (𝓝 1))
  · intro x hx
    exact ge_of_tendsto (hre x) (Eventually.of_forall (fun n => hfpos n x hx))
  · intro x
    exact le_antisymm (hle x) (by simpa only [star_star] using hle (star x))

end

/-! Construction of a tracial state on the original concrete finite diffuse factor without a supplied trace. -/
section
open scoped CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance tracialStateCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance tracialStateOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance tracialStatePreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance tracialStateLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance tracialStateStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfactor hdiff hfinite in
theorem exists_tracial_state (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    ∃ φ : M.toStarSubalgebra →L[ℂ] ℂ,
      ‖φ‖ ≤ 1 ∧ φ 1=1 ∧ (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re) ∧
      (∀ x : M.toStarSubalgebra, φ (star x)=star (φ x)) ∧
      ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x) := by
  obtain ⟨φ,hφ,h1,hpos,hquad⟩ := exists_real_quadratic_state hfactor hdiff hfinite hunit
  refine ⟨hermitianFunctional φ,(hermitianFunctional_norm_le φ).trans hφ,
    hermitianFunctional_one φ h1,?_,hermitianFunctional_star φ,
    hermitianFunctional_trace φ hquad⟩
  intro x hx
  rw [hermitianFunctional_selfAdjoint φ x hx.isSelfAdjoint,Complex.ofReal_re]
  exact hpos x hx

end

/-! Every positive normalized tracial functional agrees with the dimension on
all projections. Lower and upper dyadic bounds use actual partial isometries. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance stateDimensionCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance stateDimensionOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance stateDimensionPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance stateDimensionLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance stateDimensionStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _

theorem algebraProjection_nonneg (p : AlgebraProjection M) : 0 ≤ p.val := by
  have h : star p.val*p.val=p.val := by
    rw [p.property.isSelfAdjoint.star_eq,p.property.isIdempotentElem.eq]
  rw [← h]
  exact star_mul_self_nonneg _

theorem tracialFunctional_equivalent (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    {p q : AlgebraProjection M} (h : p.Equivalent q) : φ p.val=φ q.val := by
  obtain ⟨v,hv,ht⟩ := h
  rw [← hv,← ht,← v.initial]
  exact htrace (star v.val) v.val

theorem positiveFunctional_projection_mono (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    {p q : AlgebraProjection M} (h : p ≤ q) : (φ p.val).re ≤ (φ q.val).re := by
  have hr := hpos (AlgebraProjection.remainder p q h).val
    (algebraProjection_nonneg _)
  change 0 ≤ (φ (q.val-p.val)).re at hr
  rw [map_sub,Complex.sub_re] at hr
  linarith

theorem tracialFunctional_subequivalent (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    {p q : AlgebraProjection M} (h : p.Subequivalent q) : (φ p.val).re ≤ (φ q.val).re := by
  obtain ⟨v,hv,ht⟩ := h
  have he := tracialFunctional_equivalent φ htrace
    (show p.Equivalent v.target from ⟨v,hv,rfl⟩)
  rw [he]
  exact positiveFunctional_projection_mono φ hpos ht

variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem tracialFunctional_dyadic_subset_re (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (h1 : φ 1=1) (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    (n : ℕ) (s : Finset (DyadicIndex n)) :
    (φ ((traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n).subset s).val).re=
      dyadicWeight n s := by
  let E := traceFreeDyadicPartition hfactor hdiff ⟨1,IsStarProjection.one _⟩ n
  have he (i : DyadicIndex n) : (φ (E.leg i).target.val).re=(φ E.base.val).re := by
    exact congrArg Complex.re (tracialFunctional_equivalent φ htrace
      (show (E.leg i).target.Equivalent E.base from
        AlgebraProjection.equivalent_symm ⟨E.leg i,E.initial i,rfl⟩))
  have ht := congrArg (fun x : M.toStarSubalgebra => (φ x).re) E.total
  simp only [map_sum,Complex.re_sum,he,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,card_dyadicIndex,Nat.cast_pow,Nat.cast_ofNat,h1,Complex.one_re] at ht
  have hb : (φ E.base.val).re=1/(2 : ℝ)^n := by
    apply (eq_div_iff (ne_of_gt (pow_pos (by norm_num : (0 : ℝ)<2) n))).mpr
    nlinarith [ht]
  change (φ (E.subset s).val).re=_
  rw [E.subset_val,map_sum,Complex.re_sum]
  simp only [he,hb,Finset.sum_const,nsmul_eq_mul]
  change (s.card : ℝ)*(1/2^n)=(s.card : ℝ)/2^n
  ring

include hfinite in
theorem tracialFunctional_projection_dimension_re (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (h1 : φ 1=1)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    (p : AlgebraProjection M) : (φ p.val).re=traceFreeDimension hfactor hdiff p := by
  apply eq_of_all_dyadic_errors
  intro n
  obtain ⟨s,t,_,_,hs,ht,hl,hu,hgap⟩ := traceFreeDyadicSup_rounding hfactor hdiff hfinite
    ⟨1,IsStarProjection.one _⟩ p hunit (one_mul _) n
  have hφl := tracialFunctional_subequivalent φ hpos htrace hs
  have hφu := tracialFunctional_subequivalent φ hpos htrace ht
  rw [tracialFunctional_dyadic_subset_re hfactor hdiff φ h1 htrace] at hφl hφu
  change dyadicWeight n s ≤ traceFreeDimension hfactor hdiff p at hl
  change traceFreeDimension hfactor hdiff p ≤ dyadicWeight n t at hu
  have hn : 0 ≤ 1/(2 : ℝ)^n := by positivity
  rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring]
  apply abs_le.mpr
  constructor <;> linarith

include hfinite in
theorem tracialFunctional_projection_dimension (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (h1 : φ 1=1)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    (hstar : ∀ x : M.toStarSubalgebra, φ (star x)=star (φ x))
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    (p : AlgebraProjection M) : φ p.val=(traceFreeDimension hfactor hdiff p : ℂ) := by
  apply Complex.ext
  · exact tracialFunctional_projection_dimension_re hfactor hdiff hfinite hunit φ h1 hpos htrace p
  · have h := congrArg Complex.im (hstar p.val)
    rw [p.property.isSelfAdjoint.star_eq] at h
    change (φ p.val).im= -(φ p.val).im at h
    change (φ p.val).im=0
    linarith

end

/-! Identification of the actual tracial state with the spectral dimension
value, and unrestricted additivity for noncommuting self-adjoint operators. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance spectralAdditivityCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance spectralAdditivityOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance spectralAdditivityPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance spectralAdditivityLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance spectralAdditivityStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem functional_isDimensionSpectralValue (φ : M.toStarSubalgebra →L[ℂ] ℂ)
    (hnorm : ‖φ‖ ≤ 1)
    (hproj : ∀ p : AlgebraProjection M, φ p.val=(traceFreeDimension hfactor hdiff p : ℂ))
    (x : M.toStarSubalgebra) : IsDimensionSpectralValue hfactor hdiff x (φ x) := by
  intro Q c _
  have he : φ (∑ i, c i • (Q.piece i).val)=
      ∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
    simp only [map_sum,map_smul,smul_eq_mul,hproj]
  rw [← he,← map_sub]
  simpa only [one_mul] using φ.le_of_opNorm_le hnorm (x-∑ i, c i • (Q.piece i).val)

theorem functional_eq_dimensionSpectralValue (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (hnorm : ‖φ‖ ≤ 1)
    (hproj : ∀ p : AlgebraProjection M, φ p.val=(traceFreeDimension hfactor hdiff p : ℂ))
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    φ x=dimensionSpectralValue hfactor hdiff hfinite hunit x hx :=
  (functional_isDimensionSpectralValue hfactor hdiff φ hnorm hproj x).unique hfactor hdiff hx
    (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2

/-- The missing noncommuting additivity law, from the constructed linear state. -/
theorem dimensionSpectralValue_add (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x y : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (x+y) (hx.add hy)=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx+
      dimensionSpectralValue hfactor hdiff hfinite hunit y hy := by
  obtain ⟨φ,hnorm,h1,hpos,hstar,htrace⟩ := exists_tracial_state hfactor hdiff hfinite hunit
  have hproj := tracialFunctional_projection_dimension hfactor hdiff hfinite hunit φ h1 hpos hstar htrace
  rw [← functional_eq_dimensionSpectralValue hfactor hdiff hfinite hunit φ hnorm hproj (x+y) (hx.add hy),
    ← functional_eq_dimensionSpectralValue hfactor hdiff hfinite hunit φ hnorm hproj x hx,
    ← functional_eq_dimensionSpectralValue hfactor hdiff hfinite hunit φ hnorm hproj y hy,map_add]

include hfactor hdiff hfinite in
theorem tracialFunctional_faithful (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (φ : M.toStarSubalgebra →L[ℂ] ℂ) (hnorm : ‖φ‖ ≤ 1) (h1 : φ 1=1)
    (hpos : ∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (φ x).re)
    (hstar : ∀ x : M.toStarSubalgebra, φ (star x)=star (φ x))
    (htrace : ∀ x y : M.toStarSubalgebra, φ (x*y)=φ (y*x))
    (x : M.toStarSubalgebra) (hx : 0 ≤ x) : φ x=0 ↔ x=0 := by
  rw [functional_eq_dimensionSpectralValue hfactor hdiff hfinite hunit φ hnorm
    (tracialFunctional_projection_dimension hfactor hdiff hfinite hunit φ h1 hpos hstar htrace)
    x hx.isSelfAdjoint]
  exact dimensionSpectralValue_eq_zero_iff_of_nonneg hfactor hdiff hfinite hunit x hx

end

/-! The constructed faithful normalized trace on the original algebra.
Projection-net continuity is proved explicitly; no general normality or
representation theorem is hidden in the definition. -/
section
open Filter
open scoped Topology CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance tracePreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance traceStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

def traceFreeTrace : M.toStarSubalgebra →L[ℂ] ℂ :=
  (exists_tracial_state hfactor hdiff hfinite hunit).choose

theorem traceFreeTrace_spec :
    ‖traceFreeTrace hfactor hdiff hfinite hunit‖ ≤ 1 ∧
    traceFreeTrace hfactor hdiff hfinite hunit 1=1 ∧
    (∀ x : M.toStarSubalgebra, 0 ≤ x → 0 ≤ (traceFreeTrace hfactor hdiff hfinite hunit x).re) ∧
    (∀ x : M.toStarSubalgebra, traceFreeTrace hfactor hdiff hfinite hunit (star x)=
      star (traceFreeTrace hfactor hdiff hfinite hunit x)) ∧
    ∀ x y : M.toStarSubalgebra, traceFreeTrace hfactor hdiff hfinite hunit (x*y)=
      traceFreeTrace hfactor hdiff hfinite hunit (y*x) :=
  (exists_tracial_state hfactor hdiff hfinite hunit).choose_spec

theorem traceFreeTrace_projection (p : AlgebraProjection M) :
    traceFreeTrace hfactor hdiff hfinite hunit p.val=(traceFreeDimension hfactor hdiff p : ℂ) := by
  obtain ⟨_,h1,hpos,hstar,htrace⟩ := traceFreeTrace_spec hfactor hdiff hfinite hunit
  exact tracialFunctional_projection_dimension hfactor hdiff hfinite hunit _ h1 hpos hstar htrace p

theorem traceFreeTrace_selfAdjoint (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    traceFreeTrace hfactor hdiff hfinite hunit x=
      dimensionSpectralValue hfactor hdiff hfinite hunit x hx :=
  functional_eq_dimensionSpectralValue hfactor hdiff hfinite hunit _
    (traceFreeTrace_spec hfactor hdiff hfinite hunit).1
    (traceFreeTrace_projection hfactor hdiff hfinite hunit) x hx

theorem traceFreeTrace_faithful (x : M.toStarSubalgebra) (hx : 0 ≤ x) :
    traceFreeTrace hfactor hdiff hfinite hunit x=0 ↔ x=0 := by
  rw [traceFreeTrace_selfAdjoint hfactor hdiff hfinite hunit x hx.isSelfAdjoint]
  exact dimensionSpectralValue_eq_zero_iff_of_nonneg hfactor hdiff hfinite hunit x hx

theorem traceFreeTrace_projection_tendsto
    {I : Type*} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (q : I → AlgebraProjection M) (hq : Monotone q)
    (p : AlgebraProjection M) (hp : IsLUB (Set.range q) p) :
    Tendsto (fun i => traceFreeTrace hfactor hdiff hfinite hunit (q i).val) atTop
      (𝓝 (traceFreeTrace hfactor hdiff hfinite hunit p.val)) := by
  simp only [traceFreeTrace_projection]
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp
    (traceFreeDimension_tendsto_monotone hfactor hdiff hfinite hunit q hq p hp)

end

/-! The constructed trace is dominated by a finite sum of concrete vector
functionals. The matrix partition is constructed inside the localized corner. -/
section
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance dominationCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance dominationOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance dominationPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance dominationLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance dominationStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

theorem traceFreeTrace_matrix_diagonal {ι : Type*} [Fintype ι]
    (Q : EquivalentPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) ι)
    (x : M.toStarSubalgebra) :
    (∑ i, traceFreeTrace hfactor hdiff hfinite hunit (Q.stateCoefficient x i i))=
      traceFreeTrace hfactor hdiff hfinite hunit x := by
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  have ht := (traceFreeTrace_spec hfactor hdiff hfinite hunit).2.2.2.2
  have hi (i : ι) : τ (Q.stateCoefficient x i i)=τ ((Q.leg i).target.val*x) := by
    change τ ((star (Q.leg i).val*x)*(Q.leg i).val)=_
    rw [ht]
    congr 1
  change (∑ i, τ (Q.stateCoefficient x i i))=τ x
  simp_rw [hi]
  rw [← map_sum,← Finset.sum_mul,Q.total,one_mul]

theorem traceFreeTrace_exists_finite_vector_domination :
    ∃ (n : ℕ) (ξ : Fin n → H) (C : ℝ), 0<C ∧
      ∀ x : M.toStarSubalgebra, 0 ≤ x →
        (traceFreeTrace hfactor hdiff hfinite hunit x).re ≤
          C * ∑ i, (inner ℂ (ξ i) (x.val (ξ i))).re := by
  obtain ⟨ξ,hξ⟩ := exists_unit_vector_of_unit_ne_zero hunit
  obtain ⟨E,a,hE,ha,hloc⟩ := exists_localized_vector_functional hfactor hdiff hfinite hunit ξ hξ 1 (by norm_num)
  obtain ⟨n,_,Q,hQE,_⟩ := exists_equivalent_partition_base_le hfactor hdiff hfinite hunit E hE
  refine ⟨n,fun i => (Q.leg i).val.val ξ,a⁻¹,inv_pos.mpr ha,?_⟩
  intro x hx
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  have hi (i : Fin n) : a*(τ (Q.stateCoefficient x i i)).re ≤
      (vectorFunctional ξ (Q.stateCoefficient x i i)).re := by
    have hpos : 0 ≤ Q.stateCoefficient x i i := star_left_conjugate_nonneg hx (Q.leg i).val
    have hEx : E.val*Q.stateCoefficient x i i=Q.stateCoefficient x i i := by
      calc E.val*Q.stateCoefficient x i i =
          E.val*(Q.base.val*Q.stateCoefficient x i i) := by rw [Q.stateCoefficient_left]
        _ = Q.stateCoefficient x i i := by rw [← mul_assoc,hQE,Q.stateCoefficient_left]
    have h := (hloc (Q.stateCoefficient x i i) hpos hEx).1
    rwa [← traceFreeTrace_selfAdjoint hfactor hdiff hfinite hunit _ hpos.isSelfAdjoint] at h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hi i)
  rw [← Finset.mul_sum,← Complex.re_sum,
    traceFreeTrace_matrix_diagonal hfactor hdiff hfinite hunit] at hsum
  have hv : (∑ i, (vectorFunctional ξ (Q.stateCoefficient x i i)).re)=
      ∑ i, (inner ℂ ((Q.leg i).val.val ξ) (x.val ((Q.leg i).val.val ξ))).re := by
    rw [← Complex.re_sum,← Q.matrixVectorFunctional_apply]
    simp only [EquivalentPartition.matrixVectorFunctional,sum_apply,Complex.re_sum,
      vectorFunctional_apply]
  rw [hv] at hsum
  have h := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr ha.le)
  simpa only [← mul_assoc,inv_mul_cancel₀ ha.ne',one_mul] using h

/-- The scalar Cauchy--Schwarz bound follows from positivity of a centered square. -/
theorem traceFreeTrace_norm_sq_le (x : M.toStarSubalgebra) :
    ‖traceFreeTrace hfactor hdiff hfinite hunit x‖^2 ≤
      (traceFreeTrace hfactor hdiff hfinite hunit (star x*x)).re := by
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  obtain ⟨_,h1,hpos,hstar,_⟩ := traceFreeTrace_spec hfactor hdiff hfinite hunit
  change τ 1=1 at h1
  change ∀ x : M.toStarSubalgebra, τ (star x)=star (τ x) at hstar
  have h := hpos (star (x-(τ x) • 1)*(x-(τ x) • 1)) (star_mul_self_nonneg _)
  change 0 ≤ (τ (star (x-(τ x) • 1)*(x-(τ x) • 1))).re at h
  have he : τ (star (x-(τ x) • 1)*(x-(τ x) • 1))=
      τ (star x*x)-star (τ x)*(τ x) := by
    simp only [star_sub,star_smul,star_one,sub_mul,mul_sub,smul_mul_assoc,
      mul_smul_comm,mul_one,one_mul,map_sub,map_smul,smul_eq_mul,h1,hstar]
    ring
  rw [he,Complex.sub_re] at h
  change ‖τ x‖^2 ≤ (τ (star x*x)).re
  have hn : (star (τ x)*(τ x)).re=‖τ x‖^2 := by
    rw [RCLike.star_def,Complex.conj_mul',← Complex.ofReal_pow,Complex.ofReal_re]
  rw [hn] at h
  linarith

end

/-! Finite vector-functional representation and actual ultraweak continuity of
the constructed trace. No normality criterion is taken as an axiom. -/
open scoped BigOperators CStarAlgebra
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
local instance traceNormalCStar : CStarAlgebra M.toStarSubalgebra := {}
local instance traceNormalOrder : PartialOrder M.toStarSubalgebra := CStarAlgebra.spectralOrder _
local instance traceNormalPreorder : Preorder M.toStarSubalgebra :=
  (CStarAlgebra.spectralOrder _).toPreorder
local instance traceNormalLE : LE M.toStarSubalgebra := (CStarAlgebra.spectralOrder _).toLE
local instance traceNormalStarOrder : StarOrderedRing M.toStarSubalgebra := CStarAlgebra.spectralOrderedRing _
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)
variable (hunit : (1 : M.toStarSubalgebra) ≠ 0)

theorem traceFreeTrace_finite_vector_representation :
    ∃ (n : ℕ) (ξ η : Fin n → H), ∀ x : M.toStarSubalgebra,
      traceFreeTrace hfactor hdiff hfinite hunit x=∑ i, inner ℂ (η i) (x.val (ξ i)) := by
  obtain ⟨n,ξ,C,hC,hbound⟩ := traceFreeTrace_exists_finite_vector_domination hfactor hdiff hfinite hunit
  let V := PiLp 2 (fun _ : Fin n => H)
  let F : M.toStarSubalgebra →ₗ[ℂ] V :=
    { toFun := fun x => WithLp.toLp 2 (fun i => x.val (ξ i))
      map_add' := by intros; ext i; rfl
      map_smul' := by intros; ext i; rfl }
  let τ := traceFreeTrace hfactor hdiff hfinite hunit
  have hb (x : M.toStarSubalgebra) : ‖τ x‖ ≤ Real.sqrt C*‖F x‖ := by
    have hs := (traceFreeTrace_norm_sq_le hfactor hdiff hfinite hunit x).trans
      (hbound (star x*x) (star_mul_self_nonneg _))
    have hi (i : Fin n) : (inner ℂ (ξ i) ((star x*x).val (ξ i))).re=‖x.val (ξ i)‖^2 := by
      change (vectorFunctional (ξ i) (star x*x)).re=_
      rw [vectorFunctional_star_mul_self,← Complex.ofReal_pow,Complex.ofReal_re]
    simp only [hi] at hs
    have hFn : ‖F x‖^2=∑ i, ‖x.val (ξ i)‖^2 := PiLp.norm_sq_eq_of_L2 _ (F x)
    rw [← hFn] at hs
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt hC.le]
    exact hs
  obtain ⟨η,hη⟩ := exists_inner_factor_of_bound F τ.toLinearMap (Real.sqrt C) hb
  refine ⟨n,ξ,fun i => η i,?_⟩
  intro x
  exact (hη x).trans (PiLp.inner_apply η (F x))

theorem traceFreeTrace_normal :
    @Continuous _ _ (UltrapowerBridge.algebraUltraweakTopology M) inferInstance
      (traceFreeTrace hfactor hdiff hfinite hunit) := by
  obtain ⟨n,ξ,η,h⟩ := traceFreeTrace_finite_vector_representation hfactor hdiff hfinite hunit
  have hc : @Continuous _ _ (UltrapowerBridge.ultraweakTopology H) inferInstance
      (fun T : H →L[ℂ] H => ∑ i, inner ℂ (η i) (T (ξ i))) := by
    let : TopologicalSpace (H →L[ℂ] H) := UltrapowerBridge.ultraweakTopology H
    exact continuous_finsetSum _ (fun i _ => UltrapowerBridge.vectorFunctional_ultraweak_continuous (η i) (ξ i))
  have he : (traceFreeTrace hfactor hdiff hfinite hunit : M.toStarSubalgebra → ℂ)=
      (fun x => ∑ i, inner ℂ (η i) (x.val (ξ i))) := funext h
  rw [he]
  exact @Continuous.comp _ _ _ (UltrapowerBridge.algebraUltraweakTopology M)
    (UltrapowerBridge.ultraweakTopology H) _ _ _ hc continuous_induced_dom

end Generator.Tracial

end

end OAI
