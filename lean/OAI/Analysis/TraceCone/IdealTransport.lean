import OAI.Analysis.TraceCone.FiniteIdeal

namespace OAI

/-!
# Ideal transport through the extended trace cone

Additive idempotents recover closed ideals. The scalar limits at zero and infinity
recover the finite and zero ideals of an extended lower semicontinuous trace.
These constructions give the ideal transport in Section 2 of
*The trace cone classifies Razak–Jacelon stabilizations* (OpenAI, 2026).
-/

noncomputable section
open Filter Topology Classical
open scoped NNReal ENNReal

namespace TraceConeClassification

universe u v
variable {A : Type u} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace ExtendedTrace

@[ext] theorem ext {τ σ : ExtendedTrace A} (h : ∀ a, τ a = σ a) : τ = σ := by
  cases τ
  cases σ
  congr
  exact funext h

/-- Pointwise addition of the actual extended weights, including infinite values. -/
def add (τ σ : ExtendedTrace A) : ExtendedTrace A where
  toFun a := τ a + σ a
  map_zero := by rw [τ.map_zero, σ.map_zero, add_zero]
  map_add a b := by rw [τ.map_add, σ.map_add]; ac_rfl
  map_scale r hr a := by rw [τ.map_scale r hr, σ.map_scale r hr, mul_add]
  tracial x := by rw [τ.tracial x, σ.tracial x]
  lowerSemicontinuous := τ.lowerSemicontinuous.add σ.lowerSemicontinuous

@[simp] theorem add_apply (τ σ : ExtendedTrace A) (a : Positive A) :
    τ.add σ a = τ a + σ a := rfl

/-- The zero weight, not the weight of the zero ideal. -/
def zero : ExtendedTrace A where
  toFun _ := 0
  map_zero := rfl
  map_add _ _ := (add_zero _).symm
  map_scale _ _ _ := (mul_zero _).symm
  tracial _ := rfl
  lowerSemicontinuous := lowerSemicontinuous_const

@[simp] theorem zero_apply (a : Positive A) : (zero : ExtendedTrace A) a = 0 := rfl

/-- Additive idempotence cannot hide any finite nonzero values. -/
theorem idempotent_values {τ : ExtendedTrace A} (hτ : τ.add τ = τ) (a : Positive A) :
    τ a = 0 ∨ τ a = ∞ := by
  by_cases ha : τ a = ∞
  · exact Or.inr ha
  · left
    apply (ENNReal.add_right_inj ha).mp
    simpa only [add_apply, add_zero] using congrArg (fun σ : ExtendedTrace A => σ a) hτ

end ExtendedTrace

/-- A literal closed two-sided star ideal of the coefficient algebra. -/
def ClosedIdeal (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] :=
  {I : NonUnitalStarSubalgebra ℂ A // IsClosed (I : Set A) ∧
    (∀ (x y : A), y ∈ I → x * y ∈ I) ∧ (∀ (x y : A), x ∈ I → x * y ∈ I)}

namespace ClosedIdeal

instance : PartialOrder (ClosedIdeal A) := inferInstanceAs (PartialOrder (Subtype _))

/-- The extended trace taking zero on an ideal and infinity outside it. -/
def weight (I : ClosedIdeal A) : ExtendedTrace A :=
  (closed_ideal_weight_exists I.1 I.2.1 I.2.2.1 I.2.2.2).choose

lemma weight_apply (I : ClosedIdeal A) (a : Positive A) :
    I.weight a = if a.1 ∈ I.1 then 0 else ∞ :=
  (closed_ideal_weight_exists I.1 I.2.1 I.2.2.1 I.2.2.2).choose_spec a

@[simp] theorem weight_idempotent (I : ClosedIdeal A) : I.weight.add I.weight = I.weight := by
  apply ExtendedTrace.ext
  intro a
  rw [ExtendedTrace.add_apply, weight_apply]
  split <;> simp

@[simp] theorem finiteIdeal_weight (I : ClosedIdeal A) : I.weight.finiteIdeal = I.1 := by
  apply le_antisymm
  · apply (ExtendedTrace.finiteIdeal_le_iff _ I.1 I.2.1 I.2.2.1 I.2.2.2).mpr
    intro a ha
    by_contra hn
    rw [weight_apply, ite_eq_right hn] at ha
    exact lt_irrefl _ ha
  · intro x hx
    apply NonUnitalStarSubalgebra.le_topologicalClosure I.weight.finiteSquareAlgebra
    change I.weight (Positive.starMul x) < ∞
    simp only [weight_apply, Positive.starMul, ite_eq_left (I.2.2.1 (star x) x hx)]
    exact ENNReal.zero_lt_top

lemma weight_injective : Function.Injective (weight : ClosedIdeal A → ExtendedTrace A) := by
  intro I J h
  apply Subtype.ext
  simpa only [finiteIdeal_weight] using congrArg ExtendedTrace.finiteIdeal h

/-- The reversed order on ideal weights can be read using only addition. -/
theorem le_iff_add_weight (I J : ClosedIdeal A) :
    I ≤ J ↔ I.weight.add J.weight = I.weight := by
  constructor
  · intro h
    apply ExtendedTrace.ext
    intro a
    rw [ExtendedTrace.add_apply, weight_apply, weight_apply]
    by_cases ha : a.1 ∈ I.1
    · simp only [ite_eq_left ha, ite_eq_left (h ha), add_zero]
    · simp only [ite_eq_right ha, top_add]
  · intro h x hx
    have hs : star x * x ∈ I.1 := I.2.2.1 _ _ hx
    have hv := congrArg (fun τ : ExtendedTrace A => τ (Positive.starMul x)) h
    simp only [ExtendedTrace.add_apply, weight_apply, Positive.starMul, ite_eq_left hs,
      zero_add] at hv
    have hj : star x * x ∈ J.1 := by
      by_contra hn
      rw [ite_eq_right hn] at hv
      exact ENNReal.top_ne_zero hv
    exact (closed_ideal_star_mul_mem_iff J.1 J.2.1 J.2.2.1 x).mp hj

end ClosedIdeal

namespace ExtendedTrace

/-- The closed finite-domain ideal, with the absorption and closedness already proved. -/
def finIdeal (τ : ExtendedTrace A) : ClosedIdeal A :=
  ⟨τ.finiteIdeal, τ.isClosed_finiteIdeal, fun x _ hy => τ.mul_mem_finiteIdeal_left x hy,
    fun _ y hx => τ.mul_mem_finiteIdeal_right hx y⟩

/-- For an additive idempotent, every positive in its finite ideal has value zero.
Lower semicontinuity is essential here: the finite ideal is a norm closure. -/
theorem idempotent_zero_on_finIdeal {τ : ExtendedTrace A} (hτ : τ.add τ = τ)
    (a : Positive A) (ha : a.1 ∈ τ.finiteIdeal) : τ a = 0 := by
  obtain ⟨b, hb, ht⟩ := τ.finite_positive_dense a ha
  apply le_antisymm _ bot_le
  apply (τ.lowerSemicontinuous.isClosed_preimage 0).mem_of_tendsto ht
  apply Eventually.of_forall
  intro n
  have hzero : τ (b n) = 0 := (idempotent_values hτ (b n)).resolve_right (hb n).ne
  exact hzero.le

/-- Every additive idempotent is the literal weight of a closed two-sided ideal. -/
theorem idempotent_eq_weight {τ : ExtendedTrace A} (hτ : τ.add τ = τ) :
    τ.finIdeal.weight = τ := by
  apply ext
  intro a
  rw [ClosedIdeal.weight_apply]
  change (if a.1 ∈ τ.finiteIdeal then 0 else ∞) = τ a
  by_cases ha : a.1 ∈ τ.finiteIdeal
  · rw [ite_eq_left ha, idempotent_zero_on_finIdeal hτ a ha]
  · rw [ite_eq_right ha]
    exact (eq_top_iff.mpr (not_lt.mp (fun hf => ha
      (τ.positive_mem_finiteIdeal_of_finite a hf)))).symm

end ExtendedTrace

/-- Precisely the additive idempotents, not a chosen subclass of traces. -/
def IdempotentTrace (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] := {τ : ExtendedTrace A // τ.add τ = τ}

/-- The bijection in the first paragraph of the proof of `st:ideals`. -/
def closedIdealEquivIdempotent : ClosedIdeal A ≃ IdempotentTrace A where
  toFun I := ⟨I.weight, I.weight_idempotent⟩
  invFun τ := τ.1.finIdeal
  left_inv I := Subtype.ext (ClosedIdeal.finiteIdeal_weight I)
  right_inv τ := Subtype.ext (ExtendedTrace.idempotent_eq_weight τ.2)

/-- Uniqueness of limits for canonical cut limsup/liminf convergence. -/
theorem canonicalConvergence_unique {ι : Type*} (l : Filter ι) [l.NeBot]
    (f : ι → ExtendedTrace A) {τ σ : ExtendedTrace A}
    (hτ : CanonicalConvergence A l f τ) (hσ : CanonicalConvergence A l f σ) : τ = σ := by
  have hle {ρ κ : ExtendedTrace A} (hρ : CanonicalConvergence A l f ρ)
      (hκ : CanonicalConvergence A l f κ) (a : Positive A) : ρ a ≤ κ a := by
    rw [trace_eq_iSup_positive_cuts A ρ a]
    apply iSup_le
    intro ε
    apply iSup_le
    intro hε
    exact ((hρ (Positive.cut a ε) 1 (by norm_num)).2.trans liminf_le_limsup).trans
      (hκ a ε hε).1
  exact ExtendedTrace.ext fun a => le_antisymm (hle hτ hσ a) (hle hσ hτ a)


variable {B : Type v} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- An additive bijection of extended trace cones identifies their additive idempotents. -/
def idempotentTraceEquiv (e : ExtendedTrace A ≃ ExtendedTrace B)
    (he : ∀ τ σ, e (τ.add σ) = (e τ).add (e σ)) : IdempotentTrace A ≃ IdempotentTrace B where
  toFun τ := ⟨e τ.1, by rw [← he, τ.2]⟩
  invFun σ := ⟨e.symm σ.1, by
    apply e.injective
    rw [he, e.apply_symm_apply, σ.2]⟩
  left_inv τ := Subtype.ext (e.symm_apply_apply τ.1)
  right_inv σ := Subtype.ext (e.apply_symm_apply σ.1)

/-- Recovering the closed ideals from their idempotent trace weights. -/
def closedIdealEquivOfAdditive (e : ExtendedTrace A ≃ ExtendedTrace B)
    (he : ∀ τ σ, e (τ.add σ) = (e τ).add (e σ)) : ClosedIdeal A ≃ ClosedIdeal B :=
  closedIdealEquivIdempotent.trans ((idempotentTraceEquiv e he).trans
    closedIdealEquivIdempotent.symm)

lemma closedIdealEquivOfAdditive_weight (e : ExtendedTrace A ≃ ExtendedTrace B)
    (he : ∀ τ σ, e (τ.add σ) = (e τ).add (e σ)) (I : ClosedIdeal A) :
    (closedIdealEquivOfAdditive e he I).weight = e I.weight := by
  exact ExtendedTrace.idempotent_eq_weight
    ((idempotentTraceEquiv e he) (closedIdealEquivIdempotent I)).2

/-- The order isomorphism of closed ideals induced by an additive trace-cone bijection. -/
def closedIdealOrderEquivOfAdditive (e : ExtendedTrace A ≃ ExtendedTrace B)
    (he : ∀ τ σ, e (τ.add σ) = (e τ).add (e σ)) : ClosedIdeal A ≃o ClosedIdeal B where
  toEquiv := closedIdealEquivOfAdditive e he
  map_rel_iff' := by
    intro I J
    rw [ClosedIdeal.le_iff_add_weight, ClosedIdeal.le_iff_add_weight,
      closedIdealEquivOfAdditive_weight, closedIdealEquivOfAdditive_weight, ← he]
    exact e.injective.eq_iff


/-- Pointwise convergence implies the specified convergence, but is not used as
its definition (the converse is false in general). -/
theorem canonicalConvergence_of_pointwise {ι : Type*} (l : Filter ι) [l.NeBot]
    (f : ι → ExtendedTrace A) (σ : ExtendedTrace A)
    (h : ∀ a, Tendsto (fun i => f i a) l (𝓝 (σ a))) :
    CanonicalConvergence A l f σ := by
  intro a ε hε
  exact ⟨(h (Positive.cut a ε)).limsup_eq.le.trans (σ.monotone (Positive.cut_le a ε)),
    (h a).liminf_eq.symm.le⟩

/-- Reindexing a net by its image filter does not change the cut inequalities. -/
lemma canonicalConvergence_map_iff {ι κ : Type*} (l : Filter ι) (g : ι → κ)
    (f : κ → ExtendedTrace A) (σ : ExtendedTrace A) :
    CanonicalConvergence A (map g l) f σ ↔ CanonicalConvergence A l (f ∘ g) σ := by
  simp only [CanonicalConvergence, ← limsup_comp, ← liminf_comp, Function.comp_def]

/-- Preservation of canonical convergence for filters on the trace cone.
The image-filter identity extends this property to nets in every index type. -/
def PreservesCanonicalConvergence (f : ExtendedTrace A → ExtendedTrace B) : Prop :=
  ∀ (l : Filter (ExtendedTrace A)) (σ : ExtendedTrace A),
    CanonicalConvergence A l id σ → CanonicalConvergence B l f (f σ)

lemma PreservesCanonicalConvergence.net {f : ExtendedTrace A → ExtendedTrace B}
    (hf : PreservesCanonicalConvergence f) {ι : Type*} (l : Filter ι)
    (g : ι → ExtendedTrace A) (σ : ExtendedTrace A)
    (h : CanonicalConvergence A l g σ) :
    CanonicalConvergence B l (f ∘ g) (f σ) := by
  apply (canonicalConvergence_map_iff l g f (f σ)).mp
  apply hf
  apply (canonicalConvergence_map_iff l g id σ).mpr
  exact h

namespace ExtendedTrace

/-- Positive scalar multiples converge to the finite-ideal weight as the scalar tends to zero. -/
theorem scale_zero_limit (τ : ExtendedTrace A) :
    CanonicalConvergence A (𝓝[>] (0 : ℝ≥0)) (fun r => τ.scale r) τ.finIdeal.weight := by
  obtain ⟨I, hI, hl, hr, hu, _, ω, hω, hc⟩ := finite_domain_ideal_and_scalar_limit τ
  have he : I = τ.finiteIdeal := by
    apply le_antisymm
    · apply (hu τ.finiteIdeal τ.isClosed_finiteIdeal
        (fun x _ hy => τ.mul_mem_finiteIdeal_left x hy)
        (fun _ y hx => τ.mul_mem_finiteIdeal_right hx y)).mpr
      exact τ.positive_mem_finiteIdeal_of_finite
    · apply (τ.finiteIdeal_le_iff I hI hl hr).mpr
      exact (hu I hI hl hr).mp le_rfl
  have hωeq : ω = τ.finIdeal.weight := by
    apply ext
    intro a
    rw [hω, ClosedIdeal.weight_apply, he]
    rfl
  rwa [hωeq] at hc

lemma lowerSemicontinuous_supportWeight (τ : ExtendedTrace A) :
    LowerSemicontinuous (fun a : Positive A => if τ a = 0 then (0 : ℝ≥0∞) else ∞) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  by_cases hc : c = ∞
  · subst c
    simp
  · have he : (fun a : Positive A => if τ a = 0 then (0 : ℝ≥0∞) else ∞) ⁻¹' Set.Iic c =
        τ ⁻¹' Set.Iic 0 := by
      ext a
      by_cases ha : τ a = 0 <;> simp [ha, hc]
    rw [he]
    exact τ.lowerSemicontinuous.isClosed_preimage 0

/-- The pointwise support weight of a trace. It will be identified with the
weight of the literal zero ideal, rather than an arbitrary ideal label. -/
def supportWeight (τ : ExtendedTrace A) : ExtendedTrace A where
  toFun a := if τ a = 0 then 0 else ∞
  map_zero := by simp [τ.map_zero]
  map_add a b := by
    rw [τ.map_add]
    by_cases ha : τ a = 0 <;> by_cases hb : τ b = 0 <;> simp [ha, hb]
  map_scale r hr a := by
    rw [τ.map_scale r hr]
    by_cases ha : τ a = 0 <;> simp [ha, ENNReal.coe_ne_zero.mpr hr.ne']
  tracial x := by rw [τ.tracial x]
  lowerSemicontinuous := τ.lowerSemicontinuous_supportWeight

lemma supportWeight_apply (τ : ExtendedTrace A) (a : Positive A) :
    τ.supportWeight a = if τ a = 0 then 0 else ∞ := rfl

lemma supportWeight_idempotent (τ : ExtendedTrace A) :
    τ.supportWeight.add τ.supportWeight = τ.supportWeight := by
  apply ext
  intro a
  rw [add_apply, supportWeight_apply]
  split <;> simp

/-- The zero ideal, as an actual closed two-sided ideal in the algebra. Its
positive elements are characterized by `mem_zeroIdeal_iff` below. -/
def zeroIdeal (τ : ExtendedTrace A) : ClosedIdeal A := τ.supportWeight.finIdeal

lemma mem_zeroIdeal_iff (τ : ExtendedTrace A) (a : Positive A) :
    a.1 ∈ τ.zeroIdeal.1 ↔ τ a = 0 := by
  constructor
  · intro ha
    have hh := idempotent_zero_on_finIdeal τ.supportWeight_idempotent a ha
    rw [supportWeight_apply] at hh
    by_contra hn
    rw [ite_eq_right hn] at hh
    exact ENNReal.top_ne_zero hh
  · intro ha
    apply τ.supportWeight.positive_mem_finiteIdeal_of_finite
    rw [supportWeight_apply, ite_eq_left ha]
    exact ENNReal.zero_lt_top

lemma zeroIdeal_weight (τ : ExtendedTrace A) : τ.zeroIdeal.weight = τ.supportWeight :=
  idempotent_eq_weight τ.supportWeight_idempotent

/-- The second scalar limit from `st:scalar-limits`, including all infinite
traces and the possibility that the zero ideal is the whole algebra or zero. -/
theorem scale_infty_limit (τ : ExtendedTrace A) :
    CanonicalConvergence A atTop (fun r : ℝ≥0 => τ.scale r) τ.zeroIdeal.weight := by
  rw [zeroIdeal_weight]
  apply canonicalConvergence_of_pointwise
  intro a
  by_cases ha : τ a = 0
  · simpa only [scale_apply, supportWeight_apply, ha, ite_true, mul_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => (0 : ℝ≥0∞)) atTop (𝓝 0))
  · have ht : Tendsto (fun r : ℝ≥0 => (r : ℝ≥0∞)) atTop (𝓝 ∞) :=
      ENNReal.tendsto_coe_nhds_top.mpr tendsto_id
    have hm := ENNReal.Tendsto.mul_const ht (b := τ a) (Or.inl ENNReal.top_ne_zero)
    simpa only [scale_apply, supportWeight_apply, ite_eq_right ha, ENNReal.top_mul ha] using hm

end ExtendedTrace


namespace ExtendedTrace

lemma scale_zero (τ : ExtendedTrace A) : τ.scale 0 = zero := by
  apply ext
  intro a
  simp only [scale_apply, ENNReal.coe_zero, zero_mul, zero_apply]

end ExtendedTrace

/-- An equivalence of extended trace cones preserving addition, zero, positive
scalar multiplication, and canonical convergence in both directions.
-/
structure TraceConeEquiv (A : Type u) [NonUnitalCStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (B : Type v) [NonUnitalCStarAlgebra B] [PartialOrder B]
    [StarOrderedRing B] where
  toEquiv : ExtendedTrace A ≃ ExtendedTrace B
  map_add : ∀ τ σ, toEquiv (τ.add σ) = (toEquiv τ).add (toEquiv σ)
  map_zero : toEquiv ExtendedTrace.zero = ExtendedTrace.zero
  map_scale : ∀ (r : ℝ≥0), 0 < r → ∀ τ, toEquiv (τ.scale r) = (toEquiv τ).scale r
  continuous_toFun : PreservesCanonicalConvergence toEquiv
  continuous_invFun : PreservesCanonicalConvergence toEquiv.symm

namespace TraceConeEquiv

variable (F : TraceConeEquiv A B)

lemma map_scale_all (r : ℝ≥0) (τ : ExtendedTrace A) :
    F.toEquiv (τ.scale r) = (F.toEquiv τ).scale r := by
  by_cases hr : r = 0
  · subst r
    rw [ExtendedTrace.scale_zero, ExtendedTrace.scale_zero, F.map_zero]
  · exact F.map_scale r (pos_iff_ne_zero.mpr hr) τ

/-- The actual ideal-poset isomorphism induced by a cone equivalence. -/
def idealOrderIso : ClosedIdeal A ≃o ClosedIdeal B :=
  closedIdealOrderEquivOfAdditive F.toEquiv F.map_add

lemma idealOrderIso_weight (I : ClosedIdeal A) :
    (F.idealOrderIso I).weight = F.toEquiv I.weight :=
  closedIdealEquivOfAdditive_weight F.toEquiv F.map_add I

/-- The scalar-zero limit identifies the finite-domain ideals under the induced
ideal correspondence, including weights whose finite ideal is proper or zero. -/
theorem idealOrderIso_finIdeal (τ : ExtendedTrace A) :
    F.idealOrderIso τ.finIdeal = (F.toEquiv τ).finIdeal := by
  apply ClosedIdeal.weight_injective
  rw [F.idealOrderIso_weight]
  have hc := F.continuous_toFun.net (𝓝[>] (0 : ℝ≥0))
    (fun r => τ.scale r) τ.finIdeal.weight τ.scale_zero_limit
  simp only [Function.comp_def, F.map_scale_all] at hc
  exact canonicalConvergence_unique _ _ hc (F.toEquiv τ).scale_zero_limit

/-- The scalar-infinity limit identifies the literal zero ideals under the same
ideal correspondence. No finiteness restriction on the trace is introduced. -/
theorem idealOrderIso_zeroIdeal (τ : ExtendedTrace A) :
    F.idealOrderIso τ.zeroIdeal = (F.toEquiv τ).zeroIdeal := by
  apply ClosedIdeal.weight_injective
  rw [F.idealOrderIso_weight]
  have hc := F.continuous_toFun.net atTop
    (fun r : ℝ≥0 => τ.scale r) τ.zeroIdeal.weight τ.scale_infty_limit
  simp only [Function.comp_def, F.map_scale_all] at hc
  exact canonicalConvergence_unique _ _ hc (F.toEquiv τ).scale_infty_limit

end TraceConeEquiv
end TraceConeClassification

end

end OAI
