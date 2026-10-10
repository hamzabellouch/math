import OAI.Analysis.TracialSplitting.TensorNorms

namespace OAI

noncomputable section

universe uD uE uI uJ uX

namespace Pureness

open Filter

open scoped Topology NNReal ENNReal

namespace ClosedStarIdeal

variable {D : Type uD} [CStarAlgebra D] (J : ClosedStarIdeal D)

def quotientStarHom : D →⋆ₐ[ℂ] J.Quotient :=
  { J.quotientMap with map_star' := J.quotientMap_star }

lemma quotientStarHom_continuous : Continuous (J.quotientStarHom) := by
  exact AddMonoidHomClass.continuous_of_bound J.quotientStarHom 1
    (fun element => by
      simpa only [quotientStarHom, StarAlgHom.coe_mk', one_mul] using J.quotientMap_norm_le element)

end ClosedStarIdeal

end Pureness

namespace CurrentMain

section

open Pureness

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

def familyTraceNorm (a : D) : ℝ := ⨆ i, ‖(τ i).functional a‖

lemma familyTwoNorm_sub_le (a b : D) :
    familyTwoNorm τ (a - b) ≤ familyTwoNorm τ a + familyTwoNorm τ b := by
  simpa only [sub_eq_add_neg, familyTwoNorm_neg] using familyTwoNorm_add_le τ a (-b)

lemma familyTwoNorm_smul_le (z : ℂ) (a : D) :
    familyTwoNorm τ (z • a) ≤ ‖z‖ * familyTwoNorm τ a := by
  apply ciSup_le
  intro i
  rw [traceTwoNorm_smul]
  exact mul_le_mul_of_nonneg_left (traceTwoNorm_le_family τ i a) (norm_nonneg z)

@[simp] lemma familyTwoNorm_smul (z : ℂ) (a : D) :
    familyTwoNorm τ (z • a) = ‖z‖ * familyTwoNorm τ a := by
  apply le_antisymm (familyTwoNorm_smul_le τ z a)
  by_cases hz : z = 0
  · simp [hz]
  have hi := mul_le_mul_of_nonneg_left (familyTwoNorm_smul_le τ z⁻¹ (z • a)) (norm_nonneg z)
  simpa [smul_smul, hz, mul_assoc, norm_ne_zero_iff.mpr hz] using hi

lemma familyTwoNorm_lipschitz : LipschitzWith 1 (familyTwoNorm τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  apply abs_le.mpr
  have hab := familyTwoNorm_sub_triangle τ a b 0
  have hba := familyTwoNorm_sub_triangle τ b a 0
  simp only [sub_zero] at hab hba
  have hm := familyTwoNorm_le_norm τ (a-b)
  rw [← familyTwoNorm_sub_swap τ a b] at hba
  rw [dist_eq_norm]
  constructor <;> linarith

omit [Nonempty I] in
lemma familyTraceNorm_bdd (a : D) : BddAbove (Set.range (fun i => ‖(τ i).functional a‖)) :=
  ⟨‖a‖, by rintro _ ⟨i, rfl⟩; exact trace_norm_le_norm (τ i) a⟩

omit [Nonempty I] in
lemma traceNorm_le_family (i : I) (a : D) :
    ‖(τ i).functional a‖ ≤ familyTraceNorm τ a := le_ciSup (familyTraceNorm_bdd τ a) i

lemma familyTraceNorm_nonneg (a : D) : 0 ≤ familyTraceNorm τ a := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact (norm_nonneg _).trans (traceNorm_le_family τ i a)

lemma familyTraceNorm_le_twoNorm (a : D) : familyTraceNorm τ a ≤ familyTwoNorm τ a := by
  apply ciSup_le
  intro i
  exact (trace_norm_le_twoNorm (τ i) a).trans (traceTwoNorm_le_family τ i a)

lemma familyTraceNorm_le_norm (a : D) : familyTraceNorm τ a ≤ ‖a‖ :=
  (familyTraceNorm_le_twoNorm τ a).trans (familyTwoNorm_le_norm τ a)

end

open Pureness Filter

open scoped Topology NNReal ENNReal

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

omit [Nonempty I] in
lemma isFamilyCauchy_neg {u : ℕ → D} (hu : IsFamilyCauchy τ u) :
    IsFamilyCauchy τ (fun n => -u n) := by
  simpa only [IsFamilyCauchy, neg_sub_neg, neg_sub] using isFamilyNull_neg τ hu

end CurrentMain

namespace Pureness.ClosedStarIdeal

open scoped ComplexOrder

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (J : ClosedStarIdeal D)

variable (τ : TracialState D) (hτ : ∀ a ∈ J.ideal, τ.functional a = 0)

lemma descendedTrace_map (u : D) :
    (J.descendedTrace τ hτ).functional (J.quotientMap u) = τ.functional u := rfl

end Pureness.ClosedStarIdeal

namespace CurrentMain

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section UltraTrace

variable {D : Type uD} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

variable (θ : X → TracialState D) (U : Ultrafilter X)

lemma ultraTrace_square_nonneg (u : lp (fun _ : X => D) ∞) :
    0 ≤ ultraTraceLinear θ U (star u*u) := by
  apply ge_of_tendsto (ultraTraceValue_tendsto θ U (star u*u))
  exact Eventually.of_forall (fun n => (θ n).functional.map_nonneg (star_mul_self_nonneg (u n)))

end UltraTrace

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

variable (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

lemma familyLimitTrace_tendsto (s : X → I) (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => (τ (s n)).functional (u n)) (U : Filter X)
      (𝓝 ((familyLimitTrace τ U s).functional
        ((familyNullIdeal τ (U : Filter X)).quotientMap u))) :=
  ultraTraceValue_tendsto (fun n => τ (s n)) U u

end

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

lemma uniform_sup_ultralimit {X : Type uX} {I : Type uI} [Nonempty I]
    (U : Ultrafilter X) (f : X → I → ℝ) (M : ℝ)
    (h₀ : ∀ n i, 0 ≤ f n i) (hM : ∀ n i, f n i ≤ M) :
    (⨆ s : X → I, limUnder (U : Filter X) (fun n => f n (s n))) =
      limUnder (U : Filter X) (fun n => ⨆ i, f n i) := by
  have hb (n : X) : BddAbove (Set.range (f n)) := ⟨M, by rintro _ ⟨i,rfl⟩; exact hM n i⟩
  have hs₀ (n : X) : 0 ≤ ⨆ i, f n i := by
    obtain ⟨i⟩ := ‹Nonempty I›
    exact (h₀ n i).trans (le_ciSup (hb n) i)
  have hsM (n : X) : (⨆ i, f n i) ≤ M := ciSup_le (hM n)
  have ht (s : X → I) := bounded_ultrafilter_tendsto U (fun n => f n (s n)) M
    (fun n => by simpa only [Real.norm_eq_abs, abs_of_nonneg (h₀ n (s n))] using hM n (s n))
  have hst := bounded_ultrafilter_tendsto U (fun n => ⨆ i, f n i) M
    (fun n => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hs₀ n)] using hsM n)
  have hbound : BddAbove (Set.range (fun s : X → I =>
      limUnder (U : Filter X) (fun n => f n (s n)))) := by
    refine ⟨M,?_⟩
    rintro _ ⟨s,rfl⟩
    exact le_of_tendsto (ht s) (Eventually.of_forall (fun n => hM n (s n)))
  apply le_antisymm
  · apply ciSup_le
    intro s
    exact le_of_tendsto_of_tendsto (ht s) hst
      (Eventually.of_forall (fun n => le_ciSup (hb n) (s n)))
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hex (n : X) : ∃ i, (⨆ j, f n j) - ε < f n i :=
      exists_lt_of_lt_ciSup (sub_lt_self _ hε)
    choose s hs using hex
    have hle := le_of_tendsto_of_tendsto hst ((ht s).add_const ε)
      (Eventually.of_forall (fun n => by linarith [hs n]))
    exact hle.trans (add_le_add (le_ciSup hbound s) le_rfl)

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

variable (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

lemma familyQuotientMap_eq_zero (u : lp (fun _ : X => D) ∞) :
    (familyNullIdeal τ (U : Filter X)).quotientMap u = 0 ↔
      IsFamilyNull τ (U : Filter X) (fun n => u n) := by
  let J := familyNullIdeal τ (U : Filter X)
  change J.ideal.ringCon.mk' u = J.ideal.ringCon.mk' 0 ↔ _
  exact (show J.ideal.ringCon.mk' u = J.ideal.ringCon.mk' 0 ↔ u ∈ J.ideal from
    Quotient.eq).trans (familyNull_mem τ _ u)

lemma traceTwoNorm_limitTrace_tendsto (s : X → I) (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => traceTwoNorm (τ (s n)) (u n)) (U : Filter X)
      (𝓝 (traceTwoNorm (familyLimitTrace τ U s)
        ((familyNullIdeal τ (U : Filter X)).quotientMap u))) := by
  have ht := familyLimitTrace_tendsto τ U s (star u*u)
  rw [map_mul, ClosedStarIdeal.quotientMap_star] at ht
  exact Real.continuous_sqrt.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp ht)

lemma familyTwoNorm_limitTrace (u : lp (fun _ : X => D) ∞) :
    familyTwoNorm (familyLimitTrace τ U)
      ((familyNullIdeal τ (U : Filter X)).quotientMap u) =
      limUnder (U : Filter X) (fun n => familyTwoNorm τ (u n)) := by
  have he (s : X → I) : traceTwoNorm (familyLimitTrace τ U s)
      ((familyNullIdeal τ (U : Filter X)).quotientMap u) =
      limUnder (U : Filter X) (fun n => traceTwoNorm (τ (s n)) (u n)) := by
    exact tendsto_nhds_unique (traceTwoNorm_limitTrace_tendsto τ U s u)
      (bounded_ultrafilter_tendsto U _ ‖u‖ (fun n => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (traceTwoNorm_nonneg _ _)] using
          (traceTwoNorm_le_norm (τ (s n)) (u n)).trans
            (lp.norm_apply_le_norm ENNReal.top_ne_zero u n)))
  simp only [familyTwoNorm, he]
  exact uniform_sup_ultralimit U (fun n i => traceTwoNorm (τ i) (u n)) ‖u‖
    (fun _ _ => traceTwoNorm_nonneg _ _) (fun n i =>
      (traceTwoNorm_le_norm (τ i) (u n)).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))

lemma familyTwoNorm_limitTrace_tendsto (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => familyTwoNorm τ (u n)) (U : Filter X)
      (𝓝 (familyTwoNorm (familyLimitTrace τ U)
        ((familyNullIdeal τ (U : Filter X)).quotientMap u))) := by
  rw [familyTwoNorm_limitTrace]
  exact bounded_ultrafilter_tendsto U _ ‖u‖ (fun n => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (familyTwoNorm_nonneg τ _)] using
      (familyTwoNorm_le_norm τ _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))

lemma familyTraceNorm_limitTrace (u : lp (fun _ : X => D) ∞) :
    familyTraceNorm (familyLimitTrace τ U)
      ((familyNullIdeal τ (U : Filter X)).quotientMap u) =
      limUnder (U : Filter X) (fun n => familyTraceNorm τ (u n)) := by
  have he (s : X → I) : ‖(familyLimitTrace τ U s).functional
      ((familyNullIdeal τ (U : Filter X)).quotientMap u)‖ =
      limUnder (U : Filter X) (fun n => ‖(τ (s n)).functional (u n)‖) := by
    exact tendsto_nhds_unique (familyLimitTrace_tendsto τ U s u).norm
      (bounded_ultrafilter_tendsto U _ ‖u‖ (fun n => by
        simpa only [norm_norm] using (trace_norm_le_norm (τ (s n)) (u n)).trans
          (lp.norm_apply_le_norm ENNReal.top_ne_zero u n)))
  simp only [familyTraceNorm, he]
  exact uniform_sup_ultralimit U (fun n i => ‖(τ i).functional (u n)‖) ‖u‖
    (fun _ _ => norm_nonneg _) (fun n i =>
      (trace_norm_le_norm (τ i) (u n)).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))

lemma familyTraceNorm_limitTrace_tendsto (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => familyTraceNorm τ (u n)) (U : Filter X)
      (𝓝 (familyTraceNorm (familyLimitTrace τ U)
        ((familyNullIdeal τ (U : Filter X)).quotientMap u))) := by
  rw [familyTraceNorm_limitTrace]
  exact bounded_ultrafilter_tendsto U _ ‖u‖ (fun n => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (familyTraceNorm_nonneg τ _)] using
      (familyTraceNorm_le_norm τ _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))

lemma limitTrace_detects_zero (z : FamilyUltrapower τ U)
    (hz : ∀ s : X → I, traceTwoNorm (familyLimitTrace τ U s) z = 0) : z = 0 := by
  obtain ⟨u,rfl⟩ := (familyNullIdeal τ (U : Filter X)).quotientMap_surjective z
  apply (familyQuotientMap_eq_zero τ U u).mpr
  have ht := familyTwoNorm_limitTrace_tendsto τ U u
  have he : familyTwoNorm (familyLimitTrace τ U)
      ((familyNullIdeal τ (U : Filter X)).quotientMap u) = 0 := by
    simp only [familyTwoNorm, hz, ciSup_const]
  change Tendsto _ _ (𝓝 0)
  simpa only [he] using ht

end

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]

lemma completionTrace_tendsto (i : I) (u : familyCauchyAlgebra τ) :
    Tendsto (fun n : ℕ => (τ i).functional (u.1 n)) atTop
      (𝓝 ((completionTrace τ i).functional ((familyCauchyNullIdeal τ).quotientMap u))) :=
  cauchyTrace_tendsto τ i u

lemma completionTwoNorm_tendsto (i : I) (u : familyCauchyAlgebra τ) :
    Tendsto (fun n : ℕ => traceTwoNorm (τ i) (u.1 n)) atTop
      (𝓝 (traceTwoNorm (completionTrace τ i) ((familyCauchyNullIdeal τ).quotientMap u))) := by
  have ht := completionTrace_tendsto τ i (star u*u)
  rw [map_mul, ClosedStarIdeal.quotientMap_star] at ht
  exact Real.continuous_sqrt.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp ht)

omit [Nontrivial D] [PartialOrder D] [StarOrderedRing D] in
@[simp] lemma boundedFamilyConstant_apply {X : Type uX} (a : D) (n : X) :
    boundedFamilyConstant a n = a := rfl

lemma completionTrace_constant (i : I) (a : D) :
    (completionTrace τ i).functional (completionMap τ a) = (τ i).functional a :=
  tendsto_nhds_unique (completionTrace_tendsto τ i (cauchyConstant τ a)) tendsto_const_nhds

lemma completionTwoNorm_constant (i : I) (a : D) :
    traceTwoNorm (completionTrace τ i) (completionMap τ a) = traceTwoNorm (τ i) a := by
  unfold traceTwoNorm
  rw [← map_star, ← map_mul, completionTrace_constant]

lemma familyTwoNorm_completionMap (a : D) :
    familyTwoNorm (completionTrace τ) (completionMap τ a) = familyTwoNorm τ a := by
  simp only [familyTwoNorm, completionTwoNorm_constant]

lemma completion_distance_tendsto_zero (u : familyCauchyAlgebra τ) :
    Tendsto (fun m : ℕ => familyTwoNorm (completionTrace τ)
      ((familyCauchyNullIdeal τ).quotientMap u - completionMap τ (u.1 m)))
      atTop (𝓝 0) := by
  apply (isFamilyNull_iff (completionTrace τ) atTop _).mpr
  intro ε hε
  obtain ⟨N,hN⟩ := (isFamilyCauchy_iff τ _).mp u.2 (ε/2) (by linarith)
  filter_upwards [eventually_ge_atTop N] with m hm
  refine lt_of_le_of_lt (ciSup_le fun i => ?_) (half_lt_self hε)
  have ht := completionTwoNorm_tendsto τ i (u-cauchyConstant τ (u.1 m))
  rw [map_sub] at ht
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (traceTwoNorm_le_family τ i _).trans (hN n hn m hm).le

theorem completion_uniform_dense (x : UniformTracialCompletion τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : D, familyTwoNorm (completionTrace τ) (x-completionMap τ a) < ε := by
  obtain ⟨u,rfl⟩ := (familyCauchyNullIdeal τ).quotientMap_surjective x
  obtain ⟨m,hm⟩ := ((isFamilyNull_iff (completionTrace τ) atTop _).mp
    (completion_distance_tendsto_zero τ u) ε hε).exists
  exact ⟨u.1 m,hm⟩

lemma familyTwoNorm_abs_sub_le {E : Type uE} {J : Type uJ} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (σ : J → TracialState E) [Nonempty J] (a b : E) :
    |familyTwoNorm σ a - familyTwoNorm σ b| ≤ familyTwoNorm σ (a-b) := by
  have h₁ := familyTwoNorm_sub_triangle σ a b 0
  have h₂ := familyTwoNorm_sub_triangle σ b a 0
  simp only [sub_zero] at h₁ h₂
  rw [familyTwoNorm_sub_swap σ b a] at h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma completion_uniformTwoNorm_tendsto (u : familyCauchyAlgebra τ) :
    Tendsto (fun n : ℕ => familyTwoNorm τ (u.1 n)) atTop
      (𝓝 (familyTwoNorm (completionTrace τ) ((familyCauchyNullIdeal τ).quotientMap u))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => ?_) (completion_distance_tendsto_zero τ u)
  rw [Real.norm_eq_abs, ← familyTwoNorm_completionMap τ (u.1 n), abs_sub_comm]
  exact familyTwoNorm_abs_sub_le (completionTrace τ) _ _

lemma completionQuotientMap_eq_zero (u : familyCauchyAlgebra τ) :
    (familyCauchyNullIdeal τ).quotientMap u = 0 ↔
      IsFamilyNull τ atTop (fun n => u.1 n) := by
  let J := familyCauchyNullIdeal τ
  change J.ideal.ringCon.mk' u = J.ideal.ringCon.mk' 0 ↔ _
  have he : J.ideal.ringCon.mk' u = J.ideal.ringCon.mk' 0 ↔ u ∈ J.ideal := Quotient.eq
  exact he.trans (familyNull_mem τ atTop u.1)

lemma completionTrace_detects_zero (x : UniformTracialCompletion τ)
    (hx : ∀ i, traceTwoNorm (completionTrace τ i) x = 0) : x = 0 := by
  obtain ⟨u,rfl⟩ := (familyCauchyNullIdeal τ).quotientMap_surjective x
  apply (completionQuotientMap_eq_zero τ u).mpr
  have he : familyTwoNorm (completionTrace τ) ((familyCauchyNullIdeal τ).quotientMap u) = 0 := by
    simp only [familyTwoNorm, hx, ciSup_const]
  change Tendsto _ _ (𝓝 0)
  simpa only [he] using completion_uniformTwoNorm_tendsto τ u

end CurrentMain

namespace Pureness.ClosedStarIdeal

open scoped ComplexStarModule

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (J : ClosedStarIdeal D)

lemma quotientMap_realPart (u : D) :
    J.quotientMap (realPart u : D) = (realPart (J.quotientMap u) : J.Quotient) := by
  have hs : J.quotientMap ((2 : ℝ)⁻¹ • (u+star u)) =
      (2 : ℝ)⁻¹ • J.quotientMap (u+star u) :=
    (J.quotientMap.toLinearMap.restrictScalars ℝ).map_smul _ _
  rw [realPart_apply_coe, realPart_apply_coe, hs, map_add, J.quotientMap_star]
  rfl

lemma exists_bounded_selfAdjoint_lift {p : J.Quotient} (hp : IsStarProjection p) :
    ∃ u : D, IsSelfAdjoint u ∧ ‖u‖ ≤ 2 ∧ J.quotientMap u = p := by
  obtain ⟨v,hv,hvn⟩ := J.quotient_norm_lt_rep p (show (0 : ℝ) < 1 by norm_num)
  refine ⟨realPart v,(realPart v).property,?_,?_⟩
  · exact (realPart.norm_le v).trans
      (hvn.le.trans (by linarith [hp.norm_le p]))
  · rw [J.quotientMap_realPart, hv]
    exact hp.isSelfAdjoint.coe_realPart

end Pureness.ClosedStarIdeal

namespace CurrentMain

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section UltrapowerConstants

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

lemma familyLimitTrace_constant_tendsto (s : X → I) (a : D) :
    Tendsto (fun n => (τ (s n)).functional a) (U : Filter X)
      (𝓝 ((familyLimitTrace τ U s).functional (familyUltrapowerMap τ U a))) :=
  familyLimitTrace_tendsto τ U s (boundedFamilyConstant a)

lemma familyTwoNorm_ultrapowerMap (a : D) :
    familyTwoNorm (familyLimitTrace τ U) (familyUltrapowerMap τ U a) = familyTwoNorm τ a := by
  change familyTwoNorm (familyLimitTrace τ U)
    ((familyNullIdeal τ (U : Filter X)).quotientMap (boundedFamilyConstant a)) = _
  rw [familyTwoNorm_limitTrace]
  exact tendsto_nhds_unique
    (bounded_ultrafilter_tendsto U (fun _ => familyTwoNorm τ a) ‖a‖ (fun _ => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (familyTwoNorm_nonneg τ a)] using
        familyTwoNorm_le_norm τ a)) tendsto_const_nhds

instance familyUltrapowerNontrivial : Nontrivial (FamilyUltrapower τ U) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  refine ⟨⟨1,0,?_⟩⟩
  intro h
  have he := congrArg (familyLimitTrace τ U (fun _ => i)).functional h
  rw [(familyLimitTrace τ U (fun _ => i)).normalized, map_zero] at he
  exact one_ne_zero he

lemma familyUltrapowerMap_injective
    (hτ : ∀ a : D, (∀ i, traceTwoNorm (τ i) a = 0) → a = 0) :
    Function.Injective (familyUltrapowerMap τ U) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  apply hτ a
  intro i
  have he : familyTwoNorm τ a = 0 := by
    rw [← familyTwoNorm_ultrapowerMap τ U a, ha, familyTwoNorm_zero]
  exact le_antisymm ((traceTwoNorm_le_family τ i a).trans he.le) (traceTwoNorm_nonneg _ _)

end UltrapowerConstants

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]

lemma completion_ultrapower_faithful {X : Type uX} (U : Ultrafilter X) :
    Function.Injective (familyUltrapowerMap (completionTrace τ) U) :=
  familyUltrapowerMap_injective (completionTrace τ) U (completionTrace_detects_zero τ)

end CurrentMain

end

end OAI
