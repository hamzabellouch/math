import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.InverseEndpointCoefficientEq
import OAI.MeasureTheory.FalconerCompletion.Graphs.PairMaskProduct
import OAI.MeasureTheory.FalconerCompletion.Shells.AngularCorrelation

namespace OAI

/-! Dyadic shells and prefix decompositions. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set MeasureTheory

lemma continuous_coefficient_measurable_squareND {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (c : α → ℂ) (hc : Measurable c) (hic : Integrable c ν)
    (F : α × ℝ → ℂ) (hF : Measurable F) {C : ℝ} (hb : ∀ p, ‖F p‖ ≤ C) :
    Measurable (fun r => ∫ ξ, c ξ*F (ξ,r) ∂ν) ∧
    Integrable (fun r => ‖∫ ξ, c ξ*F (ξ,r) ∂ν‖^2) μ := by
  have hm : Measurable (fun r => ∫ ξ, c ξ*F (ξ,r) ∂ν) :=
    ((hc.comp measurable_fst).mul hF).stronglyMeasurable.integral_prod_left'.measurable
  refine ⟨hm,?_⟩
  have hnorm (r : ℝ) : ‖∫ ξ, c ξ*F (ξ,r) ∂ν‖ ≤ (∫ ξ, ‖c ξ‖ ∂ν)*C := by
    calc
      _ ≤ ∫ ξ, ‖c ξ*F (ξ,r)‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ ξ, ‖c ξ‖*C ∂ν := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
          (hic.norm.mul_const C)
        filter_upwards with ξ
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb (ξ,r)) (norm_nonneg _)
      _ = _ := integral_mul_const _ _
  apply (integrable_const (((∫ ξ, ‖c ξ‖ ∂ν)*C)^2)).mono'
    (hm.norm.pow_const 2).aestronglyMeasurable
  filter_upwards with r
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hnorm r) 2

theorem full_HF_shell_mixtureND {ι α V : Type*} [MeasurableSpace α] [MeasurableSpace V]
    (n : ℕ) (ν : Measure α) [SFinite ν] (μ : Measure V) [IsFiniteMeasure μ]
    (a v : ℝ) (L : List ι) (c : ι → α → ℂ) (m : ι → ℝ → ℂ)
    (ψ : V → ℂ) (U W : ι → α × (ℝ × V) → ℂ)
    (H : ℝ → ℂ) (A C D : ι → ℝ) {P B E : ℝ}
    (hA : ∀ i ∈ L, 0 ≤ A i) (hc : ∀ i ∈ L, Measurable (c i))
    (hic : ∀ i ∈ L, Integrable (c i) ν) (hm : ∀ i ∈ L, Measurable (m i))
    (hbM : ∀ i ∈ L, ∀ r ∈ Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v), ‖m i r‖ ≤ A i)
    (hψ : Measurable ψ) (hU : ∀ i ∈ L, Measurable (U i))
    (hW : ∀ i ∈ L, Measurable (W i)) (hP : 0 ≤ P) (hC : ∀ i ∈ L, 0 ≤ C i)
    (hbψ : ∀ w, ‖ψ w‖ ≤ P) (hbU : ∀ i ∈ L, ∀ ξ r w, ‖U i (ξ,(r,w))‖ ≤ C i)
    (hbW : ∀ i ∈ L, ∀ ξ r w, ‖W i (ξ,(r,w))‖ ≤ D i) {Ψ : ℝ → ℝ}
    (hΨ : Integrable (fun r => Ψ (r/(2:ℝ)^v))) (hΨpos : ∀ r, 0 ≤ Ψ r)
    (hone : ∀ r ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ r)
    (hB : ∀ i ∈ L, ∀ ξ, sourceAngularHFND (n+1) μ a v Ψ ψ
      (fun z => U i (ξ,z)) (fun z => W i (ξ,z)) ≤ B)
    (hH : AEStronglyMeasurable H (volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))))
    (hE : ∀ r ∈ Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v),
      ‖H r-(((2:ℝ)^((n:ℝ)*(v-a)/2):ℝ):ℂ)*(L.map (fun i => m i r*
        ∫ ξ, c i ξ*sourceAngularCorrelationND μ ψ
          (fun z => U i (ξ,z)) (fun z => W i (ξ,z)) r ∂ν)).sum‖ ≤ E) :
    Integrable (fun r => ‖H r‖^2) (volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))) ∧
    (2:ℝ)^(-a)*(∫ r in Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v), ‖H r‖^2) ≤
      2*(L.map (fun i => A i*(∫ ξ, ‖c i ξ‖ ∂ν))).sum^2*B + 3*(2:ℝ)^(v-a)*E^2 := by
  let F : ι → ℝ → ℂ := fun i r => ∫ ξ, c i ξ*sourceAngularCorrelationND μ ψ
    (fun z => U i (ξ,z)) (fun z => W i (ξ,z)) r ∂ν
  let μshell := volume.restrict (Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v))
  have hFm (i : ι) (hi : i ∈ L) : Measurable (F i) ∧ Integrable (fun r => ‖F i r‖^2) μshell := by
    apply continuous_coefficient_measurable_squareND ν μshell (c i) (hc i hi) (hic i hi)
      (fun p => sourceAngularCorrelationND μ ψ (fun z => U i (p.1,z)) (fun z => W i (p.1,z)) p.2)
      (sourceAngularCorrelationND_parameter_measurable μ hψ (hU i hi) (hW i hi))
      (C := P*C i*D i*μ.real univ)
    intro p
    exact sourceAngularCorrelationND_bound μ ψ _ _ hP (hC i hi) hbψ
      (hbU i hi p.1) (hbW i hi p.1) p.2
  have hmix (i : ι) (hi : i ∈ L) := shell_square_multiplierND μshell
    ((hm i hi).aestronglyMeasurable.mul (hFm i hi).1.aestronglyMeasurable) (hFm i hi).2
    (show ∀ᵐ r ∂μshell, ‖m i r‖ ≤ A i from by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact hbM i hi r hr)
  apply normalized_list_shell_remainderND n a v L (fun i r => m i r*F i r)
    (fun i => A i*(∫ ξ, ‖c i ξ‖ ∂ν)) H
  · intro i hi
    exact mul_nonneg (hA i hi) (integral_nonneg (fun _ => norm_nonneg _))
  · intro i hi
    exact (hmix i hi).1
  · intro i hi
    exact ((hm i hi).mul (hFm i hi).1).aestronglyMeasurable
  · intro i hi
    have henergy := continuous_HF_shell_boundND (n+1) ν μ a v (c i) (hc i hi)
      (hic i hi) hψ (hU i hi) (hW i hi) hP (hC i hi) hbψ
      (hbU i hi) (hbW i hi) hΨ hΨpos hone (hB i hi)
    exact (hmix i hi).2.trans ((mul_le_mul_of_nonneg_left henergy (sq_nonneg (A i))).trans_eq (by ring))
  · exact hH
  · exact hE

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set

noncomputable def shellRadialMultiplierND (n j : ℕ) (v r : ℝ) : ℂ :=
  (((r/(2:ℝ)^v)^((n:ℝ)/2):ℝ):ℂ)*((r/(2:ℝ)^v:ℝ):ℂ)^(-(j:ℤ))

lemma positive_shell_ratioND {v r : ℝ}
    (hr : r ∈ Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v)) :
    (1/2:ℝ) ≤ r/(2:ℝ)^v ∧ r/(2:ℝ)^v ≤ 2 := by
  have hR : 0 < (2:ℝ)^v := Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · apply (le_div_iff₀ hR).mpr
    linarith [hr.1]
  · exact (div_le_iff₀ hR).mpr hr.2

lemma shellRadialMultiplierND_bound (n j : ℕ) {v r : ℝ}
    (hr : r ∈ Icc ((2:ℝ)^v/2) (2*(2:ℝ)^v)) :
    ‖shellRadialMultiplierND n j v r‖ ≤ (2:ℝ)^((n:ℝ)/2)*(2:ℝ)^j := by
  obtain ⟨hl,hu⟩ := positive_shell_ratioND hr
  have hs : 0 < r/(2:ℝ)^v := by linarith
  have hsn : 0 ≤ (r/(2:ℝ)^v)^((n:ℝ)/2) := Real.rpow_nonneg hs.le _
  have hpow : (r/(2:ℝ)^v)^((n:ℝ)/2) ≤ (2:ℝ)^((n:ℝ)/2) :=
    Real.rpow_le_rpow hs.le hu (by positivity)
  have hi : (r/(2:ℝ)^v)⁻¹ ≤ 2 := (inv_le_comm₀ hs (by norm_num : (0:ℝ)<2)).mpr (by simpa only [one_div] using hl)
  simp only [shellRadialMultiplierND,norm_mul,zpow_neg,zpow_natCast,norm_inv,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs,abs_of_nonneg hsn,← inv_pow]
  exact mul_le_mul hpow (pow_le_pow_left₀ (inv_nonneg.mpr hs.le) hi j)
    (by positivity) (by positivity)

lemma shellRadialMultiplierND_measurable (n j : ℕ) (v : ℝ) :
    Measurable (shellRadialMultiplierND n j v) := by
  unfold shellRadialMultiplierND
  fun_prop

lemma positive_inverse_coefficient_splitND {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (e : ℝ) (j : ℕ) :
    (((t*u)^e:ℝ):ℂ)*((t*u:ℝ):ℂ)^(-(j:ℤ)) =
      ((t^e:ℝ):ℂ)*(((u^e:ℝ):ℂ)*(u:ℂ)^(-(j:ℤ)))*((t⁻¹:ℝ):ℂ)^j := by
  rw [Real.mul_rpow ht.le hu.le]
  simp only [Complex.ofReal_mul,zpow_neg,zpow_natCast,Complex.ofReal_inv,inv_pow]
  ring

lemma dyadic_inverse_coefficient_splitND (n j : ℕ) {a v r : ℝ} (hr : 0 < r) :
    (((r/(2:ℝ)^a)^((n:ℝ)/2):ℝ):ℂ)*((r/(2:ℝ)^a:ℝ):ℂ)^(-(j:ℤ)) =
      (((2:ℝ)^((n:ℝ)*(v-a)/2):ℝ):ℂ)*
        (shellRadialMultiplierND n j v r * (((2:ℝ)^(-(v-a)):ℝ):ℂ)^j) := by
  have hp : 0 < (2:ℝ)^v := Real.rpow_pos_of_pos (by norm_num) _
  have hq : 0 < (2:ℝ)^(v-a) := Real.rpow_pos_of_pos (by norm_num) _
  have he : r/(2:ℝ)^a = (2:ℝ)^(v-a)*(r/(2:ℝ)^v) := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ)<2)]
    field_simp
  rw [he,positive_inverse_coefficient_splitND hq (div_pos hr hp)]
  rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  have hring : (v-a)*((n:ℝ)/2) = (n:ℝ)*(v-a)/2 := by ring
  rw [hring,← Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
  simp only [shellRadialMultiplierND]
  ring

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open Set MeasureTheory
open scoped ComplexConjugate

lemma sum_range_flatMapND {Q A : Type*} [AddCommMonoid A]
    (m : ℕ) (L : ℕ → List Q) (F : ℕ → Q → A) :
    ((((List.range m).flatMap (fun j => (L j).map (fun x => (j,x)))).map
      (fun p => F p.1 p.2)).sum) = ∑ j ∈ Finset.range m, ((L j).map (F j)).sum := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [List.range_succ,List.flatMap_append,List.flatMap_singleton,
      List.map_append,List.sum_append,Finset.sum_range_succ,List.map_map,Function.comp_def]
    rw [ih]

variable {n : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
local notation "V" => EuclideanSpace ℝ (Fin (n+1))
local notation "Assignment" => ℂ × ((ι ⊕ κ) → List (SphereAmbientND n →L[ℝ] SphereAmbientND n))

noncomputable def inverseTermListND (J : ℕ) (S : Finset ι) (T : Finset κ) : List (ℕ × Assignment) :=
  (List.range (J+1)).flatMap (fun j => (inverseAngularTermsND j (S.disjSum T)).map (fun a => (j,a)))

lemma sum_inverseTermListND {A : Type*} [AddCommMonoid A]
    (J : ℕ) (S : Finset ι) (T : Finset κ) (F : ℕ × Assignment → A) :
    ((inverseTermListND J S T).map F).sum =
      ∑ j ∈ Finset.range (J+1), ((inverseAngularTermsND j (S.disjSum T)).map (fun p => F (j,p))).sum := by
  simpa only [inverseTermListND, Prod.mk.eta] using sum_range_flatMapND (J+1) (fun j => inverseAngularTermsND j (S.disjSum T)) (fun j p => F (j,p))

lemma mem_inverseTermListND (J : ℕ) (S : Finset ι) (T : Finset κ) (p : ℕ × Assignment) :
    p ∈ inverseTermListND J S T ↔ p.1 ≤ J ∧ p.2 ∈ inverseAngularTermsND p.1 (S.disjSum T) := by
  rcases p with ⟨j,a⟩
  simp only [inverseTermListND,List.mem_flatMap,List.mem_range,List.mem_map,Prod.mk.injEq]
  constructor
  · rintro ⟨k,hk,b,hb,hbj⟩
    rcases hbj with ⟨rfl,rfl⟩
    exact ⟨Nat.le_of_lt_succ hk,hb⟩
  · rintro ⟨hj,ha⟩
    exact ⟨j,Nat.lt_succ_of_le hj,a,ha,rfl,rfl⟩

noncomputable def spatialEndpointTransformND (scale : ℝ) (ρ : Measure V) (X : Set V) (M : ℝ)
    (b : V → V → ℂ) (p : V × (ℝ × V)) : ℂ :=
  sourceAngularTransformND ρ X M
    (fun x w => SpatialFourierND.spatialFourierPhase (n+1) scale p.1 x*b x w) p.2.1 p.2.2

omit [DecidableEq ι] [DecidableEq κ] in
lemma spatialEndpointTransformND_measurable (scale : ℝ) (ρ : Measure V) [SFinite ρ]
    (X : Set V) (M : ℝ) {b : V → V → ℂ} (hb : Measurable (Function.uncurry b)) :
    Measurable (spatialEndpointTransformND scale ρ X M b) := by
  have hm : Measurable (fun z : (V × (ℝ × V)) × V =>
      spherePlaneWaveND z.1.2.1 z.2 z.1.2.2 *
        (SpatialFourierND.spatialFourierPhase (n+1) scale z.1.1 z.2*b z.2 z.1.2.2)) := by
    apply Measurable.mul (by unfold spherePlaneWaveND; fun_prop)
    exact ((SpatialFourierND.spatialFourierPhase_continuous (n+1) scale).measurable.comp
      (measurable_fst.fst.prodMk measurable_snd)).mul
        (hb.comp (measurable_snd.prodMk measurable_fst.snd.snd))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := ρ.restrict X)).measurable.const_smul (M⁻¹)

omit [DecidableEq ι] [DecidableEq κ] in
lemma spatialEndpointTransformND_bound (scale : ℝ) (ρ : Measure V) [IsFiniteMeasure ρ]
    (X : Set V) (M : ℝ) (b : V → V → ℂ) {B : ℝ}
    (hb : ∀ x w, ‖b x w‖ ≤ B) (p : V × (ℝ × V)) :
    ‖spatialEndpointTransformND scale ρ X M b p‖ ≤ |M⁻¹| *(B*(ρ.restrict X).real univ) := by
  unfold spatialEndpointTransformND sourceAngularTransformND
  rw [norm_smul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  apply norm_integral_le_of_norm_le_const
  filter_upwards with x
  simpa only [norm_mul,spherePlaneWaveND_norm,SpatialFourierND.spatialFourierPhase_norm,one_mul]
    using hb x p.2.2

lemma all_mask_shell_factorizationND (J : ℕ) (S : Finset ι) (T : Finset κ)
    (f : V → ι → SmoothFunctionND V) (g : V → κ → SmoothFunctionND V)
    (F G : V → ℂ) (D : ι → ℝ) (E : κ → ℝ)
    (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K)
    (ρ ν : Measure V) (X Y : Set V) (M N a v r : ℝ) (hr : 0 < r) (ψ : V → ℂ) :
    (∑ j ∈ Finset.range (J+1),
      ((((r/(2:ℝ)^a)^((n:ℝ)/2):ℝ):ℂ)*((r/(2:ℝ)^a:ℝ):ℂ)^(-(j:ℤ))) *
        inverseEndpointMixtureND j S T f g F G D E δ K hδ hK ((2:ℝ)^a)⁻¹ ρ ν X Y M N r ψ) =
    (((2:ℝ)^((n:ℝ)*(v-a)/2):ℝ):ℂ)*
      ((inverseTermListND J S T).map (fun p => shellRadialMultiplierND n p.1 v r*
        ∫ ξ, paidSpatialCoefficientND p.1 S T D E ((2:ℝ)^(-(v-a))) δ K hδ hK p.2 ξ*
          sourceAngularCorrelationND (canonicalSphereMeasureND V) ψ
            (fun z => spatialEndpointTransformND ((2:ℝ)^a)⁻¹ ρ X M
              (inverseLeftEndpointND S D f F p.2) (ξ,z))
            (fun z => spatialEndpointTransformND ((2:ℝ)^a)⁻¹ ν Y N
              (inverseRightEndpointND T E g G p.2) (ξ,z)) r)).sum := by
  rw [sum_inverseTermListND,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dyadic_inverse_coefficient_splitND n j hr]
  unfold inverseEndpointMixtureND
  rw [← List.sum_map_mul_left,← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [paidSpatialCoefficientND,sourceAngularCorrelationND,spatialEndpointTransformND,
    mul_assoc,integral_const_mul]
  ring

lemma inverseTermListND_paid_cost (J : ℕ) (S : Finset ι) (T : Finset κ)
    (D : ι → ℝ) (E : κ → ℝ) {M t : ℝ}
    (hM : 1 ≤ M) (ht : 0 ≤ t) (hpaid : t*M^2 ≤ 1)
    (hD₀ : ∀ i ∈ S, 0 ≤ D i) (hE₀ : ∀ k ∈ T, 0 ≤ E k)
    (hD : ∀ i ∈ S, D i ≤ M) (hE : ∀ k ∈ T, E k ≤ M)
    (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K) :
    (((inverseTermListND (n := n) J S T).map (fun p =>
      ((2:ℝ)^((n:ℝ)/2)*(2:ℝ)^p.1)*
        ∫ ξ, ‖paidSpatialCoefficientND p.1 S T D E t δ K hδ hK p.2 ξ‖)).sum) ≤
      fullInverseCoefficientCostND n J δ K hδ hK*
        (max 1 ((S.card+T.card:ℕ):ℝ))^(2*J) := by
  rw [sum_inverseTermListND]
  exact full_paidSpatialCoefficientND_cost J S T D E hM ht hpaid hD₀ hE₀ hD hE δ K hδ hK

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
