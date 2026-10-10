import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.BracketHyperplanes01
import OAI.Combinatorics.SumProduct.Alignment.PairTail05
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
open MeasureTheory Filter
open scoped ENNReal
namespace FourierObstruction
open scoped BigOperators
open Set Submodule
noncomputable section

 

theorem finite_tests_of_dense_span {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (v : ι → E)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (K : Set E) (hK : IsCompact K) (δ B : ℝ) (hδ : 0 < δ) (hB : 0 < B) :
    ∃ S : Finset ι, ∃ η : ℝ, 0 < η ∧
      ∀ L : E →ₗ[ℂ] ℂ, (∀ f, ‖L f‖ ≤ B * ‖f‖) →
        (∃ f ∈ K, δ ≤ ‖L f‖) → ∃ i ∈ S, η ≤ ‖L (v i)‖ := by
  classical
  let ε := δ / (4 * B)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have happ (f : E) : ∃ c : ι →₀ ℂ, dist f (c.sum fun i a => a • v i) < ε := by
    have hf : f ∈ closure (Submodule.span ℂ (Set.range v) : Set E) := by
      rw [← Submodule.topologicalClosure_coe, hv]
      trivial
    obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf ε hε
    obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hg
    exact ⟨c, hfg⟩
  choose c hc using happ
  let P : E → E := fun f => (c f).sum fun i a => a • v i
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun f => Metric.ball (P f) ε)
    (fun _ => Metric.isOpen_ball) (by
      intro f _
      exact Set.mem_iUnion.mpr ⟨f, hc f⟩)
  let H := 1 + ∑ f ∈ t, ∑ i ∈ (c f).support, ‖c f i‖
  have hH : 0 < H := by
    dsimp [H]
    positivity
  let η := δ / (4 * H)
  have hη : 0 < η := by dsimp [η]; positivity
  refine ⟨t.biUnion (fun f => (c f).support), η, hη, ?_⟩
  intro L hL ⟨f, hf, hlarge⟩
  obtain ⟨g, hg, hfg⟩ := Set.mem_iUnion₂.mp (ht hf)
  have hfg' : dist f (P g) < ε := hfg
  by_contra hno
  push Not at hno
  have hPg : ‖L (P g)‖ ≤ H * η := by
    calc
      _ = ‖∑ i ∈ (c g).support, (c g i) • L (v i)‖ := by
        simp [P, Finsupp.sum, map_sum]
      _ ≤ ∑ i ∈ (c g).support, ‖c g i‖ * ‖L (v i)‖ := by
        simpa only [norm_smul] using norm_sum_le (c g).support (fun i => c g i • L (v i))
      _ ≤ ∑ i ∈ (c g).support, ‖c g i‖ * η := by
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        exact (hno i (Finset.mem_biUnion.mpr ⟨g, hg, hi⟩)).le
      _ = (∑ i ∈ (c g).support, ‖c g i‖) * η := by rw [Finset.sum_mul]
      _ ≤ H * η := by
        apply mul_le_mul_of_nonneg_right _ hη.le
        have hsum := Finset.single_le_sum (f := fun x => ∑ i ∈ (c x).support, ‖c x i‖) (fun x (_ : x ∈ t) =>
          Finset.sum_nonneg (fun i _ => norm_nonneg (c x i))) hg
        dsimp [H]
        linarith only [hsum]
  have hdist : ‖L (f - P g)‖ < B * ε := by
    calc
      _ ≤ B * ‖f - P g‖ := hL _
      _ < B * ε := mul_lt_mul_of_pos_left (by simpa only [dist_eq_norm] using hfg') hB
  have hsum := norm_add_le (L (f - P g)) (L (P g))
  rw [← map_add, sub_add_cancel] at hsum
  have he₁ : B * ε = δ / 4 := by dsimp [ε]; field_simp
  have he₂ : H * η = δ / 4 := by dsimp [η]; field_simp
  rw [he₁] at hdist
  rw [he₂] at hPg
  linarith

 

theorem compact_superset_unit_lipschitz (X : Type*) [MetricSpace X] [CompactSpace X] :
    ∃ K : Set C(X, ℂ), IsCompact K ∧
      ∀ f : C(X, ℂ), LipschitzWith 1 f → ‖f‖ ≤ 1 → f ∈ K := by
  let e := ContinuousMap.isometryEquivBoundedOfCompact X ℂ
  let A : Set (BoundedContinuousFunction X ℂ) := {f | LipschitzWith 1 f ∧ ‖f‖ ≤ 1}
  have heqc : Equicontinuous ((↑) : A → X → ℂ) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hxy f
    have h := f.property.1.dist_le_mul x y
    simp only [NNReal.coe_one, one_mul, dist_comm x y] at h
    exact h.trans_lt hxy
  have hc : IsCompact (closure A) := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : ℂ) 1) (isCompact_closedBall _ _) A (by
      intro f x hf
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact (f.norm_coe_le_norm x).trans hf.2) heqc
  refine ⟨e.symm '' closure A, hc.image e.symm.continuous, ?_⟩
  intro f hl hn
  refine ⟨e f, subset_closure ⟨hl, ?_⟩, e.symm_apply_apply f⟩
  simpa only [e, ContinuousMap.isometryEquivBoundedOfCompact_apply,
    BoundedContinuousFunction.norm_mkOfCompact] using hn

open MeasureTheory

section Probability
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

 

def discrepancy (N : ℕ) (x : ℕ → X) : C(X, ℂ) →ₗ[ℂ] ℂ where
  toFun f := (𝔼 n ∈ Finset.range N, f (x n)) - ∫ t, f t ∂μ
  map_add' f g := by
    change (𝔼 n ∈ Finset.range N, (f (x n) + g (x n))) -
      ∫ t, f t + g t ∂μ = _
    rw [Finset.expect_add_distrib, integral_add
      (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f))
      (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g))]
    ring
  map_smul' z f := by
    change (𝔼 n ∈ Finset.range N, z • f (x n)) - ∫ t, z • f t ∂μ = _
    rw [← Finset.smul_expect, integral_smul]
    simp only [RingHom.id_apply, smul_sub]

theorem discrepancy_bound (N : ℕ) (hN : 0 < N) (x : ℕ → X) (f : C(X, ℂ)) :
    ‖discrepancy μ N x f‖ ≤ 2 * ‖f‖ := by
  have hm : ‖𝔼 n ∈ Finset.range N, f (x n)‖ ≤ ‖f‖ :=
    (RCLike.norm_expect_le (K := ℂ)).trans (Finset.expect_le
      (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)) (fun n _ => f.norm_coe_le_norm _))
  have hi : ‖∫ t, f t ∂μ‖ ≤ ‖f‖ := by
    simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const (μ := μ)
      (Filter.Eventually.of_forall (f.norm_coe_le_norm))
  exact (norm_sub_le _ _).trans (by linarith only [hm, hi])

theorem discrepancy_const (N : ℕ) (hN : 0 < N) (x : ℕ → X) (z : ℂ) :
    discrepancy μ N x (ContinuousMap.const _ z) = 0 := by
  simp only [discrepancy, LinearMap.coe_mk, AddHom.coe_mk, ContinuousMap.const_apply,
    Finset.expect_const (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)),
    integral_const, probReal_univ, one_smul, sub_self]
end Probability

section Torus
variable (d : Type*) [Fintype d]
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

 
def torusHaar : Measure (UnitAddTorus d) := volume

instance torusHaar_probability : IsProbabilityMeasure (torusHaar d) :=
  inferInstanceAs (IsProbabilityMeasure (volume : Measure (UnitAddTorus d)))

theorem integral_character (k : d → ℤ) :
    ∫ t, UnitAddTorus.mFourier k t ∂torusHaar d = if k = 0 then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := d)) 0 k
  simpa only [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp,
    UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, map_one, mul_one, eq_comm,
    torusHaar] using h

 

theorem torus_character_obstruction (δ : ℝ) (hδ : 0 < δ) :
    ∃ S : Finset (d → ℤ), ∃ η : ℝ, 0 < η ∧
      ∀ N : ℕ, 0 < N → ∀ x : ℕ → UnitAddTorus d,
        (∃ f : C(UnitAddTorus d, ℂ), LipschitzWith 1 f ∧ ‖f‖ ≤ 1 ∧
          δ ≤ ‖(𝔼 n ∈ Finset.range N, f (x n)) - ∫ t, f t ∂torusHaar d‖) →
        ∃ k ∈ S, k ≠ 0 ∧ η ≤ ‖𝔼 n ∈ Finset.range N, UnitAddTorus.mFourier k (x n)‖ := by
  obtain ⟨K, hK, hmem⟩ := compact_superset_unit_lipschitz (UnitAddTorus d)
  obtain ⟨S, η, hη, htest⟩ := finite_tests_of_dense_span UnitAddTorus.mFourier
    UnitAddTorus.span_mFourier_closure_eq_top K hK δ 2 hδ (by norm_num)
  refine ⟨S, η, hη, ?_⟩
  intro N hN x ⟨f, hf, hfn, hlarge⟩
  obtain ⟨k, hk, hcorr⟩ := htest (discrepancy (torusHaar d) N x)
    (discrepancy_bound (torusHaar d) N hN x) ⟨f, hmem f hf hfn, hlarge⟩
  have hk₀ : k ≠ 0 := by
    intro hzero
    subst k
    rw [UnitAddTorus.mFourier_zero] at hcorr
    have he : (1 : C(UnitAddTorus d, ℂ)) = ContinuousMap.const _ 1 := rfl
    rw [he, discrepancy_const (torusHaar d) N hN x 1, norm_zero] at hcorr
    linarith
  refine ⟨k, hk, hk₀, ?_⟩
  have hi := integral_character d k
  rw [ite_eq_right hk₀] at hi
  simpa only [discrepancy, LinearMap.coe_mk, AddHom.coe_mk, hi, sub_zero] using hcorr

end Torus
end
end FourierObstruction

namespace BracketHyperplanes
open MeasureTheory FourierObstruction
open scoped BigOperators
noncomputable section
variable {d : ℕ}

def complexify (f : C(UnitAddTorus (Fin d),ℝ)) : C(UnitAddTorus (Fin d),ℂ) :=
  ⟨fun x => (f x : ℂ), by fun_prop⟩

lemma torusHaar_eq_volume : torusHaar (Fin d) = volume := by
  simp [torusHaar,volume,AddCircle.haarAddCircle]

lemma re_discrepancy (f : C(UnitAddTorus (Fin d),ℝ)) (N : ℕ)
    (x : ℕ → UnitAddTorus (Fin d)) :
    (discrepancy (torusHaar (Fin d)) N x (complexify f)).re =
      (𝔼 n ∈ Finset.range N, f (x n)) - ∫ t, f t := by
  simp only [discrepancy,LinearMap.coe_mk,AddHom.coe_mk,complexify,
    ContinuousMap.coe_mk,Complex.sub_re,
    torusHaar_eq_volume,Finset.expect_eq_sum_div_card]
  simp [integral_complex_ofReal]

 

theorem finite_real_character_obstruction (T : Finset C(UnitAddTorus (Fin d),ℝ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ S : Finset (Fin d → ℤ), ∃ η : ℝ, 0 < η ∧
      ∀ N : ℕ, 0 < N → ∀ x : ℕ → UnitAddTorus (Fin d),
        (∃ f ∈ T, δ ≤ (𝔼 n ∈ Finset.range N, f (x n)) - ∫ t, f t) →
        ∃ k ∈ S, k ≠ 0 ∧ η ≤ ‖𝔼 n ∈ Finset.range N, UnitAddTorus.mFourier k (x n)‖ := by
  classical
  let K : Set C(UnitAddTorus (Fin d),ℂ) := (T.image complexify : Finset _)
  have hK : IsCompact K := (T.image complexify).finite_toSet.isCompact
  obtain ⟨S,η,hη,htest⟩ := finite_tests_of_dense_span UnitAddTorus.mFourier
    UnitAddTorus.span_mFourier_closure_eq_top K hK δ 2 hδ (by norm_num)
  refine ⟨S,η,hη,?_⟩
  intro N hN x ⟨f,hf,hlarge⟩
  have hlarge' : δ ≤ ‖discrepancy (torusHaar (Fin d)) N x (complexify f)‖ := by
    rw [← re_discrepancy] at hlarge
    exact hlarge.trans (Complex.re_le_norm _)
  obtain ⟨k,hk,hcorr⟩ := htest (discrepancy (torusHaar (Fin d)) N x)
    (discrepancy_bound (torusHaar (Fin d)) N hN x)
    ⟨complexify f,Finset.mem_image.mpr ⟨f,hf,rfl⟩,hlarge'⟩
  have hk₀ : k ≠ 0 := by
    intro he
    subst k
    rw [UnitAddTorus.mFourier_zero] at hcorr
    change η ≤ ‖discrepancy (torusHaar (Fin d)) N x (ContinuousMap.const _ 1)‖ at hcorr
    rw [discrepancy_const _ _ hN,norm_zero] at hcorr
    linarith
  refine ⟨k,hk,hk₀,?_⟩
  have hi := integral_character (Fin d) k
  rw [ite_eq_right hk₀] at hi
  simpa only [discrepancy,LinearMap.coe_mk,AddHom.coe_mk,hi,sub_zero] using hcorr

lemma half_dense_mean {N : ℕ} (hN : 0 < N) (S : Finset ℕ)
    (hS : S ⊆ Finset.range N) (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n)
    (hgood : ∀ n ∈ S, (1:ℝ)/2 ≤ g n) (δ : ℝ)
    (hdens : δ*N ≤ S.card) : δ/2 ≤ (𝔼 n ∈ Finset.range N, g n) := by
  have h₁ : (S.card:ℝ)/2 ≤ ∑ n ∈ S, g n := by
    calc
      _ = ∑ _ ∈ S, (1:ℝ)/2 := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum hgood
  have h₂ : (∑ n ∈ S, g n) ≤ ∑ n ∈ Finset.range N, g n :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (fun n _ _ => hg n)
  rw [Finset.expect_eq_sum_div_card,Finset.card_range]
  apply (le_div_iff₀ (Nat.cast_pos.mpr hN)).mpr
  linarith

 

theorem compact_bracket_fourier {P : Type*} [TopologicalSpace P]
    [CompactSpace P] [T2Space P]
    (a : C(P, Fin d → ℝ)) (ha : ∀ p, a p ≠ 0) (b : C(P, ℝ))
    (K : Set (Fin d → ℝ)) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ frequencies : Finset (Fin d → ℤ), ∃ ε η : ℝ, 0 < ε ∧ 0 < η ∧
      ∀ N : ℕ, 0 < N → ∀ p : P, ∀ x : ℕ → Fin d → ℝ,
        (∀ n, x n ∈ K) → ∀ S : Finset ℕ, S ⊆ Finset.range N → δ*N ≤ S.card →
        (∀ n ∈ S, ‖((∑ i, a p i*x n i-b p : ℝ) : UnitAddCircle)‖ ≤ ε) →
        ∃ k ∈ frequencies, k ≠ 0 ∧
          η ≤ ‖𝔼 n ∈ Finset.range N, UnitAddTorus.mFourier k (torusMap (x n))‖ := by
  obtain ⟨T,ε,hε,hT,hcover⟩ := compact_bracket_tests a ha b K hK (δ/4) (by positivity)
  obtain ⟨F,η,hη,hF⟩ := finite_real_character_obstruction T (δ/4) (by positivity)
  refine ⟨F,ε,η,hε,hη,?_⟩
  intro N hN p x hx S hS hdens hsmall
  obtain ⟨f,hf,hfc⟩ := hcover p
  apply hF N hN (fun n => torusMap (x n))
  have hmean := half_dense_mean hN S hS (fun n => f (torusMap (x n)))
    (fun n => (hT f hf).1 _ |>.1)
    (fun n hn => (hfc _ (hx n) (hsmall n hn)).le) δ hdens
  refine ⟨f,hf,?_⟩
  have hi := (hT f hf).2
  linarith

end
end BracketHyperplanes

end
end
end
end

end OAI
