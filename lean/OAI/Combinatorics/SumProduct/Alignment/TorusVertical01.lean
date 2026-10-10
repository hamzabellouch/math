import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.FourierObstruction01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
open _root_.Polynomial _root_.OAI.Polynomial
end
end
 

 
section

 

namespace TorusVerticalFourier
open MeasureTheory AddCircle UnitAddTorus Set
noncomputable section

variable {d : Type*} [Fintype d]
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

 

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

variable {X : Type*} [MetricSpace X] [CompactSpace X]
    [AddAction (UnitAddTorus d) X] [ContinuousVAdd (UnitAddTorus d) X]

lemma character_add (k : d → ℤ) (s t : UnitAddTorus d) :
    mFourier k (s+t) = mFourier k s * mFourier k t := by
  simp only [mFourier,ContinuousMap.coe_mk,Pi.add_apply,fourier_apply,smul_add,toCircle_add,Circle.coe_mul,
    Finset.prod_mul_distrib]

lemma character_cancel (k : d → ℤ) (s : (UnitAddTorus d)) :
    mFourier k s * mFourier (-k) s = 1 := by
  rw [← mFourier_add,add_neg_cancel,mFourier_zero,ContinuousMap.one_apply]

 
def coeff (F : C(X, ℂ)) (k : d → ℤ) : C(X, ℂ) where
  toFun x := ∫ t : (UnitAddTorus d), mFourier (-k) t * F (t +ᵥ x) ∂volume
  continuous_toFun := by
    have h := continuous_parametric_integral_of_continuous
      (μ := (volume : Measure (UnitAddTorus d)))
      (f := fun x : X => fun t : (UnitAddTorus d) => mFourier (-k) t * F (t +ᵥ x))
      (by fun_prop) (s := Set.univ) isCompact_univ
    simpa only [Measure.restrict_univ] using h

@[simp] lemma coeff_apply (F : C(X, ℂ)) (k : d → ℤ) (x : X) :
    coeff F k x = ∫ t : (UnitAddTorus d), mFourier (-k) t * F (t +ᵥ x) ∂volume := rfl

 

lemma coeff_vadd (F : C(X, ℂ)) (k : d → ℤ) (s : (UnitAddTorus d)) (x : X) :
    coeff F k (s +ᵥ x) = mFourier k s * coeff F k x := by
  rw [coeff_apply,coeff_apply,← integral_const_mul]
  rw [← integral_add_right_eq_self
    (fun t : (UnitAddTorus d) => mFourier k s * (mFourier (-k) t * F (t +ᵥ x))) s]
  congr 1
  ext t
  rw [character_add,add_vadd]
  have hc := character_cancel k s
  calc
    mFourier (-k) t * F (t +ᵥ s +ᵥ x) =
      (mFourier k s * mFourier (-k) s) * (mFourier (-k) t * F (t +ᵥ s +ᵥ x)) := by rw [hc,one_mul]
    _ = _ := by ring

 

lemma torus_coeff_unique (F : C((UnitAddTorus d), ℂ))
    (hF : ∀ k : d → ℤ, mFourierCoeff F k = 0) : F = 0 := by
  have hc : mFourierCoeff F = (fun _ : d → ℤ => (0 : ℂ)) := funext hF
  have hsum : Summable (mFourierCoeff F) := by rw [hc]; exact summable_zero
  have h := hasSum_mFourier_series_of_summable hsum
  have hz : (fun i : d → ℤ => mFourierCoeff F i • (mFourier i : C((UnitAddTorus d), ℂ))) =
      (fun _ : d → ℤ => (0 : C((UnitAddTorus d), ℂ))) := by
    funext i
    rw [hF i]
    ext x
    exact zero_mul _
  rw [hz] at h
  exact h.unique hasSum_zero

 

lemma coeff_unique_at (F : C(X, ℂ)) (x : X)
    (hF : ∀ k : d → ℤ, coeff F k x = 0) : F x = 0 := by
  let H : C((UnitAddTorus d), ℂ) := ⟨fun t => F (t +ᵥ x), by fun_prop⟩
  have hH : H = 0 := torus_coeff_unique H (by
    intro k
    exact hF k)
  have h := congrArg (fun f : C((UnitAddTorus d), ℂ) => f 0) hH
  simpa only [H,ContinuousMap.coe_mk,zero_vadd,ContinuousMap.zero_apply] using h

 
def HasWeight (k : d → ℤ) (F : C(X, ℂ)) : Prop :=
  ∀ (s : (UnitAddTorus d)) (x : X), F (s +ᵥ x) = mFourier k s * F x

lemma coeff_hasWeight (F : C(X, ℂ)) (k : d → ℤ) : HasWeight k (coeff F k) := coeff_vadd F k

omit [CompactSpace X] [ContinuousVAdd (UnitAddTorus d) X] in
lemma hasWeight_one : HasWeight (d := d) (X := X) 0 1 := by
  intro s x
  simp only [ContinuousMap.one_apply,mFourier_zero,ContinuousMap.one_apply,mul_one]

omit [CompactSpace X] [ContinuousVAdd (UnitAddTorus d) X] in
lemma HasWeight.mul {F G : C(X, ℂ)} {k l : d → ℤ}
    (hF : HasWeight k F) (hG : HasWeight l G) : HasWeight (k+l) (F*G) := by
  intro s x
  simp only [ContinuousMap.mul_apply,hF s,hG s,mFourier_add]
  ring

omit [CompactSpace X] [ContinuousVAdd (UnitAddTorus d) X] in
lemma HasWeight.star {F : C(X, ℂ)} {k : d → ℤ}
    (hF : HasWeight k F) : HasWeight (-k) (star F) := by
  intro s x
  simp only [ContinuousMap.star_apply,hF s,mFourier_neg]
  change (starRingEnd ℂ) (_ * _) = (starRingEnd ℂ) _ * (starRingEnd ℂ) _
  exact map_mul _ _ _

 
def eigenfunctions : Set C(X, ℂ) := {F | ∃ k : d → ℤ, HasWeight k F}

 
def eigenAlgebra : StarSubalgebra ℂ C(X, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (eigenfunctions (d := d))
  star_mem' := by
    change Algebra.adjoin ℂ (eigenfunctions (d := d)) ≤ star (Algebra.adjoin ℂ (eigenfunctions (d := d)))
    refine Algebra.adjoin_le ?_
    rintro F ⟨k,hk⟩
    exact Algebra.subset_adjoin ⟨-k,hk.star⟩

omit [ContinuousVAdd (UnitAddTorus d) X] in
lemma eigenAlgebra_span : (eigenAlgebra (d := d)).toSubalgebra.toSubmodule =
    Submodule.span ℂ ((eigenfunctions (d := d) (X := X))) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro F hF
  refine Submonoid.closure_induction (fun _ => id) ⟨0,hasWeight_one⟩ ?_ hF
  rintro F G _ _ ⟨k,hk⟩ ⟨l,hl⟩
  exact ⟨k+l,hk.mul hl⟩

 
lemma coeff_eval_eq (F : C(X, ℂ)) (x y : X)
    (hxy : ∀ k : d → ℤ, coeff F k x = coeff F k y) : F x = F y := by
  let H : C((UnitAddTorus d), ℂ) := ⟨fun t => F (t +ᵥ x) - F (t +ᵥ y), by fun_prop⟩
  have hH : H = 0 := torus_coeff_unique H (by
    intro k
    change (∫ t : (UnitAddTorus d), mFourier (-k) t * (F (t +ᵥ x) - F (t +ᵥ y))
      ∂volume) = 0
    simp only [mul_sub]
    rw [integral_sub]
    · exact sub_eq_zero.mpr (hxy k)
    · exact (show Continuous (fun t : (UnitAddTorus d) => mFourier (-k) t * F (t +ᵥ x)) by
        fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    · exact (show Continuous (fun t : (UnitAddTorus d) => mFourier (-k) t * F (t +ᵥ y)) by
        fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have h := congrArg (fun f : C((UnitAddTorus d), ℂ) => f 0) hH
  simpa only [H,ContinuousMap.coe_mk,zero_vadd,ContinuousMap.zero_apply,sub_eq_zero] using h

lemma eigenAlgebra_separatesPoints : ((eigenAlgebra (d := d) (X := X))).SeparatesPoints := by
  intro x y hxy
  let F : C(X, ℂ) := ⟨fun z => (dist z x : ℂ), by fun_prop⟩
  have hF : F x ≠ F y := by
    intro h
    have h' : dist y x = 0 := by
      have hc : (0 : ℂ) = (dist y x : ℂ) := by simpa only [F,ContinuousMap.coe_mk,dist_self,Complex.ofReal_zero] using h
      exact (Complex.ofReal_eq_zero.mp hc.symm)
    exact hxy (dist_eq_zero.mp h').symm
  have hk : ∃ k : d → ℤ, coeff F k x ≠ coeff F k y := by
    by_contra h
    push Not at h
    exact hF (coeff_eval_eq F x y h)
  obtain ⟨k,hk⟩ := hk
  exact ⟨_,⟨coeff F k,Algebra.subset_adjoin ⟨k,coeff_hasWeight F k⟩,rfl⟩,hk⟩

 

theorem eigenfunctions_dense :
    (Submodule.span ℂ ((eigenfunctions (d := d) (X := X)))).topologicalClosure = ⊤ := by
  rw [← eigenAlgebra_span]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      (eigenAlgebra (d := d)) eigenAlgebra_separatesPoints)

 

lemma coeff_lipschitz [IsIsometricVAdd (UnitAddTorus d) X]
    (F : C(X, ℂ)) {C : NNReal} (hF : LipschitzWith C F) (k : d → ℤ) :
    LipschitzWith C (coeff F k) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hx : Integrable (fun t : (UnitAddTorus d) => mFourier (-k) t * F (t +ᵥ x)) volume :=
    (show Continuous (fun t : (UnitAddTorus d) => mFourier (-k) t * F (t +ᵥ x)) by
      fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hy : Integrable (fun t : (UnitAddTorus d) => mFourier (-k) t * F (t +ᵥ y)) volume :=
    (show Continuous (fun t : (UnitAddTorus d) => mFourier (-k) t * F (t +ᵥ y)) by
      fun_prop).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [dist_eq_norm,coeff_apply,coeff_apply,← integral_sub hx hy]
  have hb : ∀ t : (UnitAddTorus d),
      ‖mFourier (-k) t * F (t +ᵥ x) - mFourier (-k) t * F (t +ᵥ y)‖ ≤ C * dist x y := by
    intro t
    rw [← mul_sub,norm_mul]
    have hn : ‖mFourier (-k) t‖ = 1 := by
      simp only [mFourier,ContinuousMap.coe_mk,norm_prod,fourier_apply,Circle.norm_coe,Finset.prod_const_one]
    rw [hn,one_mul,← dist_eq_norm]
    simpa only [(isometry_vadd X t).dist_eq] using hF.dist_le_mul (t +ᵥ x) (t +ᵥ y)
  simpa only [probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := (volume : Measure (UnitAddTorus d)))
      (Filter.Eventually.of_forall hb)

 

omit [AddAction (UnitAddTorus d) X] [ContinuousVAdd (UnitAddTorus d) X] in
lemma lipschitz_mul (F G : C(X, ℂ)) {C D : NNReal}
    (hF : LipschitzWith C F) (hG : LipschitzWith D G) :
    LipschitzWith (‖F‖₊ * D + ‖G‖₊ * C) (F*G) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (F x * G x) (F y * G y) ≤ _
  calc
    _ = ‖F x * (G x-G y) + (F x-F y) * G y‖ := by rw [dist_eq_norm]; congr 1; ring
    _ ≤ ‖F x‖ * ‖G x-G y‖ + ‖F x-F y‖ * ‖G y‖ := by
      simpa only [norm_mul] using norm_add_le (F x * (G x-G y)) ((F x-F y) * G y)
    _ ≤ ‖F‖ * (D * dist x y) + (C * dist x y) * ‖G‖ := by
      gcongr
      · exact F.norm_coe_le_norm x
      · simpa only [dist_eq_norm] using hG.dist_le_mul x y
      · simpa only [dist_eq_norm] using hF.dist_le_mul x y
      · exact G.norm_coe_le_norm y
    _ = _ := by simp only [NNReal.coe_add,NNReal.coe_mul,coe_nnnorm]; ring

 
def lipEigenfunctions : Set C(X, ℂ) :=
  {F | (∃ k : d → ℤ, HasWeight k F) ∧ ∃ C : NNReal, LipschitzWith C F}

omit [CompactSpace X] [ContinuousVAdd (UnitAddTorus d) X] in
lemma lipEigenfunctions_one : (1 : C(X, ℂ)) ∈ (lipEigenfunctions (d := d)) :=
  ⟨⟨0,hasWeight_one⟩,0,LipschitzWith.const _⟩

omit [ContinuousVAdd (UnitAddTorus d) X] in
lemma lipEigenfunctions_mul {F G : C(X, ℂ)}
    (hF : F ∈ (lipEigenfunctions (d := d))) (hG : G ∈ (lipEigenfunctions (d := d))) :
    F*G ∈ (lipEigenfunctions (d := d)) := by
  obtain ⟨⟨k,hk⟩,C,hC⟩ := hF
  obtain ⟨⟨l,hl⟩,D,hD⟩ := hG
  exact ⟨⟨k+l,hk.mul hl⟩,_,lipschitz_mul F G hC hD⟩

omit [CompactSpace X] [ContinuousVAdd (UnitAddTorus d) X] in
lemma lipEigenfunctions_star {F : C(X, ℂ)} (hF : F ∈ (lipEigenfunctions (d := d))) :
    star F ∈ (lipEigenfunctions (d := d)) := by
  obtain ⟨⟨k,hk⟩,C,hC⟩ := hF
  refine ⟨⟨-k,hk.star⟩,C,LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  simpa only [ContinuousMap.star_apply,dist_star_star] using hC.dist_le_mul x y

def lipEigenAlgebra : StarSubalgebra ℂ C(X, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (lipEigenfunctions (d := d))
  star_mem' := by
    change Algebra.adjoin ℂ (lipEigenfunctions (d := d)) ≤ star (Algebra.adjoin ℂ (lipEigenfunctions (d := d)))
    refine Algebra.adjoin_le ?_
    intro F hF
    exact Algebra.subset_adjoin (lipEigenfunctions_star hF)

omit [ContinuousVAdd (UnitAddTorus d) X] in
lemma lipEigenAlgebra_span : (lipEigenAlgebra (d := d)).toSubalgebra.toSubmodule =
    Submodule.span ℂ ((lipEigenfunctions (d := d) (X := X))) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Set.Subset.trans ?_ Submodule.subset_span
  intro F hF
  exact Submonoid.closure_induction (fun _ => id) lipEigenfunctions_one
    (fun _ _ _ _ hf hg => lipEigenfunctions_mul hf hg) hF

lemma lipEigenAlgebra_separatesPoints [IsIsometricVAdd (UnitAddTorus d) X] :
    ((lipEigenAlgebra (d := d) (X := X))).SeparatesPoints := by
  intro x y hxy
  let F : C(X, ℂ) := ⟨fun z => (dist z x : ℂ), by fun_prop⟩
  have hLip : LipschitzWith 1 F := by
    simpa only [one_mul,F,ContinuousMap.coe_mk,Function.comp_def] using!
      Complex.isometry_ofReal.lipschitzWith.comp (LipschitzWith.dist_left x)
  have hF : F x ≠ F y := by
    intro h
    have h' : dist y x = 0 := by
      have hc : (0 : ℂ) = (dist y x : ℂ) := by
        simpa only [F,ContinuousMap.coe_mk,dist_self,Complex.ofReal_zero] using h
      exact Complex.ofReal_eq_zero.mp hc.symm
    exact hxy (dist_eq_zero.mp h').symm
  have hk : ∃ k : d → ℤ, coeff F k x ≠ coeff F k y := by
    by_contra h
    push Not at h
    exact hF (coeff_eval_eq F x y h)
  obtain ⟨k,hk⟩ := hk
  exact ⟨_,⟨coeff F k,Algebra.subset_adjoin
    ⟨⟨k,coeff_hasWeight F k⟩,1,coeff_lipschitz F hLip k⟩,rfl⟩,hk⟩

 
theorem lipEigenfunctions_dense [IsIsometricVAdd (UnitAddTorus d) X] :
    (Submodule.span ℂ ((lipEigenfunctions (d := d) (X := X)))).topologicalClosure = ⊤ := by
  rw [← lipEigenAlgebra_span]
  exact congrArg (Subalgebra.toSubmodule ∘ StarSubalgebra.toSubalgebra)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      (lipEigenAlgebra (d := d)) lipEigenAlgebra_separatesPoints)

 

theorem finite_vertical_obstruction_continuous
    (δ B : ℝ) (hδ : 0 < δ) (hB : 0 < B) :
    ∃ S : Finset {F : C(X, ℂ) // F ∈ (eigenfunctions (d := d))}, ∃ η : ℝ, 0 < η ∧
      ∀ L : C(X, ℂ) →ₗ[ℂ] ℂ, (∀ F, ‖L F‖ ≤ B * ‖F‖) →
        (∃ F : C(X, ℂ), LipschitzWith 1 F ∧ ‖F‖ ≤ 1 ∧ δ ≤ ‖L F‖) →
        ∃ F ∈ S, η ≤ ‖L F.val‖ := by
  obtain ⟨K,hK,hKLip⟩ := compact_superset_unit_lipschitz X
  have hd : (Submodule.span ℂ (Set.range
      (fun F : {F : C(X, ℂ) // F ∈ (eigenfunctions (d := d))} => F.val))).topologicalClosure = ⊤ := by
    simpa only [Subtype.range_coe_subtype,Set.ofPred_mem_eq] using
      (eigenfunctions_dense (X := X))
  obtain ⟨S,η,hη,hS⟩ := finite_tests_of_dense_span _ hd K hK δ B hδ hB
  refine ⟨S,η,hη,?_⟩
  intro L hL ⟨F,hLip,hNorm,hLarge⟩
  exact hS L hL ⟨F,hKLip F hLip hNorm,hLarge⟩

 

theorem finite_vertical_obstruction [IsIsometricVAdd (UnitAddTorus d) X]
    (δ B : ℝ) (hδ : 0 < δ) (hB : 0 < B) :
    ∃ S : Finset {F : C(X, ℂ) // F ∈ (lipEigenfunctions (d := d))}, ∃ η : ℝ, 0 < η ∧
      ∀ L : C(X, ℂ) →ₗ[ℂ] ℂ, (∀ F, ‖L F‖ ≤ B * ‖F‖) →
        (∃ F : C(X, ℂ), LipschitzWith 1 F ∧ ‖F‖ ≤ 1 ∧ δ ≤ ‖L F‖) →
        ∃ F ∈ S, η ≤ ‖L F.val‖ := by
  obtain ⟨K,hK,hKLip⟩ := compact_superset_unit_lipschitz X
  have hd : (Submodule.span ℂ (Set.range
      (fun F : {F : C(X, ℂ) // F ∈ (lipEigenfunctions (d := d))} => F.val))).topologicalClosure = ⊤ := by
    simpa only [Subtype.range_coe_subtype,Set.ofPred_mem_eq] using
      (lipEigenfunctions_dense (X := X))
  obtain ⟨S,η,hη,hS⟩ := finite_tests_of_dense_span _ hd K hK δ B hδ hB
  refine ⟨S,η,hη,?_⟩
  intro L hL ⟨F,hLip,hNorm,hLarge⟩
  exact hS L hL ⟨F,hKLip F hLip hNorm,hLarge⟩

omit [CompactSpace X] in
 

lemma integral_hasWeight_eq_zero [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [VAddInvariantMeasure (UnitAddTorus d) X μ]
    (F : C(X, ℂ)) {k : d → ℤ} (hk : k ≠ 0) (hF : HasWeight k F) :
    (∫ x, F x ∂μ) = 0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, k i ≠ 0 := by
    contrapose! hk
    exact funext hk
  let s : UnitAddTorus d := Pi.single i (((1 / 2 / (k i : ℝ) : ℝ) : UnitAddCircle))
  have hs : mFourier k s = -1 := by
    rw [mFourier]
    simp only [ContinuousMap.coe_mk]
    rw [Finset.prod_eq_single i]
    · simp only [s,Pi.single_eq_same]
      simpa only [zero_add,fourier_eval_zero] using
        (fourier_add_half_inv_index (T := 1) hi (by norm_num) (0 : UnitAddCircle))
    · intro j _ hji
      simp [s,Pi.single_eq_of_ne hji]
    · simp
  have heq := integral_vadd_eq_self (μ := μ) (fun x => F x) (g := s)
  simp only [hF s,hs,neg_one_mul,integral_neg] at heq
  exact CharZero.eq_neg_self_iff.mp heq.symm

 
def balanced (F : C(X, ℂ)) : C(X × X, ℂ) where
  toFun p := F p.1 * star (F p.2)
  continuous_toFun := by fun_prop

omit [CompactSpace X] [ContinuousVAdd (UnitAddTorus d) X] in
lemma balanced_invariant (F : C(X, ℂ)) {k : d → ℤ} (hF : HasWeight k F)
    (s : (UnitAddTorus d)) (p : X × X) :
    balanced F (s +ᵥ p) = balanced F p := by
  change F (s +ᵥ p.1) * star (F (s +ᵥ p.2)) = F p.1 * star (F p.2)
  rw [hF s,hF s]
  have he : star (mFourier k s) = mFourier (-k) s := mFourier_neg.symm
  rw [star_mul,he]
  calc
    mFourier k s * F p.1 * (star (F p.2) * mFourier (-k) s) =
      (mFourier k s * mFourier (-k) s) * (F p.1 * star (F p.2)) := by ring
    _ = _ := by rw [character_cancel,one_mul]

 
abbrev PairQuotient (X : Type*) [AddAction (UnitAddTorus d) X] :=
  Quotient (AddAction.orbitRel (UnitAddTorus d) (X × X))

 

def balancedDescent (F : C(X, ℂ)) {k : d → ℤ} (hF : HasWeight k F) :
    C(PairQuotient (d := d) X, ℂ) where
  toFun := Quotient.lift (balanced F) (by
    intro a b hab
    obtain ⟨s,hs⟩ := AddAction.mem_orbit_iff.mp hab
    rw [← hs]
    exact balanced_invariant F hF s b)
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    exact (balanced F).continuous

omit [CompactSpace X] [ContinuousVAdd (UnitAddTorus d) X] in
@[simp] lemma balancedDescent_apply (F : C(X, ℂ)) {k : d → ℤ} (hF : HasWeight k F)
    (p : X × X) : balancedDescent F hF ⟦p⟧ = F p.1 * star (F p.2) := rfl

omit [CompactSpace X] [ContinuousVAdd (UnitAddTorus d) X] in
 
lemma balanced_orbit_factorization {A : Type*} (f g : A → X)
    (F : C(X, ℂ)) {k : d → ℤ} (hF : HasWeight k F) (n : A) :
    F (f n) * star (F (g n)) = balancedDescent F hF ⟦(f n,g n)⟧ := rfl

end
end TorusVerticalFourier

end
end
end
end

end OAI
