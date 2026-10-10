import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.WordPlan01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
end
 
end

section
 

noncomputable section
namespace OwnTerminal
variable {G H X Y : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]

lemma project_pow (π : X → Y) (g : G) (h : H)
    (hp : ∀ x,π (g • x)=h • π x) (k : ℕ) (x : X) :
    π (g^k • x)=h^k • π x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih => simp only [pow_succ, mul_smul,ih,hp]

lemma project_inv (π : X → Y) (g : G) (h : H)
    (hp : ∀ x,π (g • x)=h • π x) (x : X) :
    π (g⁻¹ • x)=h⁻¹ • π x := by
  have he:=congrArg (fun y=>h⁻¹ • y) (hp (g⁻¹ • x))
  simpa using he.symm

lemma project_zpow (π : X → Y) (g : G) (h : H)
    (hp : ∀ x,π (g • x)=h • π x) (k : ℤ) (x : X) :
    π (g^k • x)=h^k • π x := by
  cases k with
  | ofNat k => simpa using project_pow π g h hp k x
  | negSucc k =>
    simpa only [zpow_negSucc,inv_pow] using
      project_pow π g⁻¹ h⁻¹ (project_inv π g h hp) (k+1) x

lemma project_list {E : Type*} (π : X → Y) (a : E → G) (b : E → H)
    (l : List E) (hp : ∀ e∈l,∀ x,π (a e • x)=b e • π x) (x : X) :
    π ((l.map a).prod • x)=(l.map b).prod • π x := by
  induction l generalizing x with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons,List.prod_cons,mul_smul]
    rw [hp e (by simp),ih (fun t ht=>hp t (by simp [ht]))]

open ConstructedWordPlan GlobalWordPlan RationalPivotPlan
variable {n : ℕ} (D : Pivot n)

 

lemma terminal_projection (π : X → Y) (L : Fin D.pairs → G) (S : Fin D.pairs → H)
    (j : Fin D.targets) (hp : ∀ e,D.owner e=j → ∀ x,π (L e • x)=S e • π x)
    (q₀ : ℕ) (b : Scale n) (U : Finset (Fin D.pairs))
    (hU : ∀ e∈U,D.owner e=j) (x : X) :
    π (FreeGroup.lift (letter D.index D.tail D.owner D.added L q₀ b) (baseWord D U) • x)=
      FreeGroup.lift (letter D.index D.tail D.owner D.added S q₀ b) (baseWord D U) • π x := by
  classical
  simp only [baseWord,map_list_prod,List.map_map]
  apply project_list
  intro e he
  simpa only [Function.comp_apply,FreeGroup.lift_apply_of,letter] using
    project_zpow π (L e) (S e) (hp e (hU e (Finset.mem_toList.mp he)))
      (qExponent D.index D.tail D.owner D.added q₀ b (e,1)).num

end OwnTerminal
end
 
end

section
 

 

namespace AlignmentMass
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section

variable {X O : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X] [HasOuterApproxClosed X] [Fintype O] [Nonempty O]

 

theorem finite_closed_mass (μ : ProbabilityMeasure X)
    (ν : O → ℕ → ProbabilityMeasure X) (F : O → Set X)
    (hF : ∀ o, IsClosed (F o))
    (hν : ∀ o, Tendsto (ν o) atTop (𝓝 μ))
    (hcover : ∀ n, 1 ≤ ∑ o, ν o n (F o)) :
    ((Fintype.card O : ℝ≥0)⁻¹ : ℝ≥0∞) ≤ (μ : Measure X) (⋃ o, F o) := by
  classical
  have hq : (Fintype.card O : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ _o : O, (Fintype.card O : ℝ≥0)⁻¹) = 1 := by
    simp [nsmul_eq_mul, hq]
  have hex : ∀ n, ∃ o, (Fintype.card O : ℝ≥0)⁻¹ ≤ ν o n (F o) := by
    intro n
    obtain ⟨o,_,ho⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty
      (hsum.symm ▸ hcover n)
    exact ⟨o,ho⟩
  have he : ∀ᶠ n in atTop, ∃ o, (Fintype.card O : ℝ≥0)⁻¹ ≤ ν o n (F o) :=
    Eventually.of_forall hex
  obtain ⟨o,ho⟩ := frequently_exists.mp he.frequently
  have hf : ∃ᶠ n in atTop,
      ((Fintype.card O : ℝ≥0)⁻¹ : ℝ≥0∞) ≤ (ν o n : Measure X) (F o) := by
    apply ho.mono
    intro n hn
    rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    simpa only [ENNReal.coe_inv hq] using ENNReal.coe_le_coe.mpr hn
  exact (le_limsup_of_frequently_le hf).trans
    ((ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (hν o) (hF o)).trans
      (measure_mono (Set.subset_iUnion F o)))

 

omit [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X] [Nonempty O] in
theorem cover_sum [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    [Nonempty O] {Z : Type*} [MeasurableSpace Z] (ρ : ProbabilityMeasure Z)
    (Y : O → Z → X) (hY : ∀ o, Measurable (Y o)) (F : O → Set X)
    (hF : ∀ o, MeasurableSet (F o)) (hcover : ∀ z, ∃ o, Y o z ∈ F o) :
    1 ≤ ∑ o, (ρ.map (Y o)) (F o) := by
  have hu : (⋃ o, Y o ⁻¹' F o) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
    exact hcover z
  have hh : (1:ℝ≥0∞) ≤ ∑ o, (ρ : Measure Z) (Y o ⁻¹' F o) := by
    simpa [hu] using measure_iUnion_fintype_le (ρ : Measure Z) (fun o => Y o ⁻¹' F o)
  apply ENNReal.coe_le_coe.mp
  push_cast
  simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure,
    ProbabilityMeasure.map_apply' ρ (hY _).aemeasurable (hF _)] using hh

section Thresholds
variable {J : Type*}

 
def ClosedGood (τ : ℝ) (A T : J → X → ℝ) : Set X :=
  {x | ∀ j, A j x ≤ 3*τ/2 ∨ 3*τ/2 ≤ T j x}

 
def OpenGood (τ : ℝ) (A T : J → X → ℝ) : Set X :=
  {x | ∀ j, A j x < 7*τ/4 ∨ 5*τ/4 < T j x}

 
def Success (τ : ℝ) (A T : J → X → ℝ) : Set X :=
  {x | ∀ j, 2*τ < A j x → τ < T j x}

omit [MeasurableSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X] in
lemma isClosed_closedGood (τ : ℝ) (A T : J → X → ℝ)
    (hA : ∀ j, Continuous (A j)) (hT : ∀ j, Continuous (T j)) :
    IsClosed (ClosedGood τ A T) := by
  simp only [ClosedGood, Set.ofPred_forall, Set.ofPred_or]
  exact isClosed_iInter fun j => (isClosed_le (hA j) continuous_const).union
    (isClosed_le continuous_const (hT j))

omit [MeasurableSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X] in
lemma isOpen_openGood [Finite J] (τ : ℝ) (A T : J → X → ℝ)
    (hA : ∀ j, Continuous (A j)) (hT : ∀ j, Continuous (T j)) :
    IsOpen (OpenGood τ A T) := by
  simp only [OpenGood, Set.ofPred_forall, Set.ofPred_or]
  exact isOpen_iInter_of_finite fun j => (isOpen_lt (hA j) continuous_const).union
    (isOpen_lt continuous_const (hT j))

omit [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X] in
lemma closed_subset_open {τ : ℝ} (hτ : 0 < τ) (A T : J → X → ℝ) :
    ClosedGood τ A T ⊆ OpenGood τ A T := by
  intro x hx j
  rcases hx j with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

omit [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X] in
lemma open_subset_success {τ : ℝ} (A T A' T' : J → X → ℝ)
    (hA : ∀ j x, |A' j x - A j x| ≤ τ/4)
    (hT : ∀ j x, |T' j x - T j x| ≤ τ/4) :
    OpenGood τ A T ⊆ Success τ A' T' := by
  intro x hx j hj
  rcases hx j with h | h
  · have hb := (abs_le.mp (hA j x)).2
    linarith
  · have hb := (abs_le.mp (hT j x)).1
    linarith
end Thresholds

 

omit [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X] in
theorem mixture_lower [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {B : Type*} [MeasurableSpace B]
    (η : ProbabilityMeasure B) (μ : B → ProbabilityMeasure X)
    (ρ : ProbabilityMeasure X) (S : Set X) (a : ℝ≥0∞)
    (hmix : (ρ : Measure X) S = ∫⁻ b, (μ b : Measure X) S ∂(η : Measure B))
    (hb : ∀ᵐ b ∂(η : Measure B), a ≤ (μ b : Measure X) S) :
    a ≤ (ρ : Measure X) S := by
  rw [hmix]
  simpa using (lintegral_mono_ae hb :
    (∫⁻ _b, a ∂(η : Measure B)) ≤ ∫⁻ b, (μ b : Measure X) S ∂(η : Measure B))

 

omit [Fintype O] [Nonempty O] in
theorem eventually_success_mass [Fintype O] [Nonempty O] {J : Type*} [Finite J]
    (μ : ProbabilityMeasure X) (ρ : ℕ → ProbabilityMeasure X)
    (hρ : Tendsto ρ atTop (𝓝 μ)) {τ : ℝ} (hτ : 0 < τ)
    (A T : O → J → X → ℝ) (A' T' : ℕ → O → J → X → ℝ)
    (hA : ∀ o j, Continuous (A o j)) (hT : ∀ o j, Continuous (T o j))
    (he : ∀ᶠ n in atTop, ∀ o j x,
      |A' n o j x - A o j x| ≤ τ/4 ∧ |T' n o j x - T o j x| ≤ τ/4)
    {a δ : ℝ≥0∞} (hδ : δ < a)
    (hm : a ≤ (μ : Measure X) (⋃ o, ClosedGood τ (A o) (T o))) :
    ∀ᶠ n in atTop, δ < (ρ n : Measure X) (⋃ o, Success τ (A' n o) (T' n o)) := by
  let U := ⋃ o, OpenGood τ (A o) (T o)
  have hU : IsOpen U := isOpen_iUnion fun o => isOpen_openGood τ _ _ (hA o) (hT o)
  have hsub : (⋃ o, ClosedGood τ (A o) (T o)) ⊆ U :=
    Set.iUnion_mono fun o => closed_subset_open hτ _ _
  have hmU : a ≤ (μ : Measure X) U := hm.trans (measure_mono hsub)
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hρ hU
  have hev := eventually_lt_of_lt_liminf (hδ.trans_le (hmU.trans hlim))
  filter_upwards [he,hev] with n hen hn
  apply hn.trans_le
  apply measure_mono
  exact Set.iUnion_mono fun o => open_subset_success _ _ _ _
    (fun j x => (hen o j x).1) (fun j x => (hen o j x).2)

 

theorem conditional_mass {J : Type*} [Finite J]
    (μ : ProbabilityMeasure X) (ν : O → ℕ → ProbabilityMeasure X)
    (ρ : ℕ → ProbabilityMeasure X)
    (hν : ∀ o, Tendsto (ν o) atTop (𝓝 μ))
    (hρ : Tendsto ρ atTop (𝓝 μ)) {τ : ℝ} (hτ : 0 < τ)
    (A T : O → J → X → ℝ) (A' T' : ℕ → O → J → X → ℝ)
    (hA : ∀ o j, Continuous (A o j)) (hT : ∀ o j, Continuous (T o j))
    (hcover : ∀ n, 1 ≤ ∑ o, ν o n (ClosedGood τ (A o) (T o)))
    (he : ∀ᶠ n in atTop, ∀ o j x,
      |A' n o j x - A o j x| ≤ τ/4 ∧ |T' n o j x - T o j x| ≤ τ/4) :
    ∀ᶠ n in atTop, (Fintype.card O : ℝ≥0)⁻¹ / 2 <
      ρ n (⋃ o, Success τ (A' n o) (T' n o)) := by
  have hq : 0 < (Fintype.card O : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hhalf : (Fintype.card O : ℝ≥0)⁻¹ / 2 < (Fintype.card O : ℝ≥0)⁻¹ :=
    half_lt_self (inv_pos.mpr hq)
  have hm := finite_closed_mass μ ν (fun o => ClosedGood τ (A o) (T o))
    (fun o => isClosed_closedGood τ _ _ (hA o) (hT o)) hν hcover
  rw [← ENNReal.coe_inv (ne_of_gt hq)] at hm
  have hev := eventually_success_mass μ ρ hρ hτ A T A' T' hA hT he
    (ENNReal.coe_lt_coe.mpr hhalf) hm
  apply hev.mono
  intro n hn
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hn
  exact ENNReal.coe_lt_coe.mp hn

 

theorem conditional_mass_mixture {B J : Type*} [MeasurableSpace B] [Finite J]
    (η : ProbabilityMeasure B) (μb : B → ProbabilityMeasure X)
    (μ : ProbabilityMeasure X) (ν : B → O → ℕ → ProbabilityMeasure X)
    (ρ : ℕ → ProbabilityMeasure X) (hρ : Tendsto ρ atTop (𝓝 μ))
    {τ : ℝ} (hτ : 0 < τ)
    (A T : O → J → X → ℝ) (A' T' : ℕ → O → J → X → ℝ)
    (hA : ∀ o j, Continuous (A o j)) (hT : ∀ o j, Continuous (T o j))
    (hν : ∀ᵐ b ∂(η : Measure B), ∀ o, Tendsto (ν b o) atTop (𝓝 (μb b)))
    (hcover : ∀ᵐ b ∂(η : Measure B), ∀ n,
      1 ≤ ∑ o, ν b o n (ClosedGood τ (A o) (T o)))
    (hmix : (μ : Measure X) (⋃ o, ClosedGood τ (A o) (T o)) =
      ∫⁻ b, (μb b : Measure X) (⋃ o, ClosedGood τ (A o) (T o)) ∂(η : Measure B))
    (he : ∀ᶠ n in atTop, ∀ o j x,
      |A' n o j x - A o j x| ≤ τ/4 ∧ |T' n o j x - T o j x| ≤ τ/4) :
    ∀ᶠ n in atTop, (Fintype.card O : ℝ≥0)⁻¹ / 2 <
      ρ n (⋃ o, Success τ (A' n o) (T' n o)) := by
  have hq : 0 < (Fintype.card O : ℝ≥0) := by exact_mod_cast Fintype.card_pos
  have hhalf : (Fintype.card O : ℝ≥0)⁻¹ / 2 < (Fintype.card O : ℝ≥0)⁻¹ :=
    half_lt_self (inv_pos.mpr hq)
  have hb : ∀ᵐ b ∂(η : Measure B),
      ((Fintype.card O : ℝ≥0)⁻¹ : ℝ≥0∞) ≤
        (μb b : Measure X) (⋃ o, ClosedGood τ (A o) (T o)) := by
    filter_upwards [hν,hcover] with b hn hc
    exact finite_closed_mass (μb b) (ν b) _
      (fun o => isClosed_closedGood τ _ _ (hA o) (hT o)) hn hc
  have hm := mixture_lower η μb μ _ _ hmix hb
  rw [← ENNReal.coe_inv (ne_of_gt hq)] at hm
  have hev := eventually_success_mass μ ρ hρ hτ A T A' T' hA hT he
    (ENNReal.coe_lt_coe.mpr hhalf) hm
  apply hev.mono
  intro n hn
  rw [← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] at hn
  exact ENNReal.coe_lt_coe.mp hn

end
end AlignmentMass
 

end
end

end OAI
