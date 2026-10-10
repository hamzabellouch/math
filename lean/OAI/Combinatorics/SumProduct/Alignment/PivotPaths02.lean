import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.HierarchyRates01
import OAI.Combinatorics.SumProduct.Alignment.PivotPaths01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
noncomputable section
open Filter MeasureTheory
open scoped BigOperators ENNReal Topology
noncomputable section
open scoped BigOperators Topology BoundedContinuousFunction
noncomputable section
open scoped BigOperators BoundedContinuousFunction Topology NNReal ENNReal
namespace SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
open ProductExposureLabels ProductExposureLaw SourceExposureSlots SourceResidueAlignment
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
open ConstructedWordPlan.RationalPivotPlan
open ConstructedWordPlan.GlobalWordPlan.SourceTerminalArithmetic
open RawHarmonicProbability
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (D : Pivot a)

variable (s r : ℕ) (hs : 1 ≤ s) (Fs : Finset (Scale a)) (q₀ : ℕ) (b₀ : Scale a)
local notation "I" => FiniteModelSlots.Index D s r hs Fs q₀ b₀

open Filter MeasureTheory RationalLattice MalcevCharacters
open MicrocellScale AdmissibleMicrocellBoundary RoughScales IntegerAlignment
open RoughSamplingWeights SourceMacroSelection

section Harmonic
variable (G₀ : Fin D.targets → ℚ → Fin r → Type)
variable [∀ t v c, Group (G₀ t v c)] [∀ t v c, TopologicalSpace (G₀ t v c)]
variable [∀ t v c, IsTopologicalGroup (G₀ t v c)]
variable (Γ₀ : ∀ t v c, Subgroup (G₀ t v c))
variable (n₀ : Fin D.targets → ℚ → Fin r → ℕ)
variable (c₀ : ∀ t v c, RealCoordinates (G₀ t v c) (n₀ t v c))
variable (hsk : ∀ t v c, SecondKind (c₀ t v c))
variable (A₀ : ∀ t v c, CubeFaces.Filtration (G₀ t v c))
variable (weight : ∀ t v c, Fin (n₀ t v c) → ℕ)
variable (hA : ∀ t v c k (g : G₀ t v c), g ∈ (A₀ t v c).level k ↔
  ∀ j, weight t v c j < k → (c₀ t v c).coord g j = 0)
variable (hw : ∀ t v c j, 0 < weight t v c j)
include hsk hA hw
open SourcePivotPaths SourceRawPrefix

 

theorem source_uniform_prefix_extension
    (hΓ : ∀ t v c g, g ∈ Γ₀ t v c ↔ ∀ j, ∃ z : ℤ, (c₀ t v c).coord g j = z)
    (hmono : ∀ t v c, Monotone (weight t v c))
    (h0 : ∀ t v c, (A₀ t v c).level 0 = ⊤)
    (h1 : ∀ t v c, (A₀ t v c).level 1 = ⊤)
    (hstep : ∀ t v c, (A₀ t v c).level (s+1) = ⊥)
    (M J R H : ℕ → ℕ) (L : ℕ → ℤ) (ht : ℕ → Fin a → ℤ)
    (g₀ x₀ : ∀ t, ℕ → ∀ v c, ℤ → ℤ → G₀ t v c)
    (obs₀ : ∀ t, ℕ → ∀ v c, ℤ → ℤ → ((G₀ t v c) ⧸ Γ₀ t v c) →ᵇ ℝ)
    (w0 : ℕ → ℕ) (X : ℕ → Fin a → ℕ)
    (hw0 : Tendsto w0 atTop atTop)
    (hX : ∀ N j, 4*primorial (w0 N) ≤ X N j)
    (hXt : ∀ j, Tendsto (fun N => X N j) atTop atTop)
    (hWM : ∀ N, (primorial (w0 N) : ℤ) ∣ (M N : ℤ))
    (hM : ∀ N, 0 < M N) (hMs : ∀ N, RoughScales.Smooth (w0 N) (M N : ℤ))
    (hJ : ∀ N, 0 < J N) (hRJ : ∀ N, R N = M N*J N)
    (hL : ∀ N, 0 < L N) (hsm : ∀ N, RoughScales.Smooth (w0 N) (L N))
    (hWL : ∀ N, (primorial (w0 N) : ℤ) ∣ L N) (hML : ∀ N, (M N : ℤ) ∣ L N)
    (hLexact : ∀ N, L N = (M N : ℤ)*(primorial (w0 N) : ℤ)^(w0 N))
    (hXL : ∀ t (j : Fin (m D t)), Tendsto (fun N =>
      (X N (perm D t (j.castAdd (h D t))) : ℝ)/(L N : ℝ)) atTop atTop)
    (hH : ∀ N, 0 < H N) (hRrad : ∀ N, R N = radius (M N) (H N))
    (hdom : Dominates (fun N => (H N : ℝ)) (earlierScale M (fun N => previousProduct D (X N))))
    (hxdom : Dominates (fun N => Real.log (X N D.index : ℝ)) (fun N => (H N : ℝ)))
    (hpowWM : ∀ N, primorial (w0 N)^(w0 N) ∣ M N)
    (hq₀ : 0 < q₀) (hht : ∀ N j, 0 < ht N j)
    (hheight : ∀ N e, height (ht N) (D.added e) ≤ M N)
    (hd : ∀ e, Disjoint (D.added e) (D.tail (D.owner e)))
    (hQq : terminalDenom D s r hs Fs b₀ ∣ q₀)
    (hb₀ : ∀ j, 0 < b₀ j) (hFs : ∀ b ∈ Fs, ∀ j, 0 < b j)
    (hratio : ∀ N e, ∃ d : ℤ, height (ht N) (D.added e) =
      height (ht N) (block D.index D.tail (D.owner e)) * ((primorial (w0 N) : ℤ)^(w0 N) * d))
    (metric : ∀ t v c, MetricSpace ((G₀ t v c) ⧸ Γ₀ t v c))
    (hmetric : ∀ t v c, QuotientGroup.instTopologicalSpace (Γ₀ t v c) =
      (metric t v c).toUniformSpace.toTopologicalSpace) :
    letI : ∀ t v c, MetricSpace ((G₀ t v c) ⧸ Γ₀ t v c) :=
      fun t v c => (metric t v c).replaceTopology (hmetric t v c)
    ∀ (Kobs : ℝ≥0) (Bobs : ℝ),
      (∀ t N v c b r', LipschitzWith Kobs (obs₀ t N v c b r')) →
      (∀ t N v c b r' z, |obs₀ t N v c b r' z| ≤ Bobs) →
      ∀ (Bs : Finset (Scale a)), b₀ ∈ Bs →
      pivotModulus s r hs D Fs Bs ∣ q₀ → ∀ (τ : ℝ), 0 < τ →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ E : Set (Fin a → ℕ), Earlier D.index E →
    let μ := outsideLaw (X N) (primorial (w0 N)) (primorial_pos _) (hX N)
    let Q : ℝ := (pivotOptions s r hs D Fs).card
    (Q⁻¹/3/Q)*μ.real E ≤ μ.real {u | u ∈ E ∧
      success D r s hs Fs (scalarModels D r G₀ Γ₀ M H g₀ x₀ obs₀ N) (ht N) b₀ u (u D.index) τ} + ε := by
  let : ∀ t v c, MetricSpace ((G₀ t v c) ⧸ Γ₀ t v c) :=
    fun t v c => (metric t v c).replaceTopology (hmetric t v c)
  intro Kobs Bobs hLip hBound Bs hb hq τ hτ ε hε
  let Q : ℝ := (pivotOptions s r hs D Fs).card
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact_mod_cast Finset.card_pos.mpr (pivotOptions_nonempty s r hs D Fs)
  have hV : (slotCount D s r hs Fs q₀ b₀ : ℝ) ≤ Q := by
    have hh : slotCount D s r hs Fs q₀ b₀ ≤ (pivotOptions s r hs D Fs).card := by
      dsimp only [slotCount]
      rw [Fintype.card_coe (slots D s r hs Fs q₀ b₀)]
      unfold slots
      exact Finset.card_image_le
    dsimp only [Q]
    exact_mod_cast hh
  have hExt := source_uniform_extension D s r hs Fs q₀ b₀ G₀ Γ₀ n₀ c₀ hsk A₀ weight hA hw
    hΓ hmono h0 h1 hstep M J R H L ht (fun t N _ => g₀ t N) (fun t N _ => x₀ t N)
    (fun t N _ => obs₀ t N) w0 (fun N => X N D.index) X hw0 hX (fun N => hX N D.index)
    hXt (hXt D.index) hWM hM hMs hJ hRJ hL hsm hWL hML hLexact hXL hH hRrad hdom hxdom
    hpowWM hq₀ hht hheight hd hQq hb₀ hFs hratio metric hmetric Kobs Bobs
    (fun t N _ v c b r' => hLip t N v c b r')
    (fun t N _ v c b r' z => hBound t N v c b r' z)
    Bs hb hq τ hτ (ε*Q) (mul_pos hε hQ)
  filter_upwards [hExt] with N hN
  intro E hE
  let μ := outsideLaw (X N) (primorial (w0 N)) (primorial_pos _) (hX N)
  let ν := jointLaw (X N) (X N D.index) (primorial (w0 N)) (primorial_pos _) (hX N) (hX N D.index)
  let S := scalarModels D r G₀ Γ₀ M H g₀ x₀ obs₀ N
  have hEarly : ν.real {z | z.1 ∈ E} = μ.real E := by
    apply congrArg ENNReal.toReal
    exact (measurePreserving_fst (μ := μ)
      (ν := (law (X N D.index) (primorial (w0 N)) (primorial_pos _) (hX N D.index) : Measure ℕ))).measure_preimage
        (Set.to_countable E).measurableSet.nullMeasurableSet
  have he := hN E
  simp_rw [original_success] at he
  change (Q⁻¹/3)*ν.real {z | z.1 ∈ E} ≤ (slotCount D s r hs Fs q₀ b₀ : ℝ)*
    ν.real {z | z.1 ∈ E ∧ success D r s hs Fs S (ht N) b₀ z.1 z.2 τ}+ε*Q at he
  rw [hEarly, success_mass_resample D r s hs Fs S (ht N) b₀ τ (X N)
    (primorial (w0 N)) (primorial_pos _) (hX N) E hE] at he
  have hem := mul_le_mul_of_nonneg_right hV
    (show 0 ≤ μ.real {u | u ∈ E ∧ success D r s hs Fs S (ht N) b₀ u (u D.index) τ} from measureReal_nonneg)
  change (Q⁻¹/3/Q)*μ.real E ≤ μ.real {u | u ∈ E ∧
    success D r s hs Fs S (ht N) b₀ u (u D.index) τ}+ε
  apply (mul_le_mul_iff_right₀ hQ).mp
  calc
    _ = (Q⁻¹/3)*μ.real E := by field_simp
    _ ≤ Q*μ.real {u | u ∈ E ∧ success D r s hs Fs S (ht N) b₀ u (u D.index) τ}+ε*Q :=
      he.trans (add_le_add hem le_rfl)
    _ = _ := by ring

end Harmonic
end SourceIntegerArrays.GlobalJoint.SourceFrozenFamily
end

 

 

 

noncomputable section
open scoped BigOperators
open MeasureTheory Filter Function
namespace SourcePivotPaths
open ConstructedWordPlan.GlobalWordPlan ConstructedWordPlan.AlignmentScales
open ConstructedWordPlan.RationalPivotPlan
open SourceRawPrefix
attribute [local instance] Classical.propDecidable
variable {a : ℕ} (s r : ℕ) (hs : 1 ≤ s)

def sourcePlan : (Ds : List (Pivot a)) → Plan Ds
  | [] => ()
  | D :: Ds => (pivotOptions s r hs D (multipliers (sourcePlan Ds)), sourcePlan Ds)

def gain (D : Pivot a) (Fs : Finset (Scale a)) : ℝ :=
  ((pivotOptions s r hs D Fs).card : ℝ)⁻¹/3/(pivotOptions s r hs D Fs).card

lemma gain_pos (D : Pivot a) (Fs : Finset (Scale a)) : 0 < gain s r hs D Fs := by
  have hp : 0 < ((pivotOptions s r hs D Fs).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (pivotOptions_nonempty s r hs D Fs)
  exact div_pos (div_pos (inv_pos.mpr hp) (by norm_num)) hp

lemma gain_le_one (D : Pivot a) (Fs : Finset (Scale a)) : gain s r hs D Fs ≤ 1 := by
  have hp : 1 ≤ ((pivotOptions s r hs D Fs).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (pivotOptions_nonempty s r hs D Fs)
  have hi : ((pivotOptions s r hs D Fs).card : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp
  unfold gain
  apply div_le_one_of_le₀ _ (by linarith)
  exact (div_le_self (inv_nonneg.mpr (by linarith)) (by norm_num : (1 : ℝ) ≤ 3)).trans (hi.trans hp)

def delta : List (Pivot a) → ℝ
  | [] => 1
  | D :: Ds => gain s r hs D (multipliers (sourcePlan s r hs Ds)) * delta Ds

def errorCost : List (Pivot a) → ℕ
  | [] => 0
  | D :: Ds => 1 + (pivotOptions s r hs D (multipliers (sourcePlan s r hs Ds))).card * errorCost Ds

lemma delta_pos (Ds : List (Pivot a)) : 0 < delta s r hs Ds := by
  induction Ds with
  | nil => exact zero_lt_one
  | cons D Ds ih => exact mul_pos (gain_pos s r hs D _) ih

lemma delta_le_one (Ds : List (Pivot a)) : delta s r hs Ds ≤ 1 := by
  induction Ds with
  | nil => exact le_rfl
  | cons D Ds ih =>
    exact (mul_le_mul_of_nonneg_left ih (gain_pos s r hs D _).le).trans (by simpa using gain_le_one s r hs D (multipliers (sourcePlan s r hs Ds)))

variable (S : (D : Pivot a) → ScalarModels D r) (ht : Fin a → ℤ) (τ : ℝ)

 

def runSuccess : List (Pivot a) → Scale a → (Fin a → ℕ) → Prop
  | [], _, _ => True
  | D :: Ds, b, u => ∃ p ∈ (sourcePlan s r hs (D :: Ds)).1,
      outcome D r (multipliers (sourcePlan s r hs Ds)) (S D) ht b p u (u D.index) τ ∧
        runSuccess Ds (scaleRun D 0 p b) u

 
theorem runSuccess_final (Ds : List (Pivot a)) (b : Scale a) (u : Fin a → ℕ)
    (h : runSuccess s r hs S ht τ Ds b u) :
    ∃ p : ChoicePath Ds, Admitted (sourcePlan s r hs Ds) p ∧
      ∀ D ∈ Ds, comparison D r (S D) ht (b * pathMultiplier p) u (u D.index) τ := by
  induction Ds generalizing b with
  | nil => exact ⟨(), True.intro, by simp⟩
  | cons D Ds ih =>
    obtain ⟨p,hp,hhead,htail⟩ := h
    obtain ⟨q,hq,hfinal⟩ := ih (scaleRun D 0 p b) htail
    refine ⟨(p,q), ⟨hp,hq⟩, ?_⟩
    have he : b * pathMultiplier (Ds := D :: Ds) (p,q) =
        scaleRun D 0 p b * pathMultiplier q := by
      change b * (scaleRun D 0 p 1 * pathMultiplier q) = _
      rw [scaleRun_eq_mul D p 0 b, mul_assoc]
    intro E hE
    rw [he]
    rcases List.mem_cons.mp hE with rfl | hE
    · exact hhead (pathMultiplier q) (pathMultiplier_mem _ _ hq)
    · exact hfinal E hE

variable (μ : Measure (Fin a → ℕ)) [IsProbabilityMeasure μ]

 

def stepBounds (η : ℝ) : List (Pivot a) → Scale a → Prop
  | [], _ => True
  | D :: Ds, b =>
      (∀ E : Set (Fin a → ℕ), Earlier D.index E →
        gain s r hs D (multipliers (sourcePlan s r hs Ds)) * μ.real E ≤
          μ.real {u | u ∈ E ∧ success D r s hs (multipliers (sourcePlan s r hs Ds))
            (S D) ht b u (u D.index) τ} + η) ∧
      ∀ p ∈ (sourcePlan s r hs (D :: Ds)).1,
        stepBounds η Ds (scaleRun D 0 p b)

private lemma through_disjointed {i : Fin a} {v : ℕ}
    (f : Fin v → Set (Fin a → ℕ)) (h : ∀ j, Through i (f j)) (j : Fin v) :
    Through i (disjointed f j) := by
  intro u w huw
  simp only [disjointed_eq_inter_compl, Set.mem_inter_iff, Set.mem_iInter,
    Set.mem_compl_iff]
  exact and_congr (h j u w huw) (forall_congr' (fun k => forall_congr' (fun _ => not_congr (h k u w huw))))

 

theorem iterate_mass (Ds : List (Pivot a)) (b : Scale a)
    (horder : Ds.Pairwise (fun D E => D.index < E.index))
    (η : ℝ) (hη : 0 ≤ η) (hsteps : stepBounds s r hs S ht τ μ η Ds b)
    (E : Set (Fin a → ℕ)) (hE : ∀ D ∈ Ds, Earlier D.index E) :
    delta s r hs Ds * μ.real E ≤
      μ.real {u | u ∈ E ∧ runSuccess s r hs S ht τ Ds b u} + errorCost s r hs Ds * η := by
  induction Ds generalizing b E with
  | nil => simp [delta, runSuccess, errorCost]
  | cons D Ds ih =>
    let P := pivotOptions s r hs D (multipliers (sourcePlan s r hs Ds))
    let f : Fin P.card → Path D := fun j => ((Finset.equivFin P).symm j).val
    have hf (j : Fin P.card) : f j ∈ P := ((Finset.equivFin P).symm j).property
    let A (j : Fin P.card) : Set (Fin a → ℕ) := {u | u ∈ E ∧
      outcome D r (multipliers (sourcePlan s r hs Ds)) (S D) ht b (f j) u (u D.index) τ}
    let C := disjointed A
    have hEh : Earlier D.index E := hE D (by simp)
    have hEth : Through D.index E := fun u v hv => hEh u v (fun j hj => hv j hj.le)
    have hCth (j : Fin P.card) : Through D.index (C j) :=
      through_disjointed A (fun j => through_inter hEth (outcome_through D r _ (S D) ht b (f j) τ)) j
    have hlist := List.pairwise_cons.mp horder
    let T (j : Fin P.card) : Set (Fin a → ℕ) := {u | u ∈ C j ∧
      runSuccess s r hs S ht τ Ds (scaleRun D 0 (f j) b) u}
    have htail (j : Fin P.card) : delta s r hs Ds * μ.real (C j) ≤
        μ.real (T j) + errorCost s r hs Ds * η :=
      ih (scaleRun D 0 (f j) b) hlist.2 (hsteps.2 (f j) (hf j)) (C j)
        (fun D' hD' => (hCth j).earlier (hlist.1 D' hD'))
    have hCu : (⋃ j, C j) = {u | u ∈ E ∧
        success D r s hs (multipliers (sourcePlan s r hs Ds)) (S D) ht b u (u D.index) τ} := by
      rw [show (⋃ j, C j) = ⋃ j, A j from iUnion_disjointed]
      ext u
      simp only [Set.mem_iUnion, A, Set.mem_ofPred_eq, success]
      constructor
      · rintro ⟨j,hu,hj⟩
        exact ⟨hu,f j,hf j,hj⟩
      · rintro ⟨hu,p,hp,hp'⟩
        refine ⟨Finset.equivFin P ⟨p,hp⟩,hu,?_⟩
        simpa only [f, Equiv.symm_apply_apply] using hp'
    have hCeq : μ.real (⋃ j, C j) = ∑ j, μ.real (C j) :=
      measureReal_iUnion_fintype (disjoint_disjointed A) (fun j => (Set.to_countable _).measurableSet)
    have hTdisj : Pairwise (Disjoint on T) := by
      intro i j hij
      exact (disjoint_disjointed A hij).mono Set.inter_subset_left Set.inter_subset_left
    have hTeq : μ.real (⋃ j, T j) = ∑ j, μ.real (T j) :=
      measureReal_iUnion_fintype hTdisj (fun j => (Set.to_countable _).measurableSet)
    have hTu : (⋃ j, T j) ⊆ {u | u ∈ E ∧ runSuccess s r hs S ht τ (D :: Ds) b u} := by
      apply Set.iUnion_subset
      intro j u hu
      have hA : u ∈ A j := disjointed_subset A j hu.1
      exact ⟨hA.1,f j,hf j,hA.2,hu.2⟩
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => htail j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    rw [← hCeq, ← hTeq, hCu] at hsum
    have hh := mul_le_mul_of_nonneg_left (hsteps.1 E hEh) (delta_pos s r hs Ds).le
    have hde : delta s r hs Ds * η ≤ η := mul_le_of_le_one_left hη (delta_le_one s r hs Ds)
    have hmono := measureReal_mono (μ := μ) hTu
    change (gain s r hs D (multipliers (sourcePlan s r hs Ds)) * delta s r hs Ds) * μ.real E ≤ _
    simp only [errorCost, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
    dsimp only [P] at hsum
    nlinarith

 

def localEstimates (μs : ℕ → Measure (Fin a → ℕ))
    (Ss : ℕ → (D : Pivot a) → ScalarModels D r) (hts : ℕ → Fin a → ℤ) :
    List (Pivot a) → Scale a → Prop
  | [], _ => True
  | D :: Ds, b =>
      (∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop,
        ∀ E : Set (Fin a → ℕ), Earlier D.index E →
          gain s r hs D (multipliers (sourcePlan s r hs Ds)) * (μs N).real E ≤
            (μs N).real {u | u ∈ E ∧ success D r s hs (multipliers (sourcePlan s r hs Ds))
              (Ss N D) (hts N) b u (u D.index) τ} + ε) ∧
      ∀ p ∈ (sourcePlan s r hs (D :: Ds)).1,
        localEstimates μs Ss hts Ds (scaleRun D 0 p b)

lemma eventually_stepBounds (μs : ℕ → Measure (Fin a → ℕ))
    (Ss : ℕ → (D : Pivot a) → ScalarModels D r) (hts : ℕ → Fin a → ℤ)
    (Ds : List (Pivot a)) (b : Scale a)
    (h : localEstimates s r hs τ μs Ss hts Ds b) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, stepBounds s r hs (Ss N) (hts N) τ (μs N) ε Ds b := by
  induction Ds generalizing b with
  | nil => exact Eventually.of_forall (fun _ => True.intro)
  | cons D Ds ih =>
    let P := (sourcePlan s r hs (D :: Ds)).1
    have ht : ∀ p : P, ∀ᶠ N in atTop,
        stepBounds s r hs (Ss N) (hts N) τ (μs N) ε Ds (scaleRun D 0 p.val b) :=
      fun p => ih _ (h.2 p.val p.property)
    filter_upwards [h.1 ε hε, eventually_all.mpr ht] with N hN hT
    exact ⟨hN, fun p hp => hT ⟨p,hp⟩⟩

 

theorem iterate_eventually (μs : ℕ → Measure (Fin a → ℕ)) [∀ N, IsProbabilityMeasure (μs N)]
    (Ss : ℕ → (D : Pivot a) → ScalarModels D r) (hts : ℕ → Fin a → ℤ)
    (Ds : List (Pivot a)) (b : Scale a)
    (horder : Ds.Pairwise (fun D E => D.index < E.index))
    (h : localEstimates s r hs τ μs Ss hts Ds b) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ E : Set (Fin a → ℕ), (∀ D ∈ Ds, Earlier D.index E) →
      delta s r hs Ds * (μs N).real E ≤
        (μs N).real {u | u ∈ E ∧ runSuccess s r hs (Ss N) (hts N) τ Ds b u} + ε := by
  let η := ε / (errorCost s r hs Ds + 1)
  have hc : (0 : ℝ) < errorCost s r hs Ds + 1 := by positivity
  have hη : 0 < η := div_pos hε hc
  have hcost : (errorCost s r hs Ds : ℝ) * η ≤ ε := by
    have he : η * (errorCost s r hs Ds + 1) = ε := div_mul_cancel₀ _ hc.ne'
    have heta : 0 ≤ η := hη.le
    nlinarith
  filter_upwards [eventually_stepBounds s r hs τ μs Ss hts Ds b h η hη] with N hN
  intro E hE
  exact (iterate_mass s r hs (Ss N) (hts N) τ (μs N) Ds b horder η hη.le hN E hE).trans
    (add_le_add le_rfl hcost)

 

theorem eventual_final_alignment (μs : ℕ → Measure (Fin a → ℕ)) [∀ N, IsProbabilityMeasure (μs N)]
    (Ss : ℕ → (D : Pivot a) → ScalarModels D r) (hts : ℕ → Fin a → ℤ)
    (Ds : List (Pivot a)) (horder : Ds.Pairwise (fun D E => D.index < E.index))
    (h : localEstimates s r hs τ μs Ss hts Ds 1) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N in atTop, delta s r hs Ds ≤
      (μs N).real {u | ∃ b ∈ multipliers (sourcePlan s r hs Ds),
        ∀ D ∈ Ds, comparison D r (Ss N D) (hts N) b u (u D.index) τ} + ε := by
  filter_upwards [iterate_eventually s r hs τ μs Ss hts Ds 1 horder h ε hε] with N hN
  have hm := hN Set.univ (fun D _ => earlier_univ D.index)
  have hsub : {u | u ∈ Set.univ ∧ runSuccess s r hs (Ss N) (hts N) τ Ds 1 u} ⊆
      {u | ∃ b ∈ multipliers (sourcePlan s r hs Ds),
        ∀ D ∈ Ds, comparison D r (Ss N D) (hts N) b u (u D.index) τ} := by
    intro u hu
    obtain ⟨p,hp,hfinal⟩ := runSuccess_final s r hs (Ss N) (hts N) τ Ds 1 u hu.2
    exact ⟨pathMultiplier p, pathMultiplier_mem _ _ hp, by simpa only [one_mul] using hfinal⟩
  simpa only [probReal_univ, mul_one] using hm.trans
    (add_le_add (measureReal_mono hsub) le_rfl)

end SourcePivotPaths

 

 

end
end
end
end

end OAI
