import OAI.Combinatorics.HoneycombChords.ResidualAsymptotics
import OAI.Combinatorics.HoneycombChords.FourFunctions

namespace OAI

/-!
# Ordered integral association and strip coefficient bounds

Formalized from *Critical honeycomb chords with prescribed boundary endpoints*
(OpenAI, September 26, 2026).
-/

section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Honeycomb370 Matrix Finset Set

noncomputable def gramNodeDensity {n : ℕ} (F G : Fin n → ℝ → ℝ) (w : ℝ → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  (evaluationMatrix F x).det * (evaluationMatrix G x).det * ∏ i,w (x i)
noncomputable def errorNodeDensity {n : ℕ} (F G : Fin n → ℝ → ℝ) (H w : ℝ → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  (evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 x)).det *
    (evaluationMatrix G x).det * ∏ i,w (x i)

lemma ordered_eval_nonneg {n : ℕ} (F : Fin n → ℝ → ℝ) (hF : PositiveEvaluation F)
    {x : Fin n → ℝ} (hx : Monotone x) (hx0 : ∀ i,0<x i) :
    0 ≤ (evaluationMatrix F x).det := by
  by_cases hi : Function.Injective x
  · exact (hF x (hx.strictMono_of_injective hi) hx0).le
  · obtain ⟨i,j,he,hne⟩:=Function.not_injective_iff.mp hi
    rw [Matrix.det_zero_of_column_eq hne (show ∀ a,evaluationMatrix F x a i=evaluationMatrix F x a j by
      intro a; simp [evaluationMatrix,he])]

lemma ordered_aug_zero_of_not_strict {n : ℕ} (F : Fin n → ℝ → ℝ) (H : ℝ → ℝ)
    {x : Fin n → ℝ} (hx : Monotone x) (hn : ¬StrictMono x) :
    (evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 x)).det=0 := by
  have hi : ¬Function.Injective x := fun hi ↦ hn (hx.strictMono_of_injective hi)
  obtain ⟨i,j,he,hne⟩:=Function.not_injective_iff.mp hi
  apply Matrix.det_zero_of_column_eq (show i.succ≠j.succ from fun h ↦ hne (Fin.succ_injective _ h))
  intro a
  simp [evaluationMatrix,he]

lemma nodeWeight_lattice {n : ℕ} (w : ℝ → ℝ) (x y : Fin n → ℝ) :
    (∏ i,w (x i))*(∏ i,w (y i))=(∏ i,w ((x⊓y) i))*(∏ i,w ((x⊔y) i)) := by
  rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rcases le_total (x i) (y i) with hi | hi
  · simp [Pi.inf_apply,Pi.sup_apply,min_eq_left hi,max_eq_right hi]
  · simp [Pi.inf_apply,Pi.sup_apply,min_eq_right hi,max_eq_left hi,mul_comm]

lemma gramNodeDensity_lattice {n : ℕ} (F G : Fin n → ℝ → ℝ) (w : ℝ → ℝ)
    (hF : PositiveEvaluation F) (hG : PositiveEvaluation G) (hw : ∀ p,0<p → 0 ≤ w p)
    {x y : Fin n → ℝ} (hx : StrictMono x) (hy : StrictMono y)
    (hx0 : ∀ i,0<x i) (hy0 : ∀ i,0<y i) :
    gramNodeDensity F G w x * gramNodeDensity F G w y ≤
      gramNodeDensity F G w (x⊓y) * gramNodeDensity F G w (x⊔y) := by
  have h₁:=positiveEvaluation_logsupermodular F hF hx0 hy0 hx hy
  have h₂:=positiveEvaluation_logsupermodular G hG hx0 hy0 hx hy
  have hmin : StrictMono (x⊓y) := fun i j hij ↦
    lt_min ((min_le_left _ _).trans_lt (hx hij)) ((min_le_right _ _).trans_lt (hy hij))
  have hmax : StrictMono (x⊔y) := fun i j hij ↦
    max_lt ((hx hij).trans_le (le_max_left _ _)) ((hy hij).trans_le (le_max_right _ _))
  have ha0 i : 0<(x⊓y) i := lt_min (hx0 i) (hy0 i)
  have hb0 i : 0<(x⊔y) i := (hx0 i).trans_le (le_max_left _ _)
  have hh:=mul_le_mul h₁ h₂ (mul_pos (hG x hx hx0) (hG y hy hy0)).le
    (mul_pos (hF _ hmin ha0) (hF _ hmax hb0)).le
  have hp:=mul_le_mul_of_nonneg_right hh
    (show 0 ≤ (∏ i : Fin n,w (x i))*(∏ i : Fin n,w (y i)) from
      mul_nonneg (prod_nonneg (fun i _ ↦ hw _ (hx0 i))) (prod_nonneg (fun i _ ↦ hw _ (hy0 i))))
  have he:=nodeWeight_lattice w x y
  unfold gramNodeDensity
  calc
    _ = ((evaluationMatrix F x).det*(evaluationMatrix F y).det)*
        ((evaluationMatrix G x).det*(evaluationMatrix G y).det)*
        ((∏ i,w (x i))*(∏ i,w (y i))) := by ring
    _ ≤ ((evaluationMatrix F (x⊓y)).det*(evaluationMatrix F (x⊔y)).det)*
        ((evaluationMatrix G (x⊓y)).det*(evaluationMatrix G (x⊔y)).det)*
        ((∏ i,w (x i))*(∏ i,w (y i))) := hp
    _ = _ := by rw [he]; ring

lemma gramNodeDensity_nonneg {n : ℕ} (F G : Fin n → ℝ → ℝ) (w : ℝ → ℝ)
    (hF : PositiveEvaluation F) (hG : PositiveEvaluation G) (hw : ∀ p,0<p → 0 ≤ w p)
    {x : Fin n → ℝ} (hx : Monotone x) (hx0 : ∀ i,0<x i) :
    0 ≤ gramNodeDensity F G w x :=
  mul_nonneg (mul_nonneg (ordered_eval_nonneg F hF hx hx0) (ordered_eval_nonneg G hG hx hx0))
    (prod_nonneg (fun i _ ↦ hw _ (hx0 i)))

/-- A pointwise four-functions inequality for a cross-Gram ensemble with distinct left and right Chebyshev families. -/
theorem ordered_error_four_functions_pointwise {n : ℕ} (F G : Fin n → ℝ → ℝ) (H w r : ℝ → ℝ)
    (hF : PositiveEvaluation F) (hG : PositiveEvaluation G)
    (hA : PositiveEvaluation (Fin.lastCases H F))
    (hcF : ∀ i,Continuous (F i)) (hcH : Continuous H)
    (hU : ∀ x,StrictMono x → (∀ i,0<x i) →
      0 ≤ (evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 x)).det)
    (hw : ∀ p,0<p → 0 ≤ w p) (hr : ∀ p,0<p → 0 ≤ r p)
    (hm : MonotoneOn r (Set.Ioi 0))
    {x y : Fin n → ℝ} (hx : x∈orderedPositive n) (hy : y∈orderedPositive n) :
    errorNodeDensity F G H w x * gramNodeDensity F G (fun p ↦ w p*r p) y ≤
      gramNodeDensity F G w (x⊓y) * errorNodeDensity F G H (fun p ↦ w p*r p) (x⊔y) := by
  have hmax : Monotone (x⊔y) := fun i j hij ↦ max_le_max (hx.1 hij) (hy.1 hij)
  have hmax0 i : 0<(x⊔y) i := (hx.2 i).trans_le (le_max_left _ _)
  have hmin : Monotone (x⊓y) := fun i j hij ↦ min_le_min (hx.1 hij) (hy.1 hij)
  have hmin0 i : 0<(x⊓y) i := lt_min (hx.2 i) (hy.2 i)
  have hUnonneg (z : Fin n → ℝ) (hz : Monotone z) (hz0 : ∀ i,0<z i) (v : ℝ → ℝ)
      (hv : ∀ p,0<p → 0 ≤ v p) : 0 ≤ errorNodeDensity F G H v z := by
    unfold errorNodeDensity
    have he : 0 ≤ (evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 z)).det := by
      by_cases hzmono : StrictMono z
      · exact hU z hzmono hz0
      · rw [ordered_aug_zero_of_not_strict F H hz hzmono]
    exact mul_nonneg (mul_nonneg he (ordered_eval_nonneg G hG hz hz0))
      (prod_nonneg (fun i _ ↦ hv _ (hz0 i)))
  have hright : 0 ≤ gramNodeDensity F G w (x⊓y) * errorNodeDensity F G H (fun p ↦ w p*r p) (x⊔y) :=
    mul_nonneg (gramNodeDensity_nonneg F G w hF hG hw hmin hmin0)
      (hUnonneg _ hmax hmax0 _ (fun p hp ↦ mul_nonneg (hw p hp) (hr p hp)))
  by_cases hxs : StrictMono x
  · by_cases hys : StrictMono y
    · have hb : StrictMono (x⊔y) := fun i j hij ↦
        max_lt ((hxs hij).trans_le (le_max_left _ _)) ((hys hij).trans_le (le_max_right _ _))
      let e (z : Fin n → ℝ) := (evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 z)).det /
        (evaluationMatrix F z).det
      let R (z : Fin n → ℝ) := ∏ i,r (z i)
      have he : e x ≤ e (x⊔y) := augmented_ratio_monotone_zero F H hF hA hcF hcH
        le_sup_left hx.2 hxs hb
      have hrle : R y ≤ R (x⊔y) := Finset.prod_le_prod₀
        (fun i _ ↦ hr _ (hy.2 i)) (fun i _ ↦ hm (hy.2 i) (hmax0 i) (le_max_right _ _))
      have hD := gramNodeDensity_lattice F G w hF hG hw hxs hys hx.2 hy.2
      have he0 : 0 ≤ e x := div_nonneg (hU x hxs hx.2) (hF x hxs hx.2).le
      have hR0 : 0 ≤ R y := prod_nonneg (fun i _ ↦ hr _ (hy.2 i))
      have hm₁:=mul_le_mul he hrle hR0 (he0.trans he)
      have hm₂:=mul_le_mul hD hm₁ (mul_nonneg he0 hR0)
        (mul_nonneg (gramNodeDensity_nonneg F G w hF hG hw hmin hmin0)
          (gramNodeDensity_nonneg F G w hF hG hw hmax hmax0))
      have hFx: (evaluationMatrix F x).det≠0 := (hF x hxs hx.2).ne'
      have hFb: (evaluationMatrix F (x⊔y)).det≠0 := (hF _ hb hmax0).ne'
      dsimp [e,R,gramNodeDensity] at hm₂
      simp only [Finset.prod_mul_distrib,errorNodeDensity,gramNodeDensity]
      field_simp at hm₂ ⊢
      simp only [Pi.inf_apply,Pi.sup_apply] at hm₂ ⊢
      nlinarith only [hm₂]
    · have hz : (evaluationMatrix F y).det=0 := by
        have hi : ¬Function.Injective y := fun hi ↦ hys (hy.1.strictMono_of_injective hi)
        obtain ⟨i,j,he,hne⟩:=Function.not_injective_iff.mp hi
        exact Matrix.det_zero_of_column_eq hne (fun a ↦ by simp [evaluationMatrix,he])
      simpa [gramNodeDensity,hz] using hright
  · have hz:=ordered_aug_zero_of_not_strict F H hx.1 hxs
    simpa [errorNodeDensity,hz] using hright

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace Honeycomb370
open MeasureTheory Set Finset Equiv
open CriticalHoneycomb.FiniteFunctional.StripAsymptotic

lemma orderedPositive_measurable (n : ℕ) : MeasurableSet (orderedPositive n) := by
  rw [orderedPositive_eq_iUnion]
  exact MeasurableSet.iUnion (fun m ↦ (orderedBox_closed _ _ _).measurableSet)

lemma unique_sorting_perm {n : ℕ} (x : Fin n → ℝ) (hi : Function.Injective x) :
    ∃! σ : Perm (Fin n),Monotone (x ∘ σ) := by
  obtain ⟨d,σ,hd,he⟩:=sorted_injective_real hi
  have hs : x ∘ σ.symm=d := by funext i; simp [he,Function.comp_def]
  refine ⟨σ.symm,by change Monotone (x ∘ σ.symm); rw [hs]; exact hd.monotone,?_⟩
  intro τ ht
  have htt : StrictMono (x ∘ τ) := ht.strictMono_of_injective (hi.comp τ.injective)
  have hr : Set.range (x ∘ τ)=Set.range d := by
    rw [Set.range_comp,τ.surjective.range_eq,Set.image_univ,he,Set.range_comp,σ.surjective.range_eq,Set.image_univ]
  have hf : x ∘ τ=d := (htt.range_inj_of_wellFoundedLT hd).mp hr
  apply Equiv.ext
  intro i
  apply hi
  exact (congrFun hf i).trans (congrFun hs i).symm

lemma symmetric_ordered_indicator_sum {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hperm : ∀ x (σ : Perm (Fin n)),f (x ∘ σ)=f x)
    (hzero : ∀ x,¬Function.Injective x → f x=0) (x : Fin n → ℝ) :
    (∑ σ : Perm (Fin n),(orderedPositive n).indicator f (x ∘ σ))=
      (Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0:ℝ))).indicator f x := by
  classical
  by_cases hp : ∀ i,0<x i
  · have hxp : x∈Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0:ℝ)) := by simpa
    rw [Set.indicator_of_mem hxp]
    by_cases hi : Function.Injective x
    · obtain ⟨σ,hσ,hu⟩:=unique_sorting_perm x hi
      rw [Finset.sum_eq_single σ]
      · rw [Set.indicator_of_mem (show (x ∘ σ)∈orderedPositive n from ⟨hσ,fun i ↦ hp (σ i)⟩),hperm]
      · intro τ hτ hne
        apply Set.indicator_of_notMem
        intro hh
        exact hne (hu τ hh.1)
      · simp
    · have hz:=hzero x hi
      rw [hz]
      apply sum_eq_zero
      intro σ hσ
      by_cases hmem : (x ∘ σ)∈orderedPositive n
      · rw [Set.indicator_of_mem hmem,hperm,hz]
      · exact Set.indicator_of_notMem hmem _
  · have hxp : x∉Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0:ℝ)) := by simpa only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_Ioi] using hp
    rw [Set.indicator_of_notMem hxp]
    apply sum_eq_zero
    intro σ hσ
    apply Set.indicator_of_notMem
    rintro ⟨_,hh⟩
    apply hp
    intro i
    simpa using hh (σ.symm i)

lemma integral_perm {n : ℕ} (f : (Fin n → ℝ) → ℝ) (σ : Perm (Fin n)) :
    (∫ x,f (x ∘ σ))=∫ x,f x := by
  have h:= (volume_measurePreserving_piCongrLeft (fun _ : Fin n ↦ ℝ) σ.symm).integral_comp'
    f
  simpa [MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft',Function.comp_def] using h

/-- The ordered chamber has exactly one representative of every noncollision
orbit. The integrand vanishes on collision configurations. -/
theorem integral_symmetric_ordered {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (hperm : ∀ x (σ : Perm (Fin n)),f (x ∘ σ)=f x)
    (hzero : ∀ x,¬Function.Injective x → f x=0)
    (hi : IntegrableOn f (orderedPositive n)) :
    (∫ x in Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0:ℝ)),f x)=
      (Fintype.card (Perm (Fin n)):ℝ)*(∫ x in orderedPositive n,f x) := by
  classical
  rw [←integral_indicator (MeasurableSet.univ_pi (fun _ ↦ measurableSet_Ioi))]
  simp_rw [←symmetric_ordered_indicator_sum f hperm hzero]
  rw [integral_finsetSum]
  · simp_rw [integral_perm,integral_indicator (orderedPositive_measurable n)]
    simp
  · intro σ hσ
    have hh:=hi.integrable_indicator (orderedPositive_measurable n)
    have hp:=(volume_measurePreserving_piCongrLeft (fun _ : Fin n ↦ ℝ) σ.symm).integrable_comp_emb
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ ℝ) σ.symm).measurableEmbedding (g := (orderedPositive n).indicator f)
    simpa [MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft',Function.comp_def] using hp.mpr hh

end Honeycomb370

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Honeycomb370 MeasureTheory Set Finset

lemma gramNodeDensity_continuousOn {n : ℕ} (F G : Fin n → ℝ → ℝ) (w : ℝ → ℝ)
    (hF : ∀ i,Continuous (F i)) (hG : ∀ i,Continuous (G i))
    (hw : ContinuousOn w (Set.Ioi 0)) : ContinuousOn (gramNodeDensity F G w) (orderedPositive n) := by
  apply ContinuousOn.mul
  · apply Continuous.continuousOn
    unfold evaluationMatrix
    fun_prop
  · apply continuousOn_finsetProd
    intro i _
    exact hw.comp (continuous_apply i).continuousOn (fun x hx ↦ hx.2 i)

lemma errorNodeDensity_continuousOn {n : ℕ} (F G : Fin n → ℝ → ℝ) (H w : ℝ → ℝ)
    (hF : ∀ i,Continuous (F i)) (hG : ∀ i,Continuous (G i)) (hH : Continuous H)
    (hw : ContinuousOn w (Set.Ioi 0)) : ContinuousOn (errorNodeDensity F G H w) (orderedPositive n) := by
  have ha : ∀ i,Continuous (Fin.lastCases H F i) := by
    intro i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa using hH
    · simpa using hF j
  apply ContinuousOn.mul
  · apply Continuous.continuousOn
    unfold evaluationMatrix
    have he : Continuous (fun x : Fin n → ℝ ↦ (Fin.cons (0:ℝ) x : Fin (n+1) → ℝ)) := continuous_pi (fun i ↦ by
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · simpa only [Fin.cons_zero] using (continuous_const : Continuous (fun _ : Fin n → ℝ ↦ (0:ℝ)))
      · simpa only [Fin.cons_succ] using (continuous_apply j : Continuous (fun x : Fin n → ℝ ↦ x j)))
    exact ((continuous_matrix fun i j ↦ (ha i).comp ((continuous_apply j).comp he)).matrix_det).mul
      ((continuous_matrix fun i j ↦ (hG i).comp (continuous_apply j)).matrix_det)
  · apply continuousOn_finsetProd
    intro i _
    exact hw.comp (continuous_apply i).continuousOn (fun x hx ↦ hx.2 i)

lemma errorNodeDensity_nonneg {n : ℕ} (F G : Fin n → ℝ → ℝ) (H w : ℝ → ℝ)
    (hG : PositiveEvaluation G)
    (hU : ∀ x,StrictMono x → (∀ i,0<x i) →
      0 ≤ (evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 x)).det)
    (hw : ∀ p,0<p → 0 ≤ w p) {x : Fin n → ℝ} (hx : x∈orderedPositive n) :
    0 ≤ errorNodeDensity F G H w x := by
  unfold errorNodeDensity
  have he : 0 ≤ (evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 x)).det := by
    by_cases hs : StrictMono x
    · exact hU x hs hx.2
    · rw [ordered_aug_zero_of_not_strict F H hx.1 hs]
  exact mul_nonneg (mul_nonneg he (ordered_eval_nonneg G hG hx.1 hx.2))
    (prod_nonneg (fun i _ ↦ hw _ (hx.2 i)))

/-- Ordered association comparison for a nonsymmetric Gram ensemble with positive evaluations and integrable pairings. -/
theorem ordered_error_association {n : ℕ} (F G : Fin n → ℝ → ℝ) (H w r : ℝ → ℝ)
    (hF : PositiveEvaluation F) (hG : PositiveEvaluation G)
    (hA : PositiveEvaluation (Fin.lastCases H F))
    (hcF : ∀ i,Continuous (F i)) (hcG : ∀ i,Continuous (G i)) (hcH : Continuous H)
    (hcw : ContinuousOn w (Set.Ioi 0)) (hcr : ContinuousOn r (Set.Ioi 0))
    (hU : ∀ x,StrictMono x → (∀ i,0<x i) →
      0 ≤ (evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 x)).det)
    (hw : ∀ p,0<p → 0 ≤ w p) (hr : ∀ p,0<p → 0 ≤ r p)
    (hm : MonotoneOn r (Set.Ioi 0))
    (hi₁ : IntegrableOn (errorNodeDensity F G H w) (orderedPositive n))
    (hi₂ : IntegrableOn (gramNodeDensity F G (fun p ↦ w p*r p)) (orderedPositive n))
    (hi₃ : IntegrableOn (gramNodeDensity F G w) (orderedPositive n))
    (hi₄ : IntegrableOn (errorNodeDensity F G H (fun p ↦ w p*r p)) (orderedPositive n)) :
    (∫ x in orderedPositive n,errorNodeDensity F G H w x)*
      (∫ x in orderedPositive n,gramNodeDensity F G (fun p ↦ w p*r p) x) ≤
    (∫ x in orderedPositive n,gramNodeDensity F G w x)*
      (∫ x in orderedPositive n,errorNodeDensity F G H (fun p ↦ w p*r p) x) := by
  exact orderedPositive_four_functions n _ _ _ _
    (errorNodeDensity_continuousOn F G H w hcF hcG hcH hcw)
    (gramNodeDensity_continuousOn F G _ hcF hcG (hcw.mul hcr))
    (gramNodeDensity_continuousOn F G w hcF hcG hcw)
    (errorNodeDensity_continuousOn F G H _ hcF hcG hcH (hcw.mul hcr))
    hi₁ hi₂ hi₃ hi₄
    (fun x hx ↦ errorNodeDensity_nonneg F G H w hG hU hw hx)
    (fun x hx ↦ gramNodeDensity_nonneg F G _ hF hG (fun p hp ↦ mul_nonneg (hw p hp) (hr p hp)) hx.1 hx.2)
    (fun x hx ↦ gramNodeDensity_nonneg F G w hF hG hw hx.1 hx.2)
    (fun x hx ↦ errorNodeDensity_nonneg F G H _ hG hU (fun p hp ↦ mul_nonneg (hw p hp) (hr p hp)) hx)
    (fun x hx y hy ↦ ordered_error_four_functions_pointwise F G H w r hF hG hA hcF hcH hU hw hr hm hx hy)

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix Finset Filter Topology

lemma power_det_nonneg_nonnegative {n : ℕ} (e : Fin n → ℕ) (v : Fin n → ℝ)
    (he : StrictMono e) (hv : StrictMono v) (hv0 : ∀ i,0≤v i) :
    0≤Matrix.det (fun i j=>v j^e i) := by
  let f : ℝ → ℝ := fun t=>Matrix.det (fun i j=> (v j+t)^e i)
  have hc : Continuous f := by unfold f;fun_prop
  have hp : ∀ᶠ t in 𝓝[>] (0:ℝ),0≤f t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply (power_det_pos e (fun j=>v j+t) he _ _).le
    · intro i j hij
      change v i+t<v j+t
      linarith [hv hij]
    · intro i
      exact add_pos_of_nonneg_of_pos (hv0 i) ht
  have h:=ge_of_tendsto (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hp
  simpa only [f,add_zero] using h

lemma translated_kernel_minor_pair_nonneg {n : ℕ} {a R : ℝ}
    (ha : 0≤a) (hR : 0<R) (hphase : Real.sqrt R*Real.sqrt a<Real.pi/2)
    (b : ℕ → ℝ) (hb : Monotone (fun i : Fin n=>b i))
    (hball : ∀ i,0≤b i ∧ b i≤R) (v : Fin n → ℝ)
    (hv : StrictMono v) (hv0 : ∀ i,0≤v i) (e : Fin n → ℕ) :
    0≤Matrix.det (fun i j : Fin n=>cosineKernelJet (nodalOrder b j) (e i) (b j) (-a))*
      Matrix.det (fun i j=>v j^e i) := by
  classical
  by_cases hi : Function.Injective e
  · obtain ⟨d,σ,hd,he⟩:=sorted_injective_exponents hi
    rw [he]
    let A : Matrix (Fin n) (Fin n) ℝ := fun i j=>cosineKernelJet (nodalOrder b j) (d i) (b j) (-a)
    let B : Matrix (Fin n) (Fin n) ℝ := fun i j=>v j^d i
    change 0≤(A.submatrix σ id).det*(B.submatrix σ id).det
    rw [Matrix.det_permute,Matrix.det_permute]
    have hA:=translated_beta_jet_det_nonneg ha hR hphase b hb hball d hd
    have hB:=power_det_nonneg_nonnegative d v hd hv hv0
    have hp:=mul_nonneg (sq_nonneg (((Equiv.Perm.sign σ:ℤ):ℝ))) (mul_nonneg hA hB)
    dsimp [A,B] at *
    nlinarith only [hp]
  · obtain ⟨i,j,heq,hij⟩:=Function.not_injective_iff.mp hi
    have hz : Matrix.det (fun i j : Fin n=>cosineKernelJet (nodalOrder b j) (e i) (b j) (-a))=0 := by
      apply Matrix.det_zero_of_row_eq hij
      change (fun j : Fin n=>cosineKernelJet (nodalOrder b j) (e i) (b j) (-a))=
        (fun k : Fin n=>cosineKernelJet (nodalOrder b k) (e j) (b k) (-a))
      rw [heq]
    rw [hz,zero_mul]

lemma translated_kernel_det_nonneg {n : ℕ} {a R : ℝ}
    (ha : 0≤a) (hR : 0<R) (hphase : Real.sqrt R*Real.sqrt a<Real.pi/2)
    (b : ℕ → ℝ) (hb : Monotone (fun i : Fin n=>b i))
    (hball : ∀ i,0≤b i ∧ b i≤R) (v : Fin n → ℝ)
    (hv : StrictMono v) (hv0 : ∀ i,0≤v i) :
    0≤Matrix.det (fun i j : Fin n=>cosineKernelJet (nodalOrder b i) 0 (b i) (-a+v j)) := by
  let A (m : ℕ) : Matrix (Fin n) (Fin m) ℝ := fun i k=>cosineKernelJet (nodalOrder b i) k (b i) (-a)
  let B (m : ℕ) : Matrix (Fin m) (Fin n) ℝ := fun k j=>v j^k.val
  have hp (m : ℕ) : 0≤(A m*B m).det := by
    have hsum : 0≤∑ f : Fin n → Fin m,((A m).submatrix id f).det * ((B m).submatrix f id).det := by
      apply sum_nonneg
      intro f _
      rw [←Matrix.det_transpose ((A m).submatrix id f)]
      exact translated_kernel_minor_pair_nonneg ha hR hphase b hb hball v hv hv0 (fun i=>(f i).val)
    rw [det_rectangular_binet] at hsum
    have hc : (0:ℝ)<Fintype.card (Equiv.Perm (Fin n)) := by
      exact_mod_cast (Fintype.card_pos : 0<Fintype.card (Equiv.Perm (Fin n)))
    nlinarith only [hsum,hc]
  have ht : Tendsto (fun m=>A m*B m) atTop
      (𝓝 (fun i j : Fin n=>cosineKernelJet (nodalOrder b i) 0 (b i) (-a+v j))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have h := (cosineKernelJet_translation_summable (nodalOrder b i) (b i) (-a) (v j)).hasSum.tendsto_sum_nat
    rw [←cosineKernelJet_translation] at h
    convert h using 1
    · funext m
      change (∑ k : Fin m,cosineKernelJet (nodalOrder b i) k (b i) (-a)*(v j)^k.val)=_
      exact Fin.sum_univ_eq_sum_range (fun k : ℕ=>cosineKernelJet (nodalOrder b i) k (b i) (-a)*(v j)^k) m
  exact ge_of_tendsto ((continuous_id.matrix_det).continuousAt.tendsto.comp ht) (Eventually.of_forall hp)

lemma residual_det_augment_at {n : ℕ} (F : Fin n → ℝ → ℝ) (H : ℝ → ℝ)
    (a : ℝ) (hH : H a≠0) (x : Fin n → ℝ) :
    (-1:ℝ)^n * H a * (evaluationMatrix (residualFamily F H a) x).det =
      (evaluationMatrix (Fin.lastCases H F) (Fin.cons a x)).det := by
  let B:=evaluationMatrix (Fin.lastCases H F) (Fin.cons a x)
  let A:=evaluationMatrix (Fin.lastCases H (residualFamily F H a)) (Fin.cons a x)
  let c : Fin (n+1) → ℝ := Fin.lastCases 0 (fun i=> -F i a/H a)
  have he : A.det=B.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const c (Fin.last n) (by simp [c])
    intro i j
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simp [A,B,c,evaluationMatrix]
    · simp only [A,B,c,evaluationMatrix,Fin.lastCases_castSucc,Fin.lastCases_last,residualFamily]
      ring
  rw [Matrix.det_succ_column_zero,Fin.sum_univ_castSucc] at he
  have hz : (∑ i : Fin n,(-1:ℝ)^(i.castSucc.val)*A i.castSucc 0*
      (A.submatrix i.castSucc.succAbove Fin.succ).det)=0 := by
    apply sum_eq_zero
    intro i _
    simp [A,evaluationMatrix,residualFamily,hH]
  rw [hz,zero_add] at he
  have hm : A.submatrix (Fin.last n).succAbove Fin.succ=
      evaluationMatrix (residualFamily F H a) x := by
    ext i j
    simp [A,Matrix.submatrix,evaluationMatrix,Fin.succAbove_last]
  simpa only [hm,A,B,evaluationMatrix,Fin.lastCases_last,Fin.cons_zero,Fin.val_last] using he

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Honeycomb370 MeasureTheory Set Matrix Finset

lemma familyPointDensity_integrable_ordered {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (hi : ∀ i j,IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    IntegrableOn (familyPointDensity w F G) (orderedPositive n) := by
  have hh:=(family_gram_andreief w F G hi).1
  rw [←Measure.restrict_pi_pi] at hh
  change IntegrableOn (familyPointDensity w F G) (Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0:ℝ))) at hh
  exact hh.mono_set (fun x hx i hi ↦ hx.2 i)

/-- Exact ordered Andreief identity for distinct left and right families. -/
theorem familyGram_ordered_integral {n : ℕ} (w : ℝ → ℝ) (F G : Fin n → ℝ → ℝ)
    (hi : ∀ i j,IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*w p) (Set.Ioi 0)) :
    (∫ p in orderedPositive n,familyPointDensity w F G p)=(familyGram w F G).det := by
  have ha:=(family_gram_andreief w F G hi).2
  have ho:=integral_symmetric_ordered (familyPointDensity w F G)
    (familyPointDensity_perm w F G) (familyPointDensity_eq_zero_of_not_injective w F G)
    (familyPointDensity_integrable_ordered w F G hi)
  rw [←Measure.restrict_pi_pi] at ha
  have he : (Fintype.card (Equiv.Perm (Fin n)):ℝ)*(∫ p in orderedPositive n,familyPointDensity w F G p)=
      (Fintype.card (Equiv.Perm (Fin n)):ℝ)*(familyGram w F G).det := ho.symm.trans ha
  exact (mul_left_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) he

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Honeycomb370 MeasureTheory Set Matrix Finset

lemma PositiveEvaluation.square {n : ℕ} {F : Fin n → ℝ → ℝ} (hF : PositiveEvaluation F) :
    PositiveEvaluation (fun i p ↦ F i (p^2)) := by
  intro p hp hp0
  exact hF (fun i ↦ (p i)^2) (fun i j hij ↦ (sq_lt_sq₀ (hp0 i).le (hp0 j).le).mpr (hp hij))
    (fun i ↦ sq_pos_of_pos (hp0 i))

lemma gramNodeDensity_square {n : ℕ} (F G : Fin n → ℝ → ℝ) (w : ℝ → ℝ) (p : Fin n → ℝ) :
    gramNodeDensity (fun i p ↦ F i (p^2)) (fun i p ↦ G i (p^2)) w p=familyPointDensity w F G p := by
  unfold gramNodeDensity familyPointDensity evaluationMatrix
  ring

lemma errorNodeDensity_square {n : ℕ} (F G : Fin n → ℝ → ℝ) (H w : ℝ → ℝ)
    (hH : H 0≠0) (p : Fin n → ℝ) :
    errorNodeDensity (fun i p ↦ F i (p^2)) (fun i p ↦ G i (p^2)) (fun p ↦ H (p^2)) w p=
      ((-1:ℝ)^n*H 0)*familyPointDensity w (residualFamily F H 0) G p := by
  have he : evaluationMatrix (Fin.lastCases (fun p ↦ H (p^2)) (fun i p ↦ F i (p^2))) (Fin.cons 0 p)=
      evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 (fun i ↦ (p i)^2)) := by
    ext i j
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp [evaluationMatrix]
  unfold errorNodeDensity
  rw [he,←residual_det_augment_at F H 0 hH]
  unfold familyPointDensity evaluationMatrix
  ring

/-- The actual negative coefficient can only increase when the weight is
multiplied by an increasing ratio. Left and right systems are kept distinct. -/
theorem negative_meanResidualRatio_compare (N : ℕ) (F G : Fin (2*N+1) → ℝ → ℝ)
    (H w r : ℝ → ℝ) (hF : PositiveEvaluation F) (hG : PositiveEvaluation G)
    (hA : PositiveEvaluation (Fin.lastCases H F))
    (hcF : ∀ i,Continuous (F i)) (hcG : ∀ i,Continuous (G i)) (hcH : Continuous H)
    (hcw : ContinuousOn w (Set.Ioi 0)) (hcr : ContinuousOn r (Set.Ioi 0))
    (hU : ∀ x,StrictMono x → (∀ i,0<x i) →
      0 ≤ (evaluationMatrix (Fin.lastCases H F) (Fin.cons 0 x)).det)
    (hw : ∀ p,0<p → 0 ≤ w p) (hr : ∀ p,0<p → 0 ≤ r p)
    (hm : MonotoneOn r (Set.Ioi 0)) (hH : 0<H 0)
    (hi : ∀ i j,IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hi' : ∀ i j,IntegrableOn (fun p ↦ F i (p^2)*G j (p^2)*(w p*r p)) (Set.Ioi 0))
    (hH₁ : ∀ j,IntegrableOn (fun p ↦ H (p^2)*G j (p^2)*w p) (Set.Ioi 0))
    (hH₂ : ∀ j,IntegrableOn (fun p ↦ H (p^2)*G j (p^2)*(w p*r p)) (Set.Ioi 0))
    (hd : 0<(familyGram w F G).det) (hd' : 0<(familyGram (fun p ↦ w p*r p) F G).det) :
    -meanResidualRatio w F G H 0 ≤ -meanResidualRatio (fun p ↦ w p*r p) F G H 0 := by
  let f : Fin (2*N+1) → ℝ → ℝ := fun i p ↦ F i (p^2)
  let g : Fin (2*N+1) → ℝ → ℝ := fun i p ↦ G i (p^2)
  let h : ℝ → ℝ := fun p ↦ H (p^2)
  have hAp : PositiveEvaluation (Fin.lastCases h f) := by
    convert hA.square using 1
    funext i p
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp [h,f]
  have hUp (x : Fin (2*N+1) → ℝ) (hx : StrictMono x) (hx0 : ∀ i,0<x i) :
      0 ≤ (evaluationMatrix (Fin.lastCases h f) (Fin.cons 0 x)).det := by
    convert hU (fun i ↦ (x i)^2)
      (fun i j hij ↦ (sq_lt_sq₀ (hx0 i).le (hx0 j).le).mpr (hx hij)) (fun i ↦ sq_pos_of_pos (hx0 i)) using 1
    congr 1
    ext i j
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp [f,h,evaluationMatrix]
  have hD (v : ℝ → ℝ) : gramNodeDensity f g v=familyPointDensity v F G := funext (gramNodeDensity_square F G v)
  have hE (v : ℝ → ℝ) : errorNodeDensity f g h v=fun p ↦ -(H 0)*familyPointDensity v (residualFamily F H 0) G p := by
    funext p
    rw [errorNodeDensity_square F G H v hH.ne']
    simp [pow_add,pow_mul]
  have hiR:=residualFamily_pair_integrable w F G H 0 hi hH₁
  have hiR':=residualFamily_pair_integrable (fun p ↦ w p*r p) F G H 0 hi' hH₂
  have hcompare:=ordered_error_association f g h w r hF.square hG.square hAp
    (fun i ↦ (hcF i).comp (continuous_id.pow 2)) (fun i ↦ (hcG i).comp (continuous_id.pow 2))
    (hcH.comp (continuous_id.pow 2)) hcw hcr hUp hw hr hm
    (by rw [hE]; exact (familyPointDensity_integrable_ordered w _ G hiR).const_mul _)
    (by rw [hD]; exact familyPointDensity_integrable_ordered _ F G hi')
    (by rw [hD]; exact familyPointDensity_integrable_ordered _ F G hi)
    (by rw [hE]; exact (familyPointDensity_integrable_ordered _ _ G hiR').const_mul _)
  simp_rw [hD,hE,integral_const_mul,familyGram_ordered_integral w F G hi,
    familyGram_ordered_integral _ F G hi',familyGram_ordered_integral w _ G hiR,
    familyGram_ordered_integral _ _ G hiR'] at hcompare
  unfold meanResidualRatio
  rw [←neg_div,←neg_div]
  apply (div_le_div_iff₀ hd hd').mpr
  nlinarith only [hcompare,hH]

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

/-! The strip weight has an increasing ratio to the hyperbolic secant comparison weight. -/
namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Real

private noncomputable def ratioP (u : ℝ) : ℝ := (2*u-1)*(4*u^2-3)
private noncomputable def ratioQ (u : ℝ) : ℝ := 2*u^2-1
private noncomputable def ratioE (v : ℝ) : ℝ := 11*v+64*v^2+142*v^3+104*v^4+24*v^5
private noncomputable def sechRatio (x : ℝ) : ℝ :=
  x*ratioP (Real.cosh x)/(4*Real.sinh x*ratioQ (Real.cosh x))

private lemma ratioP_pos {u : ℝ} (hu : 1≤u) : 0<ratioP u := by
  unfold ratioP
  apply mul_pos <;> nlinarith [sq_nonneg (u-1)]
private lemma ratioQ_pos {u : ℝ} (hu : 1≤u) : 0<ratioQ u := by
  unfold ratioQ
  nlinarith [sq_nonneg (u-1)]
private lemma ratioE_nonneg {v : ℝ} (hv : 0≤v) : 0≤ratioE v := by
  unfold ratioE
  positivity

private lemma sechRatio_derivative {x : ℝ} (hx : 0<x) :
    HasDerivAt sechRatio
      ((ratioP (Real.cosh x)*ratioQ (Real.cosh x)*(Real.sinh x-x)+
        x*ratioE (Real.cosh x-1))/(4*(Real.sinh x*ratioQ (Real.cosh x))^2)) x := by
  have hs : Real.sinh x≠0 := (Real.sinh_pos_iff.mpr hx).ne'
  have hq : ratioQ (Real.cosh x)≠0 := (ratioQ_pos (Real.one_le_cosh x)).ne'
  have hp : HasDerivAt (fun u ↦ ratioP (Real.cosh u))
      ((24*(Real.cosh x)^2-8*Real.cosh x-6)*Real.sinh x) x := by
    convert! (((Real.hasDerivAt_cosh x).const_mul 2).sub_const 1).mul
      ((((Real.hasDerivAt_cosh x).pow 2).const_mul 4).sub_const 3) using 1; first | rfl | (simp only [Pi.pow_apply]; ring)
  have hq' : HasDerivAt (fun u ↦ ratioQ (Real.cosh u))
      (4*Real.cosh x*Real.sinh x) x := by
    convert! (((Real.hasDerivAt_cosh x).pow 2).const_mul 2).sub_const 1 using 1; first | rfl | (norm_num [ratioQ,Pi.pow_apply]; ring)
  have h := ((hasDerivAt_id x).mul hp).div
    (((Real.hasDerivAt_sinh x).const_mul 4).mul hq') (by exact mul_ne_zero (mul_ne_zero (by norm_num) hs) hq)
  apply h.congr_deriv
  dsimp [ratioP,ratioQ,ratioE]
  have he := Real.cosh_sq_sub_sinh_sq x
  have hq0 : 2*(Real.cosh x)^2-1 ≠ 0 := hq
  have hsq : (Real.sinh x)^2=(Real.cosh x)^2-1 := by linarith
  field_simp [hs,hq0]
  ring_nf
  simp only [hsq]
  ring

private lemma sechRatio_monotone : MonotoneOn sechRatio (Set.Ioi 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi 0)
    (fun x hx ↦ (sechRatio_derivative hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (sechRatio_derivative (by simpa using hx)).hasDerivWithinAt)
  intro x hx
  have hx : 0<x := by simpa using hx
  have hp:=ratioP_pos (Real.one_le_cosh x)
  have hq:=ratioQ_pos (Real.one_le_cosh x)
  have hs : 0≤Real.sinh x-x := sub_nonneg.mpr (Real.self_le_sinh_iff.mpr hx.le)
  have he:=ratioE_nonneg (sub_nonneg.mpr (Real.one_le_cosh x))
  positivity

private lemma sinh_four (x : ℝ) :
    Real.sinh (4*x)=4*Real.sinh x*Real.cosh x*(2*(Real.cosh x)^2-1) := by
  rw [show 4*x=2*(2*x) by ring,Real.sinh_two_mul,Real.sinh_two_mul,Real.cosh_two_mul]
  linear_combination -4*Real.sinh x*Real.cosh x*(Real.cosh_sq_sub_sinh_sq x)

lemma strip_sech_ratio_eq {p : ℝ} (hp : 0<p) :
    stripDensity p * Real.cosh (3*angle*p) = sechRatio (angle*p)/angle := by
  have hc : Real.cosh (angle*p)≠0 := (Real.cosh_pos _).ne'
  have ha : angle≠0 := ne_of_gt strip_angle_pos
  rw [stripDensity,show 4*angle*p=4*(angle*p) by ring,sinh_four,
    show 3*angle*p=3*(angle*p) by ring,Real.cosh_three_mul]
  dsimp [sechRatio,ratioP,ratioQ]
  field_simp

/-- The ratio of the strip density to `1/cosh(3λp)` is increasing for positive `p`. -/
theorem strip_sech_ratio_monotone :
    MonotoneOn (fun p ↦ stripDensity p * Real.cosh (3*angle*p)) (Set.Ioi 0) := by
  intro p hp q hq hpq
  dsimp only
  rw [strip_sech_ratio_eq hp,strip_sech_ratio_eq hq]
  apply div_le_div_of_nonneg_right _ strip_angle_pos.le
  exact sechRatio_monotone (mul_pos strip_angle_pos hp) (mul_pos strip_angle_pos hq)
    (mul_le_mul_of_nonneg_left hpq strip_angle_pos.le)

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory

lemma strip_coefficient_compare (N : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    -meanResidualRatio (sechProbDensity (3*angle)) (fixedFamily N) (stripJetFamily N t)
      (fun x ↦ (C (3*angle/2) x).re) 0 ≤
    -meanResidualRatio stripDensity (fixedFamily N) (stripJetFamily N t)
      (fun x ↦ (C (3*angle/2) x).re) 0 := by
  let w:=sechProbDensity (3*angle)
  let r:=fun p ↦ (stripDensity p*Real.cosh (3*angle*p))*(Real.pi/(6*angle))
  have ha:=strip_angle_pos
  have hwr : (fun p ↦ w p*r p)=stripDensity := by
    funext p
    dsimp [w,r,sechProbDensity]
    field_simp [(Real.cosh_pos (3*angle*p)).ne',ha.ne',Real.pi_ne_zero]
    ring
  have hcF i : Continuous (fixedFamily N i) := (cosineKernelJet_contDiff_right _ 0 _ 0).continuous
  have hcG i : Continuous (stripJetFamily N t i) := (cosineKernelJet_contDiff_right _ 0 _ 0).continuous
  have hcH : Continuous (fun x ↦ (C (3*angle/2) x).re) := by
    simp_rw [cThree_real]
    exact (cosineKernelJet_contDiff_right 0 0 _ 0).continuous
  have hcw : ContinuousOn w (Set.Ioi 0) := by
    apply Continuous.continuousOn
    change Continuous (fun p : ℝ ↦ (2*(3*angle)/Real.pi)/Real.cosh ((3*angle)*p))
    exact continuous_const.div (Real.continuous_cosh.comp (continuous_const.mul continuous_id))
      (fun x ↦ (Real.cosh_pos _).ne')
  have hcr : ContinuousOn r (Set.Ioi 0) := by
    intro p hp
    have hp : 0<p := hp
    dsimp [r,stripDensity]
    have hs : Real.sinh (4*angle*p)≠0 := (Real.sinh_pos_iff.mpr (by positivity)).ne'
    fun_prop
  have hr p (hp : 0<p) : 0 ≤ r p := by
    dsimp [r]
    exact mul_nonneg (mul_nonneg (stripDensity_pos hp).le (Real.cosh_pos _).le) (by positivity)
  have hm : MonotoneOn r (Set.Ioi 0) := by
    intro p hp q hq hpq
    exact mul_le_mul_of_nonneg_right (strip_sech_ratio_monotone hp hq hpq) (by positivity)
  have hB i : interiorKnotLabels N (angle/2) i ≤ (3*angle/2)^2 :=
    (interiorKnot_le N i (half_pos ha) (by linarith)).trans (by nlinarith [sq_nonneg angle])
  have hC i := interiorKnot_le N i ht htL
  have hi i j : IntegrableOn (fun p ↦ fixedFamily N i (p^2)*stripJetFamily N t j (p^2)*w p) (Set.Ioi 0) :=
    sech_jet_pair_integrable (interiorKnot_nonneg N i (angle/2)) (interiorKnot_nonneg N j t) (hB i) (hC j) _ _
  have hi' i j : IntegrableOn (fun p ↦ fixedFamily N i (p^2)*stripJetFamily N t j (p^2)*stripDensity p) (Set.Ioi 0) :=
    strip_jet_pair_integrable (interiorKnot_nonneg N i (angle/2)) (interiorKnot_nonneg N j t) (hB i) (hC j) _ _
  have hH₁ j : IntegrableOn (fun p ↦ (C (3*angle/2) (p^2)).re*stripJetFamily N t j (p^2)*w p) (Set.Ioi 0) := by
    simp_rw [cThree_real]
    exact sech_jet_pair_integrable (sq_nonneg _) (interiorKnot_nonneg N j t) le_rfl (hC j) _ _
  have hH₂ j : IntegrableOn (fun p ↦ (C (3*angle/2) (p^2)).re*stripJetFamily N t j (p^2)*stripDensity p) (Set.Ioi 0) := by
    simp_rw [cThree_real]
    exact strip_jet_pair_integrable (sq_nonneg _) (interiorKnot_nonneg N j t) le_rfl (hC j) _ _
  have hA : PositiveEvaluation (Fin.lastCases (fun x ↦ (C (3*angle/2) x).re) (fixedFamily N)) := by
    rw [←extended_family]
    exact jet_positiveEvaluation _ (fun _ _ h ↦ extendedKnot_monotone N h) (fun i ↦ extendedKnot_nonneg N i)
  have hU (x : Fin (2*N+1) → ℝ) (hx : StrictMono x) (hx0 : ∀ i,0<x i) :
      0 ≤ (evaluationMatrix (Fin.lastCases (fun x ↦ (C (3*angle/2) x).re) (fixedFamily N)) (Fin.cons 0 x)).det := by
    rw [←residual_det_augment _ _ cThree_zero]
    simp only [pow_add,pow_mul,neg_one_sq,one_pow,one_mul,pow_one,neg_mul]
    exact (neg_pos.mpr (cThree_residual_evaluation_neg N x hx hx0)).le
  have hF:=fixedFamily_positiveEvaluation N
  have hG:=stripJet_positiveEvaluation N ht htL
  have hd : 0<(familyGram w (fixedFamily N) (stripJetFamily N t)).det :=
    familyGram_det_pos w _ _ hF hG (fun p hp ↦ by dsimp [w,sechProbDensity]; positivity) hi
  have hd' : 0<(familyGram stripDensity (fixedFamily N) (stripJetFamily N t)).det :=
    familyGram_det_pos _ _ _ hF hG (fun p hp ↦ stripDensity_pos hp) hi'
  have h:=negative_meanResidualRatio_compare N _ _ _ w r hF hG hA hcF hcG hcH hcw hcr hU
    (fun p hp ↦ by dsimp [w,sechProbDensity]; positivity) hr hm (by rw [cThree_zero]; norm_num)
    hi (by simpa only [←hwr] using hi') hH₁ (by simpa only [←hwr] using hH₂) hd (by rw [hwr]; exact hd')
  simpa only [hwr] using h

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional.StripAsymptotic
open Matrix MeasureTheory Filter Topology

lemma mixedGram_ratio_le (N : ℕ) (w : ℝ → ℝ) (F R : Fin (2*N+1) → ℝ → ℝ) (A : ℝ)
    (hfm : ∀ i,Measurable (fun p=>F i (p^2)*w p))
    (hfi : ∀ i,IntegrableOn (fun p=>|F i (p^2)*w p| *Real.cosh (angle*p)) (Set.Ioi 0))
    (hrm : ∀ i,Measurable (fun p=>R i (p^2)*w p))
    (hri : ∀ i,IntegrableOn (fun p=>|R i (p^2)*w p| *Real.cosh (angle*p)) (Set.Ioi 0))
    (hd : 0<(familyGram w F (mixedFamily N)).det)
    (hdt : ∀ t,0<t → t<angle → 0<(familyGram w F (stripJetFamily N t)).det)
    (hb : ∀ t,0<t → t<angle →
      (familyGram w R (stripJetFamily N t)).det/(familyGram w F (stripJetFamily N t)).det ≤ A) :
    (familyGram w R (mixedFamily N)).det/(familyGram w F (mixedFamily N)).det ≤ A := by
  have hcontF : ContinuousOn (fun t=>(familyGram w F (parameterFamily N t)).det) (Set.uIcc 0 angle) := by
    rw [Set.uIcc_of_le strip_angle_pos.le]
    exact (continuous_id.matrix_det).comp_continuousOn (parameterGram_continuousOn N w F hfm hfi)
  have hcontR : ContinuousOn (fun t=>(familyGram w R (parameterFamily N t)).det) (Set.uIcc 0 angle) := by
    rw [Set.uIcc_of_le strip_angle_pos.le]
    exact (continuous_id.matrix_det).comp_continuousOn (parameterGram_continuousOn N w R hrm hri)
  have hup:=intervalIntegral.integral_mono_on_of_le_Ioo (μ:=volume) strip_angle_pos.le
    hcontR.intervalIntegrable (hcontF.intervalIntegrable.const_mul A)
    (fun t ht=>by
      rw [parameterFamily_interior N ht.1 ht.2]
      exact (div_le_iff₀ (hdt t ht.1 ht.2)).mp (hb t ht.1 ht.2))
  rw [intervalIntegral.integral_const_mul,←mixedGram_det_integral N w F hfm hfi,
    ←mixedGram_det_integral N w R hrm hri] at hup
  exact (div_le_iff₀ hd).mpr hup

lemma cThree_cosh_integrable :
    IntegrableOn (fun p ↦ |(C (3*angle/2) (p^2)).re*stripDensity p| *Real.cosh (angle*p)) (Set.Ioi 0) := by
  apply weighted_cosh_norm_integrable
  have hi:=strip_jet_pair_integrable (sq_nonneg (3*angle/2)) (sq_nonneg angle) le_rfl le_rfl 0 0
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with p hp
  have he : cosineKernelJet 0 0 (angle^2) (p^2)=Real.cosh (angle*p) := by
    apply Complex.ofReal_injective
    rw [←C_eq_beta_square,C_sq _ hp.le]
  rw [he,C_eq_beta_square]
  simp only [Complex.ofReal_re]
  ring

end CriticalHoneycomb.FiniteFunctional.StripAsymptotic

end


section

namespace CriticalHoneycomb.FiniteFunctional
open StripAsymptotic Matrix MeasureTheory

lemma strip_jet_coefficient_lower (N : ℕ) {t : ℝ} (ht : 0<t) (htL : t<angle) :
    1/(68*Real.pi*Real.sqrt ((N:ℝ)+1)) ≤
    -meanResidualRatio stripDensity (fixedFamily N) (stripJetFamily N t)
      (fun x ↦ (C (3*angle/2) x).re) 0 := by
  have h:=sech_confluent_coefficient_lower N (half_pos strip_angle_pos)
    (by linarith [strip_angle_pos] : angle/2<angle) ht htL
  have he : (fun x ↦ (C (3*angle/2) x).re)=cosineKernelJet 0 0 ((3*angle/2)^2) := funext cThree_real
  rw [←he] at h
  exact h.trans (strip_coefficient_compare N ht htL)

/-- A quantitative noncancellation bound for the mixed Gram coefficient. -/
theorem source_coefficient_inverse_sqrt (N : ℕ) :
    1/(68*Real.pi*Real.sqrt ((N:ℝ)+1)) ≤ -(obliqueResidual N (C (3*angle/2)) 0).re := by
  let H:=fun x ↦ (C (3*angle/2) x).re
  have hm : Measurable (fun p ↦ H (p^2)*stripDensity p) := by
    have hH : Continuous H := by
      simp only [H,cThree_real]
      exact (cosineKernelJet_contDiff_right 0 0 _ 0).continuous
    exact (hH.measurable.comp (by fun_prop)).mul (by unfold stripDensity; fun_prop)
  have hr:=residual_cosh_integrable (fixedFamily N) H 0 (fixedFamily_measurable N) hm
    (fixedFamily_cosh_integrable N) cThree_cosh_integrable
  have hd t (ht : 0<t) (htL : t<angle) :
      0<(familyGram stripDensity (fixedFamily N) (stripJetFamily N t)).det := by
    apply familyGram_det_pos _ _ _ (fixedFamily_positiveEvaluation N) (stripJet_positiveEvaluation N ht htL)
      (fun p hp ↦ stripDensity_pos hp)
    intro i j
    exact strip_jet_pair_integrable (interiorKnot_nonneg N i (angle/2)) (interiorKnot_nonneg N j t)
      ((interiorKnot_le N i (half_pos strip_angle_pos) (by linarith [strip_angle_pos])).trans
        (by nlinarith [sq_nonneg angle])) (interiorKnot_le N j ht htL) _ _
  have hb:=mixedGram_ratio_le N stripDensity (fixedFamily N) (residualFamily (fixedFamily N) H 0)
    (-1/(68*Real.pi*Real.sqrt ((N:ℝ)+1)))
    (fixedFamily_measurable N) (fixedFamily_cosh_integrable N) (fun i ↦ (hr i).1) (fun i ↦ (hr i).2)
    (fixed_mixed_Gram_det_pos N) hd (fun t ht htL ↦ by
      have h:=strip_jet_coefficient_lower N ht htL
      change _ ≤ -((familyGram stripDensity (residualFamily (fixedFamily N) H 0) (stripJetFamily N t)).det/
        (familyGram stripDensity (fixedFamily N) (stripJetFamily N t)).det) at h
      simpa only [neg_neg,neg_div] using neg_le_neg h)
  rw [source_residual_mean (N:=N) (H:=C (3*angle/2)) (C_ofReal_re (3*angle/2))
    (cThree_in_pairingDomain N) (by rw [cThree_zero]; norm_num)]
  simp only [Complex.ofReal_re,cThree_zero,one_mul,meanResidualRatio]
  simpa only [H,neg_div,neg_neg] using neg_le_neg hb

end CriticalHoneycomb.FiniteFunctional

end

end OAI
