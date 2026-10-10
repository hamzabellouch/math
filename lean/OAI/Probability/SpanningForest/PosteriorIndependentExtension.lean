import Mathlib

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory

namespace Problem336.Observation

private def fieldRectangles {Ω : Type*} (m n : MeasurableSpace Ω) : Set (Set Ω) :=
  {s | ∃ a b, MeasurableSet[m] a ∧ MeasurableSet[n] b ∧ a ∩ b = s}

private theorem fieldRectangles_pi {Ω : Type*} (m n : MeasurableSpace Ω) :
    IsPiSystem (fieldRectangles m n) := by
  rintro s ⟨a, b, ha, hb, rfl⟩ t ⟨c, d, hc, hd, rfl⟩ _
  refine ⟨a ∩ c, b ∩ d, ha.inter hc, hb.inter hd, ?_⟩
  ext x
  simp only [Set.mem_inter_iff]
  tauto

private theorem generateFrom_fieldRectangles {Ω : Type*} (m n : MeasurableSpace Ω) :
    m ⊔ n = MeasurableSpace.generateFrom (fieldRectangles m n) := by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · intro s hs
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨s, Set.univ, hs, MeasurableSet.univ, Set.inter_univ s⟩
    · intro s hs
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨Set.univ, s, MeasurableSet.univ, hs, Set.univ_inter s⟩
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨a, b, ha, hb, rfl⟩
    exact (show MeasurableSet[m ⊔ n] a from (show m ≤ m ⊔ n from le_sup_left) a ha).inter
      (show MeasurableSet[m ⊔ n] b from (show n ≤ m ⊔ n from le_sup_right) b hb)

theorem setIntegral_eq_on_sup_of_rectangles
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)
    {m n : MeasurableSpace Ω} (hm : m ≤ mΩ) (hn : n ≤ mΩ)
    {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    (heq : ∀ a b, MeasurableSet[m] a → MeasurableSet[n] b →
      ∫ ω in a ∩ b, f ω ∂P = ∫ ω in a ∩ b, g ω ∂P) :
    ∀ s, MeasurableSet[m ⊔ n] s →
      ∫ ω in s, f ω ∂P = ∫ ω in s, g ω ∂P := by
  have hmn : m ⊔ n ≤ mΩ := sup_le hm hn
  have huniv : ∫ ω, f ω ∂P = ∫ ω, g ω ∂P := by
    simpa using heq Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
  refine MeasurableSpace.induction_on_inter
    (generateFrom_fieldRectangles m n) (fieldRectangles_pi m n) (by simp) ?_ ?_ ?_
  · rintro s ⟨a, b, ha, hb, rfl⟩
    exact heq a b ha hb
  · intro s hs ih
    rw [setIntegral_compl (hmn s hs) hf, setIntegral_compl (hmn s hs) hg, huniv, ih]
  · intro s hd hs ih
    rw [integral_iUnion (fun i => hmn _ (hs i)) hd hf.integrableOn,
      integral_iUnion (fun i => hmn _ (hs i)) hd hg.integrableOn]
    exact tsum_congr ih

theorem setIntegral_of_independent_field
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    {m n : MeasurableSpace Ω} (hm : m ≤ mΩ) (hn : n ≤ mΩ)
    {f : Ω → ℝ} (hf : StronglyMeasurable[m] f) (hfi : Integrable f P)
    (hindep : Indep m n P) {s : Set Ω} (hs : MeasurableSet[n] s) :
    ∫ ω in s, f ω ∂P = P.real s * ∫ ω, f ω ∂P := by
  calc
    _ = ∫ ω in s, (P[f | n]) ω ∂P := (setIntegral_condExp hn hfi hs).symm
    _ = ∫ _ in s, (∫ ω, f ω ∂P) ∂P :=
      integral_congr_ae (ae_restrict_of_ae (condExp_indep_eq hm hn hf hindep))
    _ = _ := by simp [smul_eq_mul]

theorem condExp_sup_independent
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    {hidden observed auxiliary : MeasurableSpace Ω}
    (hhidden : hidden ≤ mΩ) (hauxiliary : auxiliary ≤ mΩ)
    (hobserved : observed ≤ hidden) {X : Ω → ℝ}
    (hX : StronglyMeasurable[hidden] X) (hXi : Integrable X P)
    (hindep : Indep hidden auxiliary P) :
    P[X | observed ⊔ auxiliary] =ᵐ[P] P[X | observed] := by
  have ho : observed ≤ mΩ := hobserved.trans hhidden
  have hoa : observed ⊔ auxiliary ≤ mΩ := sup_le ho hauxiliary
  have hC : StronglyMeasurable[hidden] (P[X | observed]) :=
    stronglyMeasurable_condExp.mono hobserved
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hoa hXi
    (fun _ _ _ => integrable_condExp.integrableOn)
  · intro s hs _
    apply setIntegral_eq_on_sup_of_rectangles P ho hauxiliary
      integrable_condExp hXi _ s hs
    intro a b ha hb
    have hca := setIntegral_of_independent_field P hhidden hauxiliary
      (hC.indicator (hobserved a ha))
      (integrable_condExp.indicator (ho a ha)) hindep hb
    have hxa := setIntegral_of_independent_field P hhidden hauxiliary
      (hX.indicator (hobserved a ha)) (hXi.indicator (ho a ha)) hindep hb
    rw [setIntegral_indicator (ho a ha), integral_indicator (ho a ha),
      Set.inter_comm b a] at hca hxa
    rw [hca, hxa, setIntegral_condExp ho hXi ha]
  · exact (stronglyMeasurable_condExp.mono le_sup_left).aestronglyMeasurable

theorem condExp_pair_of_indep
    {Ω Θ Y V : Type*} {mΩ : MeasurableSpace Ω}
    [mΘ : MeasurableSpace Θ] [mY : MeasurableSpace Y] [mV : MeasurableSpace V]
    (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → Θ) (Z : Ω → Y) (W : Ω → V)
    (hX : Measurable X) (hZ : Measurable Z) (hW : Measurable W)
    (g : Θ → ℝ) (hg : Measurable g) (hgi : Integrable (fun ω => g (X ω)) P)
    (hindep : IndepFun (fun ω => (X ω, Z ω)) W P) :
    P[fun ω => g (X ω) | (mY.prod mV).comap (fun ω => (Z ω, W ω))] =ᵐ[P]
      P[fun ω => g (X ω) | mY.comap Z] := by
  have hobs : mY.comap Z ≤ (mΘ.prod mY).comap (fun ω => (X ω, Z ω)) := by
    rw [MeasurableSpace.comap_prodMk]
    exact le_sup_right
  have hgs : StronglyMeasurable[(mΘ.prod mY).comap (fun ω => (X ω, Z ω))]
      (fun ω => g (X ω)) :=
    ((hg.comp measurable_fst).comp (comap_measurable _)).stronglyMeasurable
  have h := condExp_sup_independent P (hX.prodMk hZ).comap_le hW.comap_le
    hobs hgs hgi hindep
  simpa only [MeasurableSpace.comap_prodMk] using h

theorem comap_eq_of_mutual_reconstruction
    {Ω A B : Type*} [mA : MeasurableSpace A] [mB : MeasurableSpace B]
    (f : Ω → A) (g : Ω → B) (forward : A → B) (backward : B → A)
    (hf : Measurable forward) (hb : Measurable backward)
    (hforward : g = forward ∘ f) (hbackward : f = backward ∘ g) :
    mA.comap f = mB.comap g := by
  exact le_antisymm
    (MeasurableSpace.comap_le_comap_of_eq_comp backward hb hbackward)
    (MeasurableSpace.comap_le_comap_of_eq_comp forward hf hforward)

theorem condExp_reconstructed_observation
    {Ω Θ Y V H : Type*} {mΩ : MeasurableSpace Ω}
    [mΘ : MeasurableSpace Θ] [mY : MeasurableSpace Y]
    [mV : MeasurableSpace V] [mH : MeasurableSpace H]
    (P : Measure Ω) [IsFiniteMeasure P]
    (X : Ω → Θ) (Z : Ω → Y) (W : Ω → V) (history : Ω → H)
    (hX : Measurable X) (hZ : Measurable Z) (hW : Measurable W)
    (decompose : H → Y × V) (reconstruct : Y × V → H)
    (hdecompose : Measurable decompose) (hreconstruct : Measurable reconstruct)
    (hparts : (fun ω => (Z ω, W ω)) = decompose ∘ history)
    (hhistory : history = reconstruct ∘ (fun ω => (Z ω, W ω)))
    (g : Θ → ℝ) (hg : Measurable g) (hgi : Integrable (fun ω => g (X ω)) P)
    (hindep : IndepFun (fun ω => (X ω, Z ω)) W P) :
    P[fun ω => g (X ω) | mH.comap history] =ᵐ[P]
      P[fun ω => g (X ω) | mY.comap Z] := by
  rw [comap_eq_of_mutual_reconstruction history (fun ω => (Z ω, W ω))
    decompose reconstruct hdecompose hreconstruct hparts hhistory]
  exact condExp_pair_of_indep P X Z W hX hZ hW g hg hgi hindep

end Problem336.Observation

end

end OAI
