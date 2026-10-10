import Mathlib
import OAI.Analysis.Conductivity.Scalarization.ApproxScalar
import OAI.Analysis.Conductivity.Geometry.RegularRegionCongrSubset
import OAI.Analysis.Conductivity.Scalarization.WeakDensityLp
import OAI.Analysis.Conductivity.Scalarization.UpdateFieldPair
import OAI.Analysis.Conductivity.Scalarization.DefectMeasure
import OAI.Analysis.Conductivity.Sobolev.WeakCompactHilbert

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology Matrix
open scoped ENNReal Matrix.Norms.Elementwise

lemma eventually_ApproxScalar_of_tendstoInMeasure
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure X) (Z : ℕ → Lp V 2 μ × Lp V 2 μ) (s : ℕ → X → ℝ)
    {a b : ℝ} (hsm : ∀ n, Measurable (s n))
    (hsb : ∀ n, ∀ᵐ x ∂μ, s n x ∈ Icc a b)
    (ht : TendstoInMeasure μ (fun n x => (Z n).2 x-s n x • (Z n).1 x) atTop (fun _ => 0)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ApproxScalar μ a b ε (Z n) := by
  intro ε hε
  have hh := (tendstoInMeasure_iff_norm.mp ht) ε hε
  simp only [sub_zero] at hh
  filter_upwards [hh.eventually (eventually_le_nhds (ENNReal.ofReal_pos.mpr hε))] with n hn
  exact ⟨s n,hsm n,hsb n,hn⟩

lemma measurable_matrix_diagonal {X : Type*} [MeasurableSpace X]
    {A : X → Symmetric3} (hA : Measurable A) (i : Fin 3) :
    Measurable (fun x => (A x).val i i) := by
  have hc : Continuous (fun q : Symmetric3 => q.val i i) :=
    (continuous_apply i).comp ((continuous_apply i).comp continuous_subtype_val)
  exact hc.measurable.comp hA

theorem exists_fine_scalar_sequence
    (μ : Measure Coord3) [μ.IsAddHaarMeasure] [Measure.InnerRegularCompactLTTop μ]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {U : Set Coord3} (hUb : Bornology.IsBounded U) (hUm : MeasurableSet U)
    [IsFiniteMeasure (μ.restrict U)] [(μ.restrict U).WeaklyRegular]
    (u : Coord3 → Fin 2 → ℝ) (A : Coord3 → Symmetric3) (hAm : Measurable A)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hint : SmoothFluxIntegrable μ U (conductivityFlux u A))
    (hdiv : ∀ j (ψ : Coord3 → ℝ), ContDiff ℝ (↑(⊤ : ℕ∞)) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U → (∫ x, fderiv ℝ ψ x ((conductivityFlux u A x).col j) ∂μ) = 0)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hgraph : ∀ᵐ x ∂μ, x ∈ U → A x ∈ matrixFiniteLaminate a b) :
    ∃ S : ℕ → CompactGlobalUpdate μ U u A,
      (∀ n, μ (U \ regularRegion (fun x => u x+(S n).du x) (S n).tensor U) = 0) ∧
      (∀ n, ∀ᵐ x ∂μ, x ∈ U → (S n).tensor x ∈ matrixFiniteLaminate a b) ∧
      Tendsto (fun n => toWeakSpace ℝ _ ((S n).fieldPair μ hE hF)) atTop
        (𝓝 (toWeakSpace ℝ _ (hE.toLp _,hF.toLp _))) ∧
      (∀ ε > 0, ∀ᶠ n in atTop, ApproxScalar (μ.restrict U) a b ε ((S n).fieldPair μ hE hF)) := by
  classical
  let η : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hηp : ∀ n, 0 < η n := fun n => div_pos zero_lt_one (Nat.cast_add_one_pos n)
  have hηt : Tendsto η atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose N O center R S hcell hdis hsu hsF hregS hgraphS hbad using
    fun n => fine_global_scalar_tensor_approximation μ ha hab hUb u A hAm hint hdiv
      hreg hgraph (hηp n) (hηp n) (hηp n)
  have hBnd := fun n => (S n).correction_energy_bound μ hUm hreg hE hF hint hdiv ha hab (hgraphS n)
  have hCE : 0 ≤ (b/a+1)*‖hE.toLp _‖ := by have hb := ha.trans hab; positivity
  have hCF : 0 ≤ (b^2/a)*‖hE.toLp _‖+‖hF.toLp _‖ := by positivity
  obtain ⟨hwE,hwF⟩ := fine_updates_weak_tendsto_zero μ hUb N O center R S η hηt
    (fun n i => subset_closure.trans (hcell n i).2.1)
    (fun n i => subset_closure.trans (hcell n i).2.2) hdis hsu hsF hCE hCF
    (fun n => (hBnd n).1) (fun n => (hBnd n).2)
  have hw : Tendsto (fun n => toWeakSpace ℝ _ ((S n).fieldPair μ hE hF)) atTop
      (𝓝 (toWeakSpace ℝ _ (hE.toLp _,hF.toLp _))) := by
    have ht := continuous_weak_pair.tendsto (0,0) |>.comp (hwE.prodMk_nhds hwF)
    have ht' := ht.const_add (toWeakSpace ℝ _ (hE.toLp _,hF.toLp _))
    simpa [CompactGlobalUpdate.fieldPair,Function.comp_def,← map_add] using ht'
  let Z := fun n => (S n).fieldPair μ hE hF
  let s : ℕ → Coord3 → ℝ := fun n x => ((S n).tensor x).val 0 0
  have hsm : ∀ n, Measurable (s n) := fun n => measurable_matrix_diagonal (S n).measurable_tensor 0
  have hsb : ∀ n, ∀ᵐ x ∂μ.restrict U, s n x ∈ Icc a b := by
    intro n
    filter_upwards [(ae_restrict_iff' hUm).mpr (hgraphS n)] with x hx
    exact matrixFiniteLaminate_diagonal_bounds ha hx 0
  let B := fun n => U \ (S n).tensor ⁻¹' spectralExtension (scalarNeighbourhood a b (η n))
  have hBt : Tendsto (fun n => (μ.restrict U) (B n)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using ENNReal.tendsto_ofReal hηt)
    · exact Eventually.of_forall fun _ => bot_le
    · exact Eventually.of_forall fun n => (Measure.restrict_apply_le U (B n)).trans (hbad n)
  have hdef : ∀ n, ∀ᵐ x ∂μ.restrict U, x ∉ B n →
      ‖(Z n).2 x-s n x • (Z n).1 x‖ ≤ 2*η n * ‖(Z n).1 x‖ := by
    intro n
    filter_upwards [(S n).fieldPair_ae μ hUm hreg hE hF,ae_restrict_mem hUm] with x hx hxU
    intro hxB
    have hxG : (S n).tensor x ∈ spectralExtension (scalarNeighbourhood a b (η n)) := by
      by_contra hn
      exact hxB ⟨hxU,hn⟩
    dsimp only [Z,s]
    rw [hx.1,hx.2]
    exact scalarNeighbourhood_defect_bound (hηp n).le hxG _
  have hr := defect_tendstoInMeasure_of_small_exceptions (μ.restrict U)
    (fun n => (Z n).1) (fun n x => (Z n).2 x-s n x • (Z n).1 x)
    (fun n => 2*η n) (fun n => mul_nonneg (by norm_num) (hηp n).le)
    (by simpa using hηt.const_mul 2) B hBt
    (show 0 ≤ (b/a)*‖hE.toLp _‖ by have hb := ha.trans hab; positivity)
    (fun n => ((S n).fieldPair_energy_bound μ hUm hreg hE hF hint hdiv ha hab (hgraphS n)).1) hdef
  exact ⟨S,hregS,hgraphS,hw,eventually_ApproxScalar_of_tendstoInMeasure (μ.restrict U) Z s hsm hsb hr⟩

end ScalarConductivity

end
end

section

noncomputable section
namespace ScalarConductivity
open MeasureTheory Set Filter Topology

lemma CompactGlobalUpdate.fieldPair_trans
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} (hUm : MeasurableSet U)
    {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (R : CompactGlobalUpdate μ U u A)
    (S : CompactGlobalUpdate μ U (fun x => u x+R.du x) R.tensor)
    (hreg : μ (U \ regularRegion u A U) = 0)
    (hreg' : μ (U \ regularRegion (fun x => u x+R.du x) R.tensor U) = 0)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U))
    (hE' : MemLp (voltageGradient (fun x => u x+R.du x)) 2 (μ.restrict U))
    (hF' : MemLp (voltageFlux (fun x => u x+R.du x) R.tensor) 2 (μ.restrict U)) :
    (R.trans μ S).fieldPair μ hE hF = S.fieldPair μ hE' hF' := by
  have he : (fun x => u x+(R.trans μ S).du x) =
      (fun x => (u x+R.du x)+S.du x) := by
    funext x
    exact (add_assoc _ _ _).symm
  apply Prod.ext
  · apply Lp.ext
    filter_upwards [(R.trans μ S).fieldPair_ae μ hUm hreg hE hF,
      S.fieldPair_ae μ hUm hreg' hE' hF'] with x hx hy
    rw [hx.1,hy.1,he]
  · apply Lp.ext
    filter_upwards [(R.trans μ S).fieldPair_ae μ hUm hreg hE hF,
      S.fieldPair_ae μ hUm hreg' hE' hF'] with x hx hy
    rw [hx.2,hy.2,he]
    rfl

lemma CompactGlobalUpdate.fieldPair_refl
    (μ : Measure Coord3) [μ.IsAddHaarMeasure]
    {U : Set Coord3} {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    (hAm : Measurable A)
    (hE : MemLp (voltageGradient u) 2 (μ.restrict U))
    (hF : MemLp (voltageFlux u A) 2 (μ.restrict U)) :
    (CompactGlobalUpdate.refl μ U u A hAm).fieldPair μ hE hF = (hE.toLp _,hF.toLp _) := by
  have he : voltageGradient (CompactGlobalUpdate.refl μ U u A hAm).du = 0 := by
    funext x
    simp [CompactGlobalUpdate.refl,voltageGradient]
  have hf : (fun x => fieldVector ((CompactGlobalUpdate.refl μ U u A hAm).dF x)) = 0 := by
    funext x
    exact map_zero fieldVectorCLM
  simp [fieldPair, he, hf]

end ScalarConductivity

end
end

end OAI
