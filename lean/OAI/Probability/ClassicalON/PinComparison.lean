import OAI.Probability.ClassicalON.BondAssociation

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory Set
open scoped BigOperators Classical
namespace ClassicalON
variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

def pinnedBondNumerator (μ : Measure Amplitude) (left right : E → V) (b : E → ℝ)
    (B : Set V) (f : (E → Bool) → ℝ) : ℝ :=
  ∫ r,∑ η,amplitudeBondWeight left right b (glueAmplitude B ⊤ r) η*
    bondPinFactor left right B η*f η ∂Measure.pi (fun _ : ↥(Bᶜ) => μ)

def pinnedBondMean (μ : Measure Amplitude) (left right : E → V) (b : E → ℝ)
    (B : Set V) (f : (E → Bool) → ℝ) : ℝ :=
  pinnedBondNumerator μ left right b B f/pinnedBondNumerator μ left right b B (fun _ => 1)

theorem continuous_pinWeightedSum (left right : E → V) (b : E → ℝ) (B : Set V)
    (f : (E → Bool) → ℝ) :
    Continuous (fun r => ∑ η,amplitudeBondWeight left right b r η*bondPinFactor left right B η*f η) := by
  exact continuous_finsetSum _ (fun η _ => ((continuous_amplitudeBondWeight _ _ _ η).mul continuous_const).mul continuous_const)

theorem pinWeightedSum_pos (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (B : Set V) (r : V → Amplitude) :
    0<∑ η,amplitudeBondWeight left right b r η*bondPinFactor left right B η*(1:ℝ) := by
  apply Finset.sum_pos'
  · intro η _
    exact mul_nonneg (mul_nonneg (amplitudeBondWeight_nonneg _ _ _ hb r η)
      (bondPinFactor_pos _ _ _ _).le) zero_le_one
  · refine ⟨fun _ => false,Finset.mem_univ _,?_⟩
    simp only [amplitudeBondWeight,bondWeight,bondProduct,Bool.false_eq_true,ite_false,Finset.prod_const_one,mul_one]
    exact mul_pos (mul_pos (amplitudeBondPrefactor_pos _ _ _ _) (clusterWeight_pos _ _ _)) (bondPinFactor_pos _ _ _ _)

theorem pinnedBondNumerator_one_pos (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e) (B : Set V) :
    0<pinnedBondNumerator μ left right b B (fun _ => 1) := by
  apply compact_integral_pos
  · exact (continuous_pinWeightedSum _ _ _ _ _).comp
      ((continuous_glueAmplitude B).comp (continuous_const.prodMk continuous_id))
  · intro r
    exact pinWeightedSum_pos _ _ _ hb _ _

theorem jointBond_le_pinnedBond (μ : Measure Amplitude) [IsProbabilityMeasure μ]
    [μ.IsOpenPosMeasure] (left right : E → V) (b : E → ℝ) (hb : ∀ e,0≤b e)
    (B : Set V) (f : (E → Bool) → ℝ) (hfn : ∀ η,0≤f η) (hfm : Monotone f) :
    jointBondMean μ left right b (fun _ η => f η)≤pinnedBondMean μ left right b B f := by
  let c := jointBondMean μ left right b (fun _ η => f η)
  let F : (V → Amplitude) → ℝ := fun r => ∑ η,amplitudeBondWeight left right b r η*
    bondPinFactor left right B η*(f η-c)
  have hF : Continuous F := continuous_pinWeightedSum _ _ _ _ _
  have ht : 0≤∫ r,F (glueAmplitude B ⊤ r) ∂Measure.pi (fun _ : ↥(Bᶜ) => μ) := by
    apply pinEndpoint_nonneg μ B hF
    intro h hh hn hm
    let g : (V → Amplitude) → (E → Bool) → ℝ := fun r η => h (fun v : B => r v)*bondPinFactor left right B η
    have hgr : ∀ η,Monotone (fun r => g r η) := by
      intro η r s hrs
      exact mul_le_mul_of_nonneg_right (hm (fun v => hrs v)) (bondPinFactor_pos _ _ _ _).le
    have hgη : ∀ r,Monotone (g r) := by
      intro r η ξ hη
      exact mul_le_mul_of_nonneg_left (bondPinFactor_monotone _ _ _ hη) (hn _)
    have hgc : ∀ η,Continuous (fun r => g r η) := by
      intro η
      exact (hh.comp (continuous_pi (fun v : B => continuous_apply v.val))).mul continuous_const
    have hi := rawBond_tilt_defect_nonneg μ left right b hb
      (f := fun _ η => f η) (g := g)
      (fun _ => continuous_const) hgc (fun _ η => hfn η)
      (fun r η => mul_nonneg (hn _) (bondPinFactor_pos _ _ _ _).le)
      (fun _ => monotone_const) hgr (fun _ => hfm) hgη
    convert hi using 1
    congr 1
    funext r
    dsimp only [F,g,c]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro η _
    ring
  have he (r : ↥(Bᶜ) → Amplitude) : F (glueAmplitude B ⊤ r)=
      (∑ η,amplitudeBondWeight left right b (glueAmplitude B ⊤ r) η*bondPinFactor left right B η*f η)-
        c*(∑ η,amplitudeBondWeight left right b (glueAmplitude B ⊤ r) η*bondPinFactor left right B η*1) := by
    dsimp only [F]
    rw [Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro η _
    ring
  simp_rw [he] at ht
  have hc (q : (E → Bool) → ℝ) : Continuous (fun r : ↥(Bᶜ) → Amplitude =>
      ∑ η,amplitudeBondWeight left right b (glueAmplitude B ⊤ r) η*bondPinFactor left right B η*q η) :=
    (continuous_pinWeightedSum _ _ _ _ q).comp ((continuous_glueAmplitude B).comp (continuous_const.prodMk continuous_id))
  rw [integral_sub (compact_integrable (hc f)) ((compact_integrable (hc (fun _ => 1))).const_mul c),integral_const_mul] at ht
  apply (le_div_iff₀ (pinnedBondNumerator_one_pos μ _ _ _ hb B)).2
  exact sub_nonneg.mp ht

end ClassicalON

end

end OAI
