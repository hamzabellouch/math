import OAI.Analysis.TriangularHilbert.HeatContinuous

namespace OAI

universe uι

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder
noncomputable section

lemma measurable_chart (i : Three) (d : ℝ) : Measurable (chart i d) :=
  ((chart_continuous i).comp (continuous_const.prodMk continuous_id)).measurable

lemma hasDerivAt_chart_of_center {f : (Three → ℝ) → ℝ} {g : (Three → ℝ) → ℝ}
    (i : Three) (d : ℝ) (z : ℝ × ℝ)
    (h : ∀ p, HasDerivAt (fun t => f (Function.update p i t)) (g p) (p i)) :
    HasDerivAt (fun e => f (chart i e z)) (g (chart i d z)) d := by
  have hd := (h (chart i d z)).comp d (chart_hasDerivAt i d z)
  simp only [mul_one] at hd
  apply hd.congr_of_eventuallyEq
  apply Eventually.of_forall
  intro e
  apply congrArg f
  ext j
  fin_cases i <;> fin_cases j <;> simp [chart,Function.update]

def planeIntegral (f : (Three → ℝ) → ℝ) (d : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ, f (chart 2 d z)

lemma planeIntegral_eq (f : (Three → ℝ) → ℝ) (i : Three) (d : ℝ) :
    planeIntegral f d = ∫ z : ℝ × ℝ, f (chart i d z) := integral_chart_eq 2 i d f

lemma hasDerivAt_planeIntegral {f g : (Three → ℝ) → ℝ} {B : (ℝ × ℝ) → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hB : Integrable B)
    (i : Three) (d : ℝ)
    (hb0 : ∀ z, ‖f (chart i d z)‖ ≤ B z)
    (hb : ∀ e ∈ Set.Ioo (d-1) (d+1), ∀ z, ‖g (chart i e z)‖ ≤ B z)
    (hd : ∀ p, HasDerivAt (fun t => f (Function.update p i t)) (g p) (p i)) :
    HasDerivAt (planeIntegral f) (planeIntegral g d) d := by
  have hs : Set.Ioo (d-1) (d+1) ∈ 𝓝 d := Ioo_mem_nhds (by linarith) (by linarith)
  have hint : Integrable (fun z => f (chart i d z)) :=
    hB.mono' (hf.comp (measurable_chart i d)).aestronglyMeasurable (Eventually.of_forall hb0)
  have hh := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun e z => f (chart i e z))
    (F' := fun e z => g (chart i e z)) hs
    (Eventually.of_forall (fun e => (hf.comp (measurable_chart i e)).aestronglyMeasurable)) hint
    (hg.comp (measurable_chart i d)).aestronglyMeasurable
    (Eventually.of_forall (fun z e he => hb e he z)) hB
    (Eventually.of_forall (fun z e _ => hasDerivAt_chart_of_center i e z hd))).2
  rw [← planeIntegral_eq g i d] at hh
  exact hh.congr_of_eventuallyEq (Eventually.of_forall (fun e => planeIntegral_eq f i e))

lemma finite_variance_bounds (σ : Three → ℝ) (hσ : ∀ w, 0 < σ w) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ (∀ w, a ≤ σ w) ∧ (∀ w, σ w ≤ b) := by
  let a := min (σ 0) (min (σ 1) (σ 2))
  let b := σ 0 + σ 1 + σ 2
  have ha : 0 < a := lt_min (hσ 0) (lt_min (hσ 1) (hσ 2))
  have hlo : ∀ w, a ≤ σ w := by
    intro w; fin_cases w
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  have hhi : ∀ w, σ w ≤ b := by
    intro w; fin_cases w <;> dsimp [b] <;> linarith [hσ 0,hσ 1,hσ 2]
  exact ⟨a,b,ha,(hlo 0).trans (hhi 0),hlo,hhi⟩

lemma abs_le_add_one_of_mem_Ioo {d e : ℝ} (he : e ∈ Set.Ioo (d-1) (d+1)) :
    |e| ≤ |d|+1 := by
  apply abs_le.mpr
  constructor <;> linarith [he.1,he.2,le_abs_self d,neg_le_abs d]

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

structure HeatPlaneIntegrable (A : Three → Matrix ι ι ℂ) (h : ℝ) (u : ι → ℝ)
    (d : ℝ) (σ : Three → ℝ) : Prop where
  energy : ∀ i v, Integrable (fun z => heatEnergy A h u (chart i d z) σ v)
  first : ∀ i v w, Integrable (fun z => heatFirst A h u (chart i d z) σ v w)
  pure : ∀ i v w, Integrable (fun z => heatPure A h u (chart i d z) σ v w)
  variance : ∀ i v w, Integrable (fun z => heatVariance A h u (chart i d z) σ v w)
  cost : ∀ i v w, Integrable (fun z => heatCost A h u (chart i d z) σ v w)
  mixed : ∀ i v w z, w ≠ v → z ≠ v → w ≠ z → Integrable (fun x => heatMixed A h u (chart i d x) σ v w z)

lemma heatPlane_integrable (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) :
    HeatPlaneIntegrable A h u d σ := by
  obtain ⟨a,b,ha,hab,hla,hlb⟩ := finite_variance_bounds σ hσ
  obtain ⟨B,hB,_,hbound⟩ := exists_heat_uniform_majorant A hh ha hab (abs_nonneg d) u
  have hb i z := hbound i d z (le_refl |d|) σ hla hlb
  have hmono (f : (Three → ℝ) → ℝ) (hf : Measurable f) (i : Three)
      (hb : ∀ z, ‖f (chart i d z)‖ ≤ B z) : Integrable (fun z => f (chart i d z)) :=
    hB.mono' (hf.comp (measurable_chart i d)).aestronglyMeasurable (Eventually.of_forall hb)
  constructor
  · intro i v
    exact hmono _ (continuous_heatEnergy A hh u hσ v).measurable i (fun z => (hb i z).energy v)
  · intro i v w
    exact hmono _ (continuous_heatFirst A hh u hσ v w).measurable i (fun z => (hb i z).first v w)
  · intro i v w
    exact hmono _ (measurable_heatPure A hh u hσ v w) i (fun z => (hb i z).pure v w)
  · intro i v w
    exact hmono _ (continuous_heatVariance A hh u hσ v w).measurable i (fun z => (hb i z).variance v w)
  · intro i v w
    exact hmono _ (measurable_heatCost A hh u hσ v w) i (fun z => (hb i z).cost v w)
  · intro i v w z hw hz hwz
    exact hmono _ (measurable_heatMixed A hh u hσ hw hz hwz) i (fun x => (hb i x).mixed v w z hw hz)

lemma planeEnergy_hasDerivAt (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    HasDerivAt (planeIntegral (fun p => heatEnergy A h u p σ v))
      (planeIntegral (fun p => heatFirst A h u p σ v w) d) d := by
  obtain ⟨a,b,ha,hab,hla,hlb⟩ := finite_variance_bounds σ hσ
  obtain ⟨B,hB,_,hb⟩ := exists_heat_uniform_majorant A hh ha hab (by positivity : 0 ≤ |d|+1) u
  apply hasDerivAt_planeIntegral (continuous_heatEnergy A hh u hσ v).measurable
    (continuous_heatFirst A hh u hσ v w).measurable hB w d
  · exact fun z => (hb w d z (by linarith) σ hla hlb).energy v
  · exact fun e he z => (hb w e z (abs_le_add_one_of_mem_Ioo he) σ hla hlb).first v w
  · exact fun p => heatEnergy_hasDerivAt_center A hh u p hσ v w

lemma planeFirst_hasDerivAt (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ w, 0 < σ w) (v w : Three) :
    HasDerivAt (planeIntegral (fun p => heatFirst A h u p σ v w))
      (planeIntegral (fun p => heatPure A h u p σ v w) d) d := by
  obtain ⟨a,b,ha,hab,hla,hlb⟩ := finite_variance_bounds σ hσ
  obtain ⟨B,hB,_,hb⟩ := exists_heat_uniform_majorant A hh ha hab (by positivity : 0 ≤ |d|+1) u
  apply hasDerivAt_planeIntegral (continuous_heatFirst A hh u hσ v w).measurable
    (measurable_heatPure A hh u hσ v w) hB w d
  · exact fun z => (hb w d z (by linarith) σ hla hlb).first v w
  · exact fun e he z => (hb w e z (abs_le_add_one_of_mem_Ioo he) σ hla hlb).pure v w
  · exact fun p => heatFirst_hasDerivAt_center A hh u p hσ v w

lemma planeFirst_hasDerivAt_other (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ a, 0 < σ a)
    {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (hwz : w ≠ z) :
    HasDerivAt (planeIntegral (fun p => heatFirst A h u p σ v w))
      (planeIntegral (fun p => heatMixed A h u p σ v w z) d) d := by
  obtain ⟨a,b,ha,hab,hla,hlb⟩ := finite_variance_bounds σ hσ
  obtain ⟨B,hB,_,hb⟩ := exists_heat_uniform_majorant A hh ha hab (by positivity : 0 ≤ |d|+1) u
  apply hasDerivAt_planeIntegral (continuous_heatFirst A hh u hσ v w).measurable
    (measurable_heatMixed A hh u hσ hw hz hwz) hB z d
  · exact fun x => (hb z d x (by linarith) σ hla hlb).first v w
  · exact fun e he x => (hb z e x (abs_le_add_one_of_mem_Ioo he) σ hla hlb).mixed v w z hw hz
  · exact fun p => heatFirst_hasDerivAt_other A hh u p hσ hw hz hwz

lemma planePure_eq_mixed (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h)
    (u : ι → ℝ) (d : ℝ) {σ : Three → ℝ} (hσ : ∀ a, 0 < σ a)
    (i : Three) {v w z : Three} (hw : w ≠ v) (hz : z ≠ v) (hwz : w ≠ z) :
    planeIntegral (fun p => heatPure A h u p σ v i) d =
      planeIntegral (fun p => heatMixed A h u p σ v w z) d := by
  have hf : planeIntegral (fun p => heatFirst A h u p σ v i) =
      planeIntegral (fun p => heatFirst A h u p σ v w) := by
    funext e
    exact (planeEnergy_hasDerivAt A hh u e hσ v i).unique (planeEnergy_hasDerivAt A hh u e hσ v w)
  have hi := planeFirst_hasDerivAt A hh u d hσ v i
  rw [hf] at hi
  exact hi.unique (planeFirst_hasDerivAt_other A hh u d hσ hw hz hwz)
end
end TriangularHilbert.Heat
end

end OAI
