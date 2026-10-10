import Mathlib
import OAI.Probability.UnimodularPercolation.Main

namespace OAI

/-! Expected mass transport and cluster averaging. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
open MeasureTheory
open scoped ENNReal
universe u v w
variable {V : Type u} {E : Type v} {ι : Type w}
attribute [local instance] Classical.propDecidable Classical.decEq

variable [Countable V] [Countable E] [Fintype ι]

omit [Countable V] [Countable E] [Fintype ι] in
theorem expected_mass_transport [Countable V] [Countable E] [Fintype ι]
    (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 ≤ weight i)
    (p : unitInterval) (m : Set E → V → V → ℝ≥0∞)
    (hm : ∀ x y, Measurable (fun ω => m ω x y))
    (hinv : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b → ∀ ω x y,
      m (b ⁻¹' ω) x y = m ω (a x) (a y)) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' y, m ω (root i) y ∂law p) =
      (∑ i, ENNReal.ofReal (weight i) * ∫⁻ ω, ∑' x, m ω x (root i) ∂law p) := by
  have hInv (a : V ≃ V) (ha : a ∈ vertexAut G) (x y : V) :
      (∫⁻ ω, m ω (a x) (a y) ∂law p) = ∫⁻ ω, m ω x y ∂law p := by
    obtain ⟨b,hb⟩ := ha
    calc
      _ = ∫⁻ ω, m (b ⁻¹' ω) x y ∂law p := lintegral_congr (fun ω => (hinv a b hb ω x y).symm)
      _ = ∫⁻ ω, m ω x y ∂(law p).map (fun ω => b ⁻¹' ω) :=
        (lintegral_map (hm x y) (measurable_set_preimage b)).symm
      _ = _ := by rw [law_map_preimage_equiv]
  have ht := htr.ennreal G hconn hloc root weight (vertexAut G) (Set.Subset.refl _) hw
    (fun x y => ∫⁻ ω, m ω x y ∂law p) hInv
  have hr (x : V) : (∫⁻ ω, ∑' y, m ω x y ∂law p) = ∑' y, ∫⁻ ω, m ω x y ∂law p :=
    lintegral_tsum (fun y => (hm x y).aemeasurable)
  have hc (y : V) : (∫⁻ ω, ∑' x, m ω x y ∂law p) = ∑' x, ∫⁻ ω, m ω x y ∂law p :=
    lintegral_tsum (fun x => (hm x y).aemeasurable)
  simp_rw [hr,hc]
  exact ht

theorem incoming_finite_ae (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1) (p : unitInterval) (m : Set E → V → V → ℝ≥0∞)
    (hm : ∀ x y, Measurable (fun ω => m ω x y))
    (hinv : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b → ∀ ω x y,
      m (b ⁻¹' ω) x y = m ω (a x) (a y))
    (hrow : ∀ ω x, ∑' y, m ω x y ≤ 1) (i : ι) :
    ∀ᵐ ω ∂law p, ∑' x, m ω x (root i) < ⊤ := by
  have ht := expected_mass_transport G hconn hloc root weight htr (fun i => (hw i).le)
    p m hm hinv
  have hupper : (∑ j, ENNReal.ofReal (weight j) * ∫⁻ ω, ∑' x, m ω x (root j) ∂law p) ≤ 1 := by
    rw [←ht]
    calc
      _ ≤ ∑ j, ENNReal.ofReal (weight j) * 1 := by
        apply Finset.sum_le_sum
        intro j _
        gcongr
        calc
          _ ≤ ∫⁻ ω : Set E, (1:ℝ≥0∞) ∂law p := lintegral_mono (fun ω => hrow ω (root j))
          _ = 1 := by simp
      _ = 1 := by
        simp only [mul_one,←ENNReal.ofReal_sum_of_nonneg (fun j _ => (hw j).le),hw1,ENNReal.ofReal_one]
  have hterm := (Finset.single_le_sum (fun j _ => (show (0:ℝ≥0∞) ≤ ENNReal.ofReal (weight j) * ∫⁻ ω, ∑' x, m ω x (root j) ∂law p from zero_le))
      (Finset.mem_univ i)).trans hupper
  have hfinite : (∫⁻ ω, ∑' x, m ω x (root i) ∂law p) ≠ ⊤ := by
    intro he
    rw [he,ENNReal.mul_top ((ENNReal.ofReal_pos.mpr (hw i)).ne')] at hterm
    exact (not_le_of_gt ENNReal.one_lt_top) hterm
  exact ae_lt_top (Measurable.tsum (fun x => hm x (root i))) hfinite

omit [Countable V] [Countable E] [Fintype ι] in
theorem expected_label_mass_transport [Countable V] [Countable E] [Fintype ι]
    (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 ≤ weight i)
    (m : (E → unitInterval) → V → V → ℝ≥0∞)
    (hm : ∀ x y, Measurable (fun l => m l x y))
    (hinv : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b → ∀ l x y,
      m (l ∘ b) x y = m l (a x) (a y)) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l, ∑' y, m l (root i) y ∂labelLaw) =
      (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l, ∑' x, m l x (root i) ∂labelLaw) := by
  have hInv (a : V ≃ V) (ha : a ∈ vertexAut G) (x y : V) :
      (∫⁻ l, m l (a x) (a y) ∂labelLaw) = ∫⁻ l, m l x y ∂labelLaw := by
    obtain ⟨b,hb⟩ := ha
    calc
      _ = ∫⁻ l, m (l ∘ b) x y ∂labelLaw := lintegral_congr (fun l => (hinv a b hb l x y).symm)
      _ = ∫⁻ l, m l x y ∂labelLaw.map (fun l => l ∘ b) :=
        (lintegral_map (hm x y) (by fun_prop)).symm
      _ = _ := by rw [labelLaw_map_precomp]
  have ht := htr.ennreal G hconn hloc root weight (vertexAut G) (Set.Subset.refl _) hw
    (fun x y => ∫⁻ l, m l x y ∂labelLaw) hInv
  have hr x : (∫⁻ l, ∑' y, m l x y ∂labelLaw) = ∑' y, ∫⁻ l, m l x y ∂labelLaw :=
    lintegral_tsum (fun y => (hm x y).aemeasurable)
  have hc y : (∫⁻ l, ∑' x, m l x y ∂labelLaw) = ∑' x, ∫⁻ l, m l x y ∂labelLaw :=
    lintegral_tsum (fun x => (hm x y).aemeasurable)
  simp_rw [hr,hc]
  exact ht

theorem label_root_cluster_average (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 ≤ weight i)
    (q : unitInterval) (hfin : ∀ x, ∀ᵐ ω ∂law q, (cluster G ω x).Finite)
    (f : (E → unitInterval) → V → ℝ≥0∞) (hf : ∀ x, Measurable (fun l => f l x))
    (hi : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b → ∀ l x,
      f (l ∘ b) x = f l (a x)) :
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l, ∑' y,
      clusterAveragingKernel G (openEdges l q) (root i) y * f l y ∂labelLaw) =
    (∑ i, ENNReal.ofReal (weight i) * ∫⁻ l, f l (root i) ∂labelLaw) := by
  have hm x y : Measurable (fun l => clusterAveragingKernel G (openEdges l q) x y * f l y) :=
    ((measurable_clusterAveragingKernel G hloc x y).comp (measurable_openEdges q)).mul (hf y)
  have ht := expected_label_mass_transport G hconn hloc root weight htr hw
    (fun l x y => clusterAveragingKernel G (openEdges l q) x y * f l y) hm
    (fun a b hab l x y => by
      rw [hi a b hab]
      exact congrArg (fun t => t * f l (a y)) (clusterAveragingKernel_aut G hab (openEdges l q) x y))
  rw [ht]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply lintegral_congr_ae
  have hfl : ∀ᵐ l ∂labelLaw, (cluster G (openEdges l q) (root i)).Finite := by
    apply ae_of_ae_map (μ := (labelLaw : Measure (E → unitInterval)))
      (p := fun ω : Set E => (cluster G ω (root i)).Finite) (measurable_openEdges q).aemeasurable
    rw [map_openEdges]
    exact hfin (root i)
  filter_upwards [hfl] with l hl
  rw [ENNReal.tsum_mul_right,clusterAveragingKernel_column G (openEdges l q) (root i) hl,one_mul]

theorem incoming_finite_ae_all (G : BondGraph V E) (hconn : Connected G)
    (hloc : LocallyFinite G) (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G)) (hw : ∀ i, 0 < weight i)
    (hw1 : ∑ i, weight i = 1)
    (hcov : ∀ x, ∃ i, ∃ a ∈ vertexAut G, a (root i) = x)
    (p : unitInterval) (m : Set E → V → V → ℝ≥0∞)
    (hm : ∀ x y, Measurable (fun ω => m ω x y))
    (hinv : ∀ a : V ≃ V, ∀ b : E ≃ E, IsAut G a b → ∀ ω x y,
      m (b ⁻¹' ω) x y = m ω (a x) (a y))
    (hrow : ∀ ω x, ∑' y, m ω x y ≤ 1) :
    ∀ᵐ ω ∂law p, ∀ y, ∑' x, m ω x y < ⊤ := by
  apply ae_all_iff.mpr
  intro y
  obtain ⟨i,a,⟨b,hab⟩,rfl⟩ := hcov y
  have hi := incoming_finite_ae G hconn hloc root weight htr hw hw1 p m hm hinv hrow i
  have hi' : ∀ᵐ ω ∂law p, ∑' x, m (b ⁻¹' ω) x (root i) < ⊤ := by
    apply ae_of_ae_map (μ := law p)
      (p := fun ω : Set E => ∑' x, m ω x (root i) < ⊤)
      (measurable_set_preimage b).aemeasurable
    rw [law_map_preimage_equiv]
    exact hi
  filter_upwards [hi'] with ω hω
  simpa only [hinv a b hab,a.tsum_eq (fun x => m ω x (a (root i)))] using hω

end Percolation

end OAI
