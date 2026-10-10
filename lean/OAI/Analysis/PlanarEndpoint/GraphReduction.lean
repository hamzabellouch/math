import OAI.Analysis.PlanarEndpoint.Extension
import OAI.Analysis.PlanarEndpoint.Fourier
import OAI.Analysis.PlanarEndpoint.GraphSelection
import OAI.Analysis.PlanarEndpoint.GraphTree

namespace OAI

/-! Gaussian regularization, Fourier evolution and endpoint maximal estimates. -/


noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace PlanarEndpoint

def ShortTimeGraphEstimate (c₀ C₀ p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (f : L2),
    AnnularFourierSupport f c₀ C₀ ((2 : ℝ) ^ j) →
    ∀ (x₀ : Plane) (t₀ s : ℝ), 0 ≤ s → s ≤ ((2 : ℝ) ^ j)⁻¹ →
    ∀ T : Plane → ℝ, Measurable T → (∀ x, T x ∈ Icc t₀ (t₀+s)) →
    ∀ lam : ℝ, 0 < lam →
    volume (Metric.ball x₀ 1 ∩ {x | lam < ‖evolution f x (T x)‖}) ≤
      ENNReal.ofReal ((C * (((2 : ℝ) ^ j) ^ (1 / 3 : ℝ)) * ‖f‖ / lam) ^ p)

lemma affine_dense_time_bound {g : ℝ → ℂ} (hg : Continuous g)
    {t₀ s B : ℝ} (hs : 0 ≤ s)
    (h : ∀ n, ‖g (t₀+s*(denseTime n).val)‖ ≤ B) :
    ∀ t ∈ Icc t₀ (t₀+s), ‖g t‖ ≤ B := by
  have hh := denseTime_bound (show Continuous (fun u => g (t₀+s*u)) by fun_prop) h
  intro t ht
  by_cases hz : s = 0
  · have he : t = t₀ := le_antisymm (by simpa [hz] using ht.2) ht.1
    simpa [he,hz] using h 0
  · have hs' : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    have hu : (t-t₀)/s ∈ Icc (0:ℝ) 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr ht.1) hs
      · exact (div_le_one hs').mpr (by linarith [ht.2])
    have he : t₀+s*((t-t₀)/s) = t := by field_simp; ring
    simpa only [he] using hh ((t-t₀)/s) hu

lemma exists_measurable_superlevel_time (f : L2)
    (hf : Integrable (fourier f) volume) (t₀ s lam : ℝ) (hs : 0 ≤ s) :
    ∃ T : Plane → ℝ, Measurable T ∧ (∀ x, T x ∈ Icc t₀ (t₀+s)) ∧
      ∀ x, (∃ t ∈ Icc t₀ (t₀+s), lam < ‖evolution f x t‖) ↔
        lam < ‖evolution f x (T x)‖ := by
  classical
  let P (n : ℕ) (x : Plane) : Prop :=
    lam < ‖evolution f x (t₀+s*(denseTime n).val)‖
  let M (x : Plane) : Prop := ∃ n, P n x
  have hp : ∀ n, MeasurableSet {x | P n x} := by
    intro n
    exact measurableSet_lt measurable_const
      (((continuous_evolution hf).comp (continuous_id.prodMk continuous_const)).norm.measurable)
  have hm : MeasurableSet {x | M x} := by
    have he : {x | M x} = ⋃ n, {x | P n x} := by ext x; simp [M]
    rw [he]
    exact MeasurableSet.iUnion hp
  have hex : ∀ x, ∃ n, ¬M x ∨ P n x := by
    intro x
    by_cases h : M x
    · obtain ⟨n,hn⟩ := h
      exact ⟨n,Or.inr hn⟩
    · exact ⟨0,Or.inl h⟩
  let T (x : Plane) : ℝ := t₀+s*(denseTime (Nat.find (hex x))).val
  have hr : ∀ x, T x ∈ Icc t₀ (t₀+s) := by
    intro x
    have hv := (denseTime (Nat.find (hex x))).property
    dsimp [T]
    constructor
    · nlinarith [hv.1]
    · nlinarith [hv.2]
  refine ⟨T,?_,hr,?_⟩
  · exact Measurable.find (p := fun n x => ¬M x ∨ P n x)
      (f := fun n (_ : Plane) => t₀+s*(denseTime n).val)
      (fun n => measurable_const) (fun n => hm.compl.union (hp n)) hex
  · intro x
    constructor
    · rintro ⟨t,ht,hlt⟩
      have hx : M x := by
        by_contra! hn
        have hb : ∀ n, ‖evolution f x (t₀+s*(denseTime n).val)‖ ≤ lam := by
          intro n
          exact le_of_not_gt (fun h => hn ⟨n,h⟩)
        exact (not_lt_of_ge (affine_dense_time_bound
          ((continuous_evolution hf).comp (continuous_const.prodMk continuous_id)) hs hb t ht)) hlt
      have hh := Nat.find_spec (hex x)
      exact hh.resolve_left (not_not.mpr hx)
    · intro hx
      exact ⟨T x,hr x,hx⟩

lemma shortTimeWeakEstimate_of_graph {c₀ C₀ p : ℝ}
    (hg : ShortTimeGraphEstimate c₀ C₀ p) : ShortTimeWeakEstimate c₀ C₀ p := by
  obtain ⟨C,hC,hg⟩ := hg
  refine ⟨C,hC,?_⟩
  intro j f hf x₀ t₀ s hs hsN lam hlam
  obtain ⟨T,hT,hr,he⟩ := exists_measurable_superlevel_time f hf.integrable t₀ s lam hs
  have heq : shortTimeLevel f x₀ t₀ s lam =
      Metric.ball x₀ 1 ∩ {x | lam < ‖evolution f x (T x)‖} := by
    ext x
    exact and_congr_right (fun _ => he x)
  rw [heq]
  exact hg j f hf x₀ t₀ s hs hsN T hT hr lam hlam

lemma shortTimeGraphEstimate_of_weak {c₀ C₀ p : ℝ}
    (hw : ShortTimeWeakEstimate c₀ C₀ p) : ShortTimeGraphEstimate c₀ C₀ p := by
  obtain ⟨C,hC,hw⟩ := hw
  refine ⟨C,hC,?_⟩
  intro j f hf x₀ t₀ s hs hsN T _ hr lam hlam
  apply le_trans (measure_mono (show
    (Metric.ball x₀ 1 ∩ {x | lam < ‖evolution f x (T x)‖}) ⊆
    shortTimeLevel f x₀ t₀ s lam from fun x hx => ⟨hx.1,T x,hr x,hx.2⟩))
  exact hw j f hf x₀ t₀ s hs hsN lam hlam

lemma mainConclusion_of_shortTimeGraph {p : ℝ} (hp : 2 < p)
    (hg : ShortTimeGraphEstimate (1/4) 4 p) {f : L2} (hf : InHThird f) :
    MainConclusion f :=
  mainConclusion_of_shortTime hp (shortTimeWeakEstimate_of_graph hg) hf

end PlanarEndpoint
end

end OAI
