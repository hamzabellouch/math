import OAI.Geometry.Immersion.ClosedSurface.PhaseWeights
import OAI.Geometry.Immersion.ClosedSurface.PhaseGrid

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean Set



lemma compact_finite_uniform_margin {X ι : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (f : ι → X → ℝ)
    (hf : ∀ i, Continuous (f i)) (hpos : ∀ x ∈ K, ∃ i, 0 < f i x) :
    ∃ (s : Finset ι) (ε : ℝ), 0 < ε ∧ ∀ x ∈ K, ∃ i ∈ s, ε < f i x := by
  classical
  choose i hi using fun x : K => hpos x x.property
  let d (p : K) : ℝ := f (i p) p / 2
  have hd (p : K) : 0 < d p := half_pos (hi p)
  let U (p : K) : Set X := {x | d p < f (i p) x}
  have hU (p : K) : IsOpen (U p) := isOpen_lt continuous_const (hf (i p))
  have hcover : K ⊆ ⋃ p : K, U p := by
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨⟨x,hx⟩, ?_⟩
    change f (i ⟨x,hx⟩) x / 2 < f (i ⟨x,hx⟩) x
    linarith [hi ⟨x,hx⟩]
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU hcover
  by_cases htn : t.Nonempty
  · let ε : ℝ := t.inf' htn d
    have hε : 0 < ε := (Finset.lt_inf'_iff htn).mpr (fun p _ => hd p)
    refine ⟨t.image i, ε, hε, ?_⟩
    intro x hx
    obtain ⟨p,hp,hxp⟩ := mem_iUnion₂.mp (ht hx)
    refine ⟨i p, Finset.mem_image.mpr ⟨p,hp,rfl⟩, ?_⟩
    exact lt_of_le_of_lt (Finset.inf'_le d hp) hxp
  · refine ⟨∅, 1, zero_lt_one, ?_⟩
    intro x hx
    obtain ⟨p,hp,_⟩ := mem_iUnion₂.mp (ht hx)
    exact (htn ⟨p,hp⟩).elim



structure PhaseBasis where
  ξ : Fin 3 → Base
  Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ
  decomposition : ∀ H, ∑ i, Q i H • covectorSquare (ξ i) = H
  nonzero : ∀ i, ξ i ≠ 0

abbrev PhaseInput (n : ℕ) := (Fin 3 → RVec n) × PhaseMean.Tensor

def PhaseBasis.margin {n : ℕ} (P : PhaseBasis) (z : PhaseInput n) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i : Fin 3 =>
    min (P.Q i z.2) ‖secondQuadratic z.1 (-(P.ξ i).2, (P.ξ i).1)‖)

lemma PhaseBasis.margin_lt_iff {n : ℕ} (P : PhaseBasis) (z : PhaseInput n) (ε : ℝ) :
    ε < P.margin z ↔ ∀ i, ε < P.Q i z.2 ∧
      ε < ‖secondQuadratic z.1 (-(P.ξ i).2, (P.ξ i).1)‖ := by
  simp [PhaseBasis.margin, Finset.lt_inf'_iff, lt_min_iff]

lemma PhaseBasis.margin_continuous {n : ℕ} (P : PhaseBasis) :
    Continuous (P.margin (n := n)) := by
  apply Continuous.finset_inf'_apply
  intro i _
  exact ((P.Q i).continuous.comp continuous_snd).min
    (continuous_secondQuadratic.comp (continuous_fst.prodMk continuous_const)).norm

lemma positive_input_has_basis {n : ℕ} {z : PhaseInput n}
    (hB : z.1 ≠ 0) (hH0 : 0 < z.2 0) (hdet : 0 < z.2 0 * z.2 2 - (z.2 1)^2) :
    ∃ P : PhaseBasis, 0 < P.margin z := by
  obtain ⟨ξ,Q,hdec,hpos,hgood,_⟩ := positive_good_phase_data hB hH0 hdet
  let P : PhaseBasis := ⟨ξ,Q,hdec,fun i => (hgood i).1⟩
  refine ⟨P,(P.margin_lt_iff z 0).mpr (fun i => ?_)⟩
  exact ⟨hpos i, norm_pos_iff.mpr (hgood i).2⟩




theorem compact_positive_phase_bases {n : ℕ} {K : Set (PhaseInput n)}
    (hK : IsCompact K)
    (hB : ∀ z ∈ K, z.1 ≠ 0)
    (hH0 : ∀ z ∈ K, 0 < z.2 0)
    (hdet : ∀ z ∈ K, 0 < z.2 0 * z.2 2 - (z.2 1)^2) :
    ∃ (s : Finset PhaseBasis) (ε : ℝ), 0 < ε ∧ ∀ z ∈ K,
      ∃ P ∈ s, ∀ i, ε < P.Q i z.2 ∧
        ε < ‖secondQuadratic z.1 (-(P.ξ i).2, (P.ξ i).1)‖ := by
  obtain ⟨s,ε,hε,hs⟩ := compact_finite_uniform_margin hK
    (fun P : PhaseBasis => P.margin) (fun P => P.margin_continuous)
    (fun z hz => positive_input_has_basis (hB z hz) (hH0 z hz) (hdet z hz))
  refine ⟨s,ε,hε,fun z hz => ?_⟩
  obtain ⟨P,hP,hpm⟩ := hs z hz
  exact ⟨P,hP,(P.margin_lt_iff z ε).mp hpm⟩

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes PhaseMean Set

lemma secondQuadratic_smul_form {n : ℕ} (B : Fin 3 → RVec n) (v : Base) (a : ℝ) :
    secondQuadratic (a • B) v = a • secondQuadratic B v := by
  ext i
  simp only [secondQuadratic, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma good_smul_form_iff {n : ℕ} {B : Fin 3 → RVec n} {ξ : Base} {a : ℝ}
    (ha : a ≠ 0) : Good (a • B) ξ ↔ Good B ξ := by
  constructor
  · rintro ⟨hξ,hq⟩
    refine ⟨hξ,fun hz => hq ?_⟩
    rw [secondQuadratic_smul_form,hz,smul_zero]
  · rintro ⟨hξ,hq⟩
    exact ⟨hξ,by rw [secondQuadratic_smul_form]; exact smul_ne_zero ha hq⟩



theorem normalized_positive_phase_bases {n : ℕ} {T : Set PhaseMean.Tensor}
    (hT : IsCompact T) (hT0 : ∀ H ∈ T, 0 < H 0)
    (hTd : ∀ H ∈ T, 0 < H 0 * H 2 - (H 1)^2) :
    ∃ (s : Finset PhaseBasis) (ε : ℝ), 0 < ε ∧
      ∀ (B : Fin 3 → RVec n) (H : PhaseMean.Tensor), B ≠ 0 → H ∈ T →
      ∃ P ∈ s, ∀ i, ε < P.Q i H ∧
        ε * ‖B‖ < ‖secondQuadratic B (-(P.ξ i).2, (P.ξ i).1)‖ := by
  let K : Set (PhaseInput n) := Metric.sphere 0 1 ×ˢ T
  have hK : IsCompact K := (isCompact_sphere (0 : Fin 3 → RVec n) 1).prod hT
  have hnorm (z : PhaseInput n) (hz : z ∈ K) : ‖z.1‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using hz.1
  obtain ⟨s,ε,hε,hs⟩ := compact_positive_phase_bases hK
    (fun z hz => norm_ne_zero_iff.mp (by rw [hnorm z hz]; norm_num))
    (fun z hz => hT0 z.2 hz.2) (fun z hz => hTd z.2 hz.2)
  refine ⟨s,ε,hε,fun B H hB hH => ?_⟩
  have hn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hunit : ‖(‖B‖⁻¹ : ℝ) • B‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  have hz : ((‖B‖⁻¹ : ℝ) • B,H) ∈ K :=
    ⟨by simpa [Metric.mem_sphere, dist_zero_right] using hunit, hH⟩
  obtain ⟨P,hPs,hP⟩ := hs _ hz
  refine ⟨P,hPs,fun i => ⟨(hP i).1,?_⟩⟩
  have hi := (hP i).2
  simp only [secondQuadratic_smul_form, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos hn] at hi
  have ht := mul_lt_mul_of_pos_right hi hn
  simpa only [mul_assoc, mul_comm, mul_left_comm, mul_inv_cancel₀ hn.ne', mul_one, one_mul] using ht



theorem uniform_normalized_phase_margin {n : ℕ} {ξ : Base} (hξ : ξ ≠ 0)
    {ε C : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (B : Fin 3 → RVec n) (υ : Base),
      ‖B‖ = 1 → ε ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖ → ‖υ‖ ≤ C →
      ∀ t : ℝ, |t| < δ → Good B (ξ + t • υ) := by
  let K₀ : Set (Fin 3 → RVec n) :=
    Metric.sphere 0 1 ∩ {B | ε ≤ ‖secondQuadratic B (-ξ.2,ξ.1)‖}
  have hk₀ : IsCompact K₀ := (isCompact_sphere _ _).inter_right
    (isClosed_le continuous_const
      (continuous_secondQuadratic.comp (continuous_id.prodMk continuous_const)).norm)
  let K : Set ((Fin 3 → RVec n) × Base) := K₀ ×ˢ Metric.closedBall 0 C
  have hk : IsCompact K := hk₀.prod (isCompact_closedBall _ _)
  obtain ⟨δ,hδ,hd⟩ := uniform_good_perturbation hk continuous_fst continuous_const continuous_snd
    (fun p hp => ⟨hξ, norm_pos_iff.mp (hε.trans_le hp.1.2)⟩)
  refine ⟨δ,hδ,fun B υ hB hmargin hυ t ht => hd t ht (B,υ) ?_⟩
  exact ⟨⟨by simpa [Metric.mem_sphere, dist_zero_right] using hB, hmargin⟩,
    by simpa [Metric.mem_closedBall, dist_zero_right] using hυ⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
