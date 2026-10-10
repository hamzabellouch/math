import Mathlib
import OAI.Probability.LatticeSurface.Convexity.BrunnMinkowski
import OAI.Probability.LatticeSurface.Convexity.CubePrekopa
import OAI.Probability.LatticeSurface.Convexity.QuantileTransport
import OAI.Probability.LatticeSurface.Convexity.WeightedPrekopa
import OAI.Probability.LatticeSurface.Dynamics.DisplacementInequality

namespace OAI

open Set MeasureTheory Filter

open scoped Topology

noncomputable section

namespace FacetVolume

def slice {n : ℕ} (K : Set (Fin (n+1) → ℝ)) (t : ℝ) : Set (Fin n → ℝ) :=
  {x | Fin.cons t x ∈ K}

def sliceVolume {n : ℕ} (K : Set (Fin (n+1) → ℝ)) (t : ℝ) : ℝ :=
  (volume (slice K t)).toReal

lemma continuous_tail (n : ℕ) : Continuous (Fin.tail : (Fin (n+1) → ℝ) → (Fin n → ℝ)) := by
  exact continuous_pi fun i => continuous_apply i.succ

lemma compact_slice {n : ℕ} {K : Set (Fin (n+1) → ℝ)} (hK : IsCompact K) (t : ℝ) :
    IsCompact (slice K t) := by
  have heq : Fin.tail '' (K ∩ {z | z 0 = t}) = slice K t := by
    ext x
    constructor
    · rintro ⟨z, ⟨hz, hzt⟩, rfl⟩
      change Fin.cons t (Fin.tail z) ∈ K
      rw [← hzt, Fin.cons_self_tail]
      exact hz
    · intro hx
      exact ⟨Fin.cons t x, ⟨hx, rfl⟩, by ext i; rfl⟩
  rw [← heq]
  exact (hK.inter_right (isClosed_eq (continuous_apply 0) continuous_const)).image (continuous_tail n)

lemma sliceVolume_nonneg {n : ℕ} (K : Set (Fin (n+1) → ℝ)) (t : ℝ) :
    0 ≤ sliceVolume K t := ENNReal.toReal_nonneg

lemma slice_nonempty_of_volume_pos {n : ℕ} {K : Set (Fin (n+1) → ℝ)} {t : ℝ}
    (hpos : 0 < sliceVolume K t) : (slice K t).Nonempty := by
  by_contra h
  simp only [sliceVolume, Set.not_nonempty_iff_eq_empty.mp h, measure_empty,
    ENNReal.toReal_zero, lt_self_iff_false] at hpos

lemma weighted_cons {n : ℕ} (s t u v : ℝ) (x y : Fin n → ℝ) :
    s • Fin.cons u x+t • Fin.cons v y = Fin.cons (s*u+t*v) (s • x+t • y) := by
  funext i
  exact Fin.cases (by rfl) (fun j => by rfl) i

lemma slices_combination_volume {n : ℕ} {K L M : Set (Fin (n+1) → ℝ)} {s t u v : ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hM : IsCompact M)
    (hKn : (slice K u).Nonempty) (hLn : (slice L v).Nonempty)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s+t=1)
    (hcomb : ∀ x ∈ K, ∀ y ∈ L, s • x+t • y ∈ M) :
    (sliceVolume K u)^s*(sliceVolume L v)^t ≤ sliceVolume M (s*u+t*v) := by
  apply compact_volume_brunn_minkowski (compact_slice hK u) (compact_slice hL v)
    (compact_slice hM _) hKn hLn hs ht hst
  intro x hx y hy
  change Fin.cons (s*u+t*v) (s • x+t • y) ∈ M
  rw [← weighted_cons]
  exact hcomb _ hx _ hy

lemma log_sliceVolume_concave {n : ℕ} {K : Set (Fin (n+1) → ℝ)} {J : Set ℝ}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hJ : Convex ℝ J)
    (hpos : ∀ u ∈ J, 0 < sliceVolume K u) :
    ConcaveOn ℝ J (fun u => Real.log (sliceVolume K u)) := by
  refine ⟨hJ, ?_⟩
  intro u hu v hv s t hs ht hst
  have hBM := slices_combination_volume hK hK hK
    (slice_nonempty_of_volume_pos (hpos u hu)) (slice_nonempty_of_volume_pos (hpos v hv))
    hs ht hst (fun x hx y hy => hcK hx hy hs ht hst)
  have hp : 0 < (sliceVolume K u)^s*(sliceVolume K v)^t :=
    mul_pos (Real.rpow_pos_of_pos (hpos u hu) _) (Real.rpow_pos_of_pos (hpos v hv) _)
  have hl := Real.log_le_log hp hBM
  simpa only [Real.log_mul (Real.rpow_pos_of_pos (hpos u hu) s).ne'
      (Real.rpow_pos_of_pos (hpos v hv) t).ne', Real.log_rpow (hpos u hu),
      Real.log_rpow (hpos v hv), smul_eq_mul] using hl

lemma continuousOn_sliceVolume {n : ℕ} {K : Set (Fin (n+1) → ℝ)} {J : Set ℝ}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hJ : Convex ℝ J) (hJo : IsOpen J)
    (hpos : ∀ u ∈ J, 0 < sliceVolume K u) : ContinuousOn (sliceVolume K) J := by
  have hl := (log_sliceVolume_concave hK hcK hJ hpos).continuousOn hJo
  have he := Real.continuous_exp.comp_continuousOn hl
  apply he.congr
  intro u hu
  exact (Real.exp_log (hpos u hu)).symm

lemma integral_indicator_one {d : ℕ} {K : Set (Fin d → ℝ)} (hK : MeasurableSet K) :
    (∫ x, K.indicator (fun _ => (1 : ℝ)) x) = (volume K).toReal := by
  rw [integral_indicator hK, integral_const]
  simp [Measure.real]

lemma integrable_indicator_pair {n : ℕ} {K : Set (Fin (n+1) → ℝ)} (hK : IsCompact K) :
    Integrable (fun z : ℝ × (Fin n → ℝ) => K.indicator (fun _ => (1 : ℝ)) (Fin.cons z.1 z.2))
      (volume.prod volume) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have he (z : ℝ × (Fin n → ℝ)) : e z = Fin.cons z.1 z.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.zero_succAbove]
  have hpres := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hi : Integrable (K.indicator (fun _ => (1 : ℝ))) :=
    (continuous_const.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have hip := hpres.integrable_comp_of_integrable hi
  change Integrable (fun x => K.indicator (fun _ => (1 : ℝ)) (e x)) volume at hip
  simp only [he, Measure.volume_eq_prod] at hip
  exact hip

lemma sliceVolume_as_integral {n : ℕ} {K : Set (Fin (n+1) → ℝ)} (hK : IsCompact K) (t : ℝ) :
    sliceVolume K t = ∫ x, K.indicator (fun _ => (1 : ℝ)) (Fin.cons t x) := by
  have heq : (fun x => K.indicator (fun _ => (1 : ℝ)) (Fin.cons t x)) =
      (slice K t).indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : Fin.cons t x ∈ K
    · simp only [indicator_of_mem hx, indicator_of_mem (show x ∈ slice K t from hx)]
    · simp only [indicator_of_notMem hx, indicator_of_notMem (show x ∉ slice K t from hx)]
  rw [heq, integral_indicator_one (compact_slice hK t).measurableSet]
  rfl

lemma integrable_sliceVolume {n : ℕ} {K : Set (Fin (n+1) → ℝ)} (hK : IsCompact K) :
    Integrable (sliceVolume K) := by
  have hi := (integrable_indicator_pair hK).integral_prod_left
  simpa only [← sliceVolume_as_integral hK] using hi

lemma integral_sliceVolume {n : ℕ} {K : Set (Fin (n+1) → ℝ)} (hK : IsCompact K) :
    (∫ t, sliceVolume K t) = (volume K).toReal := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have he (z : ℝ × (Fin n → ℝ)) : e z = Fin.cons z.1 z.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Equiv.coe_fn_mk, Fin.zero_succAbove]
  have hpres := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hint := hpres.integral_comp e.measurableEmbedding (K.indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator_one hK.measurableSet] at hint
  change (∫ x, K.indicator (fun _ => (1 : ℝ)) (e x)) = _ at hint
  simp only [he, Measure.volume_eq_prod] at hint
  rw [integral_prod _ (integrable_indicator_pair hK)] at hint
  simpa only [← sliceVolume_as_integral hK] using hint

end FacetVolume

end

end OAI
