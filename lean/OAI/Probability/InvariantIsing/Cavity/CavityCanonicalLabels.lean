import OAI.Probability.InvariantIsing.Spectral.SpectralOverlapPaths
import Mathlib.Topology.Order.ProjIcc

namespace OAI

/-! Canonical spectral labels as continuous monotone functions of the
total overlap, with the diagonal bound built into their range. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

def cavityCanonicalCoordinate {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) (t : ℝ) : ℝ :=
  ∫ r in 0..(Set.projIcc 0 1 zero_le_one t : ℝ), spectralPathDensity ρ eig hρ hρsum p a r

lemma cavityCanonicalCoordinate_nonneg {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) (t : ℝ) :
    0 ≤ cavityCanonicalCoordinate ρ eig hρ hρsum p a t :=
  intervalIntegral.integral_nonneg_of_forall (Set.projIcc 0 1 zero_le_one t).property.1
    (spectralPathDensity_nonneg ρ eig hρ hρsum p a)

lemma cavityCanonicalCoordinate_le_diagonal {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) (t : ℝ) :
    cavityCanonicalCoordinate ρ eig hρ hρsum p a t ≤ spectralGroupDiagonal ρ eig hρ hρsum p a :=
  intervalIntegral.integral_mono_interval le_rfl (Set.projIcc 0 1 zero_le_one t).property.1
    (Set.projIcc 0 1 zero_le_one t).property.2
    (Eventually.of_forall (spectralPathDensity_nonneg ρ eig hρ hρsum p a))
    (spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a ⟨zero_le_one, le_rfl⟩)

lemma cavityCanonicalCoordinate_monotone {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) :
    Monotone (cavityCanonicalCoordinate ρ eig hρ hρsum p a) := by
  intro s t hst
  have hc : (Set.projIcc 0 1 zero_le_one s : ℝ) ≤ (Set.projIcc 0 1 zero_le_one t : ℝ) :=
    max_le_max le_rfl (min_le_min le_rfl hst)
  exact intervalIntegral.integral_mono_interval le_rfl (Set.projIcc 0 1 zero_le_one s).property.1 hc
    (Eventually.of_forall (spectralPathDensity_nonneg ρ eig hρ hρsum p a))
    (spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a (Set.projIcc 0 1 zero_le_one t).property)

lemma continuous_cavityCanonicalCoordinate {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) :
    Continuous (cavityCanonicalCoordinate ρ eig hρ hρsum p a) := by
  have hi := spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a ⟨zero_le_one, le_rfl⟩
  have hp := intervalIntegral.continuousOn_primitive_interval' hi (a := 0) left_mem_uIcc
  have hp' : ContinuousOn (fun z => ∫ r in 0..z, spectralPathDensity ρ eig hρ hρsum p a r)
      (Icc 0 1) := by simpa only [uIcc_of_le zero_le_one] using hp
  exact hp'.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
    (fun t => (Set.projIcc 0 1 zero_le_one t).property)

lemma cavityCanonicalCoordinate_at_path {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) (s : ℝ) :
    cavityCanonicalCoordinate ρ eig hρ hρsum p a (p s) = spectralGroupPath ρ eig hρ hρsum p a s := by
  unfold cavityCanonicalCoordinate spectralGroupPath
  rw [Set.projIcc_of_mem zero_le_one ⟨p.nonneg s, p.le_one s⟩]

def cavityCanonicalLabel {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) (t : ℝ) : Icc (-1 : ℝ) 1 :=
  ⟨cavityCanonicalCoordinate ρ eig hρ hρsum p a t,
    ⟨le_trans (by norm_num) (cavityCanonicalCoordinate_nonneg ρ eig hρ hρsum p a t),
      (cavityCanonicalCoordinate_le_diagonal ρ eig hρ hρsum p a t).trans
        (spectralGroupDiagonal_le_one ρ eig hρ hρsum p a)⟩⟩

lemma continuous_cavityCanonicalLabel {m : ℕ} (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a)
    (hρsum : ∑ a, ρ a = 1) (p : OverlapPath) (a : Fin m) :
    Continuous (cavityCanonicalLabel ρ eig hρ hρsum p a) :=
  (continuous_cavityCanonicalCoordinate ρ eig hρ hρsum p a).subtype_mk _

end InvariantIsing

end

end OAI
