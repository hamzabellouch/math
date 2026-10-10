import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Flow.CompactPeriodization

namespace OAI

/-! On the support chart, differentiation commutes exactly with periodization.
Consequently every mixed rapid estimate transfers with the same constant. -/

noncomputable section
open Set Filter
open scoped Topology
namespace RapidForcing.CompactEmbedding

theorem chart_closed : IsClosed chart := by
  have he : chart = (⋂ i : Fin 3, {x : Space | 1 / 4 ≤ x i}) ∩
      (⋂ i : Fin 3, {x : Space | x i ≤ 3 / 4}) := by
    ext x
    simp [chart]
  rw [he]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (EuclideanSpace.proj i).continuous).inter
    (isClosed_iInter fun i => isClosed_le (EuclideanSpace.proj i).continuous continuous_const)

def ChartSupported {E : Type} [Zero E] (f : Field E) : Prop :=
  ∀ t x, x ∉ chart → f t x = 0

namespace ChartSupported
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Field E}

omit [NormedSpace ℝ E] in
theorem tsupport (hf : ChartSupported f) (t : ℝ) : tsupport (f t) ⊆ chart := by
  apply closure_minimal _ chart_closed
  intro x hx
  by_contra hn
  exact hx (hf t x hn)

theorem spatialD (hf : ChartSupported f) (i : Fin 3) :
    ChartSupported (RapidForcing.spatialD i f) := by
  intro t x hx
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  exact hx (hf.tsupport t (tsupport_fderiv_apply_subset ℝ (basis i) hm))

theorem timeD (hf : ChartSupported f) : ChartSupported (RapidForcing.timeD f) := by
  intro t x hx
  change derivWithin (fun s => f s x) (Ici 0) t = 0
  rw [show (fun s => f s x) = (fun _ => (0 : E)) from funext (fun s => hf s x hx)]
  simp

theorem spatialIter (hf : ChartSupported f) (i : Fin 3) (n : ℕ) :
    ChartSupported ((RapidForcing.spatialD i)^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih => simpa only [Function.iterate_succ_apply'] using ih.spatialD i

theorem timeIter (hf : ChartSupported f) (n : ℕ) :
    ChartSupported (RapidForcing.timeD^[n] f) := by
  induction n with
  | zero => exact hf
  | succ n ih => simpa only [Function.iterate_succ_apply'] using ih.timeD

theorem mixedD (hf : ChartSupported f) (l : ℕ) (α : MultiIndex) :
    ChartSupported (RapidForcing.mixedD l α f) :=
  (((hf.spatialIter 2 (α 2)).spatialIter 1 (α 1)).spatialIter 0 (α 0)).timeIter l

end ChartSupported

section Derivatives
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Field E}

theorem periodic_spatialD (hf : ChartSupported f) (i : Fin 3) :
    spatialD i (periodic f) = periodic (spatialD i f) := by
  funext t x
  by_cases hx : ∀ j, x j ≠ (⌊x j⌋ : ℤ)
  · have hr := representative_local_translation hx
    have he : periodic f t =ᶠ[𝓝 x]
        (fun y => f t (y - latticeVector (fun j => ⌊x j⌋))) :=
      hr.mono (fun y hy => congrArg (f t) hy)
    change fderiv ℝ (periodic f t) x (basis i) =
      fderiv ℝ (f t) (representative x) (basis i)
    rw [he.fderiv_eq, fderiv_comp_sub, hr.eq_of_nhds]
  · push Not at hx
    obtain ⟨j, hj⟩ := hx
    have hr := representative_local_outside hj
    have he : periodic f t =ᶠ[𝓝 x] (fun _ => (0 : E)) :=
      hr.mono (fun y hy => hf t (representative y) hy)
    have hd := (hf.spatialD i) t (representative x) hr.self_of_nhds
    change fderiv ℝ (periodic f t) x (basis i) = spatialD i f t (representative x)
    rw [he.fderiv_eq, hd]
    simp

theorem periodic_timeD : timeD (periodic f) = periodic (timeD f) := rfl

theorem periodic_spatialIter (hf : ChartSupported f) (i : Fin 3) (n : ℕ) :
    (spatialD i)^[n] (periodic f) = periodic ((spatialD i)^[n] f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih,
        periodic_spatialD (hf.spatialIter i n), Function.iterate_succ_apply']

theorem periodic_timeIter (n : ℕ) : timeD^[n] (periodic f) = periodic (timeD^[n] f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, periodic_timeD, Function.iterate_succ_apply']

theorem periodic_mixedD (hf : ChartSupported f) (l : ℕ) (α : MultiIndex) :
    mixedD l α (periodic f) = periodic (mixedD l α f) := by
  unfold mixedD spatialMulti
  rw [periodic_spatialIter hf,
    periodic_spatialIter (hf.spatialIter 2 (α 2)),
    periodic_spatialIter ((hf.spatialIter 2 (α 2)).spatialIter 1 (α 1)), periodic_timeIter]

theorem periodic_mixed_bound (hf : ChartSupported f) {J l : ℕ} {α : MultiIndex} {C : ℝ}
    (hb : ∀ t, 0 ≤ t → ∀ x, (1 + t) ^ J * ‖mixedD l α f t x‖ ≤ C) :
    ∀ t, 0 ≤ t → ∀ x, (1 + t) ^ J * ‖mixedD l α (periodic f) t x‖ ≤ C := by
  intro t ht x
  rw [periodic_mixedD hf]
  exact hb t ht (representative x)

theorem periodic_rapid (hf : ChartSupported f) (hr : Rapid f) : Rapid (periodic f) := by
  intro J l α
  obtain ⟨C, hC, hb⟩ := hr J l α
  exact ⟨C, hC, periodic_mixed_bound hf hb⟩

end Derivatives

end RapidForcing.CompactEmbedding

end

end OAI
