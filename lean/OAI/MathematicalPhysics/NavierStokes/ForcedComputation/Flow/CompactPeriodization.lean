import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.CompactRapidEmbedding

namespace OAI

/-! Periodization in a chart strictly separated from every integer face. The
fractional representative is only a definition: smoothness follows from local
translation or local zero, so no differentiability of the fractional part at
an integer is asserted. -/

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace RapidForcing.CompactEmbedding

def latticeVector (k : Fin 3 → ℤ) : Space := WithLp.toLp 2 (fun i => (k i : ℝ))

def representative (x : Space) : Space := WithLp.toLp 2 (fun i => Int.fract (x i))

@[simp] theorem representative_apply (x : Space) (i : Fin 3) :
    representative x i = Int.fract (x i) := rfl

@[simp] theorem latticeVector_apply (k : Fin 3 → ℤ) (i : Fin 3) :
    latticeVector k i = (k i : ℝ) := rfl

theorem representative_add_lattice (x : Space) (k : Fin 3 → ℤ) :
    representative (x + latticeVector k) = representative x := by
  ext i
  exact Int.fract_add_intCast (x i) (k i)

theorem representative_eq {x : Space} (hx : ∀ i, x i ∈ Ico (0 : ℝ) 1) :
    representative x = x := by
  ext i
  exact Int.fract_eq_self.mpr (hx i)

def periodic {E : Type} (f : Field E) : Field E := fun t x => f t (representative x)

theorem periodic_add_lattice {E : Type} (f : Field E) (t : ℝ)
    (x : Space) (k : Fin 3 → ℤ) :
    periodic f t (x + latticeVector k) = periodic f t x := by
  simp only [periodic, representative_add_lattice]

theorem periodic_eq_on_chart {E : Type} (f : Field E) (t : ℝ) {x : Space}
    (hx : x ∈ chart) : periodic f t x = f t x := by
  rw [periodic, representative_eq]
  intro i
  exact ⟨(chart_inside_unit hx i).1.le, (chart_inside_unit hx i).2⟩

theorem representative_local_translation {x : Space}
    (hx : ∀ i, x i ≠ (⌊x i⌋ : ℤ)) :
    representative =ᶠ[𝓝 x] (fun y => y - latticeVector (fun i => ⌊x i⌋)) := by
  have hlocal : ∀ i : Fin 3, ∀ᶠ y in 𝓝 x,
      (⌊x i⌋ : ℝ) < y i ∧ y i < (⌊x i⌋ : ℝ) + 1 := by
    intro i
    exact ((EuclideanSpace.proj i).continuous.continuousAt).eventually
      (Ioo_mem_nhds ((Int.floor_le (x i)).lt_of_ne (Ne.symm (hx i)))
        (Int.lt_floor_add_one (x i)))
  filter_upwards [Filter.eventually_all.mpr hlocal] with y hy
  ext i
  have hk : ⌊y i⌋ = ⌊x i⌋ := Int.floor_eq_iff.mpr ⟨(hy i).1.le, (hy i).2⟩
  simp only [representative_apply, PiLp.sub_apply, latticeVector_apply, Int.fract, hk]

theorem fract_near_integer {x : ℝ} {k : ℤ}
    (hx : x ∈ Ioo ((k : ℝ) - 1 / 8) ((k : ℝ) + 1 / 8)) :
    Int.fract x < 1 / 4 ∨ 3 / 4 < Int.fract x := by
  have hfract : Int.fract (x - (k : ℝ)) = Int.fract x := Int.fract_sub_intCast x k
  rw [← hfract]
  by_cases hp : 0 ≤ x - (k : ℝ)
  · left
    rw [Int.fract_eq_self.mpr ⟨hp, by linarith [hx.2]⟩]
    linarith [hx.2]
  · right
    have hk : ⌊x - (k : ℝ)⌋ = (-1 : ℤ) :=
      Int.floor_eq_iff.mpr ⟨by norm_num; linarith [hx.1], by norm_num; linarith⟩
    rw [Int.fract, hk]
    norm_num
    linarith [hx.1]

theorem representative_local_outside {x : Space} {i : Fin 3}
    (hx : x i = (⌊x i⌋ : ℤ)) : ∀ᶠ y in 𝓝 x, representative y ∉ chart := by
  have hl : (⌊x i⌋ : ℝ) - 1 / 8 < x i := by linarith [hx]
  have hr : x i < (⌊x i⌋ : ℝ) + 1 / 8 := by linarith [hx]
  filter_upwards [((EuclideanSpace.proj i).continuous.continuousAt).eventually
    (Ioo_mem_nhds hl hr)] with y hy
  intro hc
  rcases fract_near_integer hy with h | h
  · exact (not_lt_of_ge (hc.1 i)) h
  · exact (not_lt_of_ge (hc.2 i)) h

theorem periodic_local {E : Type} [Zero E] (f : Field E)
    (hf : ∀ t x, x ∉ chart → f t x = 0) (x : Space) :
    (∃ k : Fin 3 → ℤ, ∀ᶠ y in 𝓝 x, ∀ t, periodic f t y = f t (y - latticeVector k)) ∨
      (∀ᶠ y in 𝓝 x, ∀ t, periodic f t y = 0) := by
  by_cases hx : ∀ i, x i ≠ (⌊x i⌋ : ℤ)
  · left
    refine ⟨fun i => ⌊x i⌋, ?_⟩
    filter_upwards [representative_local_translation hx] with y hy t
    simp only [periodic, hy]
  · right
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    filter_upwards [representative_local_outside hi] with y hy t
    exact hf t (representative y) hy

theorem periodic_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Field E} (hs : ContDiff ℝ ∞ (Function.uncurry f))
    (hf : ∀ t x, x ∉ chart → f t x = 0) :
    ContDiff ℝ ∞ (Function.uncurry (periodic f)) := by
  apply contDiff_iff_contDiffAt.mpr
  rintro ⟨t, x⟩
  rcases periodic_local f hf x with ⟨k, hk⟩ | hz
  · have he : Function.uncurry (periodic f) =ᶠ[𝓝 (t, x)]
        (fun p : ℝ × Space => f p.1 (p.2 - latticeVector k)) := by
      filter_upwards [continuous_snd.continuousAt.eventually hk] with p hp
      exact hp p.1
    exact (hs.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const))).contDiffAt.congr_of_eventuallyEq he
  · have he : Function.uncurry (periodic f) =ᶠ[𝓝 (t, x)] (fun _ => (0 : E)) := by
      filter_upwards [continuous_snd.continuousAt.eventually hz] with p hp
      exact hp p.1
    exact contDiffAt_const.congr_of_eventuallyEq he

end RapidForcing.CompactEmbedding

end

end OAI
