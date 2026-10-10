import OAI.GroupTheory.PolycyclicRecognition.Geometry.ValuedEigenlineContraction

namespace OAI

/-! # Separated eigenline cones over a normed coefficient field -/

noncomputable section
namespace PolycyclicRecognition.ValuedLinearDynamics

variable {K V : Type*} [NontriviallyNormedField K] [NormedAddCommGroup V] [NormedSpace K V]

def cone (φ : V →L[K] K) (v : V) (ε : ℝ) : Set V :=
  {x | x ≠ 0 ∧ ‖remainder φ v x‖ ≤ ε * ‖φ x‖}

theorem cone_functional_ne_zero (φ : V →L[K] K) (v : V) (ε : ℝ)
    {x : V} (hx : x ∈ cone φ v ε) : φ x ≠ 0 := by
  intro hz
  have hnorm : ‖x‖ ≤ 0 := by simpa [remainder, hz] using hx.2
  exact hx.1 (norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _)))

theorem cone_norm_bound (ψ : V →L[K] K) (w x : V) (ε : ℝ)
    (hx : ‖remainder ψ w x‖ ≤ ε * ‖ψ x‖) :
    ‖x‖ ≤ (‖w‖ + ε) * ‖ψ x‖ := by
  have he : x = remainder ψ w x + ψ x • w := by simp [remainder]
  calc
    ‖x‖ = ‖remainder ψ w x + ψ x • w‖ := congrArg norm he
    _ ≤ ‖remainder ψ w x‖ + ‖ψ x • w‖ := norm_add_le _ _
    _ ≤ ε * ‖ψ x‖ + ‖ψ x‖ * ‖w‖ := by rw [norm_smul]; linarith only [hx]
    _ = (‖w‖ + ε) * ‖ψ x‖ := by ring

theorem cone_functional_lower (ψ θ : V →L[K] K) (w x : V) (ε : ℝ)
    (hx : ‖remainder ψ w x‖ ≤ ε * ‖ψ x‖) :
    (‖θ w‖ - ‖θ‖ * ε) * ‖ψ x‖ ≤ ‖θ x‖ := by
  have he : θ x - θ (remainder ψ w x) = ψ x * θ w := by simp [remainder]
  have hbound : ‖θ (remainder ψ w x)‖ ≤ (‖θ‖ * ε) * ‖ψ x‖ :=
    (θ.le_opNorm _).trans (by nlinarith [norm_nonneg θ])
  have htri := norm_sub_le (θ x) (θ (remainder ψ w x))
  rw [he, norm_mul] at htri
  nlinarith

theorem cone_functional_upper (ψ θ : V →L[K] K) (w x : V) (ε : ℝ)
    (hx : ‖remainder ψ w x‖ ≤ ε * ‖ψ x‖) :
    ‖θ x‖ ≤ (‖θ w‖ + ‖θ‖ * ε) * ‖ψ x‖ := by
  have he : θ x = θ (remainder ψ w x) + ψ x * θ w := by simp [remainder]
  calc
    ‖θ x‖ = ‖θ (remainder ψ w x) + ψ x * θ w‖ := congrArg norm he
    _ ≤ ‖θ (remainder ψ w x)‖ + ‖ψ x * θ w‖ := norm_add_le _ _
    _ ≤ ‖θ‖ * ‖remainder ψ w x‖ + ‖ψ x‖ * ‖θ w‖ :=
      add_le_add (θ.le_opNorm _) (le_of_eq (norm_mul _ _))
    _ ≤ ‖θ‖ * (ε * ‖ψ x‖) + ‖ψ x‖ * ‖θ w‖ := by gcongr
    _ = _ := by ring

theorem cone_transverse_nonzero (ψ θ : V →L[K] K) (w : V) (ε : ℝ)
    (hgap : ‖θ‖ * ε < ‖θ w‖) {x : V} (hx : x ∈ cone ψ w ε) : θ x ≠ 0 := by
  have hp : 0 < (‖θ w‖ - ‖θ‖ * ε) * ‖ψ x‖ :=
    mul_pos (sub_pos.mpr hgap) (norm_pos_iff.mpr (cone_functional_ne_zero ψ w ε hx))
  exact norm_pos_iff.mp (hp.trans_le (cone_functional_lower ψ θ w x ε hx.2))

theorem cone_transverse_bound (ψ θ : V →L[K] K) (w x : V) (ε : ℝ)
    (hε : 0 ≤ ε) (hgap : ‖θ‖ * ε < ‖θ w‖)
    (hx : ‖remainder ψ w x‖ ≤ ε * ‖ψ x‖) :
    ‖x‖ ≤ ((‖w‖ + ε) / (‖θ w‖ - ‖θ‖ * ε)) * ‖θ x‖ := by
  have hg : 0 < ‖θ w‖ - ‖θ‖ * ε := sub_pos.mpr hgap
  have hf := cone_functional_lower ψ θ w x ε hx
  calc
    ‖x‖ ≤ (‖w‖ + ε) * ‖ψ x‖ := cone_norm_bound ψ w x ε hx
    _ ≤ (‖w‖ + ε) * (‖θ x‖ / (‖θ w‖ - ‖θ‖ * ε)) :=
      mul_le_mul_of_nonneg_left ((le_div_iff₀ hg).mpr (by nlinarith [hf]))
        (add_nonneg (norm_nonneg _) hε)
    _ = _ := by ring

theorem cones_disjoint_of_separator (φ ψ θ : V →L[K] K) (v w : V) (ε : ℝ)
    (hθv : θ v = 0)
    (hsep : (‖θ‖ * ε) * (‖φ w‖ + ‖φ‖ * ε) < ‖θ w‖ - ‖θ‖ * ε) :
    Disjoint (cone φ v ε) (cone ψ w ε) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  have hθ := cone_functional_upper φ θ v x ε hx.2
  rw [hθv, norm_zero, zero_add] at hθ
  have hφ := cone_functional_upper ψ φ w x ε hy.2
  have hl := cone_functional_lower ψ θ w x ε hy.2
  have hpos : 0 < ‖ψ x‖ := norm_pos_iff.mpr (cone_functional_ne_zero ψ w ε hy)
  have hε : 0 ≤ ε := by
    have hfx : 0 < ‖φ x‖ := norm_pos_iff.mpr (cone_functional_ne_zero φ v ε hx)
    have := (norm_nonneg (remainder φ v x)).trans hx.2
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hφ (mul_nonneg (norm_nonneg θ) hε)
  have hstrict := mul_lt_mul_of_pos_right hsep hpos
  nlinarith

section Complete

variable [CompleteSpace K] [FiniteDimensional K V]

theorem small_cones_disjoint (φ ψ : V →L[K] K) (v w : V)
    (hw : w ∉ Submodule.span K ({v} : Set V)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 ≤ t → t ≤ ε → Disjoint (cone φ v t) (cone ψ w t) := by
  obtain ⟨f, hfw, hf⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw inferInstance
  let θ := f.toContinuousLinearMap
  have hθv : θ v = 0 := by
    have hh : f v ∈ (Submodule.span K ({v} : Set V)).map f :=
      ⟨v, Submodule.subset_span (Set.mem_singleton v), rfl⟩
    rw [hf, Submodule.mem_bot] at hh
    exact hh
  have hθw : θ w ≠ 0 := hfw
  let p : ℝ → ℝ := fun t => (‖θ‖ * t) * (‖φ w‖ + ‖φ‖ * t) + ‖θ‖ * t
  obtain ⟨ε, hε, hεp⟩ := PolycyclicRecognition.exists_positive_interval_lt p (by fun_prop)
    ‖θ w‖ (by simpa only [p, mul_zero, zero_mul, add_zero] using norm_pos_iff.mpr hθw)
  refine ⟨ε, hε, fun t ht htε => cones_disjoint_of_separator φ ψ θ v w t hθv ?_⟩
  have hh := hεp t ht htε
  dsimp only [p] at hh
  linarith

end Complete
end PolycyclicRecognition.ValuedLinearDynamics

end

end OAI
