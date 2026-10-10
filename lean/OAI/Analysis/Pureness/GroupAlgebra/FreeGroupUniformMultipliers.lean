import OAI.Analysis.Pureness.GroupAlgebra.FreeGroupFiniteRadial

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
local instance freeGroupUniformMultipliersDecidableEq {X : Type*} : DecidableEq X := Classical.decEq X
local instance freeGroupUniformMultipliersFreeGroupDecidableEq : DecidableEq (FreeGroup ℕ) := Classical.decEq _

def freeGroupApproximationRadius (n : ℕ) : ℝ := 1 - (1 / 2 : ℝ) ^ (n + 1)

lemma freeGroupApproximationRadius_nonneg (n : ℕ) : 0 ≤ freeGroupApproximationRadius n := by
  have h : (1 / 2 : ℝ) ^ (n + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  exact sub_nonneg.mpr h

lemma freeGroupApproximationRadius_lt_one (n : ℕ) : freeGroupApproximationRadius n < 1 := by
  have h : 0 < (1 / 2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
  exact sub_lt_self _ h

lemma freeGroupApproximationRadius_tendsto :
    Tendsto freeGroupApproximationRadius atTop (nhds 1) := by
  change Tendsto (fun n : ℕ => 1 - (1 / 2 : ℝ) ^ (n + 1)) atTop (nhds 1)
  have h : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hs := h.comp (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, sub_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub hs

variable {A H : Type*} [CStarAlgebra A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (hα : Function.Injective α)

include hα in

theorem exists_freeGroup_uniform_finite_multipliers :
    ∃ (s : ℕ → Finset (FreeGroup ℕ)) (c : ℕ → FreeGroup ℕ → ℂ),
      (∀ n (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype),
        ‖spatialFiniteFourier (G := FreeGroup ℕ) α (s n) (c n) x‖ ≤ 2 * ‖x‖) ∧
      ∀ g, Tendsto (fun n => if g ∈ s n then c n g else 0) atTop (nhds 1) := by
  have hm (n : ℕ) := exists_spatialRadialTruncation_bound (X := ℕ) α hα
    (freeGroupApproximationRadius n) (freeGroupApproximationRadius_nonneg n)
    (freeGroupApproximationRadius_lt_one n) (n + 1)
  choose m hm hnorm using hm
  refine ⟨fun n => freeGroupFiniteBall n (m n),
    fun n g => ((freeGroupApproximationRadius n ^ (canonicalFreeWord g).length : ℝ) : ℂ), ?_, ?_⟩
  · intro n x
    exact finiteRadial_norm_le α hα _ n (m n) (hnorm n) x
  · intro g
    have hs : ∀ᶠ n in atTop, g ∈ freeGroupFiniteBall n (m n) := by
      filter_upwards [eventually_mem_initialFreeSubgroup g, eventually_ge_atTop (canonicalFreeWord g).length]
        with n hgroup hn
      apply (mem_freeGroupFiniteBall n (m n) g).mpr
      exact ⟨hgroup, by have := hm n; omega⟩
    have hc : Tendsto (fun n => ((freeGroupApproximationRadius n ^ (canonicalFreeWord g).length : ℝ) : ℂ))
        atTop (nhds 1) := by
      simpa only [Function.comp_def, one_pow, Complex.ofReal_one] using
        (Complex.continuous_ofReal.tendsto _).comp
        (freeGroupApproximationRadius_tendsto.pow (canonicalFreeWord g).length)
    apply hc.congr'
    filter_upwards [hs] with n hn
    exact (ite_eq_left hn).symm

include hα in

theorem exists_freeGroup_finite_fourier_approximation :
    ∃ (s : ℕ → Finset (FreeGroup ℕ)) (c : ℕ → FreeGroup ℕ → ℂ),
      (∀ n (x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype),
        ‖spatialFiniteFourier (G := FreeGroup ℕ) α (s n) (c n) x‖ ≤ 2 * ‖x‖) ∧
      ∀ x : representedSpatialTensor α (reducedGroupAlgebra (FreeGroup ℕ)).subtype,
        Tendsto (fun n => spatialFiniteFourier (G := FreeGroup ℕ) α (s n) (c n) x) atTop (nhds x) := by
  refine (exists_freeGroup_uniform_finite_multipliers (A := A) (H := H) α hα).elim ?_
  intro s hs
  refine hs.elim ?_
  intro c h
  exact ⟨s, c, h.1, fun x => spatialFiniteFourier_tendsto_of_uniform_bound
    (G := FreeGroup ℕ) α hα s c 2 h.1 h.2 x⟩
end CuntzPureness

end

end OAI
