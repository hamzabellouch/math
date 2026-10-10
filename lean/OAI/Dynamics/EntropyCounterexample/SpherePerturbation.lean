import Mathlib

namespace OAI

noncomputable section

open Filter Topology
open scoped OnePoint

namespace Problem340

def perturbedSquare (c : ℂ) : OnePoint ℂ → OnePoint ℂ :=
  OnePoint.map (fun z : ℂ => z ^ 2 + c)

@[simp] theorem perturbedSquare_infty (c : ℂ) :
    perturbedSquare c ∞ = ∞ := rfl

@[simp] theorem perturbedSquare_coe (c z : ℂ) :
    perturbedSquare c (z : OnePoint ℂ) = ((z ^ 2 + c : ℂ) : OnePoint ℂ) := rfl

private theorem tendsto_norm_perturbedSquare (c : ℂ) :
    Tendsto (fun p : ℂ × ℂ => ‖p.2 ^ 2 + p.1‖)
      (𝓝 c ×ˢ cocompact ℂ) atTop := by
  have hz : Tendsto (fun p : ℂ × ℂ => ‖p.2‖)
      (𝓝 c ×ˢ cocompact ℂ) atTop :=
    tendsto_norm_cocompact_atTop.comp tendsto_snd
  have hp := (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hz
  have hc : Tendsto (fun p : ℂ × ℂ => -‖p.1‖)
      (𝓝 c ×ˢ cocompact ℂ) (𝓝 (-‖c‖)) := tendsto_fst.norm.neg
  apply tendsto_atTop_mono (f := fun p : ℂ × ℂ => ‖p.2‖ ^ 2 + -‖p.1‖)
  · intro p
    have h := norm_sub_norm_le (p.2 ^ 2) (-p.1)
    rw [norm_pow] at h
    simpa only [norm_neg, sub_neg_eq_add, sub_eq_add_neg, neg_neg] using h
  · exact hp.atTop_add hc

theorem continuous_perturbedSquare :
    Continuous (fun p : ℂ × OnePoint ℂ => perturbedSquare p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨c, z⟩
  induction z using OnePoint.rec with
  | infty =>
      change Tendsto _ (𝓝 (c, (∞ : OnePoint ℂ))) (𝓝 ∞)
      conv => arg 2; rw [nhds_prod_eq, OnePoint.nhds_infty_eq, prod_sup]
      rw [tendsto_sup]
      constructor
      · rw [prod_map_right, tendsto_map'_iff]
        have hproper : Tendsto (fun p : ℂ × ℂ => p.2 ^ 2 + p.1)
            (𝓝 c ×ˢ cocompact ℂ) (cocompact ℂ) := by
          simpa only [Metric.cobounded_eq_cocompact] using
            (tendsto_norm_atTop_iff_cobounded.mp (tendsto_norm_perturbedSquare c))
        change Tendsto (fun p : ℂ × ℂ => ((p.2 ^ 2 + p.1 : ℂ) : OnePoint ℂ))
          (𝓝 c ×ˢ coclosedCompact ℂ) (𝓝 ∞)
        simpa only [Function.comp_def, coclosedCompact_eq_cocompact] using
          (OnePoint.tendsto_coe_infty (X := ℂ)).comp
            (by simpa only [coclosedCompact_eq_cocompact] using hproper)
      · rw [prod_pure, tendsto_map'_iff]
        change Tendsto (fun _ : ℂ => (∞ : OnePoint ℂ)) (𝓝 c) (𝓝 ∞)
        exact tendsto_const_nhds
  | coe z =>
      change Tendsto _ (𝓝 (c, (z : OnePoint ℂ))) (𝓝 ((z ^ 2 + c : ℂ) : OnePoint ℂ))
      rw [nhds_prod_eq, OnePoint.nhds_coe_eq, prod_map_right, tendsto_map'_iff]
      have hpoly : Continuous (fun p : ℂ × ℂ => p.2 ^ 2 + p.1) := by fun_prop
      change Tendsto (fun p : ℂ × ℂ => ((p.2 ^ 2 + p.1 : ℂ) : OnePoint ℂ))
        (𝓝 c ×ˢ 𝓝 z) (𝓝 ((z ^ 2 + c : ℂ) : OnePoint ℂ))
      rw [← nhds_prod_eq]
      exact (OnePoint.continuous_coe.comp hpoly).continuousAt

def perturbedSquareMap {X : Type*} [TopologicalSpace X]
    (C : C(X, ℂ)) (z : C(X, OnePoint ℂ)) : C(X, OnePoint ℂ) where
  toFun x := perturbedSquare (C x) (z x)
  continuous_toFun := continuous_perturbedSquare.comp (C.continuous.prodMk z.continuous)

def perturbedSquareHomotopy {X : Type*} [TopologicalSpace X]
    (C : C(X, ℂ)) (z : C(X, OnePoint ℂ)) :
    (perturbedSquareMap 0 z).Homotopy (perturbedSquareMap C z) where
  toFun p := perturbedSquare ((p.1.val : ℂ) * C p.2) (z p.2)
  continuous_toFun := by
    have hC : Continuous (fun p : unitInterval × X => (p.1.val : ℂ) * C p.2) :=
      (Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
        (C.continuous.comp continuous_snd)
    exact continuous_perturbedSquare.comp (hC.prodMk (z.continuous.comp continuous_snd))
  map_zero_left x := by simp [perturbedSquareMap]
  map_one_left x := by simp [perturbedSquareMap]

theorem perturbedSquareMap_homotopic {X : Type*} [TopologicalSpace X]
    (C : C(X, ℂ)) (z : C(X, OnePoint ℂ)) :
    (perturbedSquareMap 0 z).Homotopic (perturbedSquareMap C z) :=
  ⟨perturbedSquareHomotopy C z⟩

end Problem340

end

end OAI
