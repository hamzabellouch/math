import OAI.Combinatorics.SparsestCut.Directions

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GaussianNonparallel

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => stdGaussian E

lemma gaussian_inner_zero_measure (v : E) (hv : v ≠ 0) :
    (stdGaussian E) {x | inner ℝ v x = 0} = 0 := by
  let c : ℝ≥0 := ⟨‖v‖^2, sq_nonneg _⟩
  have hc : c ≠ 0 := by
    intro h
    have := congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    change ‖v‖^2 = 0 at this
    exact hv (norm_eq_zero.mp (sq_eq_zero_iff.mp this))
  let := nullSingletonClass_gaussianReal («μ» := 0) hc
  have hmap : (stdGaussian E).map (fun x => inner ℝ v x) = gaussianReal 0 c := by
    have h := IsGaussian.map_eq_gaussianReal («μ» := stdGaussian E) (innerSL ℝ v)
    simp only [integral_strongDual_stdGaussian, variance_dual_stdGaussian,
      innerSL_apply_norm] at h
    convert h using 2
    · rfl
    · apply NNReal.eq
      change ‖v‖^2 = ((‖v‖^2).toNNReal : ℝ)
      simp
  have h := congrArg (fun ν : Measure ℝ => ν {0}) hmap
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _), measure_singleton] at h
  exact h

lemma gaussian_coordinate_ne (i : Fin m) : ∀ᵐ x : E ∂μ, x i ≠ 0 := by
  have hv : (EuclideanSpace.single i 1 : E) ≠ 0 := by
    intro h
    have hh := congrArg (fun x : E => x i) h
    simp at hh
  have h := gaussian_inner_zero_measure (EuclideanSpace.single i 1) hv
  apply ae_iff.mpr
  simpa [EuclideanSpace.inner_single_left] using h

def cross (i j : Fin m) (x y : E) : ℝ := x i * y j - x j * y i

lemma gaussian_cross_zero_measure (i j : Fin m) (hij : i ≠ j) :
    ((μ).prod μ) {z : E × E | cross i j z.1 z.2 = 0} = 0 := by
  rw [Measure.prod_apply (by unfold cross; measurability)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [gaussian_coordinate_ne i] with x hx
  let v : E := EuclideanSpace.single j (x i) - EuclideanSpace.single i (x j)
  have hv : v ≠ 0 := by
    intro h
    have hh := congrArg (fun x : E => x j) h
    have hh' : x i = 0 := by simpa [v, PiLp.single_apply, hij, Ne.symm hij] using hh
    exact hx hh'
  have hid (y : E) : inner ℝ v y = cross i j x y := by
    simp [v, cross, inner_sub_left, EuclideanSpace.inner_single_left]
  simpa only [preimage_ofPred_eq, hid, Pi.zero_apply] using gaussian_inner_zero_measure v hv

lemma ae_cross_ne (i j : Fin m) (hij : i ≠ j) :
    ∀ᵐ z : E × E ∂(μ).prod μ, cross i j z.1 z.2 ≠ 0 := by
  apply ae_iff.mpr
  simpa only [not_not] using gaussian_cross_zero_measure i j hij

lemma iid_cross_ne {N : ℕ} (i j : Fin m) (hij : i ≠ j) (a b : Fin N) (hab : a ≠ b) :
    ∀ᵐ g : Fin N → E ∂Measure.pi (fun _ => μ), cross i j (g a) (g b) ≠ 0 := by
  let ν := Measure.pi (fun _ : Fin N => μ)
  have hind : iIndepFun (fun k (g : Fin N → E) => g k) ν :=
    iIndepFun_pi («μ» := fun _ : Fin N => μ) (fun _ => aemeasurable_id)
  have hmap := (hind.indepFun hab).map_prod_eq_prod_map_map
    (measurable_pi_apply a).aemeasurable (measurable_pi_apply b).aemeasurable
  rw [(measurePreserving_eval (fun _ : Fin N => μ) a).map_eq,
    (measurePreserving_eval (fun _ : Fin N => μ) b).map_eq] at hmap
  have hh := congrArg (fun ν : Measure (E × E) => ν {z | cross i j z.1 z.2 = 0}) hmap
  rw [Measure.map_apply (by fun_prop) (by unfold cross; measurability),
    gaussian_cross_zero_measure i j hij] at hh
  apply ae_iff.mpr
  simpa only [ν, preimage_ofPred_eq, not_not] using hh

lemma iid_pairwise_nonparallel {N : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ g : Fin N → E ∂Measure.pi (fun _ => μ),
      ∀ a b, a ≠ b → ∀ t : ℝ, g a ≠ t • g b := by
  let i : Fin m := ⟨0, by omega⟩
  let j : Fin m := ⟨1, by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; simp [i,j] at this
  have hh : ∀ a b : Fin N, ∀ᵐ g : Fin N → E ∂Measure.pi (fun _ => μ),
      a ≠ b → cross i j (g a) (g b) ≠ 0 := by
    intro a b
    by_cases hab : a = b
    · exact ae_of_all _ (fun _ hn => (hn hab).elim)
    · filter_upwards [iid_cross_ne i j hij a b hab] with g hg using fun _ => hg
  have hall := (ae_all_iff.mpr (fun a => ae_all_iff.mpr (hh a)))
  filter_upwards [hall] with g hg
  intro a b hab t h
  apply hg a b hab
  rw [h]
  simp [cross]
  ring

lemma charts_pairwise_nonparallel {N S : ℕ} (hm : 2 ≤ m) :
    ∀ᵐ g : Fin S → Fin N → E ∂Measure.pi (fun _ => Measure.pi (fun _ => μ)),
      ∀ s a b, a ≠ b → ∀ t : ℝ, g s a ≠ t • g s b := by
  apply ae_all_iff.mpr
  intro s
  exact (measurePreserving_eval (fun _ : Fin S => Measure.pi (fun _ : Fin N => μ)) s).quasiMeasurePreserving.ae
    (iid_pairwise_nonparallel hm)

end UniformSparsestCut.GaussianNonparallel

end

end OAI
