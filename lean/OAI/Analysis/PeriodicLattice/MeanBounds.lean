import OAI.Analysis.PeriodicLattice.PeriodicInverse

namespace OAI

/-! Mean-zero corrections and rapid derivative bounds. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingMeanBounds {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace PeriodicInverse
open scoped ContDiff
open RapidCalculus Set MeasureTheory

def mean (H : ℝ → ℝ → ℝ) (t _y : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, H t s

theorem mean_contDiff {H : ℝ → ℝ → ℝ} (hH : ContDiff ℝ ∞ (Function.uncurry H)) :
    ContDiff ℝ ∞ (Function.uncurry (mean H)) :=
  (contDiff_intervalIntegral hH 0 1).comp contDiff_fst

theorem mean_periodic (H : ℝ → ℝ → ℝ) (t : ℝ) : Function.Periodic (mean H t) 1 := fun _ => rfl

theorem mean_timeD {H : ℝ → ℝ → ℝ} (hH : ContDiff ℝ ∞ (Function.uncurry H)) :
    biD true (mean H) = mean (biD true H) := by
  funext t y
  exact (hasDerivAt_intervalIntegral hH 0 1 t).deriv

theorem mean_spaceD (H : ℝ → ℝ → ℝ) : biD false (mean H) = 0 := by
  funext t y
  exact deriv_const _ _

theorem biD_zero (i : Bool) : biD i (0 : ℝ → ℝ → ℝ) = 0 := by
  funext t y
  cases i <;> exact deriv_const _ _

theorem mean_wordD {H : ℝ → ℝ → ℝ} (hH : ContDiff ℝ ∞ (Function.uncurry H)) (w : List Bool) :
    wordD w (mean H) = if false ∈ w then 0 else mean (wordD w H) := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [wordD_cons, ih]
    by_cases hw : false ∈ w
    · simp only [hw, ↓reduceIte, biD_zero, List.mem_cons, or_true]
    · simp only [hw, ↓reduceIte, List.mem_cons, or_false]
      cases i
      · simp only [↓reduceIte, mean_spaceD]
      · simp only [Bool.false_eq_true, ↓reduceIte, mean_timeD (wordD_contDiff hH w)]
        rfl

theorem mean_rapid {H : ℝ → ℝ → ℝ} (hH : Rapid2 H) : Rapid2 (mean H) := by
  refine ⟨mean_contDiff hH.smooth, fun w J => ?_⟩
  rw [mean_wordD hH.smooth]
  split_ifs
  · exact ⟨0, fun t _ y => by simp⟩
  · obtain ⟨C, hC⟩ := hH.bound w J
    refine ⟨C, fun t ht y => ?_⟩
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (f := fun s => (1 + t) ^ J * wordD w H t s) (C := C) (fun s _ => by
        rw [norm_mul, Real.norm_eq_abs ((1 + t)^J), abs_of_nonneg (by positivity)]
        exact hC t ht s)
    simpa only [intervalIntegral.integral_const_mul, norm_mul, Real.norm_eq_abs ((1 + t)^J),
      abs_of_nonneg (show 0 ≤ (1 + t)^J by positivity), sub_zero, abs_one, mul_one, mean] using hi

end PeriodicInverse
namespace TorusCalculus

open scoped ContDiff

section Schwarz
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem directional_commute {F : E → A} (hF : ContDiff ℝ ∞ F) (u v x : E) :
    fderiv ℝ (fun y => fderiv ℝ F y v) x u =
      fderiv ℝ (fun y => fderiv ℝ F y u) x v := by
  have hd : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have heq (w z : E) : fderiv ℝ (fun y => fderiv ℝ F y w) x z =
      fderiv ℝ (fderiv ℝ F) x z w := by
    rw [((hd x).hasFDerivAt.clm_apply (hasFDerivAt_const w x)).fderiv]
    simp
  rw [heq, heq]
  exact hF.contDiffAt.isSymmSndFDerivAt (by simp) u v

theorem lifted_spaceD_eq {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (i : Fin 3) :
    lifted (spaceD i F) = fun tx => fderiv ℝ (lifted F) tx (0, EuclideanSpace.single i 1) := by
  funext tx
  rw [lifted, spaceD_cover]
  have heq : (fun s : ℝ => spaceLift F tx.1 (tx.2 + EuclideanSpace.single i s)) =
      fun s : ℝ => lifted F (tx + s • (0, EuclideanSpace.single i 1)) := by
    funext s
    rw [single_eq_smul]
    simp only [spaceLift, lifted, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_zero, add_zero]
  rw [heq]
  have hc : HasDerivAt (fun s : ℝ => tx + s • (0, EuclideanSpace.single i 1))
      (0, EuclideanSpace.single i 1) 0 := by
    simpa only [one_smul, id_eq] using (((hasDerivAt_id (0 : ℝ)).smul_const
      ((0 : ℝ), EuclideanSpace.single i 1)).const_add tx)
  have hf : HasFDerivAt (lifted F) (fderiv ℝ (lifted F) tx)
      (tx + (0 : ℝ) • (0, EuclideanSpace.single i 1)) := by
    simpa using (hF.differentiable (by simp) tx).hasFDerivAt
  exact (hf.comp_hasDerivAt 0 hc).deriv

theorem lifted_fullTimeD_eq {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) :
    lifted (fullTimeD F) = fun tx => fderiv ℝ (lifted F) tx (1, 0) := by
  funext tx
  have hc : HasDerivAt (fun s : ℝ => (s, tx.2)) (1, 0) tx.1 :=
    (hasDerivAt_id tx.1).prodMk (hasDerivAt_const _ _)
  exact ((hF.differentiable (by simp) tx).hasFDerivAt.comp_hasDerivAt tx.1 hc).deriv

theorem spaceD_commute {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (i j : Fin 3) :
    spaceD i (spaceD j F) = spaceD j (spaceD i F) := by
  funext t q
  obtain ⟨x, rfl⟩ := mk_surjective q
  change lifted (spaceD i (spaceD j F)) (t, x) = lifted (spaceD j (spaceD i F)) (t, x)
  rw [lifted_spaceD_eq (contDiff_spaceD hF j), lifted_spaceD_eq (contDiff_spaceD hF i),
    lifted_spaceD_eq hF j, lifted_spaceD_eq hF i]
  exact directional_commute hF _ _ _

theorem spaceD_fullTimeD {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (i : Fin 3) :
    spaceD i (fullTimeD F) = fullTimeD (spaceD i F) := by
  funext t q
  obtain ⟨x, rfl⟩ := mk_surjective q
  change lifted (spaceD i (fullTimeD F)) (t, x) = lifted (fullTimeD (spaceD i F)) (t, x)
  rw [lifted_spaceD_eq (contDiff_fullTimeD hF), lifted_fullTimeD_eq (contDiff_spaceD hF i),
    lifted_fullTimeD_eq hF, lifted_spaceD_eq hF i]
  exact directional_commute hF _ _ _

end Schwarz
end TorusCalculus

namespace TorusCalculus

open scoped ContDiff

section LinearOperators
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable {ι : Type*} [Fintype ι]

theorem smooth_slice_differentiable {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (t : ℝ) :
    Differentiable ℝ (spaceLift F t) :=
  (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)

theorem fullTime_hasDerivAt {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (t : ℝ) (q : Torus) :
    HasDerivAt (fun s => F s q) (fullTimeD F t q) t := by
  obtain ⟨x, rfl⟩ := mk_surjective q
  exact ((hF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t).hasDerivAt

theorem spaceD_finite_sum {F : ι → Field A} (hF : ∀ j, ContDiff ℝ ∞ (lifted (F j))) (i : Fin 3) :
    spaceD i (∑ j, F j) = ∑ j, spaceD i (F j) := by
  funext t q
  have hh := HasDerivAt.sum (u := Finset.univ)
    (fun j _ => translation_hasDerivAt (smooth_slice_differentiable (hF j) t) q i 0)
  simpa only [spaceD, single_zero, mk_zero, add_zero, Finset.sum_apply, Finset.sum_fn] using hh.deriv

theorem fullTimeD_finite_sum {F : ι → Field A} (hF : ∀ j, ContDiff ℝ ∞ (lifted (F j))) :
    fullTimeD (∑ j, F j) = ∑ j, fullTimeD (F j) := by
  funext t q
  have hh := HasDerivAt.sum (u := Finset.univ) (fun j _ => fullTime_hasDerivAt (hF j) t q)
  simpa only [fullTimeD, Finset.sum_apply, Finset.sum_fn] using hh.deriv

theorem spaceD_scale {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (c : ℝ) (i : Fin 3) :
    spaceD i (c • F) = c • spaceD i F := by
  funext t q
  have hh := (translation_hasDerivAt (smooth_slice_differentiable hF t) q i 0).const_smul c
  simpa only [spaceD, single_zero, mk_zero, add_zero, Pi.smul_apply, Pi.smul_def] using hh.deriv

theorem laplacian_as_sum (F : Field A) :
    laplacian F = ∑ i : Fin 3, spaceD i (spaceD i F) := by
  funext t q
  simp only [laplacian, Finset.sum_apply]

end LinearOperators

theorem spaceD_component_eq {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U)) (i j : Fin 3) :
    (fun t q => spaceD i U t q j) = spaceD i (fun t q => U t q j) :=
  funext fun t => funext fun q => (spaceD_component (smooth_slice_differentiable hU t) i j q).symm

theorem fullTimeD_component_eq {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U)) (j : Fin 3) :
    (fun t q => fullTimeD U t q j) = fullTimeD (fun t q => U t q j) := by
  funext t q
  exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp_hasDerivAt t
    (fullTime_hasDerivAt hU t q)).deriv.symm

theorem divergence_as_sum (U : VectorField) :
    divergence U = ∑ j : Fin 3, spaceD j (fun t q => U t q j) := by
  funext t q
  simp only [divergence, Finset.sum_apply]

theorem contDiff_divergence {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U)) :
    ContDiff ℝ ∞ (lifted (divergence U)) :=
  ContDiff.sum (s := Finset.univ) (fun j _ => contDiff_spaceD (contDiff_component hU j) j)

theorem divergence_fullTimeD {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U)) :
    divergence (fullTimeD U) = fullTimeD (divergence U) := by
  rw [divergence_as_sum, divergence_as_sum,
    fullTimeD_finite_sum (fun j => contDiff_spaceD (contDiff_component hU j) j)]
  simp_rw [fullTimeD_component_eq hU, spaceD_fullTimeD (contDiff_component hU _)]

theorem divergence_spaceD {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U)) (i : Fin 3) :
    divergence (spaceD i U) = spaceD i (divergence U) := by
  rw [divergence_as_sum, divergence_as_sum,
    spaceD_finite_sum (fun j => contDiff_spaceD (contDiff_component hU j) j)]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [spaceD_component_eq hU, spaceD_commute (contDiff_component hU _)]

theorem divergence_finite_sum {ι : Type*} [Fintype ι] {U : ι → VectorField}
    (hU : ∀ j, ContDiff ℝ ∞ (lifted (U j))) :
    divergence (∑ j, U j) = ∑ j, divergence (U j) := by
  simp only [divergence_as_sum]
  have he (k : Fin 3) : (fun t q => (∑ j, U j) t q k) = ∑ j, (fun t q => U j t q k) := by
    funext t q
    simp only [Finset.sum_apply, WithLp.ofLp_sum]
  simp_rw [he, spaceD_finite_sum (fun j => contDiff_component (hU j) _)]
  exact Finset.sum_comm

theorem divergence_laplacian {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U)) :
    divergence (laplacian U) = laplacian (divergence U) := by
  rw [laplacian_as_sum, divergence_finite_sum (fun i => contDiff_spaceD (contDiff_spaceD hU i) i), laplacian_as_sum]
  simp_rw [divergence_spaceD (contDiff_spaceD hU _), divergence_spaceD hU]

theorem divergence_add {U V : VectorField} (hU : ContDiff ℝ ∞ (lifted U))
    (hV : ContDiff ℝ ∞ (lifted V)) : divergence (U + V) = divergence U + divergence V := by
  funext t q
  simp only [divergence, Pi.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  exact spaceD_add (smooth_slice_differentiable (contDiff_component hU i) t)
    (smooth_slice_differentiable (contDiff_component hV i) t) i q

theorem divergence_scale {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U)) (c : ℝ) :
    divergence (c • U) = c • divergence U := by
  rw [divergence_as_sum, divergence_as_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact spaceD_scale (contDiff_component hU i) c i

theorem divergence_fullForce {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U))
    (hdiv : divergence U = 0) (ν : ℝ) :
    divergence (Residual.fullForce ν U) = divergence (advection U) := by
  have he : Residual.fullForce ν U = fullTimeD U + advection U - ν • laplacian U := rfl
  rw [he]
  have hs : divergence (fullTimeD U + advection U - ν • laplacian U) =
      divergence (fullTimeD U + advection U) - divergence (ν • laplacian U) := by
    funext t q
    exact divergence_sub (smooth_slice_differentiable (F := fullTimeD U + advection U)
      ((contDiff_fullTimeD hU).add (contDiff_advection hU)) t)
      (smooth_slice_differentiable (F := ν • laplacian U) ((contDiff_laplacian hU).const_smul ν) t) q
  rw [hs, divergence_add (contDiff_fullTimeD hU) (contDiff_advection hU),
    divergence_scale (contDiff_laplacian hU), divergence_fullTimeD hU, divergence_laplacian hU, hdiv]
  have hz : fullTimeD (0 : ScalarField) = 0 := by
    funext t q
    exact deriv_const _ _
  have hl : laplacian (0 : ScalarField) = 0 := by
    simp [laplacian_as_sum, Residual.spaceD_zero]
  simp [hz, hl]

end TorusCalculus

namespace TorusCalculus
open scoped ContDiff

theorem divergence_advection {U : VectorField} (hU : ContDiff ℝ ∞ (lifted U))
    (hdiv : divergence U = 0) (t : ℝ) (q : Torus) :
    divergence (advection U) t q =
      ∑ i : Fin 3, ∑ j : Fin 3, spaceD i (fun t q => U t q j) t q *
        spaceD j (fun t q => U t q i) t q := by
  let C (i : Fin 3) : ScalarField := fun t q => U t q i
  have hC (i : Fin 3) : ContDiff ℝ ∞ (lifted (C i)) := contDiff_component hU i
  have hd (i : Fin 3) : (fun t q => advection U t q i) =
      ∑ j : Fin 3, C j * spaceD j (C i) := by
    funext t q
    simp only [advection, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, Pi.mul_apply,
      smul_eq_mul, C, spaceD_component (smooth_slice_differentiable hU t)]
  have hp (i j k : Fin 3) : spaceD i (C k * spaceD k (C j)) =
      (spaceD i (C k)) * spaceD k (C j) + C k * spaceD i (spaceD k (C j)) := by
    funext t q
    exact spaceD_smul (hC k) (contDiff_spaceD (hC j) k) i t q
  have hh (k : Fin 3) : (∑ i : Fin 3, spaceD i (spaceD k (C i))) = 0 := by
    simp_rw [spaceD_commute (hC _) _ k]
    rw [← spaceD_finite_sum (fun i => contDiff_spaceD (hC i) i)]
    change spaceD k (divergence U) = 0
    rw [hdiv, Residual.spaceD_zero]
  have hprod (i k : Fin 3) : ContDiff ℝ ∞ (lifted (C k * spaceD k (C i))) :=
    (hC k).mul (contDiff_spaceD (hC i) k)
  simp only [divergence, hd,
    spaceD_finite_sum (hprod _), hp,
    Finset.sum_apply, Pi.add_apply, Pi.mul_apply, Finset.sum_add_distrib]
  change _ + (∑ i : Fin 3, ∑ k : Fin 3, C k t q * spaceD i (spaceD k (C i)) t q) = _
  rw [Finset.sum_comm (f := fun i k : Fin 3 => C k t q * spaceD i (spaceD k (C i)) t q)]
  simp_rw [← Finset.mul_sum]
  have he (k : Fin 3) : (∑ i : Fin 3, spaceD i (spaceD k (C i)) t q) = 0 := by
    simpa only [Finset.sum_apply, Pi.zero_apply] using congrFun (congrFun (hh k) t) q
  simp only [he, mul_zero, Finset.sum_const_zero, add_zero]
  rfl

end TorusCalculus

namespace PeriodicInverse

open scoped ContDiff
open MeasureTheory TorusCalculus RapidCalculus

def horizontal (H : ℝ → ℝ → ℝ) (hp : ∀ t, Function.Periodic (H t) 1) : ScalarField :=
  fun t q => (hp t).lift (q 1)

@[simp] theorem horizontal_cover (H : ℝ → ℝ → ℝ) (hp : ∀ t, Function.Periodic (H t) 1)
    (t : ℝ) (x : Space) : horizontal H hp t (torusMk x) = H t (x 1) :=
  (hp t).lift_coe _

theorem horizontal_contDiff {H : ℝ → ℝ → ℝ} (hp : ∀ t, Function.Periodic (H t) 1)
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) : ContDiff ℝ ∞ (lifted (horizontal H hp)) :=
  hH.comp (contDiff_fst.prodMk
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) 1).contDiff.comp contDiff_snd))

theorem horizontal_algebra {H : ℝ → ℝ → ℝ} (hp : ∀ t, Function.Periodic (H t) 1)
    (hH : Rapid2 H) : Algebra (horizontal H hp) := by
  apply Algebra.tensor _ H (fun _ => 1) hH
    (boundedProfile_of_periodic contDiff_const (fun _ => rfl))
  intro t x
  simp

theorem horizontal_integral {H : ℝ → ℝ → ℝ} (hp : ∀ t, Function.Periodic (H t) 1)
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) (t : ℝ) :
    (∫ q, horizontal H hp t q ∂torusVolume) = ∫ y in (0 : ℝ)..1, H t y := by
  have hc : Continuous (hp t).lift := by
    apply QuotientAddGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, Function.Periodic.lift_coe, Function.uncurry_def, id_eq] using
      hH.continuous.comp (continuous_const.prodMk continuous_id)
  change (∫ q, (hp t).lift (q 1) ∂Measure.pi (fun _ : Fin 3 => AddCircle.haarAddCircle)) = _
  rw [integral_comp_eval (μ := fun _ : Fin 3 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (i := (1 : Fin 3)) hc.aestronglyMeasurable]
  have hm : (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := 1))
  have he := UnitAddCircle.intervalIntegral_preimage 0 (hp t).lift
  simpa only [zero_add, Function.Periodic.lift_coe, hm] using he.symm

end PeriodicInverse

end
end PeriodicLattice

end OAI
