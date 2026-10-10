import Mathlib
import OAI.Analysis.CoulombIonization.FieldAnalysis.LinearCoulomb
import OAI.Analysis.CoulombIonization.FormDomain.WeakDerivative

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff InnerProductSpace Convolution
namespace CoulombAtom
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure]
variable {ι : Type*} [Fintype ι]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [BorelSpace E] [(volume : Measure E).IsAddHaarMeasure] [Fintype ι] in
lemma lp_norm_sq (f : Lp ℂ 2 (volume : Measure E)) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def]
  simp_rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
  rw [integral_ofReal]
  rfl

omit [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [(volume : Measure E).IsAddHaarMeasure] [Fintype ι] in
lemma div_sqrt_norm_sq (f : E → ℂ) (P : E →L[ℝ] Space) (x : E) :
    ‖f x / (Real.sqrt ‖P x‖ : ℂ)‖ ^ 2 = ‖f x‖ ^ 2 / ‖P x‖ := by
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), div_pow, Real.sq_sqrt (norm_nonneg _)]

def rootCoulombFn (v : ι → E) (P : E →L[ℝ] Space) (F : weakGraph v) : E → ℂ :=
  fun x => F.val none x / (Real.sqrt ‖P x‖ : ℂ)

omit [Fintype ι] in
lemma rootCoulombFn_memLp (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) (F : weakGraph v) :
    MemLp (rootCoulombFn v P F) 2 := by
  have hweak (a : Fin 3) : IsWeakDerivative (v (i a)) (F.val none) (F.val (some (i a))) :=
    (mem_weakGraph v F.val).mp F.property (i a)
  have hm : AEStronglyMeasurable (rootCoulombFn v P F) :=
    (Lp.memLp (F.val none)).aestronglyMeasurable.div₀
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp P.continuous.norm)
        ).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi := linear_coulomb_integrable P (fun a => v (i a)) hP
    (Lp.memLp (F.val none)) (fun a => Lp.memLp (F.val (some (i a)))) hweak
  simpa only [rootCoulombFn, div_sqrt_norm_sq] using hi

def rootCoulombLp (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) (F : weakGraph v) :
    Lp ℂ 2 (volume : Measure E) := (rootCoulombFn_memLp v P i hP F).toLp _

omit [Fintype ι] in
lemma rootCoulombLp_norm_sq (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) (F : weakGraph v) :
    ‖rootCoulombLp v P i hP F‖ ^ 2 = ∫ x, ‖F.val none x‖ ^ 2 / ‖P x‖ := by
  rw [lp_norm_sq]
  apply integral_congr_ae
  filter_upwards [(rootCoulombFn_memLp v P i hP F).coeFn_toLp] with x hx
  change rootCoulombLp v P i hP F x = rootCoulombFn v P F x at hx
  rw [hx]
  exact div_sqrt_norm_sq _ P x

omit [Fintype ι] in
lemma rootCoulombLp_add (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) (F G : weakGraph v) :
    rootCoulombLp v P i hP (F + G) = rootCoulombLp v P i hP F + rootCoulombLp v P i hP G := by
  apply Lp.ext
  filter_upwards [(rootCoulombFn_memLp v P i hP (F + G)).coeFn_toLp,
    (rootCoulombFn_memLp v P i hP F).coeFn_toLp,
    (rootCoulombFn_memLp v P i hP G).coeFn_toLp,
    Lp.coeFn_add (rootCoulombLp v P i hP F) (rootCoulombLp v P i hP G),
    Lp.coeFn_add (F.val none) (G.val none)] with x h1 h2 h3 h4 h5
  change rootCoulombLp v P i hP (F + G) x = _ at h1
  rw [h1, h4]
  change _ = (rootCoulombLp v P i hP F x) + (rootCoulombLp v P i hP G x)
  change rootCoulombLp v P i hP F x = _ at h2
  change rootCoulombLp v P i hP G x = _ at h3
  rw [h2, h3]
  change ((F.val none + G.val none) x) / _ = _
  rw [h5]
  exact add_div _ _ _

omit [Fintype ι] in
lemma rootCoulombLp_smul (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) (c : ℂ) (F : weakGraph v) :
    rootCoulombLp v P i hP (c • F) = c • rootCoulombLp v P i hP F := by
  apply Lp.ext
  filter_upwards [(rootCoulombFn_memLp v P i hP (c • F)).coeFn_toLp,
    (rootCoulombFn_memLp v P i hP F).coeFn_toLp,
    Lp.coeFn_smul c (rootCoulombLp v P i hP F),
    Lp.coeFn_smul c (F.val none)] with x h1 h2 h3 h4
  change rootCoulombLp v P i hP (c • F) x = _ at h1
  change rootCoulombLp v P i hP F x = _ at h2
  rw [h1, h3]
  simp only [Pi.smul_apply]
  rw [h2]
  change ((c • F.val none) x) / _ = c • (rootCoulombFn v P F x)
  rw [h4]
  simp only [Pi.smul_apply, smul_eq_mul, rootCoulombFn, mul_div_assoc]

lemma rootCoulombLp_bound (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) (F : weakGraph v) :
    ‖rootCoulombLp v P i hP F‖ ≤ 2 * ‖F‖ := by
  have hb := linear_coulomb_bound P (fun a => v (i a)) hP (Z := 1) (by norm_num)
    (Lp.memLp (F.val none)) (fun a => Lp.memLp (F.val (some (i a))))
    (fun a => (mem_weakGraph v F.val).mp F.property (i a))
  simp only [mul_one, one_mul, one_pow, ← lp_norm_sq, ← rootCoulombLp_norm_sq v P i hP] at hb
  have hc (j : Option ι) : ‖F.val j‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le F.val j) 2
  have hs : (∑ a : Fin 3, ‖F.val (some (i a))‖ ^ 2) ≤ 3 * ‖F‖ ^ 2 := by
    calc
      _ ≤ ∑ _a : Fin 3, ‖F‖ ^ 2 := Finset.sum_le_sum fun _ _ => hc _
      _ = _ := by simp
  nlinarith [hc none, norm_nonneg (rootCoulombLp v P i hP F), norm_nonneg F]

def rootCoulombMap (v : ι → E) (P : E →L[ℝ] Space) (i : Fin 3 → ι)
    (hP : ∀ a, P (v (i a)) = EuclideanSpace.single a 1) :
    weakGraph v →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  LinearMap.mkContinuous
    { toFun := rootCoulombLp v P i hP
      map_add' := rootCoulombLp_add v P i hP
      map_smul' := rootCoulombLp_smul v P i hP }
    2 (rootCoulombLp_bound v P i hP)

end CoulombAtom

end

end OAI
