import OAI.Probability.InvariantIsing.Fields.FieldHeightGradient
import OAI.Probability.InvariantIsing.Fields.FieldRadialCovariance

namespace OAI

/-! The radial row sign of the actual finite-height Hessian. The proof
transports the already proved covariance-scaling order of magnetization,
using the literal gradient identity on a neighborhood of a strict field. -/

noncomputable section
open IsingPerceptron Set Filter
open scoped BigOperators NNReal Topology

namespace InvariantIsing

lemma fieldMagnetizationLevel_congr {h k : FieldStep} (he : h = k)
    (i : Fin (h.depth + 1)) (j : Fin (k.depth + 1)) (hij : i.val = j.val) :
    fieldMagnetizationLevel h i = fieldMagnetizationLevel k j := by
  cases he
  have hi : i = j := Fin.ext hij
  subst j
  rfl

lemma fieldStrictHeightCone_smul {n : ℕ} {r : Fin (n + 1) → ℝ}
    (hr : r ∈ fieldStrictHeightCone n) {a : ℝ} (ha : 0 < a) :
    a • r ∈ fieldStrictHeightCone n := by
  intro j
  have he : fieldHeightIncrement (a • r) j = a * fieldHeightIncrement r j := by
    unfold fieldHeightIncrement
    split_ifs <;> simp only [Pi.smul_apply, smul_eq_mul] <;> ring
  rw [he]
  exact mul_pos ha (hr j)

theorem fieldHeight_radial_hessian_nonpos (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (hI : IsOpen I)
    (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) :
    ∑ j, F.PP i j (r, 0) * r j ≤ 0 := by
  classical
  let k := fieldStepOfStrictHeights h r hs
  let c : ℝ → ℝ≥0 := fun t => ⟨Real.sqrt (1 + t), Real.sqrt_nonneg _⟩
  let w := h.cut i.succ - h.cut i.castSucc
  let d := if i = Fin.last h.depth then (1 / 2 : ℝ) else 0
  let g := fun t : ℝ => -w / 2 * fieldMagnetizationLevel (fieldScaleCovariance k (c t)) i + d
  have hw : 0 ≤ w := sub_nonneg.mpr (h.ordered_cut.monotone i.castSucc_le_succ)
  have hg : Antitone g := by
    intro a b hab
    have hc : c a ≤ c b := by
      change Real.sqrt (1 + a) ≤ Real.sqrt (1 + b)
      exact Real.sqrt_le_sqrt (by linarith)
    have hb := fieldMagnetizationLevel_radial k hc i
    dsimp only [g]
    have hneg : -w / 2 ≤ 0 := by linarith
    have hh := mul_le_mul_of_nonpos_left hb hneg
    linarith
  have hm : Tendsto (fun t : ℝ => r + t • r) (𝓝 0) (𝓝 r) := by
    simpa using (show ContinuousAt (fun t : ℝ => r + t • r) 0 by fun_prop).tendsto
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ), r + t • r ∈ I := hm.eventually (hI.mem_nhds hr)
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < 1 + t :=
    (isOpen_lt continuous_const (continuous_const.add continuous_id)).mem_nhds (by norm_num)
  have he : g =ᶠ[𝓝 0] fun t : ℝ => F.P i (r + t • r, 0) := by
    filter_upwards [hmem, hpos] with t htI ht
    have htR : r + t • r ∈ fieldStrictHeightCone h.depth := by
      have heq : r + t • r = (1 + t) • r := by module
      rw [heq]
      exact fieldStrictHeightCone_smul hs ht
    have hsq : (c t : ℝ) ^ 2 = 1 + t := Real.sq_sqrt ht.le
    have heq : r + t • r = fun j => (c t : ℝ) ^ 2 * r j := by
      funext j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsq]
      ring
    have hk : fieldStepOfStrictHeights h (r + t • r) htR =
        fieldScaleCovariance k (c t) := by
      unfold fieldStepOfStrictHeights fieldWithHeights fieldScaleCovariance k
      congr 1
    have hh := fieldHeight_gradient_identification h F hU (r + t • r) htI htR i
    rw [fieldMagnetizationLevel_congr hk i i rfl] at hh
    dsimp only [g, w, d]
    linarith
  have hd : HasDerivAt (fun t : ℝ => F.P i (r + t • r, 0))
      (∑ j, F.PP i j (r, 0) * r j) 0 := by
    have hv := (hasDerivAt_const (0 : ℝ) r).add ((hasDerivAt_id (0 : ℝ)).smul_const r)
    have hp : HasDerivAt (fun t : ℝ => (r + t • r, (0 : ℝ))) (r, 0) 0 := by
      simpa using hv.prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have hF : HasFDerivAt (F.P i)
        (fieldFiniteLinear (fun j => F.PP i j (r, 0)) (F.PX i (r, 0)))
        (r + (0 : ℝ) • r, 0) := by simpa using F.derivativeP i (r, 0) hr
    simpa [fieldFiniteLinear_apply, Function.comp_def] using
      hF.comp_hasDerivAt (f := fun t : ℝ => (r + t • r, (0 : ℝ))) 0 hp
  exact (hd.congr_of_eventuallyEq he).nonpos_of_antitone hg

end InvariantIsing

end

end OAI
