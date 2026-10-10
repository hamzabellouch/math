import OAI.Analysis.AllenCahn.JetProducts

namespace OAI

noncomputable section
namespace DeGiorgi
open scoped ContDiff

theorem positiveAC_all_jets (n k : ℕ) :
    JetControl (positiveDefectClass n) (fun _ _ => 1) (fun v => v) k ∧
    (∀ i, JetControl (positiveDefectClass n) (fun _ _ => 1)
      (fun v => coordDeriv (inverseProfile v) i) k) ∧
    JetControl (positiveDefectClass n) diffuseDefect diffuseDefect k ∧
    ∀ i j, JetControl (positiveDefectClass n) defectRoot (fun v => inverseHessian v i j) k := by
  induction k with
  | zero => exact positiveAC_jet_base n
  | succ k ih =>
    rcases ih with ⟨hJv,hJp,hJD,hJT⟩
    have hv (v) (h : v ∈ positiveDefectClass n) := h.1
    have hp (i) (v) (h : v ∈ positiveDefectClass n) := coordDeriv_smooth (inverseProfile_smooth h.1 h.2.1) i
    have hq (v) (h : v ∈ positiveDefectClass n) : ContDiff ℝ ∞ (defectWeight v) :=
      contDiff_const.sub (h.1.pow 2)
    have hD (v) (h : v ∈ positiveDefectClass n) := diffuseDefect_smooth h.1 h.2.1
    have hT (i j) (v) (h : v ∈ positiveDefectClass n) := inverseHessian_smooth h.1 h.2.1 i j
    have hDn (v) (h : v ∈ positiveDefectClass n) (x) := (h.2.2.2 x).le
    have hJDu : JetControl (positiveDefectClass n) (fun _ _ => 1) diffuseDefect k :=
      hJD.mono_weight (fun v _ x => diffuseDefect_le_one v x)
    have hJq : JetControl (positiveDefectClass n) (fun _ _ => 1) defectWeight k := by
      have HH := hJv.mul_bounded hv hv (fun _ _ _ => zero_le_one) hJv
      exact (JetControl.const (positiveDefectClass n) 1 k).sub (fun _ _ => contDiff_const)
        (fun v h => (hv v h).mul (hv v h)) HH |>.congr (fun v _ => by funext x; simp [defectWeight,pow_two])
    have hJb (i : Fin n) : JetControl (positiveDefectClass n) (fun _ _ => 1)
        (fun v x => 2*Real.sqrt 2*v x*coordDeriv (inverseProfile v) i x) k := by
      have HH := (hJv.const_mul hv (2*Real.sqrt 2)).mul_bounded
        (fun v h => contDiff_const.mul (hv v h)) (hp i) (fun _ _ _ => zero_le_one) (hJp i)
      exact HH
    have hb (v) (_ : v ∈ positiveDefectClass n) (g : Space n → ℝ) (x) :
        fderiv ℝ g x (diffuseDrift v x) = ∑ i : Fin n,
          (2*Real.sqrt 2*v x*coordDeriv (inverseProfile v) i x)*coordDeriv g i x := by
      rw [fderiv_diffuseDrift, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hbc (i) (v) (h : v ∈ positiveDefectClass n) : ContDiff ℝ ∞
        (fun x => 2*Real.sqrt 2*v x*coordDeriv (inverseProfile v) i x) :=
      (contDiff_const.mul (hv v h)).mul (hp i v h)
    have hJS : JetControl (positiveDefectClass n) diffuseDefect defectSource k := by
      have h1 := (JetControl.const (positiveDefectClass n) 1 k).sub (fun _ _ => contDiff_const) hD hJDu
      have h2 := hJq.mul_bounded hq (fun v h => contDiff_const.sub (hD v h))
        (fun _ _ _ => zero_le_one) h1
      have h3 := (h2.const_mul (fun v h => (hq v h).mul (contDiff_const.sub (hD v h))) 2).mul_bounded
        (fun v h => contDiff_const.mul ((hq v h).mul (contDiff_const.sub (hD v h)))) hD hDn hJD
      have h4 : JetControl (positiveDefectClass n) diffuseDefect
          (fun v x => ∑ i : Fin n, ∑ j : Fin n, inverseHessian v i j x*inverseHessian v i j x) k := by
        apply JetControl.sum Finset.univ
        · intro i _ v h
          exact ContDiff.sum (fun j _ => (hT i j v h).mul (hT i j v h))
        · intro i _
          apply JetControl.sum Finset.univ
          · intro j _ v h
            exact (hT i j v h).mul (hT i j v h)
          · intro j _
            exact positiveAC_root_product (hT i j) (hT i j) (hJT i j) (hJT i j)
      have h4s (v) (h : v ∈ positiveDefectClass n) : ContDiff ℝ ∞
          (fun x => ∑ i : Fin n, ∑ j : Fin n, inverseHessian v i j x*inverseHessian v i j x) :=
        ContDiff.sum (fun i _ => ContDiff.sum (fun j _ => (hT i j v h).mul (hT i j v h)))
      exact (h3.sub (fun v h => (contDiff_const.mul ((hq v h).mul
        (contDiff_const.sub (hD v h)))).mul (hD v h))
        (fun v h => contDiff_const.mul (h4s v h)) (h4.const_mul h4s 2)).congr
        (fun v _ => by funext x; simp only [defectSource,defectPotential,hessianSquare_eq_sum,pow_two])
    have hJD' : JetControl (positiveDefectClass n) diffuseDefect diffuseDefect (k+1) := by
      apply JetControl.bootstrap hD (fun v h => defectSource_smooth h.1 h.2.1) hbc
        (fun v h => smooth_C2 (hD v h)) (fun _ h => h.2.2.2) hb
        (fun _ h => diffuseDefect_drift_eq_source h.1 h.2.1 h.2.2.1)
        (show 0 ≤ 2*Real.sqrt 2 by positivity) (relativeDefectConstant_pos n).le (defectSourceConstant_pos n).le
        (fun _ h => diffuseDrift_bound (smooth_C2 h.1) h.2.1 h.2.2.1)
        (fun _ h => diffuseDefect_relative_gradient_bound h.1 h.2.1 h.2.2.1)
        (fun v h x => ?_) hJb hJD hJS
      rw [diffuseDefect_drift_eq_source h.1 h.2.1 h.2.2.1]
      exact (defectSource_bounds h.1 h.2.1 h.2.2.1).1 x
    have hJT' (i j : Fin n) : JetControl (positiveDefectClass n) defectRoot
        (fun v => inverseHessian v i j) (k+1) := by
      let R (v : Space n → ℝ) (x : Space n) :=
        -defectWeight v x*diffuseDefect v x*inverseHessian v i j x +
        Real.sqrt 2*v x*defectWeight v x*diffuseDefect v x*
          coordDeriv (inverseProfile v) i x*coordDeriv (inverseProfile v) j x -
        defectWeight v x*(coordDeriv (inverseProfile v) i x*coordDeriv (diffuseDefect v) j x+
          coordDeriv (inverseProfile v) j x*coordDeriv (diffuseDefect v) i x) +
        2*Real.sqrt 2*v x*(∑ a : Fin n, inverseHessian v i a x*inverseHessian v a j x)
      have hdD (a) (v) (h : v ∈ positiveDefectClass n) := coordDeriv_smooth (hD v h) a
      have hR (v) (h : v ∈ positiveDefectClass n) : ContDiff ℝ ∞ (R v) :=
        ((((hq v h).neg.mul (hD v h)).mul (hT i j v h)).add
          (((((contDiff_const.mul (hv v h)).mul (hq v h)).mul (hD v h)).mul (hp i v h)).mul (hp j v h))).sub
          ((hq v h).mul (((hp i v h).mul (hdD j v h)).add ((hp j v h).mul (hdD i v h)))) |>.add
            ((contDiff_const.mul (hv v h)).mul (ContDiff.sum (fun a _ => (hT i a v h).mul (hT a j v h))))
      have hJR : JetControl (positiveDefectClass n) defectRoot R k := by
        have hnR (v) (_ : v ∈ positiveDefectClass n) (x) := (defectRoot_pos v x).le
        have h1 := ((hJq.const_mul hq (-1)).mul_bounded
          (fun v h => contDiff_const.mul (hq v h)) hD (fun _ _ _ => zero_le_one) hJDu).mul_bounded
          (fun v h => (contDiff_const.mul (hq v h)).mul (hD v h)) (hT i j) hnR (hJT i j)
        have h2a := ((((hJv.const_mul hv (Real.sqrt 2)).mul_bounded
          (fun v h => contDiff_const.mul (hv v h)) hq (fun _ _ _ => zero_le_one) hJq).mul_bounded
          (fun v h => (contDiff_const.mul (hv v h)).mul (hq v h)) (hp i)
          (fun _ _ _ => zero_le_one) (hJp i)).mul_bounded
          (fun v h => ((contDiff_const.mul (hv v h)).mul (hq v h)).mul (hp i v h)) (hp j)
          (fun _ _ _ => zero_le_one) (hJp j))
        have h2 := (h2a.mul_bounded
          (fun v h => (((contDiff_const.mul (hv v h)).mul (hq v h)).mul (hp i v h)).mul (hp j v h))
          hD hDn hJD).mono_weight (fun v h x => defect_le_root h x)
        have h3a := (hJp i).mul_bounded (hp i) (hdD j) hDn (hJD'.deriv hD j)
        have h3b := (hJp j).mul_bounded (hp j) (hdD i) hDn (hJD'.deriv hD i)
        have h3c := h3a.add (fun v h => (hp i v h).mul (hdD j v h))
          (fun v h => (hp j v h).mul (hdD i v h)) h3b
        have h3 := (hJq.mul_bounded hq
          (fun v h => ((hp i v h).mul (hdD j v h)).add ((hp j v h).mul (hdD i v h))) hDn h3c).mono_weight
          (fun v h x => defect_le_root h x)
        have h4a : JetControl (positiveDefectClass n) diffuseDefect
            (fun v x => ∑ a : Fin n, inverseHessian v i a x*inverseHessian v a j x) k := by
          apply JetControl.sum Finset.univ
          · intro a _ v h
            exact (hT i a v h).mul (hT a j v h)
          · intro a _
            exact positiveAC_root_product (hT i a) (hT a j) (hJT i a) (hJT a j)
        have h4 := ((hJv.const_mul hv (2*Real.sqrt 2)).mul_bounded
          (fun v h => contDiff_const.mul (hv v h))
          (fun v h => ContDiff.sum (fun a _ => (hT i a v h).mul (hT a j v h))) hDn h4a).mono_weight
          (fun v h x => defect_le_root h x)
        have hs1 (v) (h : v ∈ positiveDefectClass n) :=
          (((contDiff_const (c := (-1 : ℝ))).mul (hq v h)).mul (hD v h)).mul (hT i j v h)
        have hs2 (v) (h : v ∈ positiveDefectClass n) :=
          (((((contDiff_const (c := Real.sqrt 2)).mul (hv v h)).mul (hq v h)).mul (hp i v h)).mul (hp j v h)).mul (hD v h)
        have hs3 (v) (h : v ∈ positiveDefectClass n) :=
          (hq v h).mul (((hp i v h).mul (hdD j v h)).add ((hp j v h).mul (hdD i v h)))
        have hs4 (v) (h : v ∈ positiveDefectClass n) : ContDiff ℝ ∞
            (fun x => 2*Real.sqrt 2*v x*(∑ a : Fin n, inverseHessian v i a x*inverseHessian v a j x)) :=
          ((contDiff_const (c := 2*Real.sqrt 2)).mul (hv v h)).mul (ContDiff.sum (fun a _ => (hT i a v h).mul (hT a j v h)))
        exact (((h1.add hs1 hs2 h2).sub (fun v h => (hs1 v h).add (hs2 v h)) hs3 h3).add
          (fun v h => ((hs1 v h).add (hs2 v h)).sub (hs3 v h)) hs4 h4).congr
          (fun v _ => by funext x; dsimp [R]; ring)
      exact JetControl.bootstrap (hT i j) hR hbc
        (fun v h => smooth_C2 (defectRoot_smooth h.1 h.2.1 h.2.2.2))
        (fun v _ => defectRoot_pos v) hb
        (fun v h => inverseHessian_drift_system h.1 h.2.1 h.2.2.1 i j)
        (show 0 ≤ 2*Real.sqrt 2 by positivity) (relativeDefectConstant_pos n).le
        (by have := (defectSourceConstant_pos n).le; positivity)
        (fun _ h => diffuseDrift_bound (smooth_C2 h.1) h.2.1 h.2.2.1)
        (fun _ h x => (defectRoot_bounds h.1 h.2.1 h.2.2.1 h.2.2.2 x).1)
        (fun _ h x => (defectRoot_bounds h.1 h.2.1 h.2.2.1 h.2.2.2 x).2) hJb (hJT i j) hJR
    refine ⟨?_, ?_, hJD', hJT'⟩
    · apply JetControl.of_derivs hv (positiveAC_jet_base n).1
      intro i
      have HH := (hJq.mul_bounded hq (hp i) (fun _ _ _ => zero_le_one) (hJp i)).const_mul
        (fun v h => (hq v h).mul (hp i v h)) (1/Real.sqrt 2)
      exact HH.congr (fun v h => by
        funext x
        rw [coordDeriv_profile (h.1.differentiable (by simp)) h.2.1]
        ring)
    · intro i
      apply JetControl.of_derivs (hp i) ((positiveAC_jet_base n).2.1 i)
      intro j
      exact (hJT i j).mono_weight (fun v h x => defectRoot_le_one h.2.2.2 x)

end DeGiorgi
end

end OAI
