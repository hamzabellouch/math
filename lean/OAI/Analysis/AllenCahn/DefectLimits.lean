import OAI.Analysis.AllenCahn.SmallDefect

namespace OAI

noncomputable section
namespace DeGiorgi
open Filter Set Topology
open scoped NNReal
open scoped ContDiff
open Filter Topology

lemma SmallDefectConverges.D_over_root_vanishes {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0))
    (l : List (Fin n)) (x : Space n) :
    Tendsto (fun j => (defectRoot (v j) 0)⁻¹*coordinateJet (diffuseDefect (v j)) l x)
      atTop (𝓝 0) := by
  have HH := (smallDefect_root_tendsto hv he).mul (hg.at_D l x)
  have heq (j : ℕ) : defectRoot (v j) 0*((diffuseDefect (v j) 0)⁻¹*
      coordinateJet (diffuseDefect (v j)) l x) =
      (defectRoot (v j) 0)⁻¹*coordinateJet (diffuseDefect (v j)) l x := by
    rw [← defectRoot_sq ((hv j).2.2.2 0)]
    field_simp [(defectRoot_pos (v j) 0).ne']
  simpa only [heq,zero_mul] using HH

lemma profile_contDiff : ContDiff ℝ ∞ profile := by
  have hT : ContDiff ℝ ∞ Real.tanh := by
    rw [funext Real.tanh_eq_sinh_div_cosh]
    exact Real.contDiff_sinh.div Real.contDiff_cosh (fun y => (Real.cosh_pos y).ne')
  exact hT.comp (contDiff_id.div_const _)

lemma SmallDefectConverges.v_limit {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) (x : Space n) :
    Tendsto (fun j => v j x) atTop (𝓝 (profile (g none x))) := by
  have hc : Continuous profile := profile_contDiff.continuous
  have HH : Tendsto (fun j => profile (inverseProfile (v j) x)) atTop
      (𝓝 (profile (g none x))) := hc.continuousAt.tendsto.comp (hg.at_U [] x)
  have heq : (fun j => profile (inverseProfile (v j) x)) = fun j => v j x :=
    funext (fun j => profile_inverseProfile (hv j).2.1 x)
  change Tendsto (fun j => profile (inverseProfile (v j) x)) atTop (𝓝 (profile (g none x))) at HH
  rw [heq] at HH
  exact HH

theorem SmallDefectConverges.tensor_tangential {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0))
    (i : Fin n) (x : Space n) :
    ∑ k : Fin n, coordDeriv (g none) k x*g (some (some (i,k))) x = 0 := by
  have H := tendsto_finsetSum Finset.univ (fun k _ => (hg.at_U [k] x).mul (hg.at_T i k [] x))
  have H' := (hg.D_over_root_vanishes hv he [i] x).const_mul (-1/2 : ℝ)
  have heq (j : ℕ) : (∑ k : Fin n, coordinateJet (inverseProfile (v j)) [k] x*
      ((defectRoot (v j) 0)⁻¹*coordinateJet (inverseHessian (v j) i k) [] x)) =
      (-1/2 : ℝ)*((defectRoot (v j) 0)⁻¹*coordinateJet (diffuseDefect (v j)) [i] x) := by
    simp only [coordinateJet,coordDeriv_diffuseDefect_sum (hv j).1 (hv j).2.1]
    calc (∑ k : Fin n, coordDeriv (inverseProfile (v j)) k x*
        ((defectRoot (v j) 0)⁻¹*inverseHessian (v j) i k x)) =
        (defectRoot (v j) 0)⁻¹*∑ k : Fin n, coordDeriv (inverseProfile (v j)) k x*inverseHessian (v j) i k x := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
      _ = _ := by ring
  simp_rw [heq] at H
  simpa only [coordinateJet,mul_zero] using tendsto_nhds_unique H H'

lemma inverseHessian_transport {n : ℕ} {v : Space n → ℝ}
    (hv : ContDiff ℝ ∞ v) (hi : ∀ x, v x ∈ Set.Ioo (-1 : ℝ) 1)
    (i j : Fin n) (x : Space n) :
    (∑ k : Fin n, coordDeriv (inverseProfile v) k x*coordDeriv (inverseHessian v i j) k x) =
      -(∑ k : Fin n, inverseHessian v i k x*inverseHessian v j k x) -
        (1/2 : ℝ)*coordDeriv (coordDeriv (diffuseDefect v) i) j x := by
  have hU := inverseProfile_smooth hv hi
  have hT := inverseHessian_smooth hv hi
  have hp (k : Fin n) := coordDeriv_smooth hU k
  have hs : ContDiff ℝ ∞ (fun y => ∑ k : Fin n,
      coordDeriv (inverseProfile v) k y*inverseHessian v i k y) :=
    ContDiff.sum (fun k _ => (hp k).mul (hT i k))
  have hD : coordDeriv (diffuseDefect v) i = fun y => -2*∑ k : Fin n,
      coordDeriv (inverseProfile v) k y*inverseHessian v i k y :=
    funext (coordDeriv_diffuseDefect_sum hv hi i)
  have hm (k : Fin n) : coordDeriv (inverseHessian v i k) j = coordDeriv (inverseHessian v i j) k :=
    coordDeriv_comm (smooth_C2 (hp i)) k j
  have HH := congrArg (fun f : Space n → ℝ => coordDeriv f j x) hD
  have hscale := congrFun (coordinateJet_const_mul hs (-2) [j]) x
  simp only [coordinateJet] at hscale
  rw [hscale,coordDeriv_sum _ (fun k _ => ((hp k).mul (hT i k)).differentiable (by simp))] at HH
  simp_rw [coordDeriv_mul ((hp _).differentiable (by simp)) ((hT i _).differentiable (by simp)),hm] at HH
  have hkj (k : Fin n) : coordDeriv (coordDeriv (inverseProfile v) k) j x = inverseHessian v j k x := by
    exact congrFun (coordDeriv_comm (smooth_C2 hU) k j) x
  simp_rw [hkj] at HH
  rw [Finset.sum_add_distrib] at HH
  linarith

theorem SmallDefectConverges.tensor_transport {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0))
    (a b : Fin n) (x : Space n) :
    ∑ k : Fin n, coordDeriv (g none) k x*coordDeriv (g (some (some (a,b)))) k x = 0 := by
  have H := tendsto_finsetSum Finset.univ (fun k _ => (hg.at_U [k] x).mul (hg.at_T a b [k] x))
  have H0 := tendsto_finsetSum Finset.univ (fun k _ =>
    (hg.tensor_vanishes hv he a k [] x).mul (hg.at_T b k [] x))
  have HD := hg.D_over_root_vanishes hv he [b,a] x
  have HE := H0.neg.sub (HD.const_mul (1/2 : ℝ))
  have heq (j : ℕ) : (∑ k : Fin n, coordinateJet (inverseProfile (v j)) [k] x*
      ((defectRoot (v j) 0)⁻¹*coordinateJet (inverseHessian (v j) a b) [k] x)) =
      -(∑ k : Fin n, coordinateJet (inverseHessian (v j) a k) [] x*
        ((defectRoot (v j) 0)⁻¹*coordinateJet (inverseHessian (v j) b k) [] x)) -
        (1/2 : ℝ)*((defectRoot (v j) 0)⁻¹*coordinateJet (diffuseDefect (v j)) [b,a] x) := by
    simp only [coordinateJet]
    have HH := congrArg (fun r : ℝ => (defectRoot (v j) 0)⁻¹*r)
      (inverseHessian_transport (hv j).1 (hv j).2.1 a b x)
    simp only [mul_sub,mul_neg,Finset.mul_sum] at HH
    simpa only [mul_assoc,mul_left_comm,mul_comm] using HH
  simp_rw [heq] at H
  simpa only [coordinateJet,zero_mul,Finset.sum_const_zero,neg_zero,mul_zero,sub_zero]
    using tendsto_nhds_unique H HE

lemma SmallDefectConverges.D_vanishes {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0))
    (l : List (Fin n)) (x : Space n) :
    Tendsto (fun j => coordinateJet (diffuseDefect (v j)) l x) atTop (𝓝 0) := by
  have HH := he.mul (hg.at_D l x)
  have heq (j : ℕ) : diffuseDefect (v j) 0*((diffuseDefect (v j) 0)⁻¹*
      coordinateJet (diffuseDefect (v j)) l x) = coordinateJet (diffuseDefect (v j)) l x := by
    field_simp [((hv j).2.2.2 0).ne']
  simpa only [heq,zero_mul] using HH

lemma SmallDefectConverges.positive {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n) :
    g (some none) 0=1 ∧ ∀ x, 0 < g (some none) x :=
  normalized_defect_limit_positive (fun j => (hv j).1) (fun j => (hv j).2.1)
    (fun j => (hv j).2.2.1) (fun j => (hv j).2.2.2) (hg.2 (some none) [])

lemma SmallDefectConverges.tensor_trace {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0)) (x : Space n) :
    ∑ i : Fin n, g (some (some (i,i))) x = 0 := by
  have H := tendsto_finsetSum Finset.univ (fun i _ => hg.at_T i i [] x)
  have H' := ((hg.v_limit hv x).mul (hg.D_over_root_vanishes hv he [] x)).const_mul (-Real.sqrt 2)
  have heq (j : ℕ) : (∑ i : Fin n, (defectRoot (v j) 0)⁻¹*coordinateJet (inverseHessian (v j) i i) [] x) =
      -Real.sqrt 2*(v j x*((defectRoot (v j) 0)⁻¹*coordinateJet (diffuseDefect (v j)) [] x)) := by
    simp only [coordinateJet,← Finset.mul_sum]
    have HH := inverseProfile_laplacian_eq (smooth_C2 (hv j).1) (hv j).2.1 (hv j).2.2.1 x
    rw [laplacian_eq_sum_coordDeriv (smooth_C2 (inverseProfile_smooth (hv j).1 (hv j).2.1))] at HH
    change (∑ i : Fin n, inverseHessian (v j) i i x) = _ at HH
    rw [HH]
    ring
  simp_rw [heq] at H
  simpa only [coordinateJet,mul_zero] using tendsto_nhds_unique H H'

lemma SmallDefectConverges.controlled_over_root_vanishes {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0))
    {f : (Space n → ℝ) → Space n → ℝ} {k : ℕ}
    (hf : JetControl (positiveDefectClass n) diffuseDefect f k)
    (l : List (Fin n)) (hl : l.length ≤ k) (x : Space n) :
    Tendsto (fun j => (defectRoot (v j) 0)⁻¹*coordinateJet (f (v j)) l x) atTop (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := hf l hl
  apply squeeze_zero_norm (a := fun j => C*((defectRoot (v j) 0)⁻¹*diffuseDefect (v j) x))
  · intro j
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (inv_pos.mpr (defectRoot_pos (v j) 0))]
    calc _ ≤ (defectRoot (v j) 0)⁻¹*(C*diffuseDefect (v j) x) :=
      mul_le_mul_of_nonneg_left (hb (v j) (hv j) x) (inv_pos.mpr (defectRoot_pos (v j) 0)).le
      _ = _ := by ring
  · simpa only [mul_zero,coordinateJet] using (hg.D_over_root_vanishes hv he [] x).const_mul C

theorem SmallDefectConverges.tensor_harmonic {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0))
    (a b : Fin n) (x : Space n) :
    Laplacian.laplacian (g (some (some (a,b)))) x = 0 := by
  have hJ := positiveAC_all_jets n 2
  have hvD : JetControl (positiveDefectClass n) diffuseDefect
      (fun v x => v x*diffuseDefect v x) 2 :=
    hJ.1.mul_bounded (fun _ h => h.1) (fun _ h => diffuseDefect_smooth h.1 h.2.1)
      (fun _ h x => (h.2.2.2 x).le) hJ.2.2.1
  have HD := (hg.controlled_over_root_vanishes hv he hvD [b,a] (by simp) x).const_mul (-Real.sqrt 2)
  have H := tendsto_finsetSum Finset.univ (fun i _ => hg.at_T a b [i,i] x)
  have heq (j : ℕ) : (∑ i : Fin n, (defectRoot (v j) 0)⁻¹*
      coordinateJet (inverseHessian (v j) a b) [i,i] x) =
      -Real.sqrt 2*((defectRoot (v j) 0)⁻¹*
        coordinateJet (fun y => v j y*diffuseDefect (v j) y) [b,a] x) := by
    rw [← Finset.mul_sum]
    have hU := inverseProfile_smooth (hv j).1 (hv j).2.1
    have hTp : (∑ i : Fin n, coordinateJet (inverseHessian (v j) a b) [i,i] x) =
        Laplacian.laplacian (coordinateJet (inverseProfile (v j)) [b,a]) x :=
      (laplacian_eq_sum_coordDeriv (smooth_C2 (inverseHessian_smooth (hv j).1 (hv j).2.1 a b)) x).symm
    rw [hTp,coordinateJet_laplacian hU]
    have hLU : Laplacian.laplacian (inverseProfile (v j)) =
        fun y => -Real.sqrt 2*(v j y*diffuseDefect (v j) y) := by
      funext y
      rw [inverseProfile_laplacian_eq (smooth_C2 (hv j).1) (hv j).2.1 (hv j).2.2.1]
      ring
    rw [hLU,coordinateJet_const_mul ((hv j).1.mul (diffuseDefect_smooth (hv j).1 (hv j).2.1))]
    ring
  simp_rw [heq] at H
  have HH := tendsto_nhds_unique H HD
  rw [laplacian_eq_sum_coordDeriv (smooth_C2 (hg.1 (some (some (a,b)))))]
  simpa only [coordinateJet,mul_zero] using HH

lemma normalized_defect_equation {n : ℕ} {v : Space n → ℝ} (hv : v ∈ positiveDefectClass n)
    (x : Space n) :
    (diffuseDefect v 0)⁻¹*Laplacian.laplacian (diffuseDefect v) x =
      -2*(∑ i : Fin n, ∑ j : Fin n, ((defectRoot v 0)⁻¹*inverseHessian v i j x)^2) +
        2*Real.sqrt 2*v x*(∑ k : Fin n, coordDeriv (inverseProfile v) k x*
          ((diffuseDefect v 0)⁻¹*coordDeriv (diffuseDefect v) k x)) +
        2*(1-v x^2)*((diffuseDefect v 0)⁻¹*diffuseDefect v x)*(1-diffuseDefect v x) := by
  have hsq : (∑ i : Fin n, ∑ j : Fin n, ((defectRoot v 0)⁻¹*inverseHessian v i j x)^2) =
      (diffuseDefect v 0)⁻¹*hessianSquare v x := by
    rw [hessianSquare_eq_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [← defectRoot_sq (hv.2.2.2 0)]
    ring
  have hp : (∑ k : Fin n, coordDeriv (inverseProfile v) k x*
      ((diffuseDefect v 0)⁻¹*coordDeriv (diffuseDefect v) k x)) =
      (diffuseDefect v 0)⁻¹*inner ℝ (gradient (inverseProfile v) x) (gradient (diffuseDefect v) x) := by
    rw [inner_gradient_eq_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [diffuseDefect_laplacian hv.1 hv.2.1 hv.2.2.1,hsq,hp]
  change (diffuseDefect v 0)⁻¹*(-2*hessianSquare v x+_+_) = _
  dsimp only [defectWeight,diffuseDefect]
  ring

theorem SmallDefectConverges.defect_equation {n : ℕ} {v : ℕ → Space n → ℝ}
    {g : SmallDefectIndex n → Space n → ℝ} (hg : SmallDefectConverges v g)
    (hv : ∀ j, v j ∈ positiveDefectClass n)
    (he : Tendsto (fun j => diffuseDefect (v j) 0) atTop (𝓝 0)) (x : Space n) :
    Laplacian.laplacian (g (some none)) x =
      -2*(∑ i : Fin n, ∑ j : Fin n, (g (some (some (i,j))) x)^2) +
        2*Real.sqrt 2*profile (g none x)*(∑ k : Fin n, coordDeriv (g none) k x*
          coordDeriv (g (some none)) k x) +
        2*(1-profile (g none x)^2)*g (some none) x := by
  have HL := tendsto_finsetSum Finset.univ (fun i _ => hg.at_D [i,i] x)
  have HS := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_finsetSum Finset.univ (fun j _ => (hg.at_T i j [] x).pow 2))
  have HP := tendsto_finsetSum Finset.univ (fun k _ => (hg.at_U [k] x).mul (hg.at_D [k] x))
  have HV := hg.v_limit hv x
  have HQ := (tendsto_const_nhds (x := (1 : ℝ))).sub (HV.pow 2)
  have HZ := (tendsto_const_nhds (x := (1 : ℝ))).sub (hg.D_vanishes hv he [] x)
  have HD := hg.at_D [] x
  have HR := ((HS.const_mul (-2 : ℝ)).add ((HV.const_mul (2*Real.sqrt 2)).mul HP)).add
    (((HQ.const_mul 2).mul HD).mul HZ)
  have heq (j : ℕ) : (∑ i : Fin n, (diffuseDefect (v j) 0)⁻¹*coordinateJet (diffuseDefect (v j)) [i,i] x) =
      -2*(∑ i : Fin n, ∑ k : Fin n, ((defectRoot (v j) 0)⁻¹*coordinateJet (inverseHessian (v j) i k) [] x)^2) +
        2*Real.sqrt 2*v j x*(∑ k : Fin n, coordinateJet (inverseProfile (v j)) [k] x*
          ((diffuseDefect (v j) 0)⁻¹*coordinateJet (diffuseDefect (v j)) [k] x)) +
        2*(1-v j x^2)*((diffuseDefect (v j) 0)⁻¹*coordinateJet (diffuseDefect (v j)) [] x)*
          (1-coordinateJet (diffuseDefect (v j)) [] x) := by
    rw [← Finset.mul_sum]
    simp only [coordinateJet]
    rw [← laplacian_eq_sum_coordDeriv (smooth_C2 (diffuseDefect_smooth (hv j).1 (hv j).2.1))]
    exact normalized_defect_equation (hv j) x
  simp_rw [heq] at HL
  have HH := tendsto_nhds_unique HL HR
  rw [laplacian_eq_sum_coordDeriv (smooth_C2 (hg.1 (some none)))]
  simpa only [coordinateJet,sub_zero,mul_one] using HH

def profileWeight (s : ℝ) : ℝ := 1-profile s^2

lemma profile_hasDerivAt (s : ℝ) :
    HasDerivAt profile (profileWeight s/Real.sqrt 2) s := by
  let y := s/Real.sqrt 2
  have H := (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (Real.cosh_pos y).ne'
  have he : (Real.cosh y*Real.cosh y-Real.sinh y*Real.sinh y)/Real.cosh y^2 =
      1-Real.tanh y^2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  change HasDerivAt (fun z => Real.sinh z/Real.cosh z)
    ((Real.cosh y*Real.cosh y-Real.sinh y*Real.sinh y)/Real.cosh y^2) y at H
  rw [he,← funext Real.tanh_eq_sinh_div_cosh] at H
  have HH := H.comp s ((hasDerivAt_id s).div_const (Real.sqrt 2))
  change HasDerivAt (fun s => Real.tanh (s/Real.sqrt 2)) _ s
  simpa only [Function.comp_def,id_eq,profileWeight,profile,y,div_eq_mul_inv,one_mul] using HH

lemma profileWeight_contDiff : ContDiff ℝ ∞ profileWeight :=
  contDiff_const.sub (profile_contDiff.pow 2)

lemma profileWeight_pos (s : ℝ) : 0 < profileWeight s := by
  dsimp [profileWeight,profile]
  linarith [Real.tanh_sq_lt_one (s/Real.sqrt 2)]

lemma profileWeight_hasDerivAt (s : ℝ) :
    HasDerivAt profileWeight (-Real.sqrt 2*profile s*profileWeight s) s := by
  have H := (hasDerivAt_const s (1 : ℝ)).sub ((profile_hasDerivAt s).pow 2)
  have he : (0 : ℝ)-2*profile s^(2-1)*(profileWeight s/Real.sqrt 2) =
      -Real.sqrt 2*profile s*profileWeight s := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    norm_num only [Nat.reduceSub,pow_one,zero_sub]
    field_simp
    rw [hsq]
    ring
  change HasDerivAt profileWeight (0-2*profile s^(2-1)*(profileWeight s/Real.sqrt 2)) s at H
  rwa [he] at H

lemma profileWeight_hasDerivAt_twice (s : ℝ) :
    HasDerivAt (deriv profileWeight) ((3*profile s^2-1)*profileWeight s) s := by
  have H := ((profile_hasDerivAt s).mul (profileWeight_hasDerivAt s)).const_mul (-Real.sqrt 2)
  have he : -Real.sqrt 2*(profileWeight s/Real.sqrt 2*profileWeight s+
       profile s*(-Real.sqrt 2*profile s*profileWeight s)) =
       (3*profile s^2-1)*profileWeight s := by
    have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    field_simp
    dsimp [profileWeight]
    nlinarith [congrArg (fun r : ℝ => r*(profile s^2)*(1-profile s^2)) hsq]
  have hfun : deriv profileWeight = fun s => -Real.sqrt 2*(profile s*profileWeight s) := by
    funext s
    rw [(profileWeight_hasDerivAt s).deriv]
    ring
  rw [hfun]
  rw [he] at H
  simpa only [Pi.mul_apply] using H

lemma gradient_comp_inner {n : ℕ} {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (c x : Space n) : gradient (fun z => f (inner ℝ c z)) x = deriv f (inner ℝ c x) • c := by
  have H := (hf (inner ℝ c x)).hasDerivAt.comp_hasFDerivAt x (innerSL ℝ c).hasFDerivAt
  change HasFDerivAt (fun z : Space n => f (inner ℝ c z))
    (deriv f (inner ℝ c x) • innerSL ℝ c) x at H
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left, H.fderiv, real_inner_smul_left]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply]

lemma gradient_inner {n : ℕ} (c x : Space n) : gradient (fun z => inner ℝ c z) x = c := by
  have H := gradient_comp_inner (f := id) differentiable_id c x
  simpa using H

lemma laplacian_inner {n : ℕ} (c x : Space n) :
    Laplacian.laplacian (fun z => inner ℝ c z) x = 0 := by
  simpa only [zero_add] using PoissonSupport.DeGiorgi.laplacian_affine c 0 x

end DeGiorgi
end

end OAI
