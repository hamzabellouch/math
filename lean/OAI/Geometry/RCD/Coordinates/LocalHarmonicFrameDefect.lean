import OAI.Geometry.RCD.Coordinates.RegularFrameDefect
import OAI.Geometry.RCD.Coordinates.LocalPoissonRegularExtension

namespace OAI

/-! # Quantitative gradient expansion in the original local harmonic coordinates -/

open Set Filter MeasureTheory Metric
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.local_harmonic_frame_defect {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0) (p : X)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    {R b : ℝ} (hR : 0<R) (hb : 4*R<b)
    (hH : ∀ i, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p b) (u i))
    (L : Fin n → ℝ≥0) (hL : ∀ i, ∀ᵐ x ∂(hausdorff n X).restrict (ball p b),
      localGamma (hausdorff n X) hX.quadratic (u i) (u i) x≤(L i:ℝ)^2)
    (g : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (q : Lp ℝ 2 (hausdorff n X)) (hq : IsWeakLaplacian (hausdorff n X) hX.quadratic g.val q)
    (d : SobolevSpace (hausdorff n X) hX.quadratic) (A : ℝ≥0)
    (hd : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic d x|≤A)
    (hqr : q =ᵐ[(hausdorff n X).restrict (ball p (2*R))]
      SobolevSpace.toLp (hausdorff n X) hX.quadratic d)
    (δ : X → ℝ) (hδ : ∀ᵐ x ∂(hausdorff n X).restrict (ball p R), 0≤δ x)
    (htrace : ∀ᵐ x ∂(hausdorff n X).restrict (ball p R),
      |∑ i, localGamma (hausdorff n X) hX.quadratic (u i) (u i) x-(n:ℝ)|≤δ x)
    (hsquare : ∀ᵐ x ∂(hausdorff n X).restrict (ball p R),
      |∑ i, ∑ j, (localGamma (hausdorff n X) hX.quadratic (u i) (u j) x)^2-(n:ℝ)|≤δ x) :
    ∀ᵐ x ∂(hausdorff n X).restrict (ball p R), δ x≤1 →
      |localGamma (hausdorff n X) hX.quadratic g.val g.val x-
        ∑ i, (localGamma (hausdorff n X) hX.quadratic (u i) g.val x)^2|≤
      Real.sqrt (6*δ x)*|localGamma (hausdorff n X) hX.quadratic g.val g.val x| := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  have hext (i : Fin n) := hX.local_poisson_regular_extension hn (u i) 0
    (show 0<2*R by positivity) (show 2*(2*R)<b by linarith)
    ((isConstantLaplacianOn_zero_iff μ hQ _ (u i)).mpr (hH i)) (L i) (hL i)
  choose U Q hU hrep hQzero using hext
  let f : Fin (n+1) → compactLaplacianCore μ hQ univ := Fin.snoc U g
  let qf : Fin (n+1) → Lp ℝ 2 μ := Fin.snoc Q q
  let df : Fin (n+1) → SobolevSpace μ hQ := Fin.snoc (fun _ => 0) d
  let Af : Fin (n+1) → ℝ≥0 := Fin.snoc (fun _ => 0) A
  have hqf (j : Fin (n+1)) : IsWeakLaplacian μ hQ (f j).val (qf j) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [f,qf,Fin.snoc_last] using hq
    · simpa only [f,qf,Fin.snoc_castSucc] using hU i
  have hz : SobolevSpace.toLp μ hQ (0 : SobolevSpace μ hQ) =ᵐ[μ] fun _ => (0:ℝ) := by
    simpa only [map_zero] using! (Lp.coeFn_zero ℝ 2 μ)
  have hdz : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (0 : SobolevSpace μ hQ) x|≤(0:ℝ≥0) := by
    filter_upwards [hz] with x hx
    simp only [hx,abs_zero,NNReal.coe_zero,le_refl]
  have hdf (j : Fin (n+1)) : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (df j) x|≤Af j := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [df,Af,Fin.snoc_last] using hd
    · simpa only [df,Af,Fin.snoc_castSucc] using hdz
  have hqfr (j : Fin (n+1)) : qf j =ᵐ[μ.restrict (ball p (2*R))] SobolevSpace.toLp μ hQ (df j) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [qf,df,Fin.snoc_last] using hqr
    · simpa only [qf,df,Fin.snoc_castSucc] using
        (hQzero i).trans (Filter.EventuallyEq.symm (ae_restrict_of_ae hz))
  have hsmall : ball p (2*R)⊆ball p b := ball_subset_ball (by linarith)
  have hpairs (i j : Fin n) : localGamma μ hQ (f i.castSucc).val (f j.castSucc).val
      =ᵐ[μ.restrict (ball p R)] localGamma μ hQ (u i) (u j) := by
    have hh := localGamma_pair_congr_ae μ hQ (hrep i) (hrep j)
    simpa only [f,Fin.snoc_castSucc] using! ae_restrict_of_ae_restrict_of_subset
      (ball_subset_ball (by linarith : R≤2*R)) hh
  have ht : ∀ᵐ x ∂μ.restrict (ball p ((2*R)/2)),
      |∑ i : Fin n, localGamma μ hQ (f i.castSucc).val (f i.castSucc).val x-(n:ℝ)|≤δ x := by
    rw [show (2*R)/2=R by ring]
    filter_upwards [htrace,ae_all_iff.mpr (fun i => ae_all_iff.mpr (hpairs i))] with x hx hp
    simpa only [hp] using hx
  have hs : ∀ᵐ x ∂μ.restrict (ball p ((2*R)/2)),
      |∑ i : Fin n, ∑ j : Fin n, (localGamma μ hQ (f i.castSucc).val (f j.castSucc).val x)^2-(n:ℝ)|≤δ x := by
    rw [show (2*R)/2=R by ring]
    filter_upwards [hsquare,ae_all_iff.mpr (fun i => ae_all_iff.mpr (hpairs i))] with x hx hp
    simpa only [hp] using hx
  have hf (j : Fin (n+1)) : ∃ F : X →ᵇ ℝ, SobolevSpace.toLp μ hQ (f j).val =ᵐ[μ] F := by
    obtain ⟨v,C,hv,hvc,-,hvr⟩ := (f j).property.1
    exact ⟨ofCompactSupport v hv.continuous hvc,hvr⟩
  choose F hF using hf
  have hd' : ∀ᵐ x ∂μ.restrict (ball p ((2*R)/2)), 0≤δ x := by
    simpa only [show (2*R)/2=R by ring] using hδ
  have hh := hX.regular_frame_defect hn hK p f (show 0<2*R by positivity)
    F hF qf hqf df Af hdf hqfr δ hd' ht hs
  rw [show (2*R)/2=R by ring] at hh
  have hpair (i : Fin n) : localGamma μ hQ (U i).val g.val
      =ᵐ[μ.restrict (ball p R)] localGamma μ hQ (u i) g.val :=
    ae_restrict_of_ae_restrict_of_subset (ball_subset_ball (by linarith))
      (localGamma_pair_congr_ae μ hQ (hrep i) EventuallyEq.rfl)
  filter_upwards [hh,ae_all_iff.mpr hpair] with x hx hp
  simp only [f,Fin.snoc_last,Fin.snoc_castSucc] at hx
  change δ x≤1 →
    |localGamma μ hQ g.val g.val x-∑ i, (localGamma μ hQ (U i).val g.val x)^2|≤
      Real.sqrt (6*δ x)*|localGamma μ hQ g.val g.val x| at hx
  have heq : (∑ i, (localGamma μ hQ (U i).val g.val x)^2)=
      ∑ i, (localGamma μ hQ (u i) g.val x)^2 :=
    Finset.sum_congr rfl (fun i _ => congrArg (fun a : ℝ => a^2) (hp i))
  rw [heq] at hx
  exact hx

end RegularPointCoordinates

end

end OAI
