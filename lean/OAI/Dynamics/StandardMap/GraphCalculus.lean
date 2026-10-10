import OAI.Dynamics.StandardMap.VariedDirichlet

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma hasStrictDerivAt_phi (k x : ℝ) : HasStrictDerivAt (phi k) (potential k x) x := by
  have h := ((hasStrictDerivAt_id x).const_mul 2).add
    (((Real.hasStrictDerivAt_sin (2*Real.pi*x)).comp x
      ((hasStrictDerivAt_id x).const_mul (2*Real.pi))).const_mul k)
  convert! h using 1
  dsimp only [potential]
  ring

lemma hasStrictFDerivAt_liftedOrbit (k q a : ℝ) (n : ℕ) :
    HasStrictFDerivAt (fun z : ℝ × ℝ => liftedOrbit k z.1 z.2 n)
      (sSolution (orbitCoefficient k q a) n • ContinuousLinearMap.fst ℝ ℝ ℝ+
       tSolution (orbitCoefficient k q a) n • ContinuousLinearMap.snd ℝ ℝ ℝ) (q,a) := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [sSolution,tSolution,linearSolution] using
      (hasStrictFDerivAt_fst : HasStrictFDerivAt (Prod.fst : ℝ × ℝ → ℝ) _ (q,a))
  | one => simpa [sSolution,tSolution,linearSolution] using
      (hasStrictFDerivAt_snd : HasStrictFDerivAt (Prod.snd : ℝ × ℝ → ℝ) _ (q,a))
  | more n h0 h1 =>
    have h := ((hasStrictDerivAt_phi k (liftedOrbit k q a (n+1))).comp_hasStrictFDerivAt (q,a) h1).sub h0
    apply h.congr_fderiv
    apply ContinuousLinearMap.ext
    intro z
    change potential k (liftedOrbit k q a (n+1)) *
      (sSolution (orbitCoefficient k q a) (n+1)*z.1+tSolution (orbitCoefficient k q a) (n+1)*z.2)-
      (sSolution (orbitCoefficient k q a) n*z.1+tSolution (orbitCoefficient k q a) n*z.2) =
      (orbitCoefficient k q a (n+1)*sSolution (orbitCoefficient k q a) (n+1)-sSolution (orbitCoefficient k q a) n)*z.1+
      (orbitCoefficient k q a (n+1)*tSolution (orbitCoefficient k q a) (n+1)-tSolution (orbitCoefficient k q a) n)*z.2
    dsimp only [orbitCoefficient]
    ring

lemma hasDerivAt_of_regular_level (F : ℝ × ℝ → ℝ) (b : ℝ → ℝ) (x s t : ℝ)
    (hD : HasStrictFDerivAt F
      (s • ContinuousLinearMap.fst ℝ ℝ ℝ+t • ContinuousLinearMap.snd ℝ ℝ ℝ) (x,b x))
    (ht : t ≠ 0) (hb : ContinuousAt b x)
    (hlevel : ∀ᶠ y in 𝓝 x, F (y,b y)=F (x,b x)) :
    HasDerivAt b (-s/t) x := by
  let L : (ℝ × ℝ) →L[ℝ] ℝ := s • ContinuousLinearMap.fst ℝ ℝ ℝ+t • ContinuousLinearMap.snd ℝ ℝ ℝ
  have hInv : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := t⁻¹ • ContinuousLinearMap.id ℝ ℝ)
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
    · apply ContinuousLinearMap.ext; intro z; simp [L,ht]
  let ψ := hD.implicitFunctionOfProdDomain hInv
  have he : ∀ᶠ y in 𝓝 x, ψ y=b y := by
    have hpair : Tendsto (fun y => (y,b y)) (𝓝 x) (𝓝 (x,b x)) :=
      tendsto_id.prodMk_nhds hb
    filter_upwards [hpair.eventually (hD.eventually_apply_eq_iff_implicitFunctionOfProdDomain hInv),hlevel] with y hy hy'
    exact hy.mp hy'
  have hd := (hD.hasStrictFDerivAt_implicitFunctionOfProdDomain hInv).hasFDerivAt.hasDerivAt
  have heq : (-(L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).inverse.comp
      (L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ))) 1 = -s/t := by
    have hh : (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).inverse
        ((L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1)=s/t := by
      apply hInv.inverse_apply_eq.mpr
      simp only [L,ContinuousLinearMap.comp_apply,add_apply,smul_apply]
      change s*1+t*0=s*0+t*(s/t)
      field_simp
      ring
    change -(L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).inverse
      ((L.comp (ContinuousLinearMap.inl ℝ ℝ ℝ)) 1) = -s/t
    rw [hh,neg_div]
  change HasDerivAt ψ _ x at hd
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq (EventuallyEq.symm he)
end StandardMapEntropy

end OAI
