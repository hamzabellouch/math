import OAI.Dynamics.StandardMap.ChangeVariablesBounds

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace StandardMapEntropy
noncomputable def planeDual (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  a • ContinuousLinearMap.fst ℝ ℝ ℝ+b • ContinuousLinearMap.snd ℝ ℝ ℝ
noncomputable def planeMatrix (a b c d : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (planeDual a b).prod (planeDual c d)
@[simp] lemma planeDual_apply (a b : ℝ) (z : ℝ × ℝ) : planeDual a b z=a*z.1+b*z.2 := rfl
@[simp] lemma planeMatrix_apply (a b c d : ℝ) (z : ℝ × ℝ) :
    planeMatrix a b c d z=(a*z.1+b*z.2,c*z.1+d*z.2) := rfl
lemma planeMatrix_det (a b c d : ℝ) : (planeMatrix a b c d).det=a*d-b*c := by
  change (planeMatrix a b c d).toLinearMap.det=_
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ),Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply,Module.Basis.coe_finTwoProd_repr]

lemma label_graph_derivative (Q : ℝ × ℝ → ℝ) (X : ℝ × ℝ → ℝ)
    (S : Set (ℝ × ℝ)) (z : ℝ × ℝ) (yc a b u v : ℝ)
    (hQ : HasStrictFDerivAt Q (planeDual u v) (X z,z.2))
    (hR : HasStrictFDerivAt Q (planeDual a b) (z.1,yc))
    (hu : u ≠ 0) (hX : ContinuousWithinAt X S z)
    (hlevel : ∀ᶠ w in 𝓝[S] z, Q (X w,w.2)=Q (w.1,yc))
    (hlevel0 : Q (X z,z.2)=Q (z.1,yc)) :
    HasFDerivWithinAt (fun w => (X w,w.2)) (planeMatrix (a/u) (-v/u) 0 1) S z := by
  let F : (ℝ × ℝ) × ℝ → ℝ := fun w => Q (w.2,w.1.2)-Q (w.1.1,yc)
  let A := planeDual (-a) v
  have hD : HasStrictFDerivAt F
      (A.comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+u • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (z,X z) := by
    have hp1 := hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (z,X z))
    have hp2 := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := z)).comp (z,X z) (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (z,X z)))
    have hp3 := (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := z)).comp (z,X z) (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (z,X z)))
    have hh := (hQ.comp (z,X z) (hp1.prodMk hp2)).sub
      (hR.comp (z,X z) (hp3.prodMk (hasStrictFDerivAt_const yc (z,X z))))
    apply hh.congr_fderiv
    apply ContinuousLinearMap.ext
    intro w
    change u*w.2+v*w.1.2-(a*w.1.1+b*0)=(-a*w.1.1+v*w.1.2)+u*w.2
    ring
  have hx := hasFDerivWithinAt_of_regular_level F X S z A u hD hu hX (by
    filter_upwards [hlevel] with w hw
    dsimp only [F]
    rw [hw,hlevel0]; ring)
  have ht := hx.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).hasFDerivWithinAt
  apply ht.congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  apply Prod.ext
  · change (-u⁻¹)*((-a)*w.1+v*w.2)=a/u*w.1+(-v/u)*w.2
    ring
  · change w.2=0*w.1+1*w.2
    ring

lemma transverse_jacobian_bounds (A B C x α β c C₀ : ℝ)
    (hB : B ≠ 0) (hC : C ≠ 0) (_hc : 0 ≤ c) (hC₀ : 0 ≤ C₀)
    (hα : 0 ≤ α) (_hβ : 0 ≤ β) (hsmall : α*β ≤ 1)
    (hlo : c ≤ |B/C|) (hhi : |B/C| ≤ C₀)
    (hA : |A/B| ≤ α) (hx : |x| ≤ β) :
    c*(1-α*β) ≤ |(B+A*x)/C| ∧ |(B+A*x)/C| ≤ C₀*(1+α*β) := by
  have he : (B+A*x)/C=(B/C)*(1+(A/B)*x) := by field_simp
  have hprod : |A/B*x| ≤ α*β := by rw [abs_mul]; exact mul_le_mul hA hx (abs_nonneg _) hα
  have hupper : |1+(A/B)*x| ≤ 1+α*β := by
    calc
      _ ≤ |(1:ℝ)|+|A/B*x| := abs_add_le _ _
      _ ≤ _ := by simpa using add_le_add (le_refl (1:ℝ)) hprod
  have hlower : 1-α*β ≤ |1+(A/B)*x| := by
    have ht := abs_sub_abs_le_abs_sub (1:ℝ) (-A/B*x)
    simp only [abs_one,neg_div,neg_mul,abs_neg,sub_neg_eq_add] at ht
    linarith
  rw [he,abs_mul]
  exact ⟨mul_le_mul hlo hlower (by linarith) (abs_nonneg _),
    mul_le_mul hhi hupper (abs_nonneg _) hC₀⟩

lemma sweep_graph_derivative (F : ℝ × ℝ → ℝ) (X : ℝ → ℝ) (Θ : ℝ × ℝ → ℝ)
    (S : Set (ℝ × ℝ)) (z : ℝ × ℝ) (A B C D x' : ℝ)
    (hF : HasStrictFDerivAt F (planeDual C D) (z.1,Θ z))
    (hR : HasStrictFDerivAt F (planeDual A B) (X z.2,z.2))
    (hX : HasStrictDerivAt X x' z.2)
    (hD : D ≠ 0) (hΘ : ContinuousWithinAt Θ S z)
    (hlevel : ∀ᶠ w in 𝓝[S] z, F (w.1,Θ w)=F (X w.2,w.2))
    (hlevel0 : F (z.1,Θ z)=F (X z.2,z.2)) :
    HasFDerivWithinAt (fun w => (w.1,Θ w))
      (planeMatrix 1 0 (-C/D) ((B+A*x')/D)) S z := by
  let G : (ℝ × ℝ) × ℝ → ℝ := fun w => F (w.1.1,w.2)-F (X w.1.2,w.1.2)
  let L := planeDual C (-(B+A*x'))
  have hGD : HasStrictFDerivAt G
      (L.comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)+D • ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ) (z,Θ z) := by
    have hp := hasStrictFDerivAt_fst (𝕜 := ℝ) (p := (z,Θ z))
    have h1 := (hasStrictFDerivAt_fst (𝕜 := ℝ) (p := z)).comp (z,Θ z) hp
    have h2 := (hasStrictFDerivAt_snd (𝕜 := ℝ) (p := z)).comp (z,Θ z) hp
    have h3 := hasStrictFDerivAt_snd (𝕜 := ℝ) (p := (z,Θ z))
    have hh := (hF.comp (z,Θ z) (h1.prodMk h3)).sub
      (hR.comp (z,Θ z) ((hX.hasStrictFDerivAt.comp (z,Θ z) h2).prodMk h2))
    apply hh.congr_fderiv
    apply ContinuousLinearMap.ext
    intro w
    change C*w.1.1+D*w.2-(A*(w.1.2*x')+B*w.1.2)=
      (C*w.1.1+(-(B+A*x'))*w.1.2)+D*w.2
    ring
  have hθ := hasFDerivWithinAt_of_regular_level G Θ S z L D hGD hD hΘ (by
    filter_upwards [hlevel] with w hw
    dsimp only [G]
    rw [hw,hlevel0]; ring)
  have ht := (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).hasFDerivWithinAt.prodMk hθ
  apply ht.congr_fderiv
  apply ContinuousLinearMap.ext
  intro w
  apply Prod.ext
  · change w.1=1*w.1+0*w.2
    ring
  · change (-D⁻¹)*(C*w.1+(-(B+A*x'))*w.2)=(-C/D)*w.1+((B+A*x')/D)*w.2
    ring
end StandardMapEntropy

end OAI
