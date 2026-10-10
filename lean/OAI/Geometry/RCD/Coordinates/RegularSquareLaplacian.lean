import OAI.Geometry.RCD.Sobolev.WeakLaplacianProduct

namespace OAI

/-! # Actual local Laplacians of squared regular functions -/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A local Sobolev representative of the source suffices. The global
weak Laplacian remains the actual L² source of the compact extension. -/
theorem IsWeakLaplacian.square_local {Ω : Set X}
    (g G dg : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ g d) (A B L : ℝ≥0)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x|≤A)
    (hdg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dg x|≤B)
    (hL : ∀ᵐ x ∂μ, localGamma μ hQ g g x≤(L:ℝ)^2)
    (hGr : SobolevSpace.toLp μ hQ G =ᵐ[μ.restrict Ω] localGamma μ hQ g g)
    (hdr : d =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ dg) :
    ∃ q : Lp ℝ 2 μ,
      IsWeakLaplacian μ hQ (SobolevSpace.product μ hQ g g A A) q ∧
      q =ᵐ[μ.restrict Ω] SobolevSpace.toLp μ hQ
        (SobolevSpace.product μ hQ g dg A B+
          SobolevSpace.product μ hQ g dg A B+(2:ℝ) • G) := by
  obtain ⟨q,hq,hqr⟩ := hd.product μ hQ g g d d hd A A L hg hg hL
  refine ⟨q,hq,?_⟩
  simp only [map_add,map_smul]
  let P := SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ g dg A B)
  filter_upwards [ae_restrict_of_ae hqr,hdr,hGr,
    ae_restrict_of_ae (SobolevSpace.product_coe μ hQ g dg A B hg hdg),
    ae_restrict_of_ae (Lp.coeFn_add (P+P) ((2:ℝ) • SobolevSpace.toLp μ hQ G)),
    ae_restrict_of_ae (Lp.coeFn_add P P),
    ae_restrict_of_ae (Lp.coeFn_smul (2:ℝ) (SobolevSpace.toLp μ hQ G))]
    with x hq hd hG hP hsum hdouble hsmul
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hsum hdouble hsmul
  change q x=((P+P)+(2:ℝ) • SobolevSpace.toLp μ hQ G) x
  rw [hsum,hdouble,hsmul,hq,hd,← hG]
  change _=P x+P x+2*SobolevSpace.toLp μ hQ G x
  rw [show P x=SobolevSpace.toLp μ hQ g x*SobolevSpace.toLp μ hQ dg x from hP]

omit [BorelSpace X] [ProperSpace X] in
theorem squareLaplacianSource_bound (g G dg : SobolevSpace μ hQ) (A B C : ℝ≥0)
    (hg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g x|≤A)
    (hdg : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dg x|≤B)
    (hG : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ G x|≤C) :
    ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ
      (SobolevSpace.product μ hQ g dg A B+
        SobolevSpace.product μ hQ g dg A B+(2:ℝ) • G) x|≤2*A*B+2*C := by
  simp only [map_add,map_smul]
  let P := SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ g dg A B)
  filter_upwards [hg,hdg,hG,SobolevSpace.product_coe μ hQ g dg A B hg hdg,
    Lp.coeFn_add (P+P) ((2:ℝ) • SobolevSpace.toLp μ hQ G),Lp.coeFn_add P P,
    Lp.coeFn_smul (2:ℝ) (SobolevSpace.toLp μ hQ G)] with x hg hdg hG hp hs ha hm
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hs ha hm
  change |((P+P)+(2:ℝ) • SobolevSpace.toLp μ hQ G) x|≤_
  rw [hs,ha,hm]
  have hP : |P x|≤(A:ℝ)*B := by
    change |SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ g dg A B) x|≤_
    rw [hp,abs_mul]
    exact mul_le_mul hg hdg (abs_nonneg _) A.coe_nonneg
  calc
    |P x+P x+2*SobolevSpace.toLp μ hQ G x|
      ≤ |P x|+|P x|+|2*SobolevSpace.toLp μ hQ G x| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 2*A*B+2*C := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith

end RegularPointCoordinates

end

end OAI
