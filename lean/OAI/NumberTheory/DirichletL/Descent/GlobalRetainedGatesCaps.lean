import OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesRadius

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open InverseSecondUniformCutoff
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma uniform_radius_cap (G E : Finset ι) (hEG : E⊆G)
    (Z delta eta L Y tau Lcol LY : ℝ) (hZ : 0<Z) (hL : 0≤L) (hY : 0<Y)
    (hLc : L≤Z^Lcol) (hYi : Y⁻¹≤Z^LY) :
    uniformSecondRadius p Z delta eta G E L Y (Z^tau)≤
      Z^(delta+eta+2*Lcol+tau+LY) := by
  have hr : primeProductNorm p E/primeProductNorm p G≤1 :=
    (div_le_one (primeProductNorm_pos p hp G)).mpr (primeProductNorm_mono p hp hEG)
  have hr0 : 0≤primeProductNorm p E/primeProductNorm p G := by
    exact div_nonneg (primeProductNorm_pos p hp E).le (primeProductNorm_pos p hp G).le
  have hs : (primeProductNorm p E/primeProductNorm p G)^2≤1 := pow_le_one₀ hr0 hr
  unfold uniformSecondRadius
  rw [div_eq_mul_inv]
  calc
    _ ≤ Z^(delta+eta)*1*(Z^Lcol)^2*Z^tau*Z^LY := by gcongr
    _ = _ := by
      rw [mul_one,←Real.rpow_mul_natCast hZ.le]
      repeat rw [←Real.rpow_add hZ]
      congr 1
      norm_num
      ring

lemma bare_frequency_norm_le (a k : O) (ha : a≠0) :
    ‖eisEmbedding k‖^2≤‖eisEmbedding (a*k)‖^2 := by
  have hh := element_norm_ge_one a ha
  rw [map_mul,norm_mul,mul_pow]
  exact le_mul_of_one_le_left (sq_nonneg _) hh

include hp in

theorem supported_outer_caps
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (Z delta eta L Y tau b X Lcol LY Lcap : ℝ)
    (hZ : 1≤Z) (hL : 0≤L) (hY : 0<Y) (hLc : L≤Z^Lcol) (hYi : Y⁻¹≤Z^LY)
    (hgeom : b*X≤Z^Lcap) (hphysical : delta+eta+2*Lcol+tau+LY≤Lcap) :
    ∀x∈supportedRetainedSource p extra original negative J lists pool
      (fun G E=>uniformSecondRadius p Z delta eta G E L Y (Z^tau)) b X,
      ∀i,outerNorms p x i≤Z^Lcap := by
  intro x hx i
  have hret := supported_subset p extra original negative J lists pool _ b X hx
  have hm := (mem_unifiedSource p pool _ _ x).mp hret
  have hg : primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤Z^Lcap :=
    (geometrySource_gate p _ b X x hx).trans hgeom
  have hG : primeProductNorm p x.second.sourceCommon≤Z^Lcap :=
    (le_mul_of_one_le_right (primeProductNorm_pos p hp _).le (primeProductNorm_ge_one p hp _)).trans hg
  have hV : primeProductNorm p x.second.overlap≤Z^Lcap :=
    (le_mul_of_one_le_left (primeProductNorm_pos p hp _).le (primeProductNorm_ge_one p hp _)).trans hg
  fin_cases i
  · exact hG
  · exact (primeProductNorm_mono p hp hm.2.2.1).trans hG
  · exact hV
  · have hb := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) _ _).mp hm.2.2.2.2
    exact (bare_frequency_norm_le _ _ (actualSecondMultiplier_ne_zero p x)).trans
      (hb.2.trans ((uniform_radius_cap p hp _ _ hm.2.2.1 Z delta eta L Y tau Lcol LY
        (zero_lt_one.trans_le hZ) hL hY hLc hYi).trans
        (Real.rpow_le_rpow_of_exponent_le hZ hphysical)))

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
