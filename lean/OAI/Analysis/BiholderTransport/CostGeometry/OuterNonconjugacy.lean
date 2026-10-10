import Mathlib
import OAI.Analysis.BiholderTransport.LinearAlgebra.NormalRelativeHessianBound
import OAI.Analysis.BiholderTransport.Regularity.OuterSplitLowerTest
import OAI.Analysis.BiholderTransport.LinearAlgebra.PositiveBilinearBound

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff BoundedContinuousFunction

namespace WeakMTWTransport
section OuterNonconjugacy
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]
  [MeasurableSpace M] [BorelSpace M]

lemma WeakMTW.modified_outer_nonconjugate (hmtw : WeakMTW (n := n) (M := M))
    {lam cap : ℝ} (hlam : 0 < lam) (hcap : 0 ≤ cap) {x0 a : M}
    {uv : (M →ᵇ ℝ)×(M →ᵇ ℝ)} (huv : uv∈densityDualClass (metricVolume n) lam cap x0)
    {r : TangentSpace 𝓘(ℝ,Model n) a} (hr : r∈minimizingVectors a)
    {φ : ℝ → ℝ} (hmono : StrictMono φ) (hφ : ContDiffAt ℝ 2 φ (uv.1 a))
    {l : ℝ} (hd : HasDerivAt φ l (uv.1 a)) (hl : 1 < l)
    (hconc : iteratedDeriv 2 φ (uv.1 a) ≤ 0)
    (hmount : ∀ y : M,φ (uv.1 a)+cost a (riemannianExp a r)-cost y (riemannianExp a r) ≤ φ (uv.1 y)) :
    Function.Injective (fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n)
      (riemannianExp a r) (riemannianExp a v)) r) := by
  have hlp : 0 < l := zero_lt_one.trans hl
  have ht : 0 < l⁻¹ := inv_pos.mpr hlp
  have ht1 : l⁻¹ < 1 := (inv_lt_one₀ hlp).mpr hl
  let s0 := (l⁻¹+1)/2
  have hts : l⁻¹ < s0 := by dsimp [s0]; linarith only [ht1]
  have hs0 : s0 < 1 := by dsimp [s0]; linarith only [ht1]
  have hp := contracted_minimizer_mem_injectivityDomain hr ht ht1
  obtain ⟨m,hm,Hm⟩ := exists_divided_hessian_baseline hr ht hts hs0
  obtain ⟨C,hC,HC⟩ := hmtw.exists_normal_relative_hessian_bound hlam hcap hp (div_pos hm hlp)
  let D := fderiv ℝ (fun v => extChartAt 𝓘(ℝ,Model n) (riemannianExp a r) (riemannianExp a v)) r
  have hz (ξ : TangentSpace 𝓘(ℝ,Model n) a) (hξ : D ξ=0) : ξ=0 := by
    by_contra hne
    have hk : mfderiv 𝓘(ℝ,TangentSpace 𝓘(ℝ,Model n) a) 𝓘(ℝ,Model n)
        (riemannianExp a) r ξ=0 := by rw [exp_mfderiv_apply_eq_coordinate]; exact hξ
    have H := conjugate_radial_hessian_tendsto_atBot hr hk (inner_self_ne_zero.mpr hne)
    let A := hessianValue a (l⁻¹ • r) ξ
    let K := |A|+C*‖ξ‖^2
    have hK : 0 ≤ K := add_nonneg (abs_nonneg A) (mul_nonneg hC (sq_nonneg _))
    have hb := H.eventually (eventually_lt_atBot (-l*K-1))
    have hn : ∀ᶠ s : ℝ in 𝓝[<] 1,s0 ≤ s ∧ s < 1 :=
      (((eventually_gt_nhds hs0).filter_mono nhdsWithin_le_nhds).mono (fun _ h => h.le)).and self_mem_nhdsWithin
    obtain ⟨s,hs,hlt⟩ := (hn.and hb).exists
    have hsp : 0 < s := ht.trans_le (hts.le.trans hs.1)
    obtain ⟨f,hf,hfv,hflo,hfD,hfH⟩ := outer_split_lower_test hr hmono hφ hd hlp.ne' hmount hsp hs.2
    have hscalar (d : TangentSpace 𝓘(ℝ,Model n) a) :
        0 ≤ -(iteratedDeriv 2 φ (uv.1 a)/l^3)*(inner ℝ r d)^2 :=
      mul_nonneg (neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg hconc (pow_nonneg hlp.le _))) (sq_nonneg _)
    have hpos (d : TangentSpace 𝓘(ℝ,Model n) a) :
        (m/l)*‖d‖^2 ≤ fderiv ℝ (fderiv ℝ f) 0 d d+hessianValue a (l⁻¹ • r) d := by
      rw [hfH]
      have Hbase := mul_le_mul_of_nonneg_left (Hm s hs.1 hs.2 d) ht.le
      have Halgebra : l⁻¹*(hessianValue a (l⁻¹ • r) d/l⁻¹-hessianValue a (s • r) d/s)=
          -(l*s)⁻¹*hessianValue a (s • r) d+hessianValue a (l⁻¹ • r) d := by
        field_simp
        ring
      rw [Halgebra] at Hbase
      have HP := hscalar d
      simp only [div_eq_mul_inv] at Hbase HP ⊢
      nlinarith only [Hbase,HP]
    have HB := HC x0 uv huv f hf hfD hfv.symm hflo hpos ξ
    rw [hfH] at HB
    have HA : -A ≤ |A| := neg_le_abs A
    have HS := hscalar ξ
    have Hbound : -hessianValue a (s • r) ξ/(l*s) ≤ K := by
      dsimp [A,K] at *
      simp only [mul_inv_rev,div_eq_mul_inv] at *
      nlinarith only [HB,HA,HS]
    have Hmul := (div_le_iff₀ (mul_pos hlp hsp)).mp Hbound
    have Hls : l*s ≤ l := by nlinarith only [hs.2,hlp]
    have Hmul' := mul_le_mul_of_nonneg_left Hls hK
    linarith only [Hmul,Hmul',hlt]
  intro p q hpq
  apply sub_eq_zero.mp
  apply hz (p-q)
  rw [map_sub,hpq,sub_self]

end OuterNonconjugacy
end WeakMTWTransport

end

end

end

end OAI
