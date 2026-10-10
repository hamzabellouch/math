import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.AnalyticCentering
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.BiasedSequenceOfFailure
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.BinIndex
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.ConstantsA
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.MeanZeroOfNonpretentious
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.ProductOneBounded
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.SmoothCutoffExists

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology
open MeasureTheory intervalIntegral
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Filter Finset
open scoped BigOperators Matrix.Norms.L2Operator
open scoped BigOperators ContDiff
open Finset Filter Classical
open scoped BigOperators ContDiff Topology
open scoped BigOperators Topology

namespace OrdinaryCorrelations.ElliottCompletion
open OrdinaryAnalyticCentering ElliottReductions RawLower

lemma relative_error_tendsto (C C₀ : ℝ) (hC : 0 ≤ C₀) :
    Tendsto (fun B:ℝ=>5*(B*B^(-1-GraphKernel.PrimeSystem.eta/2:ℝ))+
      C*(B*B^(-10001/10000:ℝ)+B*(J C₀ B:ℝ)/P₀ B)) atTop (nhds 0) := by
  have hg : Tendsto (fun B:ℝ=>B*B^(-1-GraphKernel.PrimeSystem.eta/2:ℝ)) atTop (nhds 0) := by
    have ht := tendsto_rpow_neg_atTop (by norm_num [GraphKernel.PrimeSystem.eta,
      GraphKernel.PrimeSystem.epsilon] : 0 < GraphKernel.PrimeSystem.eta/2)
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with B hB
    rw [show (-(GraphKernel.PrimeSystem.eta/2):ℝ)=1+(-1-GraphKernel.PrimeSystem.eta/2) by ring,
      Real.rpow_add hB,Real.rpow_one]
  have ha : Tendsto (fun B:ℝ=>B*B^(-10001/10000:ℝ)) atTop (nhds 0) := by
    have ht := tendsto_rpow_neg_atTop (by norm_num : 0 < (1/10000:ℝ))
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with B hB
    rw [show (-(1/10000):ℝ)=1+(-10001/10000:ℝ) by norm_num,
      Real.rpow_add hB,Real.rpow_one]
  simpa only [mul_zero,zero_add] using (hg.const_mul 5).add
    ((ha.add (RawCutoff.defect_scale_tendsto C₀ hC).2).const_mul C)

theorem anchored (f g : ℕ→ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (hmf : Multiplicative f) (hmg : Multiplicative g)
    (hNP : UniformlyNonpretentious f ∨ UniformlyNonpretentious g)
    (h : ℕ) (hh : 0 < h) : Tendsto (shiftAverage f g 0 h) atTop (nhds 0) := by
  by_contra hfail
  obtain ⟨h1f,h1g,hfd,hgd⟩ := finite_defects_of_correlation_failure f g hf hg hmf hmg 0 h hfail
  have hfail' : ¬Tendsto (cesaro (fun m=>f m*g (m+h))) atTop (nhds 0) := by
    have he : shiftAverage f g 0 h = cesaro (fun m=>f m*g (m+h)) := by
      funext M
      simp only [cesaro,shiftAverage,Nat.add_zero]
    rwa [←he]
  obtain ⟨γ,hγ,hγ1,N,hN,hNpos,hbias⟩ := biased_sequence_of_failure _ hfail'
  let τ : ℝ := 1+γ/128
  have hτ1 : 1 < τ := by dsimp [τ]; linarith
  have hτ2 : τ < 2 := by dsimp [τ]; linarith
  have hτγ : τ-1 ≤ γ/64 := by dsimp [τ]; linarith
  let T : ℝ := 128/γ
  have hT : 0 < T := by dsimp [T]; positivity
  have hTγ : 32/T^2 ≤ γ/64 := by
    have hγT : γ*T=128 := by dsimp [T]; field_simp
    have hT128 : 128 ≤ T := (le_div_iff₀ hγ).mpr (by linarith)
    have he : γ*T^2=128*T := by calc
      _ = (γ*T)*T := by ring
      _ = _ := by rw [hγT]
    apply (div_le_iff₀ (sq_pos_of_pos hT)).mpr
    nlinarith
  obtain ⟨phi,hφ,hφc,hφb,hφs,hφone⟩ := RawCutoff.smooth_cutoff_exists T hT
  obtain ⟨C₀,c,hC₀,hc,hBin⟩ := RawDivisorBin.raw_bin f g hf hg hmf hmg h1f h1g hfd hgd τ hτ1 hτ2
  have hC₀0 : 0 ≤ C₀ := by linarith
  obtain ⟨C,hC,hCent⟩ := analytic_centering f g hf hg hmf hmg hNP h hh τ C₀ T
    hτ1 hτ2 hC₀ hT phi hφ hφb hφs
  have hRaw := raw_lower f g hf hg hmf hmg h C₀ γ τ T hC₀0 hγ hτ1.le hτγ hT hTγ phi hφb hφone
  have hGraph := GraphBridge.centered_graph_bound h hh τ T C₀ hτ1.le hτ2 hC₀0 phi hφb hφs
  let k : ℝ := γ*c/8
  have hk : 0 < k := by dsimp [k]; positivity
  have hRate := (relative_error_tendsto C C₀ hC₀0).eventually
    (gt_mem_nhds (show 0 < k/2 by positivity))
  obtain ⟨B,hBin,hRaw,hGraph,hCent,hRate,hB⟩ :=
    (hBin.and (hRaw.and (hGraph.and (hCent.and (hRate.and (eventually_ge_atTop (1:ℝ))))))).exists
  obtain ⟨H,D,hD,hmod,hmass⟩ := hBin
  have hH : 0 < H := by linarith [hD.1]
  have hB0 : 0 < B := by linarith
  have hL : 0 < L₀ B := zero_lt_one.trans_le (RawDivisorBin.L₀_ge_one B)
  have hscale : 0 < L₀ B/B := div_pos hL hB0
  let a : ℕ→ℂ := fun d=>star (f d*g d)
  have ha : ∀ d∈D, ‖a d‖ ≤ 1 := by
    intro d hdD
    dsimp [a]
    rw [starRingEnd_apply,norm_star]
    exact product_oneBounded hf hg _ _
  let δ : ℝ := (k/2)*(L₀ B/B)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hlong : Tendsto (fun j:ℕ=>H*(N j:ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hN).const_mul_atTop hH
  have hlo := hN.eventually (hRaw H D hD hmod)
  have hce := hlong.eventually (hCent H D hD a ha)
  have hgr := hlong.eventually (hGraph H D hD a f g ha hf hg δ hδ)
  obtain ⟨j,hlo,hce,hgr⟩ := (hlo.and (hce.and hgr)).exists
  have hNj : 0 < (N j:ℝ) := by exact_mod_cast hNpos j
  have hX : 0 < H*(N j:ℝ) := mul_pos hH hNj
  have hraw := hlo (hbias j)
  have hlower : (k*(L₀ B/B))*(H*(N j:ℝ)) ≤
      ‖rawSum phi B D a f g h (H*(N j))‖ := by
    have he := mul_le_mul_of_nonneg_left hmass
      (show 0 ≤ (γ/8)*(N j:ℝ)*H by positivity)
    apply le_trans _ hraw
    convert he using 1; dsimp [k]; ring
  have hgr' := (div_le_iff₀ hX).mp hgr
  let α : ℝ := 5*B^(-1-GraphKernel.PrimeSystem.eta/2:ℝ)*L₀ B+
    C*L₀ B*(B^(-10001/10000:ℝ)+(J C₀ B:ℝ)/P₀ B)
  have hbudget : α+δ < k*(L₀ B/B) := by
    have hs : α = (L₀ B/B)*(5*(B*B^(-1-GraphKernel.PrimeSystem.eta/2:ℝ))+
        C*(B*B^(-10001/10000:ℝ)+B*(J C₀ B:ℝ)/P₀ B)) := by
      dsimp [α]
      field_simp
    have hh := mul_lt_mul_of_pos_left hRate hscale
    rw [←hs] at hh
    dsimp [δ]
    linarith
  have htri := norm_add_le
    (rawSum phi B D a f g h (H*(N j:ℝ))-centeredSum phi B D a f g h (H*(N j:ℝ)))
    (centeredSum phi B D a f g h (H*(N j:ℝ)))
  rw [sub_add_cancel] at htri
  have hupper : ‖rawSum phi B D a f g h (H*(N j:ℝ))‖ ≤ (α+δ)*(H*(N j:ℝ)) := by
    apply htri.trans
    apply (add_le_add hce hgr').trans_eq
    dsimp [α]
    ring
  have hlt := mul_lt_mul_of_pos_right hbudget hX
  exact (not_lt_of_ge hlower) (hupper.trans_lt hlt)

end OrdinaryCorrelations.ElliottCompletion

end

end OAI
