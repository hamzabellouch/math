import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Traces.NormAnnihilatorTraceKernel
import OAI.Analysis.JiangSu.Excision.ExcisionFullnessError
import OAI.Analysis.JiangSu.Nonunital.Essentiality

namespace OAI

section

noncomputable section
namespace NonunitalSI
open Pureness CurrentMain DirectComparison NonunitalGamma Filter Topology
open scoped ComplexOrder ENNReal

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma inr_commutator (x : A) (c : Unitization ℂ A) :
    (Unitization.inr x : Unitization ℂ A)*c-c*Unitization.inr x=
      Unitization.inr (x*c.snd-c.snd*x) := by
  apply Unitization.ext
  · change (Unitization.inr x*c).fst-(c*Unitization.inr x).fst=0
    simp only [Unitization.fst_mul,Unitization.fst_inr,mul_zero,zero_mul,sub_self]
  · change (Unitization.inr x*c).snd-(c*Unitization.inr x).snd=x*c.snd-c.snd*x
    simp only [Unitization.snd_mul,Unitization.fst_inr,
      Unitization.snd_inr,zero_smul,zero_add,add_zero]
    abel

lemma norm_central_boundedInr (U : Ultrafilter ℕ) (f : lp (fun _ : ℕ => A) ∞)
    (hf : ∀ a : A,Tendsto (fun n => ‖f n*a-a*f n‖) (U : Filter ℕ) (𝓝 0))
    (c : Unitization ℂ A) :
    Tendsto (fun n => ‖boundedInr (A := A) f n*c-c*boundedInr (A := A) f n‖) (U : Filter ℕ) (𝓝 0) := by
  simpa only [boundedInr_apply,inr_commutator,Unitization.norm_inr] using hf c.snd

lemma uniform_traceTwoNorm_approximate_unit [CompactSpace (NormalizedTrace A)]
    {r : ℝ} (hr : 0<r) :
    ∃ b : A,0≤b ∧ ‖b‖≤1 ∧ ∀ τ : NormalizedTrace A,
      traceTwoNorm τ.unitized (1-Unitization.inr b)≤r := by
  obtain ⟨b,hbp,hbn,hbt⟩ := uniform_trace_approximate_unit (A := A) (r^2) (sq_pos_of_pos hr)
  let B : Unitization ℂ A := Unitization.inr b
  have hBp : 0≤B := map_nonneg (Unitization.inrNonUnitalStarAlgHom ℂ A) hbp
  have hB1 : B≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg B hBp).mp (by
    simpa only [B,Unitization.norm_inr] using hbn.le)
  have hxp : 0≤1-B := sub_nonneg.mpr hB1
  have hx1 : 1-B≤1 := sub_le_self _ hBp
  refine ⟨b,hbp,hbn.le,fun τ => ?_⟩
  have hm := (τ.unitized.functional.monotone
    (NonunitalGamma.positive_contraction_square_le hxp hx1)).1
  have hs := traceTwoNorm_sq τ.unitized (1-B)
  rw [hxp.isSelfAdjoint.star_eq] at hs
  change (τ.unitized.functional ((1-B)*(1-B))).re≤(τ.unitized.functional (1-B)).re at hm
  simp only [B,map_sub,τ.unitized.normalized,NormalizedTrace.unitized_inr,Complex.sub_re,Complex.one_re] at hm
  have hb := hbt τ
  change 1-r^2<(τ.functional b).re at hb
  change _≤1-(τ.functional b).re at hm
  change traceTwoNorm τ.unitized (1-B)≤r
  nlinarith [traceTwoNorm_nonneg τ.unitized (1-B)]

 theorem eventual_hereditary_upperCut_trace_lower [Nontrivial A]
    [CompactSpace (NormalizedTrace A)]
    (hsimple : NonunitalGamma.TopologicallySimple A)
    (hprojectionless : ∀ p : A,IsStarProjection p → p=0) (U : Ultrafilter ℕ)
    (f : lp (fun _ : ℕ => A) ∞) (hf : ∀ n,0≤f n) (hfn : ∀ n,‖f n‖≤1)
    (hcentral : ∀ a : A,Tendsto (fun n => ‖f n*a-a*f n‖) (U : Filter ℕ) (𝓝 0))
    {t : ℝ} (ht : 0<t)
    (hlarge : ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,t≤(τ.functional (f n)).re)
    (hdefect : ∀ η : ℝ,0<η → ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,
      (τ.functional (f n-f n*f n)).re<η)
    (c : Unitization ℂ A) (hc : 0≤c) (hcn : ‖c‖≤1) (hc0 : c≠0) :
    ∃ β : ℝ,0<β ∧ ∀ δ : ℝ,0<δ → δ≤1 →
      ∀ᶠ n in (U : Filter ℕ),∀ τ : NormalizedTrace A,
        2*β≤(τ.unitized.functional (hereditaryUpperCut δ (Unitization.inr (f n)) c)).re := by
  let r : ℝ := t/16
  have hr : 0<r := by dsimp [r]; positivity
  obtain ⟨u,hu,hun,hut⟩ := uniform_traceTwoNorm_approximate_unit (A := A) hr
  obtain ⟨m,X,Y,hXY⟩ := ideal_factorization_through_unitization hsimple hprojectionless c hc0 u hr
  let C : ℝ := ∑ i,‖X i‖*‖Y i‖
  have hC : 0≤C := Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let M : ℝ := C+1
  have hM : 0<M := by dsimp [M]; linarith
  let β : ℝ := (t/(8*M))^2/2
  refine ⟨β,by dsimp [β]; positivity,?_⟩
  intro δ hδ hδ1
  let Q : ℕ → Unitization ℂ A := fun n => CFC.sqrt (upperCut δ (Unitization.inr (f n)))
  have hQ (n : ℕ) : ‖Q n‖≤1 := norm_sqrt_upperCut_le hδ _ (by simpa only [Unitization.norm_inr] using hfn n)
  have herr : Tendsto (fun n => ∑ i,‖Q n*X i-X i*Q n‖*‖Y i‖) (U : Filter ℕ) (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun i _ =>
      (norm_central_upperCut_sqrt U (boundedInr (A := A) f)
        (fun n => Unitization.inr_nonneg_iff.mpr (hf n)) (X i)
        (norm_central_boundedInr U f hcentral (X i)) hδ hδ1).mul_const ‖Y i‖)
    simpa only [zero_mul,Finset.sum_const_zero,boundedInr_apply] using h
  have hevent := (tendsto_order.1 herr).2 r hr
  have hdevent := hdefect (δ*(t/4)) (by positivity)
  filter_upwards [hlarge,hevent,hdevent] with n hn he hd
  intro τ
  have hτlo : t/2≤(τ.unitized.functional (upperCut δ (Unitization.inr (f n)))).re := by
    have hlo := upperCut_trace_lower τ.unitized hδ (Unitization.inr (f n))
      (Unitization.inr_nonneg_iff.mpr (hf n)) (by simpa only [Unitization.norm_inr] using hfn n)
    have hdiv : (τ.functional (f n-f n*f n)).re/δ<t/4 :=
      (div_lt_iff₀ hδ).mpr (by nlinarith [hd τ])
    simp only [←Unitization.inr_mul,←Unitization.inr_sub,NormalizedTrace.unitized_inr] at hlo
    linarith [hn τ]
  have hQsq : (traceTwoNorm τ.unitized (Q n))^2=
      (τ.unitized.functional (upperCut δ (Unitization.inr (f n)))).re := by
    rw [traceTwoNorm_sq]
    dsimp [Q]
    rw [(CFC.sqrt_nonneg (upperCut δ (Unitization.inr (f n) : Unitization ℂ A))).isSelfAdjoint.star_eq,
      CFC.sqrt_mul_sqrt_self _ (upperCut_nonneg hδ.le _)]
  have hQn : traceTwoNorm τ.unitized (Q n)≤1 := (traceTwoNorm_le_norm _ _).trans (hQ n)
  have hQ0 := traceTwoNorm_nonneg τ.unitized (Q n)
  have hQlo : t/2≤traceTwoNorm τ.unitized (Q n) := by nlinarith
  have hrel := traceTwoNorm_relative_factorization τ.unitized (Q n) c (Unitization.inr u)
    (hQ n) hcn X Y
  have hqc0 := traceTwoNorm_nonneg τ.unitized (Q n*c)
  have hqc : t/(8*M)≤traceTwoNorm τ.unitized (Q n*c) := by
    apply (div_le_iff₀ (by positivity : 0<8*M)).mpr
    have huτ := hut τ
    change _≤_+_+C*_+_ at hrel
    dsimp [M,r] at *
    nlinarith
  have hsq : (traceTwoNorm τ.unitized (Q n*c))^2=
      (τ.unitized.functional (hereditaryUpperCut δ (Unitization.inr (f n)) c)).re := by
    rw [traceTwoNorm_sq]
    congr 2
    simp only [Q,star_mul,hc.isSelfAdjoint.star_eq,
      (CFC.sqrt_nonneg (upperCut δ (Unitization.inr (f n) : Unitization ℂ A))).isSelfAdjoint.star_eq,
      hereditaryUpperCut]
    calc
      c*CFC.sqrt (upperCut δ (Unitization.inr (f n)))*(CFC.sqrt (upperCut δ (Unitization.inr (f n)))*c)=
          c*(CFC.sqrt (upperCut δ (Unitization.inr (f n)))*CFC.sqrt (upperCut δ (Unitization.inr (f n))))*c := by noncomm_ring
      _=c*upperCut δ (Unitization.inr (f n))*c := by
        rw [CFC.sqrt_mul_sqrt_self _ (upperCut_nonneg hδ.le _)]
  dsimp [β]
  have hpow : (t/(8*M))^2≤(traceTwoNorm τ.unitized (Q n*c))^2 :=
    (sq_le_sq₀ (by positivity) hqc0).mpr hqc
  linarith

end NonunitalSI

end
end

end OAI
