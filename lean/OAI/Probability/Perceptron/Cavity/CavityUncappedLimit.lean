import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityBulkUncappedLog
import OAI.Probability.Perceptron.Cavity.CavityCounts
import OAI.Probability.Perceptron.Cavity.CavitySphericalGrid
import OAI.Probability.Perceptron.Cavity.BulkCavityData
import OAI.Probability.Perceptron.Variational.UniformUncapLimit

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators BoundedContinuousFunction NNReal

theorem cavityBulkFullLog_rounded_tendsto (n d : ℕ) (N M : ℕ→ℕ) (g : Jet3)
    (hg : HasCompactSupport (g.d1 : ℝ→ℝ)) (v : ℕ→ℕ→ℝ)
    (P : Measure BrownianPath) [IsProbabilityMeasure P] (hBrow : IsBrownianReal brownianEval P)
    (η : Measure Time) [IsProbabilityMeasure η] {B K a c KC : ℝ} (hB : B<1)
    (ha0 : 0≤a) (haK : a≤K) (hc : |c|≤KC)
    (hK : ∀ j,M j/(N j+1:ℕ)*‖g.d1‖^2≤K)
    (hC : ∀ j (b : BulkDisorder (N j+1) (M j)) x,|bulkC (N j+1) (M j) g b.1 x|≤KC)
    (hL2 : Tendsto (fun j=>bulkReplicaMean (N j) (M j) g.f (v j) 1
      (fun b x=>(bulkC (N j+1) (M j) g b.1 (x 0)-c)^2)) atTop (𝓝 0))
    (hcap : ∀ (Λ : ℝ) (hΛ : 1≤Λ),Tendsto (fun j=>cavityBulkLog n d (N j) (M j) g (v j) Λ hΛ-
      roundedCavityLog n d g.f Λ hΛ η B ha0 haK j) atTop (𝓝 0)) :
    Tendsto (fun j=>cavityBulkFullLog n d (N j) (M j) g (v j)-
      ((n+1:ℕ)/2*c+roundedCavityValue n d g P η B ha0 haK j)) atTop (𝓝 0) := by
  let U:=Real.exp (2*((n+1:ℕ)/2*KC+(d:ℝ)*‖g.f‖)+2*(n+1:ℕ)*K)
  let V:=Real.exp (2*((d:ℝ)*‖g.f‖))*Real.exp (2*(n+1:ℕ)*a)
  let F:=fun j=>cavityBulkFullLog n d (N j) (M j) g (v j)-
    ((n+1:ℕ)/2*c+roundedCavityValue n d g P η B ha0 haK j)
  let G:=fun Λ j=>if hΛ : 1≤Λ then
      (∫ b,cavityBulkCompError n d (N j) (M j) g (v j) Λ hΛ c b
        ∂(bulkDisorderLaw (N j+1) (M j)).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d (N j) (M j)))))+
      (cavityBulkLog n d (N j) (M j) g (v j) Λ hΛ-roundedCavityLog n d g.f Λ hΛ η B ha0 haK j)
    else 0
  apply tendsto_zero_of_uniform_inverse_cap F G (C:=U+V) (by dsimp [U,V]; positivity)
  · intro Λ hΛ j
    have hb:=cavityBulk_uncap_annealed n d (N j) (M j) g (v j) Λ hΛ K KC (hK j) (hC j)
    have hr:=roundedCavity_uncap n d g P hBrow η hB ha0 haK j hΛ
    have he:=cavityBulkFullLog_decomposition n d (N j) (M j) g (v j) Λ hΛ c K KC hc (hK j) (hC j)
    dsimp only at he hb
    have hid : F j-G Λ j=
      (∫ b,cavityBulkUncapError n d (N j) (M j) g (v j) Λ hΛ b
        ∂(bulkDisorderLaw (N j+1) (M j)).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d (N j) (M j)))))-
      (roundedCavityValue n d g P η B ha0 haK j-roundedCavityLog n d g.f Λ hΛ η B ha0 haK j) := by
      dsimp [F,G]; rw [dite_eq_left hΛ,he]; ring
    rw [hid]
    have hV : roundedCavityValue n d g P η B ha0 haK j-roundedCavityLog n d g.f Λ hΛ η B ha0 haK j≤V/Λ := by
      exact hr.2.trans_eq (by dsimp [V]; ring)
    have hU : (∫ b,cavityBulkUncapError n d (N j) (M j) g (v j) Λ hΛ b
        ∂(bulkDisorderLaw (N j+1) (M j)).prod (stdGaussian (EuclideanSpace ℝ (CavityBulkNoiseIndex n d (N j) (M j)))))≤U/Λ := hb.2.2
    have hU0 : 0≤U/Λ:=by dsimp [U]; positivity
    have hV0 : 0≤V/Λ:=by dsimp [V]; positivity
    rw [add_div]
    exact abs_le.mpr ⟨by linarith [hb.2.1,hr.1],by linarith [hb.2.1,hr.1]⟩
  · intro Λ hΛ
    have hcomp:=cavityBulkCompError_tendsto_zero n d N M g hg v Λ hΛ c KC hc hC hL2
    simpa only [G,dite_eq_left hΛ,zero_add] using hcomp.add (hcap Λ hΛ)

theorem bulk_cavity_uniform_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hBrow : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0≤α)
    (g : Jet3) (hg : HasCompactSupport (g.d1 : ℝ→ℝ)) {K : ℝ} (hK0 : 0≤K)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (M : ℕ→ℕ) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
      (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
      (D : BulkCavityData M g v s α K μ hg)
      (KC : ℝ) (_hDc : |D.c|≤KC)
      (_hK : ∀ j,((M (s j)+2:ℕ):ℝ)/(s j+1:ℕ)*‖g.d1‖^2≤K)
      (_hC : ∀ j (b : BulkDisorder (s j+1) (M (s j)+2)) x,
        |bulkC (s j+1) (M (s j)+2) g b.1 x|≤KC)
      (d : ℕ), |(d:ℝ)-(n+1:ℕ)*α|≤1 →
      ∀ δ : ℝ,0<δ → ∀ᶠ j : ℕ in atTop,
      (n+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ ≤
        cavityBulkFullLog n d (s j) (M (s j)+2) g (v (s j)) := by
  filter_upwards [finiteSphericalFieldValue_depth_uniform (K/2) (by positivity) ε hε] with n hn
  intro M v s μ D KC hDc hK hC d hd δ hδ
  let η:=markedTimePair K μ
  let B:=(α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)
  have hA0 : 0≤α*‖g.d1‖^2:=mul_nonneg hα (sq_nonneg _)
  have hB : B<1:=(div_lt_one (by linarith : 0<1+α*‖g.d1‖^2)).mpr (by linarith)
  let V:=roundedCavityValue n d g P η B D.a_nonneg D.a_le_K
  let U:=fun j=>cavityBulkFullLog n d (s j) (M (s j)+2) g (v (s j))
  have hfull : Tendsto (fun j=>U j-((n+1:ℕ)/2*D.c+V j)) atTop (𝓝 0) :=
    cavityBulkFullLog_rounded_tendsto n d s (fun j=>M (s j)+2) g hg (fun j=>v (s j)) P hBrow
      η hB D.a_nonneg D.a_le_K hDc hK hC D.c_L2 (D.capped n d)
  have hm:=roundedProfileMoment_tendsto η hB
  have he:=cappedAError_tendsto (quantileRoundLaw η) (⟨η,inferInstance⟩ : ProbabilityMeasure Time)
    (quantileRoundLaw_tendsto η) hB
  let R:=fun j=>(n+1:ℕ)*((D.c+D.a)/2+(terminalVariational P α g.f).toReal-roundedProfileMoment η B j-
    cappedAError (quantileRoundLaw η j) η B-ε)-‖g.f‖
  have hR : Tendsto R atTop (𝓝 ((n+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖)) := by
    have h:=((((tendsto_const_nhds (x:=(D.c+D.a)/2+(terminalVariational P α g.f).toReal)).sub hm).sub he).sub_const ε).const_mul ((n+1:ℕ):ℝ)
    have h':=h.sub_const ‖g.f‖
    have heq : (n+1:ℕ)*((D.c+D.a)/2+(terminalVariational P α g.f).toReal-
        cavityProfileMoment η B-0-ε)-‖g.f‖ =
        (n+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖ := by
      rw [show (D.c+D.a)/2=cavityProfileMoment η B from D.radial]
      ring
    rw [heq] at h'
    exact h'
  have ht:=hR.add hfull
  simp only [add_zero] at ht
  have hev:=ht.eventually (Ioi_mem_nhds (show
    (n+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ <
    (n+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖ from by linarith))
  filter_upwards [hev] with j hj
  have hlo:=roundedCavityValue_lower P hα g n d η hB D.a_nonneg D.a_le_K D.support D.field_bound hd hn j
  change _<R j+(U j-((n+1:ℕ)/2*D.c+V j)) at hj
  dsimp [R] at hj
  dsimp [V,U] at hj
  linarith

theorem cavity_good_fullLog_lower (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) {α : ℝ} (hα : 0<α)
    (g : Jet3) (hg : HasCompactSupport (g.d1 : ℝ→ℝ))
    (G : CavityGoodParameters α g.f) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k : ℕ in atTop,∀ d : ℕ,|(d:ℝ)-(k+1:ℕ)*α|≤1→∀ δ : ℝ,0<δ→
      ∀ᶠ n : ℕ in atTop,∀ v∈bulkJointGoodSet α g.f G.J n,
      (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ≤
        cavityBulkFullLog k d n (patternCount α (n+1)) g v := by
  let M:=cavityOmittedCount α
  let K:=(α+2)*‖g.d1‖^2
  let KC:=(α+2)*‖g.dilationMark hg‖
  have hK0 : 0≤K:=by dsimp [K]; positivity
  have hK : ∀ n,((M n+2:ℕ):ℝ)/(n+1:ℕ)*‖g.d1‖^2≤K := fun n=>
    mul_le_mul_of_nonneg_right (cavity_omitted_bound hα.le n) (sq_nonneg _)
  have hC : ∀ n (b : BulkDisorder (n+1) (M n+2)) x,|bulkC (n+1) (M n+2) g b.1 x|≤KC := by
    intro n b x
    exact (bulkC_bound n (M n+2) g hg b x).trans
      (mul_le_mul_of_nonneg_right (cavity_omitted_bound hα.le n) (norm_nonneg _))
  filter_upwards [bulk_cavity_uniform_lower P hB hα.le g hg hK0 ε hε] with k hk
  intro d hd δ hδ
  apply cavity_eventually_uniform (bulkJointGoodSet α g.f G.J)
    {v : ℕ→ℝ | ∀ p,v p∈Icc (1:ℝ) 2} (fun _=>1) (by intro p; constructor <;> norm_num)
    (fun _ _ h=>h.2) G.nonempty
  intro v hv hvG
  have hdO : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n) g.f p (v n)) atTop (𝓝 0) :=
    fun p=>(G.deviation v hvG p).2
  have hdF : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n+2) g.f p (v n)) atTop (𝓝 0) := by
    intro p
    apply (G.deviation v hvG p).1.congr'
    filter_upwards [cavity_omitted_full hα] with n hn
    rw [show M n+2=patternCount α (n+1) from hn]
  have hv1 : ∀ n p,1≤v n p:=fun n p=>(hv n p).1
  have hv2 : ∀ n p,|v n (p+1)|≤(2:ℝ) := by
    intro n p
    rw [abs_of_nonneg (by linarith [(hv n (p+1)).1])]
    exact (hv n (p+1)).2
  by_contra hnot
  have hbad : ∃ᶠ n : ℕ in atTop,cavityBulkFullLog k d n (patternCount α (n+1)) g (v n)<
      (k+1:ℕ)*((terminalVariational P α g.f).toReal-ε)-‖g.f‖-δ := by
    simpa only [not_eventually,not_le] using hnot
  obtain ⟨q,hq,hqbad⟩:=extraction_of_frequently_atTop hbad
  obtain ⟨ν,t,ht,ho⟩:=compact_array_law_subsequence (fun j=>bulkGibbsArrayLaw (q j) (M (q j)) g.f (v (q j)))
  let b:=q∘t
  have hb : StrictMono b:=hq.comp ht
  obtain ⟨μ,u,hu,hf⟩:=compact_array_law_subsequence (fun j=>bulkMarkedArrayLaw (b j) (M (b j)+2) g (v (b j)) K (hK (b j)))
  let s:=b∘u
  have hs : StrictMono s:=hb.comp hu
  have ho' : Tendsto (fun j=>bulkGibbsArrayLaw (s j) (M (s j)) g.f (v (s j))) atTop (𝓝 ν):=
    ho.comp hu.tendsto_atTop
  have hf' : Tendsto (fun j=>bulkMarkedArrayLaw (s j) (M (s j)+2) g (v (s j)) K (hK (s j))) atTop (𝓝 μ):=hf
  obtain ⟨D⟩:=bulk_cavity_data M g hg v hv1 (by norm_num : (0:ℝ)≤2) hv2 hdO hdF s hs α hα.le
    ((cavity_omitted_density hα).comp hs.tendsto_atTop) ν ho' K hK0 hK μ hf'
  have hDc : |D.c|≤KC := D.c_bound.trans (by dsimp [KC]; nlinarith [norm_nonneg (g.dilationMark hg)])
  have hlow:=hk M v s μ D KC hDc (fun j=>hK (s j)) (fun j=>hC (s j)) d hd δ hδ
  obtain ⟨j,hj,hje⟩:=(hlow.and (hs.tendsto_atTop.eventually (cavity_omitted_full hα))).exists
  rw [show M (s j)+2=patternCount α (s j+1) from hje] at hj
  exact (not_lt_of_ge hj) (hqbad (t (u j)))

end SphericalPerceptronFreeEnergy
end

end OAI
