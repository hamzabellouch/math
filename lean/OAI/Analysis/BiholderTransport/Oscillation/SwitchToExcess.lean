import Mathlib
import OAI.Analysis.BiholderTransport.Oscillation.ScalarFirstSwitch
import OAI.Analysis.BiholderTransport.Coordinates.RayBenchmark
import OAI.Analysis.BiholderTransport.Oscillation.LowerSwitch
import OAI.Analysis.BiholderTransport.Convexity.ConvexNormSq
import OAI.Analysis.BiholderTransport.Oscillation.SwitchNorms

namespace OAI

section

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
section SwitchToExcess
variable {n:ℕ} {M:Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x:M=>TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.switch_to_positive_excess (hmtw:WeakMTW (n:=n) (M:=M))
    {u v:M → ℝ} (hu:Continuous u) (hv:Continuous v) (hd:IsCostDualPair u v)
    {x:M} {p q:TangentSpace 𝓘(ℝ,Model n) x} (hp:p∈minimizingVectors x) (hq:q∈minimizingVectors x)
    {α D b r R H eta C d:ℝ} {Bc Bo:ℝ → ℝ} (ho:Continuous Bo)
    (ha:v (riemannianExp x p)=α) (ha1:v (riemannianExp x q)=α+D)
    (hb:0 < b) (hD:0 < D) (hr:0 ≤ r) (hR:0 ≤ R) (hC:0 ≤ C)
    (hg0:contactGap u v x (riemannianExp x p)≤r)
    (hg1:contactGap u v x (riemannianExp x q)≤r)
    (hangle:‖p‖^2-inner ℝ p q≤6*D)
    (heta:0 ≤ eta) (heta1:eta≤1/128) (hrb:r≤b/4) (hbD:b≤D/16)
    (hob:∀s,0 ≤ Bo s ∧ Bo s≤H) (ho0:Bo 0≤1+1/1024) (ho1:Bo 1=0)
    (hol:∀s≤1/16,1≤Bo s) (hbar:∀s∈Icc (1/16) (1-eta),Bo 0+1≤Bo s)
    (hc0:∀s,-1≤Bc s) (hc1:∀s≤1/2,1-1/1024≤Bc s)
    (hsmall:‖((8*b/D):ℝ) • p‖<d)
    (hanchor:b*H+2*r+6*D*(8*b/D)+(C*‖p‖^2)*(8*b/D)^2≤R)
    (hosc:∀z:M,sectionOscillation u v z R≤(1+eta)*D)
    (hlower:4*eta*D+2*r+12*D*(8*b/D)+2*(C*‖p‖^2)*(8*b/D)^2+b≤D)
    (hlower':2*(C*‖p‖^2)*(8*b/D)≤2*D)
    (hnorm:2*(8*b/D)*‖p‖^2+2*b*H+2*r≤D/4)
    (herror:r+(C+1)*(8*b/D)^2*‖p‖^2≤b/1024)
    (hTaylor:∀z:M,∀p' w:TangentSpace 𝓘(ℝ,Model n) z,
      p'∈minimizingVectors z → ‖w‖<d → cost (riemannianExp z w) (riemannianExp z p')≤
        cost z (riemannianExp z p')-inner ℝ p' w+C*‖w‖^2) :
    ∃y:M,b / 1024 ≤ modifiedExcess v α D b Bc Bo y := by
  let z:TangentBundle 𝓘(ℝ,Model n) M:=⟨x,p⟩
  let T:ℝ:=8*b/D
  have hT:0<T:=by dsimp [T]; positivity
  have hT1:T≤1/2:=by dsimp [T]; apply (div_le_iff₀ hD).mpr; linarith only [hbD]
  have hg0':contactGap (cTransform v) v x (riemannianExp x p)≤r:=by rwa [←hd.1]
  have hg1':contactGap (cTransform v) v x (riemannianExp x q)≤r:=by rwa [←hd.1]
  have ho02:Bo 0≤2:=by linarith only [ho0]
  obtain ⟨t,ht,ym,yp,hym,hyp,hcm,hcp,hanch⟩:=actual_first_switch (n := n) (z := z) hv hp ho ha ha1 hb hD hrb hbD
    heta (by linarith only [heta1]) (fun s=>(hob s).1) ho02 ho1 hol hbar hg0' hg1'
  have ht0:0 ≤ t:=ht.1.le
  have ht1:t≤1/2:=ht.2.trans hT1
  have htt:t^2≤T^2:=sq_le_sq₀ ht0 hT.le |>.mpr ht.2
  have hTp:‖t • p‖<d:=by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht0]
    have H:=mul_le_mul_of_nonneg_right ht.2 (norm_nonneg p)
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hT.le] at hsmall
    exact H.trans_lt hsmall
  have hbench:=ray_benchmark hv hp hq ha hg1' hangle ht0 hTp (hTaylor x)
  have hbench':-cost (sprayFlow t z).1 (riemannianExp x q)-v (riemannianExp x q)≥
      -‖p‖^2/2-α-r+(‖p‖^2-6*D)*t-(C*‖p‖^2)*t^2:=by simpa only [mul_assoc] using hbench
  have hbCH:0 ≤ C*‖p‖^2:=mul_nonneg hC (sq_nonneg _)
  have htimeC:=mul_le_mul_of_nonneg_left htt hbCH
  have htimeD:=mul_le_mul_of_nonneg_left ht.2 (show 0 ≤ 6*D by positivity)
  obtain ⟨hga0,hga1⟩:=ray_original_section_anchors hu hv hd hp ho hb.le hob ha ht0
    (by linarith only [ht1]) (hanch t ⟨ht0,le_rfl⟩).2 hbench'
  have hmove:b*H+2*r+6*D*t+(C*‖p‖^2)*t^2≤R:=by linarith only [hanchor,htimeC,htimeD]
  have hbase:b*H+r≤R:=by
    have hnon:0 ≤ 6*D*t+(C*‖p‖^2)*t^2:=by positivity
    linarith only [hmove,hr,hnon]
  have hmod:=modified_contact_original_section hu hv hd ho hb.le hob hcm
  have hmR:ym∈gapSection u v (sprayFlow t z).1 R:=by
    change contactGap u v (sprayFlow t z).1 ym≤R
    exact hmod.trans (by linarith only [hbase,hr])
  have ha0R:riemannianExp x p∈gapSection u v (sprayFlow t z).1 R:=hga0.trans hbase
  have ha1R:riemannianExp x q∈gapSection u v (sprayFlow t z).1 R:=hga1.trans hmove
  have hlev:-2*eta*D≤v ym-α:=by
    have H:=(le_div_iff₀ hD).mp (section_absolute_level_bounds hv hd hR hD ha0R ha1R hmR ha ha1
      (hosc (sprayFlow t z).1)).1
    have hdeta:=mul_nonneg heta hD.le
    nlinarith only [H,hdeta]
  have hstart:rayBenchmarkGap z ym α (v ym) b (Bo ((v ym-α)/D)) D r (C*‖p‖^2) 0≤-b/2:=by
    have HG:=dualPair_gap_nonneg hv hd x ym
    have HL:=mul_le_mul_of_nonneg_left (hol _ hym.le) hb.le
    change contactGap u v x (riemannianExp x p)≤r at hg0
    rw [contactGap,cost_minimizingVector hp,ha] at hg0
    dsimp only [rayBenchmarkGap,z]
    rw [sprayFlow_zero]
    norm_num only [mul_zero,zero_pow (by decide : (2:ℕ)≠0),add_zero,sub_zero]
    dsimp only [contactGap] at HG
    linarith only [HG,HL,hg0,hrb]
  have hfinish:0≤rayBenchmarkGap z ym α (v ym) b (Bo ((v ym-α)/D)) D r (C*‖p‖^2) t:=by
    have HG:=cTransform_gap_nonneg (continuous_modifiedDatum hv α D b ho)
      (sprayFlow t z).1 (riemannianExp x q)
    have h1:(v (riemannianExp x q)-α)/D=1:=by rw [ha1,add_sub_cancel_left,div_self hD.ne']
    dsimp only [contactGap,modifiedDatum] at hcm HG
    rw [h1,ho1,mul_zero,add_zero] at HG
    dsimp only [rayBenchmarkGap]
    linarith only [HG,hcm,hbench']
  have hlowert:4*eta*D+2*r+12*D*t+2*(C*‖p‖^2)*t^2+b≤D:=by
    have HD:=mul_le_mul_of_nonneg_left ht.2 (show 0≤12*D by positivity)
    linarith only [hlower,htimeC,HD]
  have hlower't:2*(C*‖p‖^2)*t≤2*D:= (mul_le_mul_of_nonneg_left ht.2 (by positivity)).trans hlower'
  have htime:=benchmark_lower_switch_time hb.le hD ht0 ht1 hbCH (hob _).1 hlev hlowert
    hlower't hstart hfinish
  obtain ⟨pm,hpm,hem⟩:=exists_minimizing_vector (n:=n) (sprayFlow t z).1 ym
  obtain ⟨pp,hpp,hep⟩:=exists_minimizing_vector (n:=n) (sprayFlow t z).1 yp
  have hmA:pm∈activeLogs (modifiedDatum v α D b Bo) (sprayFlow t z).1:=⟨hpm,by rwa [hem]⟩
  have hpA:pp∈activeLogs (modifiedDatum v α D b Bo) (sprayFlow t z).1:=⟨hpp,by rwa [hep]⟩
  have hnormt:2*t*‖p‖^2+2*b*H+2*r≤D/4:=by
    have H:=mul_le_mul_of_nonneg_right ht.2 (show 0≤2*‖p‖^2 by positivity)
    nlinarith only [H,hnorm]
  obtain ⟨hN1,hN2⟩:=active_switch_norm_brackets (z := z) hmA hpA hD hb.le hbD ht0 ht1 hob ho02
    (by rw [hem]; exact hym.le) (by rw [hep]; linarith only [hyp,heta1]) (hanch t ⟨ht0,le_rfl⟩) hnormt
  obtain ⟨w,hw,hwN⟩:=exists_convex_norm_sq hpA hmA hN1 hN2
  obtain ⟨hwmin,hwcontact⟩:=hmtw.active_hull_double_contact (continuous_modifiedDatum hv α D b ho) hw
  refine ⟨riemannianExp (sprayFlow t z).1 w,?_⟩
  apply positive_modified_excess_at_midnorm (z := z) hv hp ho ha hb.le hD hbD ht0 ht1 ?_ hg0'
    hc0 hc1 ho0 hTp ?_ w hwmin hwN hwcontact (hTaylor (sprayFlow t z).1)
  · calc b/(32*D) ≤ b/(20*D) := div_le_div_of_nonneg_left hb.le (by positivity) (by linarith only [hD])
         _ ≤ t := htime
  · have HH:=mul_le_mul_of_nonneg_left htt (show 0≤(C+1)*‖p‖^2 by positivity)
    nlinarith only [herror,HH]

end SwitchToExcess
end WeakMTWTransport

end
end

end OAI
