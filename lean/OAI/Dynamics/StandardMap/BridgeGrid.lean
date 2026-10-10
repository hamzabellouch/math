import OAI.Dynamics.StandardMap.BridgeDecay

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy

structure BridgeGrid (Rw Rh : ℕ) where
  p : ℕ
  u : DyadicTime
  v : DyadicTime
  b : ℤ
  N : ℕ
  r : ℕ
  large : 100≤ N
  narrow : (r:ℝ)≤ (N:ℝ)/1000
  hu : ((2^p:ℕ):ℝ)*(u:ℝ)=(b:ℝ)
  hv : ((2^p:ℕ):ℝ)*(v:ℝ)=(b:ℝ)+(N:ℝ)
  sw : Fin Rw → DyadicTime
  tw : Fin Rw → DyadicTime
  sh : Fin Rh → DyadicTime
  th : Fin Rh → DyadicTime
  aw : Fin Rw → ℤ
  nw : Fin Rw → ℕ
  ah : Fin Rh → ℤ
  nh : Fin Rh → ℕ
  pw : ∀j,0< nw j
  ph : ∀j,0< nh j
  hwleft : ∀j,-(r:ℤ)≤ aw j
  hwright : ∀j,aw j+(nw j:ℤ)≤ r
  hhleft : ∀j,-(r:ℤ)≤ ah j-(N:ℤ)
  hhright : ∀j,ah j+(nh j:ℤ)-(N:ℤ)≤ r
  hsw : ∀j,((2^p:ℕ):ℝ)*(sw j:ℝ)=((aw j+b):ℤ)
  htw : ∀j,((2^p:ℕ):ℝ)*(tw j:ℝ)=((aw j+b):ℤ)+(nw j:ℝ)
  hsh : ∀j,((2^p:ℕ):ℝ)*(sh j:ℝ)=((ah j+b):ℤ)
  hth : ∀j,((2^p:ℕ):ℝ)*(th j:ℝ)=((ah j+b):ℤ)+(nh j:ℝ)
lemma aligned_scale (p l : ℕ) (s : DyadicTime) (a : ℤ)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)) :
    ((2^(p+l):ℕ):ℝ)*(s:ℝ)=((a*2^l:ℤ):ℝ) := by
  push_cast at hs ⊢
  rw [pow_add]
  nlinarith [congrArg (fun x : ℝ => x*(2:ℝ)^l) hs]
lemma aligned_scale_end (p l : ℕ) (s : DyadicTime) (a : ℤ) (m : ℕ)
    (hs : ((2^p:ℕ):ℝ)*(s:ℝ)=(a:ℝ)+(m:ℝ)) :
    ((2^(p+l):ℕ):ℝ)*(s:ℝ)=((a*2^l:ℤ):ℝ)+((m*2^l:ℕ):ℝ) := by
  have hh := aligned_scale p l s (a+(m:ℤ)) (by simpa only [Int.cast_add,Int.cast_natCast] using hs)
  push_cast at hh ⊢
  nlinarith
lemma observation_nonneg_aligned {R : ℕ} (k : ℝ) (hk : 0≤ k) (n : ℕ) (hn : 0< n)
    (s t : Fin R → DyadicTime) (a : Fin R → ℤ) (m : Fin R → ℕ) (hm : ∀i,0< m i)
    (hs : ∀i,(n:ℝ)*(s i:ℝ)=(a i:ℝ)) (ht : ∀i,(n:ℝ)*(t i:ℝ)=(a i:ℝ)+(m i:ℝ))
    (F : (Fin R → ℝ) → ℝ) (hF0 : ∀d,0≤ arrayObservation s t F d) :
    ∀z,0≤ shortfallObservation k a m F z := by
  intro z
  rw [←arrayObservation_sample k hk n hn s t a m hm hs ht F]
  exact hF0 _
lemma length_from_window (a : ℤ) (m r : ℕ) (h1 : -(r:ℤ)≤ a) (h2 : a+(m:ℤ)≤ r) : m≤ 2*r := by omega
lemma BridgeGrid.sample_bound {Rw Rh : ℕ} (B : BridgeGrid Rw Rh)
    (k : ℝ) (hc : BridgeScalarControl k) (l : ℕ)
    (Fw : (Fin Rw → ℝ) → ℝ) (Fh : (Fin Rh → ℝ) → ℝ) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hW0 : ∀d,0≤ arrayObservation B.sw B.tw Fw d) (hH0 : ∀d,0≤ arrayObservation B.sh B.th Fh d)
    (hlog : 1≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L≤ growthBase k)
    (η : ℝ) (hη : 0<η) (hδ : growthBase k^(-(1/10:ℝ)*((B.N*2^l:ℕ):ℝ))<η/2)
    (F : DistanceArray → ℝ) (hF : Continuous F) (D : ℝ) (hD : 0≤ D)
    (hFW : ∀d,F d≤ D*arrayObservation B.sw B.tw Fw d)
    (hzero : ∀d,¬((999/1000:ℝ)*((B.v:ℝ)-(B.u:ℝ))< d.val B.u B.v ∧ η< arrayObservation B.sh B.th Fh d) → F d=0) :
    (∫ d,F d ∂sampleLaw k hc.nonneg (2^(B.p+l)) (by positivity))≤ D*bridgeRealConstant*
      ((∫ d,arrayObservation B.sw B.tw Fw d ∂sampleLaw k hc.nonneg (2^(B.p+l)) (by positivity))+
        growthBase k^(-(1/10:ℝ)*((B.N*2^l:ℕ):ℝ)))*
      ((∫ d,arrayObservation B.sh B.th Fh d ∂sampleLaw k hc.nonneg (2^(B.p+l)) (by positivity))/(η/2)) := by
  have hp : (0:ℤ)≤ 2^l := by positivity
  have h1 : 1≤ 2^l := Nat.one_le_pow l 2 (by omega)
  have hwL (j) : -((B.r*2^l:ℕ):ℤ)≤ B.aw j*2^l := by
    have hh := mul_le_mul_of_nonneg_right (B.hwleft j) hp
    push_cast; nlinarith
  have hwR (j) : B.aw j*2^l+((B.nw j*2^l:ℕ):ℤ)≤ ((B.r*2^l:ℕ):ℤ) := by
    have hh := mul_le_mul_of_nonneg_right (B.hwright j) hp
    push_cast; nlinarith
  have hhL (j) : -((B.r*2^l:ℕ):ℤ)≤ B.ah j*2^l-((B.N*2^l:ℕ):ℤ) := by
    have hh := mul_le_mul_of_nonneg_right (B.hhleft j) hp
    push_cast; nlinarith
  have hhR (j) : B.ah j*2^l+((B.nh j*2^l:ℕ):ℤ)-((B.N*2^l:ℕ):ℤ)≤ ((B.r*2^l:ℕ):ℤ) := by
    have hh := mul_le_mul_of_nonneg_right (B.hhright j) hp
    push_cast; nlinarith
  have hsw (j) : ((2^(B.p+l):ℕ):ℝ)*(B.sw j:ℝ)=(((B.aw j*2^l+B.b*2^l):ℤ):ℝ) := by
    simpa only [add_mul] using aligned_scale B.p l (B.sw j) (B.aw j+B.b) (B.hsw j)
  have htw (j) : ((2^(B.p+l):ℕ):ℝ)*(B.tw j:ℝ)=(((B.aw j*2^l+B.b*2^l):ℤ):ℝ)+((B.nw j*2^l:ℕ):ℝ) := by
    simpa only [add_mul] using aligned_scale_end B.p l (B.tw j) (B.aw j+B.b) (B.nw j) (B.htw j)
  have hsh (j) : ((2^(B.p+l):ℕ):ℝ)*(B.sh j:ℝ)=(((B.ah j*2^l+B.b*2^l):ℤ):ℝ) := by
    simpa only [add_mul] using aligned_scale B.p l (B.sh j) (B.ah j+B.b) (B.hsh j)
  have hth (j) : ((2^(B.p+l):ℕ):ℝ)*(B.th j:ℝ)=(((B.ah j*2^l+B.b*2^l):ℤ):ℝ)+((B.nh j*2^l:ℕ):ℝ) := by
    simpa only [add_mul] using aligned_scale_end B.p l (B.th j) (B.ah j+B.b) (B.nh j) (B.hth j)
  have hnonnegW : ∀z,0≤ shortfallObservation k (fun j => B.aw j*2^l) (fun j => B.nw j*2^l) Fw z := by
    intro z
    have hh := observation_nonneg_aligned k hc.nonneg (2^(B.p+l)) (by positivity) B.sw B.tw
      (fun j => B.aw j*2^l+B.b*2^l) (fun j => B.nw j*2^l) (fun j => Nat.mul_pos (B.pw j) (by positivity)) hsw htw Fw hW0
      (torusIter k (-(B.b*2^l)) z)
    rw [←shortfallObservation_shift,←torusIter_add,add_neg_cancel,torusIter_zero] at hh
    exact hh
  have hnonnegH : ∀z,0≤ shortfallObservation k (fun j => B.ah j*2^l) (fun j => B.nh j*2^l) Fh z := by
    intro z
    have hh := observation_nonneg_aligned k hc.nonneg (2^(B.p+l)) (by positivity) B.sh B.th
      (fun j => B.ah j*2^l+B.b*2^l) (fun j => B.nh j*2^l) (fun j => Nat.mul_pos (B.ph j) (by positivity)) hsh hth Fh hH0
      (torusIter k (-(B.b*2^l)) z)
    rw [←shortfallObservation_shift,←torusIter_add,add_neg_cancel,torusIter_zero] at hh
    exact hh
  apply sample_bridge_integral k hc (2^(B.p+l)) (B.N*2^l) (B.r*2^l) (by positivity)
    (le_trans B.large (Nat.le_mul_of_pos_right _ (by positivity)))
    (by push_cast; nlinarith [mul_le_mul_of_nonneg_right B.narrow (show (0:ℝ)≤ 2^l by positivity)])
    B.u B.v (B.b*2^l) (aligned_scale B.p l B.u B.b B.hu) (aligned_scale_end B.p l B.v B.b B.N B.hv)
    B.sw B.tw B.sh B.th (fun j => B.aw j*2^l) (fun j => B.nw j*2^l) Fw
    (fun j => B.ah j*2^l) (fun j => B.nh j*2^l) Fh
    (fun j => Nat.mul_pos (B.pw j) (by positivity)) (fun j => Nat.mul_pos (B.ph j) (by positivity))
    hsw htw hsh hth L hFw hFh
    (fun j => length_from_window _ _ _ (hwL j) (hwR j))
    (fun j => length_from_window (B.ah j*2^l-((B.N*2^l:ℕ):ℤ)) _ _ (hhL j) (by linarith [hhR j]))
    (fun j x hx hx' => by simpa only [sub_zero] using window_indices (a := B.aw j*2^l) (b := 0) (r := B.r*2^l) (by simpa only [sub_zero] using hwL j) (by simpa only [sub_zero] using hwR j) x hx hx')
    (fun j x hx hx' => window_indices (hhL j) (hhR j) x hx hx')
    hnonnegW hnonnegH hlog hLM η hη hδ F hF D hD hFW hzero
end StandardMapEntropy

end OAI
