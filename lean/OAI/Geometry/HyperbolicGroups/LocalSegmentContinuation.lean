import Mathlib
import OAI.Geometry.HyperbolicGroups.StationaryInterpolation
import OAI.Geometry.HyperbolicGroups.LocalSegmentTools

namespace OAI

section


noncomputable section
open Set Metric
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X] [CompactSpace X]

omit [CompactSpace X] in
lemma UniformLocalCATZero.mono {r s : ℝ} (h : UniformLocalCATZero (X:=X) r) (hs : s≤r) :
    UniformLocalCATZero (X:=X) s := fun x => by
  obtain ⟨U,hU,hcat⟩ := h x
  exact ⟨U,(ball_subset_ball hs).trans hU,hcat⟩

/-- Uniform endpoint continuation of every actual local metric geodesic. -/
theorem IsLocalSegment.continuation {α : ℝ → X} {A r : ℝ}
    (hα : IsLocalSegment α A) (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r)
    (g : IsGeodesic X) {a b : X} (ha : dist a (α 0)≤r/2000)
    (hb : dist b (α 1)≤r/2000) :
    ∃ β : ℝ → X, ∃ B : ℝ, IsLocalSegment β B ∧ β 0=a ∧ β 1=b ∧
      ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t)≤
        (1-t)*dist (α 0) a+t*dist (α 1) b := by
  obtain ⟨ε,hε,hd⟩ := hα.local_dist
  obtain ⟨n,hn⟩ := exists_nat_gt (max (2/ε) (10000*(A+1)/r))
  let N := n+1
  have hN : 0<N := by dsimp [N]; omega
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hlarge : 2/ε<(N:ℝ) := by dsimp [N]; push_cast; linarith [(le_max_left (2/ε) (10000*(A+1)/r)).trans_lt hn]
  have he : 2/(N:ℝ)<ε := (div_lt_iff₀ hNr).mpr (by have := (div_lt_iff₀ hε).mp hlarge; nlinarith)
  have hA : A/(N:ℝ)<r/10000 := by
    have hh : 10000*(A+1)/r<(N:ℝ) := by dsimp [N]; push_cast; linarith [(le_max_right (2/ε) (10000*(A+1)/r)).trans_lt hn]
    have hh' := (div_lt_iff₀ hr).mp hh
    apply (div_lt_iff₀ hNr).mpr
    nlinarith
  let τ : ℕ → ℝ := fun i => (i:ℝ)/N
  have hτ (i : ℕ) (hi : i≤N) : τ i ∈ Icc (0:ℝ) 1 :=
    ⟨by dsimp [τ]; positivity,(div_le_one hNr).mpr (by exact_mod_cast hi)⟩
  have hτ0 : τ 0=0 := by simp [τ]
  have hτN : τ N=1 := by simp [τ,ne_of_gt hNr]
  have hτdiff (i j : ℕ) : |τ i-τ j|=|(i:ℝ)-(j:ℝ)|/N := by
    dsimp [τ]; rw [←sub_div,abs_div,abs_of_pos hNr]
  let q : Fin (n+2) → X := fun i => α (τ i)
  have hqd (i j : ℕ) (hi : i≤N) (hj : j≤N) (hij : |(i:ℝ)-(j:ℝ)|≤2) :
      dist (α (τ i)) (α (τ j))=(|(i:ℝ)-(j:ℝ)|/N)*A := by
    rw [hd _ (hτ i hi) _ (hτ j hj) (by rw [hτdiff]; exact (div_le_div_of_nonneg_right hij hNr.le).trans_lt he),hτdiff]
  have hstep (i : ℕ) (hi : i<N) : dist (α (τ i)) (α (τ (i+1)))=A/N := by
    rw [hqd i (i+1) (by omega) (by omega) (by push_cast; rw [show (i:ℝ)-((i:ℝ)+1)= -1 by ring]; norm_num)]
    push_cast
    rw [show (i:ℝ)-((i:ℝ)+1)= -1 by ring]
    norm_num; ring
  have hdouble (i : ℕ) (hi : i+2≤N) : dist (α (τ i)) (α (τ (i+2)))=2*A/N := by
    rw [hqd i (i+2) (by omega) hi (by push_cast; rw [show (i:ℝ)-((i:ℝ)+2)= -2 by ring]; norm_num)]
    push_cast
    rw [show (i:ℝ)-((i:ℝ)+2)= -2 by ring]
    norm_num; ring
  let ρ := r/100
  have hρ : 0<ρ := by dsimp [ρ]; positivity
  have hcρ : UniformLocalCATZero (X:=X) ρ := hc.mono (by dsimp [ρ]; linarith)
  have hnear : ∀ i : Fin n,
      dist (q (FiniteMidpointFixedPoint.left i)) (q (FiniteMidpointFixedPoint.center i))<ρ/10 ∧
      dist (q (FiniteMidpointFixedPoint.right i)) (q (FiniteMidpointFixedPoint.center i))<ρ/10 := by
    intro i
    change dist (α (τ i)) (α (τ (i.val+1)))<ρ/10 ∧ dist (α (τ (i.val+2))) (α (τ (i.val+1)))<ρ/10
    rw [hstep i (by dsimp [N]; omega),dist_comm (α (τ (i.val+2))),show i.val+2=(i.val+1)+1 by omega,
      hstep (i.val+1) (by dsimp [N]; have := i.isLt; omega)]
    dsimp [ρ]; constructor <;> linarith
  have hmid : ∀ i : Fin n, q (FiniteMidpointFixedPoint.center i)=
      g.midpoint (q (FiniteMidpointFixedPoint.left i)) (q (FiniteMidpointFixedPoint.right i)) := by
    intro i
    change α (τ (i.val+1))=g.midpoint (α (τ i)) (α (τ (i.val+2)))
    have hi : i.val+2≤N := by dsimp [N]; have := i.isLt; omega
    have h0 := hstep i (by omega)
    have h1 := hstep (i.val+1) (by omega)
    have h2 := hdouble i hi
    apply hcρ.eq_midpoint_of_dist g (o:=α (τ (i.val+1)))
    · rw [mem_ball,h0]; dsimp [ρ]; linarith
    · rw [mem_ball,dist_comm]; change dist (α (τ (i.val+1))) (α (τ ((i.val+1)+1)))<ρ/3
      rw [h1]; dsimp [ρ]; linarith
    · exact mem_ball_self (by positivity)
    · rw [h0,h2]; ring
    · change dist (α (τ (i.val+1))) (α (τ ((i.val+1)+1)))=_
      rw [h1,h2]; ring
  obtain ⟨p,hp,hpm⟩ := LocalPolygonContinuation.exists_stationary hρ hcρ g q hnear hmid
    (a:=a) (b:=b) (by change dist a (α (τ 0))≤ρ/20; rw [hτ0]; dsimp [ρ]; linarith)
    (by change dist b (α (τ N))≤ρ/20; rw [hτN]; dsimp [ρ]; linarith)
  let P : ℕ → X := fun i => p ⟨min i N,by dsimp [N]; omega⟩
  have hP (i : ℕ) (hi : i≤N) : P i=p ⟨i,by dsimp [N] at hi; omega⟩ := by
    dsimp [P]; congr; exact min_eq_left hi
  have hcloseP (i : ℕ) (hi : i≤N) : dist (P i) (α (τ i))≤r/2000 := by
    rw [hP i hi]
    have hh := hp.2.2 (⟨i,by dsimp [N] at hi; omega⟩ : Fin (n+2))
    change dist (p ⟨i,_⟩) (α (τ i))≤ρ/20 at hh
    dsimp [ρ] at hh; linarith
  have hshort (i : ℕ) (hi : i<N) : dist (P i) (P (i+1))<r/500 := by
    have hh := dist_triangle4 (P i) (α (τ i)) (α (τ (i+1))) (P (i+1))
    rw [hstep i hi,dist_comm (α (τ (i+1)))] at hh
    linarith [hcloseP i (by omega),hcloseP (i+1) (by omega)]
  have hpm' (i : ℕ) (hi : i+2≤N) : P (i+1)=g.midpoint (P i) (P (i+2)) := by
    rw [hP (i+1) (by omega),hP i (by omega),hP (i+2) hi]
    exact hpm ⟨i,by dsimp [N] at hi; omega⟩
  let β := SegmentChain.unitCurve hN P (StationaryInterpolation.edge g P)
  have hβ : IsLocalSegment β ((N:ℝ)*dist (P 0) (P 1)) :=
    StationaryInterpolation.isLocalSegment g hc hN P (fun i hi => (hshort i hi).trans (by linarith)) hpm'
  have hβ0 : β 0=a := by
    dsimp only [β]
    rw [SegmentChain.unitCurve_zero hN P _ (fun i _ => StationaryInterpolation.edge_spec g P i),hP 0 (by omega)]
    exact hp.1
  have hβ1 : β 1=b := by
    dsimp only [β]
    rw [SegmentChain.unitCurve_one hN P _ (fun i _ => StationaryInterpolation.edge_spec g P i),hP N le_rfl]
    exact hp.2.1
  have hclose : ∀ t ∈ Icc (0:ℝ) 1, dist (α t) (β t)<r/10 := by
    intro t ht
    have hNt : (N:ℝ)*t ∈ Icc (0:ℝ) N := ⟨mul_nonneg hNr.le ht.1,by nlinarith [ht.2]⟩
    obtain ⟨i,hi⟩ := SegmentChain.interval_cover hN hNt
    have hai : |t-τ i|≤1/(N:ℝ) := by
      apply (le_div_iff₀ hNr).mpr
      calc
        |t-τ i| *(N:ℝ)=|(t-τ i)*(N:ℝ)| := by rw [abs_mul,abs_of_pos hNr]
        _=|(N:ℝ)*t-(i:ℝ)| := by congr 1; dsimp [τ]; field_simp
        _≤1 := abs_le.mpr ⟨by linarith [hi.1],by linarith [hi.2]⟩
    have had : dist (α t) (α (τ i))≤A/N := by
      have hh := hα.dist_le ht (hτ i (Nat.le_of_lt i.isLt))
      apply hh.trans
      convert mul_le_mul_of_nonneg_right hai hα.nonneg using 1; ring
    have hbp : dist (P i) (β t)≤dist (P i) (P (i.val+1)) := by
      change dist (P i) (SegmentChain.curve hN P (StationaryInterpolation.edge g P) ((N:ℝ)*t))≤_
      rw [SegmentChain.curve_eq hN P _ (fun i _ => StationaryInterpolation.edge_spec g P i) i hi,
        (StationaryInterpolation.edge_spec g P i).dist_from_source ⟨by linarith [hi.1],by linarith [hi.2]⟩]
      nlinarith [dist_nonneg (x:=P i) (y:=P (i.val+1)),hi.1,hi.2]
    have hh := dist_triangle4 (α t) (α (τ i)) (P i) (β t)
    rw [dist_comm (α (τ i)) (P i)] at hh
    linarith [hcloseP i (Nat.le_of_lt i.isLt),hshort i i.isLt]
  refine ⟨β,_,hβ,hβ0,hβ1,?_⟩
  intro t ht
  simpa only [hβ0,hβ1] using hα.close_chord hβ hr hc g hclose t ht

end HyperbolicObstruction
end
end

section

end

end OAI
