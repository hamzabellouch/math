import Mathlib
import OAI.Geometry.HyperbolicGroups.IndexedFillingValue

namespace OAI

section


/-! A midpoint-stationary short polygon interpolates to an actual
constant-speed local geodesic, rather than merely to a combinatorial chain. -/
noncomputable section
open Set Metric
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

abbrev IsGeodesic.segment (g : IsGeodesic X) (a b : X) : ℝ → X := (g a b).choose
lemma IsGeodesic.segment_spec (g : IsGeodesic X) (a b : X) : IsSegment (g.segment a b) a b :=
  (g a b).choose_spec

lemma UniformLocalCATZero.segment_unique {r : ℝ} (hc : UniformLocalCATZero (X:=X) r)
    {a b : X} {α β : ℝ → X} (hα : IsSegment α a b) (hβ : IsSegment β a b)
    (hab : dist a b < r) : EqOn α β (Icc 0 1) := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg hab
  obtain ⟨U,hU,hcat⟩ := hc a
  have ha : a ∈ U := hU (mem_ball_self hr)
  have hb : b ∈ U := hU (by simpa [mem_ball,dist_comm] using hab)
  intro t ht
  have hmem {γ : ℝ → X} (hγ : IsSegment γ a b) : γ t ∈ U := by
    apply hU
    rw [mem_ball,dist_comm,hγ.dist_from_source ht]
    have hh : t*dist a b  ≤  dist a b := by nlinarith [ht.2,dist_nonneg (x:=a) (y:=b)]
    exact hh.trans_lt hab
  have he {γ : ℝ → X} (hγ : IsSegment γ a b) :
      (⟨γ t,hmem hγ⟩ : U)=CATZero.segment hcat ⟨a,ha⟩ ⟨b,hb⟩ t := by
    apply CATZero.eq_segment_of_dist hcat ht
    · exact hγ.dist_from_source ht
    · change dist (γ t) b=(1-t)*dist a b
      have hh := hγ.2.2 t ht 1 (by norm_num)
      rw [hγ.2.1,abs_of_nonpos (sub_nonpos.mpr ht.2)] at hh
      simpa only [neg_sub] using hh
  exact congrArg Subtype.val ((he hα).trans (he hβ).symm)

namespace StationaryInterpolation
variable (g : IsGeodesic X) {r : ℝ} (hc : UniformLocalCATZero (X:=X) r)
  {N : ℕ} (hN : 0 < N) (p : ℕ → X)
  (hshort : ∀ i, i < N → dist (p i) (p (i+1)) < r)
  (hmid : ∀ i, i+2 ≤ N → p (i+1)=g.midpoint (p i) (p (i+2)))

abbrev edge : ℕ → ℝ → X := fun i => g.segment (p i) (p (i+1))
lemma edge_spec (i : ℕ) : IsSegment (edge g p i) (p i) (p (i+1)) := g.segment_spec _ _

include hmid in
lemma edge_length_eq {i : ℕ} (hi : i < N) :
    dist (p i) (p (i+1))=dist (p 0) (p 1) := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have he := hmid i (by omega)
    have hl := g.dist_left_midpoint (p i) (p (i+2))
    have hr := g.dist_midpoint_right (p i) (p (i+2))
    rw [←he] at hl hr
    change dist (p (i+1)) (p (i+2))=_
    rw [hr,←hl,ih (by omega)]

include hc hshort hmid in
lemma double_eq {i : ℕ} (hi : i+2 ≤ N) {t : ℝ} (ht : t ∈ Icc (i:ℝ) ((i:ℝ)+2)) :
    SegmentChain.curve hN p (edge g p) t = g.segment (p i) (p (i+2)) ((t-i)/2) := by
  let δ := g.segment (p i) (p (i+2))
  have hd : IsSegment δ (p i) (p (i+2)) := g.segment_spec _ _
  have hm : δ (1/2)=p (i+1) := (hmid i hi).symm
  have hzero : δ 0=p i := hd.1
  have hone : δ 1=p (i+2) := hd.2.1
  have hleft : IsSegment (fun u => δ (u/2)) (p i) (p (i+1)) := by
    have hh := hd.reparam (by norm_num : (0:ℝ) ∈ Icc 0 1) (by norm_num : (1/2:ℝ) ∈ Icc 0 1)
    simpa only [mul_zero,zero_add,mul_one_div,hzero,hm] using hh
  have hright : IsSegment (fun u => δ ((1+u)/2)) (p (i+1)) (p (i+2)) := by
    have hh := hd.reparam (by norm_num : (1/2:ℝ) ∈ Icc 0 1) (by norm_num : (1:ℝ) ∈ Icc 0 1)
    rw [hm,hone] at hh
    convert hh using 1
    funext u
    congr 1
    ring
  by_cases hle : t ≤ (i:ℝ)+1
  · let j : Fin N := ⟨i,by omega⟩
    have htj : t ∈ Icc (j:ℝ) ((j:ℝ)+1) := ⟨ht.1,hle⟩
    rw [SegmentChain.curve_eq hN p (edge g p) (fun k _ => edge_spec g p k) j htj]
    exact hc.segment_unique (edge_spec g p i) hleft (hshort i (by omega))
      ⟨by linarith [ht.1],by linarith⟩
  · let j : Fin N := ⟨i+1,by omega⟩
    have htj : t ∈ Icc (j:ℝ) ((j:ℝ)+1) := by
      change (i+1:ℕ) ≤ t ∧ t ≤ (i+1:ℕ)+1
      push_cast
      constructor <;> linarith [ht.2]
    rw [SegmentChain.curve_eq hN p (edge g p) (fun k _ => edge_spec g p k) j htj]
    have hh := hc.segment_unique (edge_spec g p (i+1)) hright (hshort (i+1) (by omega))
      (show t-(i+1:ℕ) ∈ Icc (0:ℝ) 1 from by push_cast; constructor <;> linarith [ht.2])
    change g.segment (p (i+1)) (p (i+1+1)) (t-(i+1:ℕ))=_ at hh
    convert hh using 1
    dsimp [δ]
    congr 1
    push_cast
    ring

include hc hshort hmid in
lemma curve_local_dist {s t : ℝ} (hs : s ∈ Icc (0:ℝ) N) (ht : t ∈ Icc (0:ℝ) N)
    (hst : |s-t| < 1) :
    dist (SegmentChain.curve hN p (edge g p) s) (SegmentChain.curve hN p (edge g p) t)=
      |s-t| * dist (p 0) (p 1) := by
  obtain ⟨i,hi⟩ := SegmentChain.interval_cover hN hs
  obtain ⟨j,hj⟩ := SegmentChain.interval_cover hN ht
  have same (k : Fin N) (hs' : s ∈ Icc (k:ℝ) ((k:ℝ)+1)) (ht' : t ∈ Icc (k:ℝ) ((k:ℝ)+1)) :
      dist (SegmentChain.curve hN p (edge g p) s) (SegmentChain.curve hN p (edge g p) t)=
        |s-t| * dist (p 0) (p 1) := by
    rw [SegmentChain.curve_eq hN p (edge g p) (fun k _ => edge_spec g p k) k hs',
      SegmentChain.curve_eq hN p (edge g p) (fun k _ => edge_spec g p k) k ht']
    rw [(edge_spec g p k).2.2 _ ⟨by linarith [hs'.1],by linarith [hs'.2]⟩
      _ ⟨by linarith [ht'.1],by linarith [ht'.2]⟩]
    rw [show s-(k:ℝ)-(t-(k:ℝ))=s-t by ring,edge_length_eq g p hmid k.isLt]
  have both (k : ℕ) (hk : k+2 ≤ N) (hs' : s ∈ Icc (k:ℝ) ((k:ℝ)+2))
      (ht' : t ∈ Icc (k:ℝ) ((k:ℝ)+2)) :
      dist (SegmentChain.curve hN p (edge g p) s) (SegmentChain.curve hN p (edge g p) t)=
        |s-t| * dist (p 0) (p 1) := by
    rw [double_eq g hc hN p hshort hmid hk hs',double_eq g hc hN p hshort hmid hk ht']
    rw [(g.segment_spec (p k) (p (k+2))).2.2 _ ⟨by linarith [hs'.1],by linarith [hs'.2]⟩
      _ ⟨by linarith [ht'.1],by linarith [ht'.2]⟩]
    have hd : dist (p k) (p (k+2))=2*dist (p 0) (p 1) := by
      have hh := g.dist_left_midpoint (p k) (p (k+2))
      rw [←hmid k hk,edge_length_eq g p hmid (by omega : k < N)] at hh
      linarith
    rw [hd,show (s-(k:ℝ))/2-(t-(k:ℝ))/2=(s-t)/2 by ring,abs_div]
    norm_num
    ring
  rcases lt_trichotomy i.val j.val with hlt|he|hgt
  · have hji : j.val=i.val+1 := by
      have hjr : (j:ℝ) < (i:ℝ)+2 := by have := (abs_lt.mp hst).1; linarith [hi.2,hj.1]
      have hjn : j.val < i.val+2 := by exact_mod_cast hjr
      omega
    apply both i (by have := j.isLt; omega) ⟨hi.1,by linarith [hi.2]⟩
    have hj1 := hj.1; have hj2 := hj.2
    change (j.val:ℝ) ≤ t at hj1
    change t ≤ (j.val:ℝ)+1 at hj2
    rw [hji] at hj1 hj2
    push_cast at hj1 hj2
    constructor <;> linarith
  · have hij : i=j := Fin.ext he
    subst j
    exact same i hi hj
  · have hij : i.val=j.val+1 := by
      have hir : (i:ℝ) < (j:ℝ)+2 := by have := (abs_lt.mp hst).2; linarith [hi.1,hj.2]
      have hin : i.val < j.val+2 := by exact_mod_cast hir
      omega
    apply both j (by have := i.isLt; omega) _ ⟨hj.1,by linarith [hj.2]⟩
    have hi1 := hi.1; have hi2 := hi.2
    change (i.val:ℝ) ≤ s at hi1
    change s ≤ (i.val:ℝ)+1 at hi2
    rw [hij] at hi1 hi2
    push_cast at hi1 hi2
    constructor <;> linarith

include hc hshort hmid in
lemma isLocalSegment :
    IsLocalSegment (SegmentChain.unitCurve hN p (edge g p)) ((N:ℝ)*dist (p 0) (p 1)) := by
  refine ⟨mul_nonneg (Nat.cast_nonneg _) dist_nonneg,
    SegmentChain.unitCurve_continuousOn hN p (edge g p) (fun k _ => edge_spec g p k),
    1/(N:ℝ),by positivity,?_⟩
  intro s hs t ht hst
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have hin (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : (N:ℝ)*u ∈ Icc (0:ℝ) N :=
    ⟨mul_nonneg hn.le hu.1,by nlinarith [hu.2]⟩
  have hh : |(N:ℝ)*s-(N:ℝ)*t| < 1 := by
    rw [←mul_sub,abs_mul,abs_of_pos hn]
    have hh := (lt_div_iff₀ hn).mp hst
    nlinarith
  unfold SegmentChain.unitCurve
  rw [curve_local_dist g hc hN p hshort hmid (hin s hs) (hin t ht) hh,
    ←mul_sub,abs_mul,abs_of_pos hn]
  ring

end StationaryInterpolation
end HyperbolicObstruction
end
end

section

end

end OAI
