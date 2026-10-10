import Mathlib
import OAI.Geometry.HyperbolicGroups.LocalGeodesicCover

namespace OAI

section


noncomputable section
open Set Metric
open scoped unitInterval Topology
namespace HyperbolicObstruction
variable {X : Type*} [MetricSpace X]

lemma local_dist_le_global {γ : ℝ → X} {L ε : ℝ} (hε : 0<ε)
    (hlocal : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, |s-t|<ε → dist (γ s) (γ t)≤|s-t| *L)
    {s t : ℝ} (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    dist (γ s) (γ t) ≤ |s-t| *L := by
  obtain ⟨N,hN⟩ := exists_nat_gt (2/ε)
  have hn : 0<N := by
    by_contra hh
    have hz : N=0 := by omega
    rw [hz,Nat.cast_zero] at hN
    exact (not_lt_of_ge (by positivity : 0≤2/ε)) hN
  have hn' : (0:ℝ)<N := Nat.cast_pos.mpr hn
  have he : 2/(N:ℝ)<ε := by
    have := (div_lt_iff₀ hε).mp hN
    exact (div_lt_iff₀ hn').mpr (by nlinarith)
  let q : ℕ → ℝ := fun i => (1-(i:ℝ)/N)*s+((i:ℝ)/N)*t
  have hq (i : ℕ) (hi : i≤N) : q i ∈ Icc (0:ℝ) 1 := by
    have hi0 : 0≤(i:ℝ)/N := by positivity
    have hi1 : (i:ℝ)/N≤1 := (div_le_one hn').mpr (by exact_mod_cast hi)
    dsimp [q]
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr hi1) hs.1) (mul_nonneg hi0 ht.1)
    · nlinarith [mul_nonneg (sub_nonneg.mpr hi1) (sub_nonneg.mpr hs.2),
        mul_nonneg hi0 (sub_nonneg.mpr ht.2)]
  have hd (i : ℕ) : |q i-q (i+1)|=|s-t|/(N:ℝ) := by
    dsimp [q]
    push_cast
    rw [show (1-(i:ℝ)/N)*s+((i:ℝ)/N)*t-
      ((1-((i:ℝ)+1)/N)*s+(((i:ℝ)+1)/N)*t)=(s-t)/N by ring,abs_div,abs_of_pos hn']
  have hst : |s-t|≤1 := abs_le.mpr ⟨by linarith [hs.1,ht.2],by linarith [hs.2,ht.1]⟩
  have hb : |s-t|/(N:ℝ)<ε := (div_le_div_of_nonneg_right hst hn'.le).trans_lt ((div_le_div_of_nonneg_right (by norm_num : (1:ℝ)≤2) hn'.le).trans_lt he)
  have hh := dist_le_range_sum_of_dist_le (f:=fun i => γ (q i)) (n:=N)
    (d:=fun _ => |s-t|/(N:ℝ)*L) (fun {i} hi =>
      by simpa only [hd] using hlocal _ (hq i (by omega)) _ (hq (i+1) (by omega)) (by rw [hd]; exact hb))
  have hq0 : q 0=s := by simp [q]
  have hqN : q N=t := by simp [q,ne_of_gt hn']
  rw [hq0,hqN,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hh
  have heq : (N:ℝ)*(|s-t|/(N:ℝ)*L)=|s-t| *L := by field_simp
  simpa only [heq] using hh

namespace LocalGeodesic
variable {o : X} {r : ℝ} (hr : 0<r) (hc : UniformLocalCATZero (X:=X) r) (g : IsGeodesic X)

include hr hc g

lemma close_length {a b : LocalGeodesic o} (hab : dist a b<r/10) :
    |a.length-b.length|≤dist (endpoint a) (endpoint b) := by
  suffices hh : |a.length-b.length|≤dist (extend a.val 1) (extend b.val 1) by
    simpa only [extend_one,endpoint] using hh
  apply a.localSegment.close_length b.localSegment hr hc g
  · intro t ht
    rw [extend_mem _ ht,extend_mem _ ht]
    exact (ContinuousMap.dist_apply_le_dist (⟨t,ht⟩:I)).trans_lt hab
  · simp only [extend_zero,a.start,b.start]

lemma length_continuous : Continuous (@length X _ o) := by
  rw [Metric.continuous_iff]
  intro a ε hε
  refine ⟨min (r/10) ε,lt_min (by positivity) hε,fun b hb => ?_⟩
  rw [Real.dist_eq]
  exact ((close_length hr hc g (lt_min_iff.mp hb).1).trans
    (by simpa using endpoint_lipschitz.dist_le_mul b a)).trans_lt (lt_min_iff.mp hb).2

lemma length_variation {α : ℝ → X} {A : ℝ} (hα : IsLocalSegment α A)
    (ρ : C(I,LocalGeodesic o)) (hp : ∀ t : I, endpoint (ρ t)=α t) (s t : I) :
    |(ρ s).length-(ρ t).length|≤|(s:ℝ)-t| *A := by
  obtain ⟨ε,hε,he⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous ρ.continuous) (r/10) (by positivity)
  have hh := @local_dist_le_global ℝ _ (fun u => (ρ (projIcc 0 1 zero_le_one u)).length) A ε hε
    (by intro u hu v hv huv
        rw [projIcc_of_mem zero_le_one hu,projIcc_of_mem zero_le_one hv,Real.dist_eq]
        apply (close_length hr hc g (he (by simpa [Subtype.dist_eq,Real.dist_eq] using huv))).trans
        rw [hp,hp]
        exact hα.dist_le hu hv) (s:=s) (t:=t) s.property t.property
  simpa only [projIcc_of_mem zero_le_one s.property,projIcc_of_mem zero_le_one t.property,Real.dist_eq] using hh

end LocalGeodesic
end HyperbolicObstruction
end
end

section

end

end OAI
