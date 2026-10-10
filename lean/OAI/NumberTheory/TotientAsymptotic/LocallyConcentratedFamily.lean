import OAI.NumberTheory.TotientAsymptotic.ConcentratedPrefix
import OAI.NumberTheory.TotientAsymptotic.NaturalCoordinateUpper

namespace OAI

/-! Positive-volume candidate families with upper bounds at every local tail scale. -/
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace TotientAsymptotic

attribute [local instance] Classical.propDecidable

def localCoordinateCap (n : ℕ) (B : ℝ) (i : Fin n) : ℝ :=
  2*B*rho^(i.val+1)*(n-i.val:ℕ)/(n:ℝ)

def locallyConcentratedFamily (m n : ℕ) (B c : ℝ) (L : ℕ) : Set (Fin n → ℝ) :=
  headLimitedFamily m n B c ∩
    {u | ∀ i,i.val+L+2 ≤ n → u i ≤ localCoordinateCap n B i}

lemma measurableSet_locallyConcentratedFamily (m n : ℕ) (B c : ℝ) (L : ℕ) :
    MeasurableSet (locallyConcentratedFamily m n B c L) := by
  apply (measurableSet_headLimitedFamily _ _ _ _).inter
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter (fun i => ?_)
  by_cases hi : i.val+L+2 ≤ n
  · simpa [hi] using
      (measurableSet_le (show Measurable (fun u : Fin n → ℝ => u i) from measurable_pi_apply i) measurable_const)
  · simp [hi]

lemma coordinate_cap_of_not_bad {N : ℕ} {B : ℝ} (hB : 0 < B)
    {i : Fin (N+2)} (hi : i.val < N) {u : Fin (N+2) → ℝ}
    (hu : u ∉ fordCoordinateBad N B i) :
    u i ≤ localCoordinateCap (N+2) B i := by
  have hn : (0:ℝ)<N+2 := by positivity
  have hidx : (i.val:ℝ)+1 < N+2 := by exact_mod_cast (show i.val+1 < N+2 by omega)
  have hd : 0 < 1-(i.val+1:ℝ)/(N+2) := by
    exact sub_pos.mpr ((div_lt_one hn).mpr hidx)
  have hcenter : 0 < fordSimplexCenter N B i :=
    mul_pos (mul_pos hB (pow_pos rho_pos _)) hd
  have hh : |u i/fordSimplexCenter N B i-1| ≤ 1/40 := le_of_not_gt hu
  have hupper := (abs_le.mp hh).2
  have hule : u i ≤ (41/40:ℝ)*fordSimplexCenter N B i := by
    apply (div_le_iff₀ hcenter).mp
    linarith only [hupper]
  have hcap : (41/40:ℝ)*fordSimplexCenter N B i ≤
      localCoordinateCap (N+2) B i := by
    have he : fordSimplexCenter N B i =
        B*rho^(i.val+1)*((N+2-i.val:ℕ)-1)/(N+2:ℝ) := by
      unfold fordSimplexCenter
      rw [Nat.cast_sub (by omega : i.val ≤ N+2)]
      simp only [Nat.cast_add,Nat.cast_ofNat]
      field_simp
      ring
    rw [he,localCoordinateCap]
    have hb : 0 ≤ B*rho^(i.val+1)/(N+2:ℝ) :=
      div_nonneg (mul_nonneg hB.le (pow_pos rho_pos _).le) hn.le
    have hni : (0:ℝ) ≤ (N+2-i.val:ℕ) := Nat.cast_nonneg _
    calc
      _ = (B*rho^(i.val+1)/(N+2:ℝ))*((41/40:ℝ)*((N+2-i.val:ℕ)-1)) := by ring
      _ ≤ (B*rho^(i.val+1)/(N+2:ℝ))*(2*(N+2-i.val:ℕ)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hni]) hb
      _ = _ := by push_cast; ring
  exact hule.trans hcap

lemma local_family_failure_subset {m N L : ℕ} {B c : ℝ}
    (hB : 0 < B) (hL : 1 ≤ L) :
    headLimitedFamily m (N+2) B c ⊆
      locallyConcentratedFamily m (N+2) B c L ∪ prefixConcentrationFailure N L B := by
  intro u hu
  by_cases hc : ∀ i : Fin (N+2),i.val+L+2 ≤ N+2 →
      u i ≤ localCoordinateCap (N+2) B i
  · exact Or.inl ⟨hu,hc⟩
  · right
    push Not at hc
    obtain ⟨i,hi,hbad⟩ := hc
    have hiN : i.val < N := by omega
    apply Set.mem_iUnion.mpr
    refine ⟨i,Set.mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hiN,by omega⟩,?_⟩⟩
    refine ⟨geometric_family_subset_prefix hB.le hu.1,?_⟩
    by_contra hnot
    exact (not_le.mpr hbad) (coordinate_cap_of_not_bad hB hiN hnot)

theorem locally_concentrated_volume_lower : ∃ c δ : ℝ,∃ L : ℕ,
    0 < c ∧ 0 < δ ∧ 1 ≤ L ∧
    ∀ H : ℕ,1 ≤ H → ∀ᶠ x : ℝ in atTop,
      ∀ N : ℕ,N+2+H=m x →
        δ*G x (N+2) ≤ volume.real
          (locallyConcentratedFamily (m x) (N+2) (B x) c L) := by
  obtain ⟨c,δ,hc,hδ,hvolume⟩ := head_limited_volume_lower
  obtain ⟨C,k,hC,hk,hfailure⟩ := prefix_concentration_failure_bound
  have hq : Real.exp (-k)<1 := Real.exp_lt_one_iff.mpr (by linarith only [hk])
  have ht : Tendsto (fun L : ℕ => C*Real.exp (-k*(L:ℝ))/(1-Real.exp (-k)))
      atTop (nhds 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-k)).le hq).const_mul C
    convert hh.div_const (1-Real.exp (-k)) using 1
    · funext L
      rw [←Real.exp_nat_mul]
      congr 2
      ring_nf
    · simp
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds (half_pos hδ)))
  let L := max J 1
  have hL : 1 ≤ L := le_max_right _ _
  refine ⟨c,δ/2,L,hc,half_pos hδ,hL,?_⟩
  intro H hH
  filter_upwards [hvolume H hH,B_tendsto.eventually (eventually_gt_atTop (0:ℝ))]
    with x hx hB
  intro N hN
  let S := headLimitedFamily (m x) (N+2) (B x) c
  let T := locallyConcentratedFamily (m x) (N+2) (B x) c L
  let E := prefixConcentrationFailure N L (B x)
  have hsub : S ⊆ T ∪ E := local_family_failure_subset hB hL
  have hfinite : volume (T ∪ E) ≠ ⊤ := by
    apply measure_ne_top_of_subset (s:=prefixRegion (N+2) (B x) 0 0)
    · intro u hu
      rcases hu with hu|hu
      · exact geometric_family_subset_prefix hB.le hu.1.1
      · obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hu
        obtain ⟨_,hi⟩ := Set.mem_iUnion.mp hi
        exact hi.1
    · exact prefixRegion_volume_ne_top (by omega) _
  have hm := (measureReal_mono hsub hfinite).trans (measureReal_union_le T E)
  have he := hfailure N L (B x) hB
  have hG := prefixRegion_real_eq_G hB.le (by omega : 0 < N+2)
  rw [hG] at he
  have hb : volume.real E ≤ (δ/2)*G x (N+2) :=
    he.trans (mul_le_mul_of_nonneg_right (hJ L (le_max_left _ _)).le (G_pos hB _).le)
  have hs := hx N hN
  change δ*G x (N+2) ≤ volume.real S at hs
  nlinarith only [hm,hb,hs]

end TotientAsymptotic

end

end OAI
