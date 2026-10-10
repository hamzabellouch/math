import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphBalls
import OAI.Probability.CriticalPercolation.Growth.SuperpolynomialRadius
import OAI.Probability.CriticalPercolation.GraphGeometry.UniformGeometry
import OAI.Probability.CriticalPercolation.Criticality.SubexponentialVolumes

namespace OAI

section
section
noncomputable section
open Set Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

def maxVolume (n : ℕ) : ℕ := sSup (Set.range fun v => (G.vertexBall v n).ncard)

lemma volume_le_maxVolume (hq : G.QuasiTransitive) (v : V) (n : ℕ) :
    (G.vertexBall v n).ncard ≤ G.maxVolume n := by
  obtain ⟨M,hM⟩ := G.uniform_ball_bound hq n
  exact le_csSup ⟨M,by rintro _ ⟨w,rfl⟩; exact hM w⟩ ⟨v,rfl⟩

lemma exists_maxVolume [Nonempty V] (hq : G.QuasiTransitive) (n : ℕ) :
    ∃ v, G.maxVolume n=(G.vertexBall v n).ncard := by
  obtain ⟨M,hM⟩ := G.uniform_ball_bound hq n
  have hne : (Set.range fun v => (G.vertexBall v n).ncard).Nonempty := Set.range_nonempty _
  obtain ⟨v,hv⟩ := Nat.sSup_mem hne ⟨M,by rintro _ ⟨w,rfl⟩; exact hM w⟩
  exact ⟨v,hv.symm⟩

lemma vertexBall_add_cover (o : V) (r s : ℕ) :
    G.vertexBall o (r+s) ⊆ ⋃ v∈G.vertexBall o r, G.vertexBall v s := by
  induction s with
  | zero =>
    intro v hv
    exact Set.mem_iUnion₂.mpr ⟨v,hv,rfl⟩
  | succ s ih =>
    rintro w (hw|hw)
    · obtain ⟨v,hv,hw⟩ := Set.mem_iUnion₂.mp (ih hw)
      exact Set.mem_iUnion₂.mpr ⟨v,hv,G.vertexBall_mono v (Nat.le_succ _) hw⟩
    · obtain ⟨z,hz,hzw⟩ := Set.mem_iUnion₂.mp hw
      obtain ⟨v,hv,hz⟩ := Set.mem_iUnion₂.mp (ih hz)
      exact Set.mem_iUnion₂.mpr ⟨v,hv,G.vertexBall_step hz hzw⟩

lemma ncard_biUnion_le_sum {ι X : Type*} (S : Finset ι) (F : ι → Set X)
    (hF : ∀ i∈S, (F i).Finite) :
    (⋃ i∈(S : Set ι), F i).ncard ≤ ∑ i∈S, (F i).ncard := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    simp only [Finset.mem_insert] at hF
    rw [Finset.coe_insert,Set.biUnion_insert,Finset.sum_insert ha]
    exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left
      (ih (fun i hi => hF i (Or.inr hi))) _)

lemma maxVolume_submultiplicative [Nonempty V] (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive) (r s : ℕ) :
    G.maxVolume (r+s) ≤ G.maxVolume r*G.maxVolume s := by
  obtain ⟨o,ho⟩ := G.exists_maxVolume hq (r+s)
  rw [ho]
  have hfin := G.vertexBall_finite hl o r
  have hu := hfin.biUnion fun v _ => G.vertexBall_finite hl v s
  calc
    _ ≤ (⋃ v∈G.vertexBall o r, G.vertexBall v s).ncard :=
      Set.ncard_le_ncard (G.vertexBall_add_cover o r s) hu
    _ ≤ ∑ v∈hfin.toFinset, (G.vertexBall v s).ncard := by
      simpa only [Set.Finite.coe_toFinset] using ncard_biUnion_le_sum hfin.toFinset
        (fun v => G.vertexBall v s) (fun v _ => G.vertexBall_finite hl v s)
    _ ≤ ∑ _v∈hfin.toFinset, G.maxVolume s := Finset.sum_le_sum fun v _ => G.volume_le_maxVolume hq v s
    _ = (G.vertexBall o r).ncard*G.maxVolume s := by
      simp only [Finset.sum_const,nsmul_eq_mul,Set.ncard_eq_toFinset_card _ hfin,Nat.cast_id]
    _ ≤ _ := Nat.mul_le_mul_right _ (G.volume_le_maxVolume hq o r)

lemma maxVolume_pos [Nonempty V] (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (n : ℕ) :
    0<G.maxVolume n := by
  obtain ⟨v⟩ := ‹Nonempty V›
  exact (G.vertexBall_ncard_pos hl v n).trans_le (G.volume_le_maxVolume hq v n)

lemma log_maxVolume_subadditive [Nonempty V] (hl : G.LocallyFinite) (hq : G.QuasiTransitive) :
    Subadditive (fun n => Real.log (G.maxVolume n : ℝ)) := by
  intro r s
  have hr : (0:ℝ)<G.maxVolume r := Nat.cast_pos.mpr (G.maxVolume_pos hl hq r)
  have hs : (0:ℝ)<G.maxVolume s := Nat.cast_pos.mpr (G.maxVolume_pos hl hq s)
  have hrs : (0:ℝ)<G.maxVolume (r+s) := Nat.cast_pos.mpr (G.maxVolume_pos hl hq _)
  calc
    _ ≤ Real.log ((G.maxVolume r : ℝ)*G.maxVolume s) := Real.log_le_log hrs (by
      exact_mod_cast G.maxVolume_submultiplicative hl hq r s)
    _ = _ := Real.log_mul hr.ne' hs.ne'

lemma uniform_subexponential_of_log_limit [Nonempty V] (hl : G.LocallyFinite)
    (hq : G.QuasiTransitive)
    (hlim : Tendsto (fun n => Real.log (G.maxVolume n : ℝ)/(n:ℝ)) atTop (𝓝 0)) :
    G.SubexponentialGrowth := by
  intro o ε hε
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hε))
  refine ⟨max N 1,?_⟩
  intro n hn
  have hn0 : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  calc
    _ ≤ Real.log (G.maxVolume n : ℝ) := Real.log_le_log
      (Nat.cast_pos.mpr (G.vertexBall_ncard_pos hl o n)) (by exact_mod_cast G.volume_le_maxVolume hq o n)
    _ ≤ ε*n := (div_lt_iff₀ hn0).mp (hN n (by omega)) |>.le

theorem growth_alternative [Nonempty V] (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) :
    G.SubexponentialGrowth ∨ ∃ a : ℝ, 0<a ∧ ∃ N : ℕ, ∀ n≥N, ∀ v : V,
      a*n ≤ Real.log ((G.vertexBall v n).ncard : ℝ) := by
  let u := fun n => Real.log (G.maxVolume n : ℝ)
  have hu : Subadditive u := G.log_maxVolume_subadditive hl hq
  have hnon : ∀ n, 0≤u n := fun n => Real.log_nonneg (by exact_mod_cast G.maxVolume_pos hl hq n)
  have hb : BddBelow (Set.range fun n => u n/(n:ℝ)) := ⟨0,by
    rintro x ⟨n,rfl⟩
    exact div_nonneg (hnon n) (Nat.cast_nonneg _)⟩
  have hlim := hu.tendsto_lim hb
  have hlimnon : 0≤hu.lim := ge_of_tendsto hlim (Eventually.of_forall fun n => div_nonneg (hnon n) (Nat.cast_nonneg _))
  by_cases hz : hu.lim=0
  · exact Or.inl (G.uniform_subexponential_of_log_limit hl hq (hz ▸ hlim))
  · have hpos : 0<hu.lim := lt_of_le_of_ne hlimnon (Ne.symm hz)
    obtain ⟨C,hC⟩ := G.uniform_orbit_density_radius hc hq
    refine Or.inr ⟨hu.lim/2,half_pos hpos,2*C+1,?_⟩
    intro n hn v
    have hnC : C<n := by omega
    obtain ⟨o,ho⟩ := G.exists_maxVolume hq (n-C)
    obtain ⟨φ,hφ⟩ := hC o v
    have hsub : G.vertexBall (φ.vertex o) (n-C) ⊆ G.vertexBall v n := by
      have hh := G.vertexBall_add hφ (n-C)
      simpa only [Nat.add_sub_of_le hnC.le] using hh
    have hcard := Set.ncard_le_ncard hsub (G.vertexBall_finite hl v n)
    rw [Aut.vertexBall_ncard G φ,← ho] at hcard
    have hm : (0:ℝ)<(n-C : ℕ) := by exact_mod_cast (show 0<n-C by omega)
    have hh := (le_div_iff₀ hm).mp (hu.lim_le_div hb (by omega : n-C≠0))
    have hlog := Real.log_le_log (Nat.cast_pos.mpr (G.maxVolume_pos hl hq (n-C)))
      (Nat.cast_le.mpr hcard)
    change hu.lim*(n-C : ℕ) ≤ u (n-C) at hh
    have he : ((n-C : ℕ):ℝ)=(n:ℝ)-C := Nat.cast_sub hnC.le
    rw [he] at hh
    change u (n-C) ≤ _ at hlog
    have hnc : 2*(C:ℝ)+1≤n := by exact_mod_cast hn
    nlinarith

theorem superpolynomial_or_polynomial_scales :
    G.SuperpolynomialGrowth ∨ ∃ d : ℕ, ∀ R : ℕ, ∃ n≥R, ∃ v : V,
      (G.vertexBall v n).ncard ≤ n^d := by
  by_cases h : G.SuperpolynomialGrowth
  · exact Or.inl h
  · unfold SuperpolynomialGrowth at h
    push Not at h
    obtain ⟨d,hd⟩ := h
    exact Or.inr ⟨d,fun R => by
      obtain ⟨n,hn,v,hv⟩ := hd R
      exact ⟨n,hn,v,hv.le⟩⟩

end CriticalPercolation.BondGraph
end
end
end

end OAI
