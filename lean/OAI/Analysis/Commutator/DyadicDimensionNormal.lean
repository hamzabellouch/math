import Mathlib
import OAI.Analysis.Commutator.CoherentComparison

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology

open Filter

namespace Kadison.PartialIsometryOrder.DyadicPartition

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [Nontrivial H] [TopologicalSpace.SeparableSpace H]

variable (M : VonNeumannAlgebra H) (hfac : FactorCorner.IsFactor M)
  (hd : DiffuseProjection.HasNoMinimalProjections M) (hfin : IsFiniteAlgebra M)

include hfin in
theorem dimension_tendsto_of_strong_increasing {p : H →L[ℂ] H}
    (hpM : p∈M) (hp : IsStarProjection p) (P : ℕ → H →L[ℂ] H)
    (hPM : ∀ n,P n∈M) (hP : ∀ n,IsStarProjection (P n)) (hmono : Monotone P)
    (hPp : ∀ n,P n≤p) (hlim : ∀ x,Tendsto (fun n => P n x) atTop (𝓝 (p x))) :
    Tendsto (fun n => dimension M hfac hd (P n)) atTop (𝓝 (dimension M hfac hd p)) := by
  let d (n : ℕ) := dimension M hfac hd (P n)
  let L := sSup (Set.range d)
  have hdmono : Monotone d := fun n m h => dimension_mono M hfac hd (hPM n) (hP n) (hmono h)
  have hb : BddAbove (Set.range d) := ⟨1,by
    rintro _ ⟨n,rfl⟩
    exact dimension_le_one M hfac hd (P n)⟩
  have hnL (n : ℕ) : d n≤L := le_csSup hb (Set.mem_range_self n)
  have hLpos : 0≤L := (dimension_nonneg M hfac hd (P 0)).trans (hnL 0)
  have hLp : L≤dimension M hfac hd p := by
    apply csSup_le (Set.range_nonempty d)
    rintro _ ⟨n,rfl⟩
    exact dimension_mono M hfac hd (hPM n) (hP n) (hPp n)
  have hLeq : L=dimension M hfac hd p := by
    by_contra hne
    have hlt : L<dimension M hfac hd p := lt_of_le_of_ne hLp hne
    have ht : Tendsto (fun n : ℕ => (1:ℝ)/2^n) atTop (𝓝 0) := by
      simpa only [div_pow,one_pow] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/2:ℝ))
          (by norm_num : (1/2:ℝ)<1))
    obtain ⟨n,hn⟩ := (ht.eventually_lt_const (sub_pos.mpr hlt)).exists
    let D := partition M hfac hd n
    have hDb : dimension M hfac hd D.base=(1:ℝ)/2^n := dimension_base M hfac hd hfin n
    have hDpos : 0<dimension M hfac hd D.base := by rw [hDb]; positivity
    have hDp : dimension M hfac hd D.base≤dimension M hfac hd p := by rw [hDb]; linarith
    obtain ⟨v,hvi⟩ := subEquivalent_of_dimension_le M hfac hd hfin D.base_mem hpM
      D.base_projection hp hDp
    have hqM : v.final∈M := M.mul_mem v.mem (M.star_mem' v.mem)
    have hq : dimension M hfac hd v.final=dimension M hfac hd D.base :=
      dimension_congr_equivalent M hfac hd v.final_projection D.base_projection
        (by simpa only [hvi] using v.equivalentSupports.symm)
    have hr := v.residual_target_projection hp
    have hdr := dimension_difference M hfac hd hfin hpM hqM hp v.final_projection v.target_le
    have hPr : ∀ k,dimension M hfac hd (P k)≤dimension M hfac hd (p-v.final) := by
      intro k
      have hk := hnL k
      change dimension M hfac hd (P k)≤L at hk
      rw [hdr,hq,hDb]
      linarith
    have hcmp := subEquivalent_of_strong_increasing M hfac hd hfin hp
      (M.sub_mem hpM hqM) hr P hPM hP hmono hPp hPr hlim
    have heq : p-v.final=p := finite_subEquivalent_antisymm_of_le hfin hpM hp
      (sub_le_self _ v.final_projection.nonneg) hcmp
    rw [heq,hq] at hdr
    linarith
  rw [←hLeq]
  exact tendsto_atTop_ciSup hdmono hb

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
