import Mathlib
import OAI.Analysis.Commutator.DyadicDimensionComparison

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
lemma extend_comparison {p r q : H →L[ℂ] H} (hp : IsStarProjection p)
    (hrM : r∈M) (hr : IsStarProjection r) (hqM : q∈M) (hq : IsStarProjection q)
    (hqp : q≤p) (v : Link M p r) (hvi : v.initial≤q)
    (hdr : dimension M hfac hd q≤dimension M hfac hd r) :
    ∃ w : Link M p r,v≤w ∧ w.initial=q := by
  let b : Link M q r := ⟨v.val,v.mem,v.triple,hvi,v.target_le⟩
  have hiM : b.initial∈M := M.mul_mem (M.star_mem' b.mem) b.mem
  have hfM : b.final∈M := M.mul_mem b.mem (M.star_mem' b.mem)
  have heq := dimension_congr_equivalent M hfac hd b.initial_projection b.final_projection
    b.equivalentSupports
  have hds := dimension_difference M hfac hd hfin hqM hiM hq b.initial_projection b.source_le
  have hdt := dimension_difference M hfac hd hfin hrM hfM hr b.final_projection b.target_le
  obtain ⟨u,hui⟩ := subEquivalent_of_dimension_le M hfac hd hfin
    (M.sub_mem hqM hiM) (M.sub_mem hrM hfM) (b.residual_source_projection hq)
    (b.residual_target_projection hr) (by rw [hds,hdt,heq]; linarith)
  let z := b.extend hq hr u
  have hzp : z.initial≤p := by
    apply (z.initial_projection.le_iff_mul_eq_right hp).mpr
    calc
      p*z.initial = p*(q*z.initial) := by
        rw [(z.initial_projection.le_iff_mul_eq_right hq).mp z.source_le]
      _ = z.initial := by
        rw [←mul_assoc,(hq.le_iff_mul_eq_right hp).mp hqp,
          (z.initial_projection.le_iff_mul_eq_right hq).mp z.source_le]
  let w : Link M p r := ⟨z.val,z.mem,z.triple,hzp,z.target_le⟩
  refine ⟨w,?_,?_⟩
  · exact b.le_extend hq hr u
  · change z.initial=q
    rw [Link.extend_initial,hui]
    abel

include hfin in
theorem exists_coherent_comparisons {p r : H →L[ℂ] H} (hp : IsStarProjection p)
    (hrM : r∈M) (hr : IsStarProjection r) (P : ℕ → H →L[ℂ] H)
    (hPM : ∀ n,P n∈M) (hP : ∀ n,IsStarProjection (P n)) (hmono : Monotone P)
    (hPp : ∀ n,P n≤p) (hdim : ∀ n,dimension M hfac hd (P n)≤dimension M hfac hd r) :
    ∃ v : ℕ → Link M p r,Monotone v ∧ ∀ n,(v n).initial=P n := by
  classical
  obtain ⟨b,hb⟩ := subEquivalent_of_dimension_le M hfac hd hfin (hPM 0) hrM (hP 0) hr (hdim 0)
  let V (n : ℕ) := {v : Link M p r // v.initial=P n}
  let v0 : V 0 := ⟨⟨b.val,b.mem,b.triple,b.source_le.trans (hPp 0),b.target_le⟩,hb⟩
  have hstep (n : ℕ) (v : V n) : ∃ w : V (n+1),v.val≤w.val := by
    obtain ⟨w,hvw,hw⟩ := extend_comparison M hfac hd hfin hp hrM hr (hPM (n+1))
      (hP (n+1)) (hPp (n+1)) v.val (by rw [v.property]; exact hmono (Nat.le_succ n)) (hdim (n+1))
    exact ⟨⟨w,hw⟩,hvw⟩
  let step (n : ℕ) (v : V n) : V (n+1) := (hstep n v).choose
  let v : (n : ℕ) → V n := fun n => Nat.rec v0 step n
  refine ⟨fun n => (v n).val,?_,fun n => (v n).property⟩
  apply monotone_nat_of_le_succ
  intro n
  exact (hstep n (v n)).choose_spec

include hfin in
theorem subEquivalent_of_strong_increasing {p r : H →L[ℂ] H} (hp : IsStarProjection p)
    (hrM : r∈M) (hr : IsStarProjection r) (P : ℕ → H →L[ℂ] H)
    (hPM : ∀ n,P n∈M) (hP : ∀ n,IsStarProjection (P n)) (hmono : Monotone P)
    (hPp : ∀ n,P n≤p) (hdim : ∀ n,dimension M hfac hd (P n)≤dimension M hfac hd r)
    (hlim : ∀ x,Tendsto (fun n => P n x) atTop (𝓝 (p x))) : SubEquivalent M p r := by
  obtain ⟨v,hvmono,hvi⟩ := exists_coherent_comparisons M hfac hd hfin hp hrM hr P hPM hP hmono hPp hdim
  have hc : IsChain (·≤·) (Set.range v) := by
    rintro _ ⟨n,rfl⟩ _ ⟨m,rfl⟩ hne
    rcases le_total n m with h|h
    · exact Or.inl (hvmono h)
    · exact Or.inr (hvmono h)
  obtain ⟨u,hu⟩ := chain_has_upper M hp hr (Set.range v) hc (Set.range_nonempty v)
  have hPu (n : ℕ) : P n≤u.initial := by
    rw [←hvi n]
    exact ((Link.le_def _ _).mp (hu (Set.mem_range_self n))).1
  have hEq : u.initial*p=p := by
    ext x
    have hconv := u.initial.continuous.tendsto (p x) |>.comp (hlim x)
    have heq (n : ℕ) : u.initial (P n x)=P n x := by
      exact congrArg (fun T : H →L[ℂ] H => T x)
        (((hP n).le_iff_mul_eq_right u.initial_projection).mp (hPu n))
    have hconv' : Tendsto (fun n => u.initial (P n x)) atTop (𝓝 (p x)) := by
      simpa only [heq] using hlim x
    exact tendsto_nhds_unique hconv hconv'
  refine ⟨u,le_antisymm u.source_le ((hp.le_iff_mul_eq_right u.initial_projection).mpr hEq)⟩

end Kadison.PartialIsometryOrder.DyadicPartition

end

end
end

end OAI
