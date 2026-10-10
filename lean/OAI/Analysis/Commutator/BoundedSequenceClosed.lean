import Mathlib
import OAI.Analysis.Commutator.HilbertSequence
import OAI.Analysis.Commutator.UltrafilterDiagonal

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction

open Filter UniformSpace Completion

namespace Kadison.HilbertSequence

variable {A H : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable (ω : Ultrafilter ℕ) (v : A →L[ℂ] H)

def mapPre (a : ℕ →ᵇ A) : Pre ω H :=
  ⟨BoundedContinuousFunction.comp v v.lipschitzWith a⟩

def mapVector (a : ℕ →ᵇ A) : Space ω H := (mapPre ω v a : Space ω H)

omit [InnerProductSpace ℂ H] in
@[simp] lemma seq_sub' (a b : Pre ω H) (i : ℕ) : (a-b).seq i=a.seq i-b.seq i := rfl

lemma norm_map_difference_tendsto (a b : ℕ →ᵇ A) :
    Tendsto (fun i => ‖v (a i)-v (b i)‖) (ω : Filter ℕ)
      (𝓝 ‖mapVector ω v a-mapVector ω v b‖) := by
  simpa only [mapVector,←Completion.coe_sub,Completion.norm_coe,seq_sub',mapPre,BoundedContinuousFunction.comp_apply] using
    tendsto_norm ω H (mapPre ω v a-mapPre ω v b)

theorem bounded_image_isClosed (hω : (ω : Filter ℕ)≤atTop)
    (K : Set A) (C : ℝ) (hK : ∀ a∈K, ‖a‖≤C) :
    IsClosed {x : Space ω H | ∃ a : ℕ →ᵇ A, (∀ i, a i∈K) ∧ mapVector ω v a=x} := by
  classical
  apply isClosed_of_closure_subset
  intro x hx
  let ε (n : ℕ) : ℝ := (1/2:ℝ)^n
  have hε (n : ℕ) : 0<ε n := pow_pos (by norm_num) n
  have hanti {j k : ℕ} (hjk : j≤k) : ε k≤ε j :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hjk
  have hn (n : ℕ) : ∃ a : ℕ →ᵇ A, (∀ i, a i∈K) ∧ ‖mapVector ω v a-x‖<ε n := by
    obtain ⟨y,⟨a,ha,rfl⟩,hy⟩ := Metric.mem_closure_iff.mp hx (ε n) (hε n)
    exact ⟨a,ha,by simpa only [dist_eq_norm,norm_sub_rev] using hy⟩
  choose f hf he using hn
  have hpair (j k : ℕ) (hjk : j≤k) :
      ∀ᶠ i in (ω : Filter ℕ), ‖v (f j i)-v (f k i)‖≤3*ε j := by
    have hlt : ‖mapVector ω v (f j)-mapVector ω v (f k)‖<3*ε j := by
      have h := norm_sub_le_norm_sub_add_norm_sub (mapVector ω v (f j)) x (mapVector ω v (f k))
      rw [norm_sub_rev x] at h
      have hj := he j
      have hk := he k
      have hk' := hanti hjk
      have hp := hε j
      linarith
    exact (norm_map_difference_tendsto ω v (f j) (f k)).eventually (gt_mem_nhds hlt) |>.mono
      (fun _ hi => le_of_lt hi)
  let p (n i : ℕ) : Prop := ∀ j≤n, ∀ k≤n, j≤k → ‖v (f j i)-v (f k i)‖≤3*ε j
  have hp (n : ℕ) : ∀ᶠ i in (ω : Filter ℕ), p n i := by
    have hh : ∀ᶠ i in (ω : Filter ℕ), ∀ j∈Finset.range (n+1),
        ∀ k∈Finset.range (n+1), j≤k → ‖v (f j i)-v (f k i)‖≤3*ε j := by
      apply (eventually_all_finset (Finset.range (n+1))).mpr
      intro j _
      apply (eventually_all_finset (Finset.range (n+1))).mpr
      intro k _
      by_cases hjk : j≤k
      · exact (hpair j k hjk).mono (fun _ hi _ => hi)
      · exact Eventually.of_forall (fun _ hi => (hjk hi).elim)
    filter_upwards [hh] with i hi
    intro j hj k hk hjk
    exact hi j (Finset.mem_range.mpr (by omega)) k (Finset.mem_range.mpr (by omega)) hjk
  obtain ⟨d,hd,hreq⟩ := UltrafilterDiagonal.depth hω p hp
  let a : ℕ →ᵇ A := BoundedContinuousFunction.mkOfDiscrete (fun i => f (d i/2) i) (2*C)
    (fun i j => (dist_le_norm_add_norm _ _).trans (by
      have hi := hK _ (hf (d i/2) i)
      have hj := hK _ (hf (d j/2) j)
      linarith))
  have ha (i : ℕ) : a i∈K := hf (d i/2) i
  have hnorm (j : ℕ) : ‖mapVector ω v a-mapVector ω v (f j)‖≤3*ε j := by
    apply le_of_tendsto (norm_map_difference_tendsto ω v a (f j))
    filter_upwards [hd.eventually (eventually_ge_atTop (2*j+2))] with i hi
    have hleft : j≤d i/2 := by omega
    have hright : d i/2<d i := by omega
    have hh := hreq i (d i/2) hright j hleft (d i/2) (le_refl _) hleft
    simpa only [a,BoundedContinuousFunction.mkOfDiscrete_apply,norm_sub_rev] using hh
  have hnorm' (j : ℕ) : ‖mapVector ω v a-x‖≤4*ε j := by
    have h := norm_sub_le_norm_sub_add_norm_sub (mapVector ω v a) (mapVector ω v (f j)) x
    have h1 := hnorm j
    have h2 := he j
    linarith
  have hlim : Tendsto (fun j => 4*ε j) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)))
  have hz : ‖mapVector ω v a-x‖≤0 := ge_of_tendsto hlim (Eventually.of_forall hnorm')
  exact ⟨a,ha,sub_eq_zero.mp (norm_le_zero_iff.mp hz)⟩

end Kadison.HilbertSequence

end

end
end

end OAI
