import Mathlib
import OAI.Probability.CriticalPercolation.Harmonic.LazyWalkHilbert
import OAI.Probability.CriticalPercolation.Harmonic.LazyWalkProbability

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical Pointwise BigOperators

namespace CriticalPercolation.HarmonicAnalysis.WordGeometry
variable {A : Type*} [Group A] (W : WordGeometry A)

lemma exists_word_ball_boundary [Infinite A] (r : ℕ) :
    ∃ a∈W.ball (r+1), a∉W.ball r := by
  by_contra! hbad
  have he : W.ball (r+1)=W.ball r :=
    Finset.Subset.antisymm hbad (W.ball_mono (by omega))
  have hs : ∀ n, W.ball n⊆W.ball r := by
    intro n
    induction n with
    | zero =>
      apply W.ball_mono
      omega
    | succ n ih =>
      change W.generators^(n+1)⊆W.ball r
      rw [pow_succ]
      have hh := Finset.mul_subset_mul ih (Finset.Subset.refl W.generators)
      exact hh.trans (by simpa only [ball,←pow_succ] using he.le)
  have hfinite : (Set.univ:Set A).Finite := (W.ball r).finite_toSet.subset (by
    intro a _
    obtain ⟨n,hn⟩ := W.exists_mem_ball a
    exact hs n hn)
  exact Set.infinite_univ hfinite

lemma regular_word_displacement (f : RegularHilbert A) (C : ℝ)
    (hgen : ∀ s∈W.generators, ‖regular s f-f‖≤C) (r : ℕ)
    {a : A} (ha : a∈W.ball r) : ‖regular a f-f‖≤(r:ℝ)*C := by
  induction r generalizing a with
  | zero =>
    have he : a=1 := by simpa [ball] using ha
    simp [he]
  | succ r ih =>
    change a∈W.generators^(r+1) at ha
    rw [pow_succ] at ha
    obtain ⟨b,hb,s,hs,rfl⟩ := Finset.mem_mul.mp ha
    have he : regular (b*s) f-f = regular b (regular s f-f)+(regular b f-f) := by
      rw [regular_mul,map_sub]
      abel
    rw [he]
    calc
      _ ≤ ‖regular b (regular s f-f)‖+‖regular b f-f‖ := norm_add_le _ _
      _ = ‖regular s f-f‖+‖regular b f-f‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ C+(r:ℝ)*C := add_le_add (hgen s hs) (ih hb)
      _ = _ := by push_cast; ring

lemma regular_energy_displacement (f : RegularHilbert A) (r : ℕ)
    {a : A} (ha : a∈W.ball r) :
    ‖regular a f-f‖≤(r:ℝ)*Real.sqrt (4*(W.generators.card:ℝ)*W.walkEnergy f) := by
  apply W.regular_word_displacement f _ ?_ r ha
  intro s hs
  have h := (Finset.single_le_sum (f := fun t => ‖regular t f-f‖^2)
    (fun _ _ => sq_nonneg _) hs).trans_eq (W.walkEnergy_gradient f)
  have he : 0≤4*(W.generators.card:ℝ)*W.walkEnergy f := by
    exact mul_nonneg (by positivity) (W.walkEnergy_nonneg f)
  have hsqrt := Real.sq_sqrt he
  nlinarith [norm_nonneg (regular s f-f),Real.sqrt_nonneg (4*(W.generators.card:ℝ)*W.walkEnergy f)]

lemma supported_energy_bound [Infinite A] (r : ℕ) (f : RegularHilbert A)
    (hsupp : ∀ a∉W.ball r, f a=0) :
    f 1^2≤(r+1:ℝ)^2*4*(W.generators.card:ℝ)*W.walkEnergy f := by
  obtain ⟨a,ha,ha'⟩ := W.exists_word_ball_boundary r
  have hai : a⁻¹∉W.ball r := by
    intro hh
    have hi := Finset.inv_mem_inv hh
    apply ha'
    simpa only [ball,←inv_pow,W.inv_eq,inv_inv] using hi
  have hp := lp.norm_apply_le_norm (by norm_num : (2:ENNReal)≠0) (regular a f-f) 1
  have hb := W.regular_energy_displacement f (r+1) ha
  have hv : ‖(regular a f-f) 1‖=|f 1| := by
    simp only [lp.coeFn_sub,Pi.sub_apply,regular_apply,mul_one,hsupp a⁻¹ hai,
      zero_sub,norm_neg,Real.norm_eq_abs]
  rw [hv] at hp
  have h := hp.trans hb
  have ht := pow_le_pow_left₀ (abs_nonneg (f 1)) h 2
  have he : 0≤4*(W.generators.card:ℝ)*W.walkEnergy f :=
    mul_nonneg (by positivity) (W.walkEnergy_nonneg f)
  rw [mul_pow,Real.sq_sqrt he,sq_abs] at ht
  push_cast at ht
  nlinarith

lemma walkState_energy_pos [Infinite A] (n : ℕ) : 0<W.walkEnergy (W.walkState n) := by
  have hp := W.walkState_one_pos n
  have hb := W.supported_energy_bound n (W.walkState n) (fun _ ha => W.walkState_support n ha)
  have hn := W.walkEnergy_nonneg (W.walkState n)
  by_contra! h
  have he : W.walkEnergy (W.walkState n)=0 := le_antisymm h hn
  rw [he,mul_zero] at hb
  nlinarith

lemma walkState_energy_lower [Infinite A] (n : ℕ) :
    1≤((W.ball n).card:ℝ)^2*(2*(n:ℝ)+1)^2*4*(W.generators.card:ℝ)*
      W.walkEnergy (W.walkState (2*n)) := by
  have hn := W.walkState_norm_lower n
  have hb := W.supported_energy_bound (2*n) (W.walkState (2*n))
    (fun _ ha => W.walkState_support _ ha)
  rw [W.walkState_double_at_one] at hb
  have hsq : 1≤((W.ball n).card:ℝ)^2*(‖W.walkState n‖^2)^2 := by
    nlinarith [mul_self_le_mul_self (by norm_num : (0:ℝ)≤1) hn]
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg ((W.ball n).card:ℝ))
  push_cast at hh
  nlinarith

end CriticalPercolation.HarmonicAnalysis.WordGeometry
end
end

end OAI
