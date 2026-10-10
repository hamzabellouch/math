import OAI.Analysis.PeriodicLattice.DerivativeWords

namespace OAI

/-! Rapid decay estimates for all profile derivatives. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingRapidBounds {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace RapidCalculus

open Set Filter Topology TorusCalculus
open scoped ContDiff

structure BoundedProfile (h : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ h
  bound : ∀ k : ℕ, ∃ C : ℝ, ∀ z : ℝ, ‖iteratedDeriv k h z‖ ≤ C

theorem BoundedProfile.deriv {h : ℝ → ℝ} (hh : BoundedProfile h) :
    BoundedProfile (deriv h) := by
  refine ⟨ContDiff.iterate_deriv 1 hh.smooth, fun k => ?_⟩
  simpa only [iteratedDeriv_succ'] using hh.bound (k + 1)

theorem BoundedProfile.neg {h : ℝ → ℝ} (hh : BoundedProfile h) :
    BoundedProfile (-h) := by
  refine ⟨hh.smooth.neg, fun k => ?_⟩
  obtain ⟨C, hC⟩ := hh.bound k
  exact ⟨C, fun z => by simpa only [iteratedDeriv_neg, Pi.neg_apply, norm_neg] using hC z⟩

inductive Algebra : ScalarField → Prop
  | zero : Algebra 0
  | tensor (F : ScalarField) (f : ℝ → ℝ → ℝ) (h : ℝ → ℝ)
      (hf : Rapid2 f) (hh : BoundedProfile h)
      (cover : ∀ t x, F t (torusMk x) = h (x 2) * f t (x 1)) : Algebra F
  | add {F G : ScalarField} : Algebra F → Algebra G → Algebra (F + G)
  | mul {F G : ScalarField} : Algebra F → Algebra G → Algebra (F * G)
  | scale (c : ℝ) {F : ScalarField} : Algebra F → Algebra (c • F)

theorem Algebra.smooth {F : ScalarField} (hF : Algebra F) : ContDiff ℝ ∞ (lifted F) := by
  induction hF with
  | zero => exact contDiff_const
  | tensor F f h hf hh he =>
    have hc (i : Fin 3) : ContDiff ℝ ∞ (fun tx : ℝ × Space => tx.2 i) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).contDiff.comp contDiff_snd
    change ContDiff ℝ ∞ (fun tx : ℝ × Space => F tx.1 (torusMk tx.2))
    simp_rw [he]
    exact (hh.smooth.comp (hc 2)).mul (hf.smooth.comp (contDiff_fst.prodMk (hc 1)))
  | add hF hG ihF ihG => exact ihF.add ihG
  | mul hF hG ihF ihG => exact ihF.mul ihG
  | scale c hF ihF => exact (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ × Space => c)).smul ihF

theorem Algebra.bound {F : ScalarField} (hF : Algebra F) (J : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ q : Torus, (1 + t) ^ J * ‖F t q‖ ≤ C := by
  induction hF generalizing J with
  | zero => exact ⟨0, fun t _ q => by simp⟩
  | tensor F f h hf hh he =>
    obtain ⟨C, hC⟩ := hf.bound [] J
    obtain ⟨D, hD⟩ := hh.bound 0
    have hD₀ : 0 ≤ D := (norm_nonneg _).trans (hD 0)
    refine ⟨D * C, fun t ht q => ?_⟩
    obtain ⟨x, rfl⟩ := mk_surjective q
    rw [he, norm_mul]
    calc
      _ = ‖h (x 2)‖ * ((1 + t) ^ J * ‖f t (x 1)‖) := by ring
      _ ≤ D * ((1 + t) ^ J * ‖f t (x 1)‖) :=
        mul_le_mul_of_nonneg_right (hD (x 2)) (by positivity)
      _ ≤ D * C := mul_le_mul_of_nonneg_left (hC t ht (x 1)) hD₀
  | @add F G hF hG ihF ihG =>
    obtain ⟨C, hC⟩ := ihF J
    obtain ⟨D, hD⟩ := ihG J
    refine ⟨C + D, fun t ht q => ?_⟩
    change (1 + t) ^ J * ‖F t q + G t q‖ ≤ C + D
    calc
      _ ≤ (1 + t) ^ J * (‖F t q‖ + ‖G t q‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ C + D := by rw [mul_add]; exact add_le_add (hC t ht q) (hD t ht q)
  | @mul F G hF hG ihF ihG =>
    obtain ⟨C, hC⟩ := ihF J
    obtain ⟨D, hD⟩ := ihG 0
    have hD₀ : 0 ≤ D := by
      have hz : ‖G 0 0‖ ≤ D := by simpa only [pow_zero, one_mul] using hD 0 le_rfl 0
      exact (norm_nonneg _).trans hz
    refine ⟨C * D, fun t ht q => ?_⟩
    change (1 + t) ^ J * ‖F t q * G t q‖ ≤ C * D
    rw [norm_mul, ← mul_assoc]
    calc
      _ ≤ ((1 + t) ^ J * ‖F t q‖) * D := mul_le_mul_of_nonneg_left (by simpa using hD t ht q) (by positivity)
      _ ≤ C * D := mul_le_mul_of_nonneg_right (hC t ht q) hD₀
  | @scale c F hF ihF =>
    obtain ⟨C, hC⟩ := ihF J
    refine ⟨‖c‖ * C, fun t ht q => ?_⟩
    change (1 + t) ^ J * ‖c • F t q‖ ≤ ‖c‖ * C
    rw [norm_smul, mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hC t ht q) (norm_nonneg _)

theorem tensor_spaceD_zero {F : ScalarField} {f : ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (he : ∀ t x, F t (torusMk x) = h (x 2) * f t (x 1)) : spaceD 0 F = 0 := by
  funext t q
  obtain ⟨x, rfl⟩ := mk_surjective q
  rw [spaceD_cover]
  simp only [spaceLift, he]
  change deriv (fun s : ℝ => h (x 2 + 0) * f t (x 1 + 0)) 0 = 0
  exact deriv_const _ _

theorem tensor_spaceD_one {F : ScalarField} {f : ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (he : ∀ t x, F t (torusMk x) = h (x 2) * f t (x 1)) (t : ℝ) (x : Space) :
    spaceD 1 F t (torusMk x) = h (x 2) * biD false f t (x 1) := by
  rw [spaceD_cover]
  simp only [spaceLift, he]
  change deriv (fun s : ℝ => h (x 2 + 0) * f t (x 1 + s)) 0 = _
  have hd := (((hf.comp ((contDiff_const (c := t)).prodMk contDiff_id)).differentiable (by simp) (x 1 + 0)).hasDerivAt.comp 0
    ((hasDerivAt_id (0 : ℝ)).const_add (x 1))).const_mul (h (x 2))
  simpa [biD, Function.comp_def] using hd.deriv

theorem tensor_spaceD_two {F : ScalarField} {f : ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h)
    (he : ∀ t x, F t (torusMk x) = h (x 2) * f t (x 1)) (t : ℝ) (x : Space) :
    spaceD 2 F t (torusMk x) = deriv h (x 2) * f t (x 1) := by
  rw [spaceD_cover]
  simp only [spaceLift, he]
  change deriv (fun s : ℝ => h (x 2 + s) * f t (x 1 + 0)) 0 = _
  have hd := (((hh.differentiable (by simp) (x 2 + 0)).hasDerivAt.comp 0
    ((hasDerivAt_id (0 : ℝ)).const_add (x 2))).mul_const (f t (x 1)))
  simpa [Function.comp_def] using hd.deriv

theorem tensor_fullTimeD {F : ScalarField} {f : ℝ → ℝ → ℝ} {h : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (he : ∀ t x, F t (torusMk x) = h (x 2) * f t (x 1)) (t : ℝ) (x : Space) :
    fullTimeD F t (torusMk x) = h (x 2) * biD true f t (x 1) := by
  simp only [fullTimeD, he]
  exact deriv_const_mul _ ((hf.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)

theorem Algebra.spaceDeriv {F : ScalarField} (hF : Algebra F) (i : Fin 3) : Algebra (spaceD i F) := by
  induction hF with
  | zero =>
    have hz : spaceD i (0 : ScalarField) = 0 := by funext t q; exact deriv_const _ _
    rw [hz]; exact Algebra.zero
  | tensor F f h hf hh he =>
    fin_cases i
    · change Algebra (spaceD 0 F)
      rw [tensor_spaceD_zero he]; exact Algebra.zero
    · exact Algebra.tensor _ _ _ (hf.biD false) hh (tensor_spaceD_one hf.smooth he)
    · exact Algebra.tensor _ _ _ hf hh.deriv (tensor_spaceD_two hh.smooth he)
  | @add F G hF hG ihF ihG =>
    have he : spaceD i (F + G) = spaceD i F + spaceD i G := by
      funext t q
      exact TorusCalculus.spaceD_add
        ((hF.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
        ((hG.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) i q
    rw [he]; exact ihF.add ihG
  | @mul F G hF hG ihF ihG =>
    have he : spaceD i (F * G) = spaceD i F * G + F * spaceD i G := by
      funext t q
      exact spaceD_smul hF.smooth hG.smooth i t q
    rw [he]; exact (ihF.mul hG).add (hF.mul ihG)
  | @scale c F hF ihF =>
    have he : spaceD i (c • F) = c • spaceD i F := by
      funext t q
      exact deriv_const_mul _ (hasDerivAt_translation hF.smooth t q i 0).differentiableAt
    rw [he]; exact ihF.scale c

theorem Algebra.timeDeriv {F : ScalarField} (hF : Algebra F) : Algebra (fullTimeD F) := by
  induction hF with
  | zero =>
    have hz : fullTimeD (0 : ScalarField) = 0 := by funext t q; exact deriv_const _ _
    rw [hz]; exact Algebra.zero
  | tensor F f h hf hh he =>
    exact Algebra.tensor _ _ _ (hf.biD true) hh (tensor_fullTimeD hf.smooth he)
  | @add F G hF hG ihF ihG =>
    have he : fullTimeD (F + G) = fullTimeD F + fullTimeD G := by
      funext t q
      obtain ⟨x, rfl⟩ := mk_surjective q
      exact deriv_add
        ((hF.smooth.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
        ((hG.smooth.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
    rw [he]; exact ihF.add ihG
  | @mul F G hF hG ihF ihG =>
    have he : fullTimeD (F * G) = fullTimeD F * G + F * fullTimeD G := by
      funext t q
      obtain ⟨x, rfl⟩ := mk_surjective q
      exact deriv_mul
        ((hF.smooth.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
        ((hG.smooth.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
    rw [he]; exact (ihF.mul hG).add (hF.mul ihG)
  | @scale c F hF ihF =>
    have he : fullTimeD (c • F) = c • fullTimeD F := by
      funext t q
      obtain ⟨x, rfl⟩ := mk_surjective q
      exact deriv_const_mul _
        ((hF.smooth.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t)
    rw [he]; exact ihF.scale c

theorem boundedProfile_of_periodic {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h)
    (hp : Function.Periodic h 1) : BoundedProfile h := by
  refine ⟨hs, fun k => ?_⟩
  have hpk : Function.Periodic (iteratedDeriv k h) 1 := by
    induction k with
    | zero => exact hp
    | succ k ih => simpa only [iteratedDeriv_succ] using periodic_deriv ih
  have hsk : ContDiff ℝ ∞ (iteratedDeriv k h) := by
    rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv _ hs
  obtain ⟨C, hC⟩ := (hpk.isBounded_of_continuous (by norm_num) hsk.continuous).exists_norm_le
  exact ⟨C, fun z => hC _ (mem_range_self z)⟩

def VectorAlgebra (U : VectorField) : Prop := ∀ j : Fin 3, Algebra (fun t q => U t q j)

theorem VectorAlgebra.smooth {U : VectorField} (hU : VectorAlgebra U) :
    ContDiff ℝ ∞ (lifted U) := contDiff_euclidean.mpr fun j => (hU j).smooth

theorem VectorAlgebra.spaceDeriv {U : VectorField} (hU : VectorAlgebra U) (i : Fin 3) :
    VectorAlgebra (spaceD i U) := by
  intro j
  have he : (fun t q => spaceD i U t q j) = spaceD i (fun t q => U t q j) := by
    funext t q
    exact (spaceD_component ((hU.smooth.comp (contDiff_const.prodMk contDiff_id)).differentiable
      (by simp)) i j q).symm
  rw [he]; exact (hU j).spaceDeriv i

theorem VectorAlgebra.timeDeriv {U : VectorField} (hU : VectorAlgebra U) :
    VectorAlgebra (fullTimeD U) := by
  intro j
  have he : (fun t q => fullTimeD U t q j) = fullTimeD (fun t q => U t q j) := by
    funext t q
    obtain ⟨x, rfl⟩ := mk_surjective q
    have ht := ((hU.smooth.comp (contDiff_id.prodMk (contDiff_const (c := x)))).differentiable (by simp) t).hasDerivAt
    exact ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).hasFDerivAt.comp_hasDerivAt t ht).deriv.symm
  rw [he]; exact (hU j).timeDeriv

theorem VectorAlgebra.add {U V : VectorField} (hU : VectorAlgebra U) (hV : VectorAlgebra V) :
    VectorAlgebra (U + V) := fun j => (hU j).add (hV j)

theorem VectorAlgebra.scale {U : VectorField} (hU : VectorAlgebra U) (c : ℝ) :
    VectorAlgebra (c • U) := fun j => (hU j).scale c

theorem VectorAlgebra.sub {U V : VectorField} (hU : VectorAlgebra U) (hV : VectorAlgebra V) :
    VectorAlgebra (U - V) := by
  have he : U - V = U + (-1 : ℝ) • V := by simp [sub_eq_add_neg]
  rw [he]; exact hU.add (hV.scale (-1))

theorem VectorAlgebra.diffusion {U : VectorField} (hU : VectorAlgebra U) :
    VectorAlgebra (laplacian U) := by
  have he : laplacian U = spaceD 0 (spaceD 0 U) + spaceD 1 (spaceD 1 U) +
      spaceD 2 (spaceD 2 U) := by funext t q; exact Fin.sum_univ_three _
  rw [he]
  exact ((hU.spaceDeriv 0).spaceDeriv 0).add
    ((hU.spaceDeriv 1).spaceDeriv 1) |>.add ((hU.spaceDeriv 2).spaceDeriv 2)

theorem VectorAlgebra.selfTransport {U : VectorField} (hU : VectorAlgebra U) :
    VectorAlgebra (advection U) := by
  intro j
  have he : (fun t q => advection U t q j) =
      (fun t q => U t q 0 * spaceD 0 U t q j) +
      (fun t q => U t q 1 * spaceD 1 U t q j) +
      (fun t q => U t q 2 * spaceD 2 U t q j) := by
    funext t q
    simp only [advection, Fin.sum_univ_three, PiLp.add_apply, PiLp.smul_apply, Pi.add_apply, smul_eq_mul]
  rw [he]
  exact ((hU 0).mul (hU.spaceDeriv 0 j)).add
    ((hU 1).mul (hU.spaceDeriv 1 j)) |>.add ((hU 2).mul (hU.spaceDeriv 2 j))

theorem VectorAlgebra.fullForce {U : VectorField} (hU : VectorAlgebra U) (ν : ℝ) :
    VectorAlgebra (Residual.fullForce ν U) := (hU.timeDeriv.add hU.selfTransport).sub (hU.diffusion.scale ν)

theorem norm_le_sum_components (x : Space) : ‖x‖ ≤ ∑ i : Fin 3, ‖x i‖ := by
  have hx : x = ∑ i : Fin 3, EuclideanSpace.single i (x i) := by
    ext j
    fin_cases j <;> simp [Fin.sum_univ_three]
  calc
    ‖x‖ = ‖∑ i : Fin 3, EuclideanSpace.single i (x i)‖ := congrArg norm hx
    _ ≤ ∑ i : Fin 3, ‖EuclideanSpace.single i (x i)‖ := norm_sum_le _ _
    _ = _ := by simp

theorem VectorAlgebra.bound {U : VectorField} (hU : VectorAlgebra U) (J : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ q : Torus, (1 + t) ^ J * ‖U t q‖ ≤ C := by
  choose C hC using fun i => (hU i).bound J
  refine ⟨∑ i : Fin 3, C i, fun t ht q => ?_⟩
  calc
    _ ≤ (1 + t) ^ J * ∑ i : Fin 3, ‖U t q i‖ :=
      mul_le_mul_of_nonneg_left (norm_le_sum_components (U t q)) (by positivity)
    _ = ∑ i : Fin 3, (1 + t) ^ J * ‖U t q i‖ := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hC i t ht q)

theorem iterate_timeD_eq_fullTimeD {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {F : Field A} (hF : ContDiff ℝ ∞ (lifted F)) (r : ℕ) :
    ∀ t : ℝ, 0 ≤ t → ∀ q, timeD^[r] F t q = fullTimeD^[r] F t q := by
  have hsm (k : ℕ) : ContDiff ℝ ∞ (lifted (fullTimeD^[k] F)) := by
    induction k with
    | zero => exact hF
    | succ k ih => rw [Function.iterate_succ_apply']; exact contDiff_fullTimeD ih
  induction r with
  | zero => exact fun _ _ _ => rfl
  | succ r ih =>
    intro t ht q
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rw [timeD_congr_nonneg ih ht]
    exact timeD_eq_fullTimeD (hsm r) ht q

theorem VectorAlgebra.mixed_bound {U : VectorField} (hU : VectorAlgebra U)
    (r J : ℕ) (α : MultiIndex) :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ q : Torus, (1 + t) ^ J * ‖mixedD r α U t q‖ ≤ C := by
  have hsp (V : VectorField) (hV : VectorAlgebra V) (i : Fin 3) (k : ℕ) :
      VectorAlgebra ((spaceD i)^[k] V) := by
    induction k with
    | zero => exact hV
    | succ k ih => rw [Function.iterate_succ_apply']; exact ih.spaceDeriv i
  let V := (spaceD 2)^[α 2] ((spaceD 1)^[α 1] ((spaceD 0)^[α 0] U))
  have hV : VectorAlgebra V := hsp _ (hsp _ (hsp _ hU 0 _) 1 _) 2 _
  have htime : VectorAlgebra (fullTimeD^[r] V) := by
    induction r with
    | zero => exact hV
    | succ r ih => rw [Function.iterate_succ_apply']; exact ih.timeDeriv
  obtain ⟨C, hC⟩ := htime.bound J
  refine ⟨C, fun t ht q => ?_⟩
  change (1 + t) ^ J * ‖timeD^[r] V t q‖ ≤ C
  rw [iterate_timeD_eq_fullTimeD hV.smooth r t ht]
  exact hC t ht q

theorem rapidPair_of_algebra {U G : VectorField} (hU : VectorAlgebra U) (hG : VectorAlgebra G) :
    ∃ C : ℕ → MultiIndex → ℕ → ℕ, RapidPair U G C := by
  have hc (r : ℕ) (α : MultiIndex) (J : ℕ) : ∃ N : ℕ, ∀ t : ℝ, 0 ≤ t →
      spatialSup (mixedD r α U) t + spatialSup (mixedD r α G) t ≤ (N : ℝ) / (1 + t) ^ J := by
    obtain ⟨C, hC⟩ := hU.mixed_bound r J α
    obtain ⟨D, hD⟩ := hG.mixed_bound r J α
    obtain ⟨N, hN⟩ := exists_nat_ge (C + D)
    refine ⟨N, fun t ht => ?_⟩
    have hpos : 0 < (1 + t) ^ J := by positivity
    have hsup {F : VectorField} {B : ℝ} (hF : ∀ q, (1 + t) ^ J * ‖F t q‖ ≤ B) :
        spatialSup F t ≤ B / (1 + t) ^ J := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨q, rfl⟩
      exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hF q)
    calc
      _ ≤ C / (1 + t) ^ J + D / (1 + t) ^ J := add_le_add (hsup (hC t ht)) (hsup (hD t ht))
      _ = (C + D) / (1 + t) ^ J := (add_div _ _ _).symm
      _ ≤ _ := div_le_div_of_nonneg_right hN hpos.le
  choose C hC using hc
  exact ⟨C, fun r J α t ht => hC r α J t ht⟩

end RapidCalculus

namespace FluidLift
open scoped ContDiff
open RapidCalculus

theorem velocity_algebra (d : Input) (hd : d.WellFormed) : VectorAlgebra (velocity d) := by
  intro i
  have hs := boundedProfile_of_periodic slope_contDiff slope_periodic
  have he := boundedProfile_of_periodic eta_contDiff eta_periodic
  fin_cases i
  · exact Algebra.tensor _ _ _ (a_rapid2 d hd) hs (fun t x => by simp)
  · exact Algebra.tensor _ _ _ (b_rapid2 d hd) hs (fun t x => by simp)
  · exact Algebra.tensor _ _ _ ((b_rapid2 d hd).biD false) he.neg (fun t x => by simp [bdy, biD])

theorem force_rapid (ν : ℝ) (d : Input) (hd : d.WellFormed) :
    ∃ C : ℕ → MultiIndex → ℕ → ℕ, RapidPair (velocity d) (force ν d) C :=
  rapidPair_of_algebra (velocity_algebra d hd) ((velocity_algebra d hd).fullForce ν)

end FluidLift

end
end PeriodicLattice

end OAI
