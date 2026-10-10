import OAI.NumberTheory.JointDickman.Probability.RootSiteLaw

namespace OAI

/-! # The exact finite-residue law at every site of a block -/

namespace JointDickman
open Finset

noncomputable def rootHitType {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} (root : ι → ZMod p) (r : ZMod p) : I.powerset :=
  ⟨rootHitSet I root r, mem_powerset.mpr (filter_subset _ _)⟩

theorem root_site_pushMass {ι : Type*} [DecidableEq ι]
    (I : Finset ι) {p : ℕ} [NeZero p] (root : ι → ZMod p)
    (hinj : Set.InjOn root I) :
    finitePushMass (fun (_ : ZMod p) => 1/(p : ℝ)) (rootHitType I root) =
      fun S => categoricalSubsetMass I (fun _ => 1/(p : ℝ)) S.val := by
  classical
  funext S
  have h := root_site_uniform_mean I root hinj
    (fun R => if R = S.val then (1 : ℝ) else 0)
  have hr : (∑ R ∈ I.powerset, categoricalSubsetMass I (fun _ => 1/(p : ℝ)) R *
      (if R = S.val then (1 : ℝ) else 0)) =
      categoricalSubsetMass I (fun _ => 1/(p : ℝ)) S.val := by
    simp only [mul_ite, mul_one, mul_zero]
    exact sum_ite_eq' I.powerset S.val _ |>.trans (ite_eq_left S.property)
  rw [hr] at h
  simpa only [finitePushMass, rootHitType, Subtype.ext_iff, sum_div,
    ite_div, zero_div] using h

noncomputable def blockSiteRoot (M p : ℕ) (i : Fin M) : ZMod p :=
  -((i.val+1 : ℕ) : ZMod p)

theorem blockSiteRoot_injective (M p : ℕ) (hp : M < p) :
    Function.Injective (blockSiteRoot M p) := by
  intro i k hik
  have hcast : ((i.val+1 : ℕ) : ZMod p) = ((k.val+1 : ℕ) : ZMod p) :=
    neg_injective hik
  have hv := congrArg ZMod.val hcast
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
  apply Fin.ext
  omega

noncomputable def blockPrimeHit (M p : ℕ) (r : ZMod p) : (univ : Finset (Fin M)).powerset :=
  rootHitType univ (blockSiteRoot M p) r

theorem blockPrimeHit_divisibility (M p n : ℕ) (i : Fin M) :
    i ∈ (blockPrimeHit M p (n : ZMod p)).val ↔ p ∣ n+(i.val+1) := by
  change (i ∈ rootHitSet univ (blockSiteRoot M p) (n : ZMod p)) ↔ _
  unfold rootHitSet
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, blockSiteRoot]
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_add, Nat.cast_one]
  constructor
  · intro h
    rw [← h]
    ring
  · intro h
    exact (eq_neg_of_add_eq_zero_left h).symm

theorem blockPrimeHit_pushMass (M p : ℕ) [NeZero p] (hp : M < p) :
    finitePushMass (fun (_ : ZMod p) => 1/(p : ℝ)) (blockPrimeHit M p) =
      fun S => categoricalSubsetMass univ (fun _ : Fin M => 1/(p : ℝ)) S.val :=
  root_site_pushMass univ (blockSiteRoot M p)
    (fun _ _ _ _ h => blockSiteRoot_injective M p hp h)

end JointDickman

end OAI
