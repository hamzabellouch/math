import OAI.Analysis.PeriodicLattice.Energy

namespace OAI

/-! Iterated derivatives of periodic fields and tensor profiles. -/

namespace PeriodicLattice

local instance finiteFunctionEncodingDerivativeWords {n : ℕ} {A : Type*} [Encodable A] :
    Encodable (Fin n → A) := Encodable.finArrow

noncomputable section

namespace FluidLift

theorem force_classical_unique (ν : ℝ) (hν : 0 ≤ ν) (d : Input) :
    UniqueClassical ν (force ν d) (velocity d) 0 :=
  TorusCalculus.classical_unique hν (classical_solution ν d)

end FluidLift

namespace RapidCalculus

open Set Filter Topology
open scoped ContDiff

section TwoVariables
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

def biD (i : Bool) (F : ℝ → ℝ → A) : ℝ → ℝ → A :=
  if i then fun t y => deriv (fun s => F s y) t else fun t y => deriv (F t) y

def wordD (w : List Bool) (F : ℝ → ℝ → A) : ℝ → ℝ → A :=
  w.foldr biD F

@[simp] theorem wordD_nil (F : ℝ → ℝ → A) : wordD [] F = F := rfl
@[simp] theorem wordD_cons (i : Bool) (w : List Bool) (F : ℝ → ℝ → A) :
    wordD (i :: w) F = biD i (wordD w F) := rfl

theorem wordD_append (w v : List Bool) (F : ℝ → ℝ → A) :
    wordD (w ++ v) F = wordD w (wordD v F) := List.foldr_append

theorem partial_contDiff {F : ℝ → ℝ → A}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (i : Bool) :
    ContDiff ℝ ∞ (Function.uncurry (biD i F)) := by
  cases i
  · exact TorusCalculus.contDiff_partial hF
  · have h := TorusCalculus.contDiff_partial (v := fun y t => F t y)
      (hF.comp (contDiff_snd.prodMk contDiff_fst))
    exact h.comp (contDiff_snd.prodMk contDiff_fst)

theorem wordD_contDiff {F : ℝ → ℝ → A}
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (w : List Bool) :
    ContDiff ℝ ∞ (Function.uncurry (wordD w F)) := by
  induction w with
  | nil => exact hF
  | cons i w ih => exact partial_contDiff ih i

theorem wordD_eventuallyEq {F G : ℝ → ℝ → A} {t : ℝ}
    (h : F =ᶠ[𝓝 t] G) (w : List Bool) : wordD w F =ᶠ[𝓝 t] wordD w G := by
  induction w with
  | nil => exact h
  | cons i w ih =>
    cases i
    · filter_upwards [ih] with s hs
      funext y
      simp only [wordD_cons, biD, Bool.false_eq_true, ↓reduceIte, hs]
    · filter_upwards [eventually_eventually_nhds.mpr ih] with s hs
      funext y
      have he : (fun u => wordD w F u y) =ᶠ[𝓝 s] (fun u => wordD w G u y) :=
        hs.mono fun u hu => congrFun hu y
      exact he.deriv_eq

theorem wordD_tensor (p : ℝ → ℝ) (V : ℝ → A)
    (hp : ContDiff ℝ ∞ p) (hV : ContDiff ℝ ∞ V) (w : List Bool) :
    wordD w (fun t y => p t • V y) =
      fun t y => iteratedDeriv (w.count true) p t • iteratedDeriv (w.count false) V y := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [wordD_cons, ih]
    have hp' : ContDiff ℝ ∞ (iteratedDeriv (w.count true) p) := by
      rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv _ hp
    have hV' : ContDiff ℝ ∞ (iteratedDeriv (w.count false) V) := by
      rw [iteratedDeriv_eq_iterate]; exact ContDiff.iterate_deriv _ hV
    funext t y
    cases i
    · simpa [biD, List.count_cons, iteratedDeriv_succ, Pi.smul_def] using
        (((hV'.differentiable (by simp) y).hasDerivAt).const_smul (iteratedDeriv (w.count true) p t)).deriv
    · simpa [biD, List.count_cons, iteratedDeriv_succ, Pi.smul_def] using
        (((hp'.differentiable (by simp) t).hasDerivAt).smul_const (iteratedDeriv (w.count false) V y)).deriv

theorem wordD_schedule (V : ℕ → ℝ → A) (hV : ∀ n, ContDiff ℝ ∞ (V n))
    (w : List Bool) (n : ℕ) {t : ℝ} (ht : (n : ℝ) ≤ t) (ht' : t ≤ n + 1)
    (y : ℝ) :
    wordD w (Profiles.schedule V) t y =
      Profiles.mixedPartial (w.count true) (w.count false) (Profiles.schedule V) t y := by
  rw [Profiles.schedule_mixedPartial V _ _ n ht ht']
  have he := wordD_eventuallyEq (Profiles.schedule_eventually_on_slot V n ht ht') w
  rw [congrFun he.eq_of_nhds y, wordD_tensor _ _ (Profiles.pulse_contDiff n) (hV n)]

structure Rapid2 (F : ℝ → ℝ → A) : Prop where
  smooth : ContDiff ℝ ∞ (Function.uncurry F)
  bound : ∀ (w : List Bool) (J : ℕ), ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ y : ℝ,
    (1 + t) ^ J * ‖wordD w F t y‖ ≤ C

theorem Rapid2.biD {F : ℝ → ℝ → A} (hF : Rapid2 F) (i : Bool) :
    Rapid2 (biD i F) := by
  refine ⟨partial_contDiff hF.smooth i, fun w J => ?_⟩
  simpa only [wordD_append, wordD_cons, wordD_nil] using hF.bound (w ++ [i]) J

end TwoVariables

theorem wordD_pair (F G : ℝ → ℝ → ℝ)
    (hF : ContDiff ℝ ∞ (Function.uncurry F)) (hG : ContDiff ℝ ∞ (Function.uncurry G))
    (w : List Bool) :
    wordD w (fun t y => (F t y, G t y)) = fun t y => (wordD w F t y, wordD w G t y) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [wordD_cons, ih]
    have hhF := wordD_contDiff hF w
    have hhG := wordD_contDiff hG w
    funext t y
    cases i
    · exact (((hhF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y).hasDerivAt.prodMk
        ((hhG.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) y).hasDerivAt).deriv
    · exact (((hhF.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t).hasDerivAt.prodMk
        ((hhG.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) t).hasDerivAt).deriv

end RapidCalculus

namespace FluidLift
open scoped ContDiff
open RapidCalculus Profiles

theorem v_rapid2 (d : Input) (hd : d.WellFormed) : Rapid2 (v d) := by
  refine ⟨v_contDiff d, fun w J => ?_⟩
  let F : ℕ → ℤ → ℝ := fun n j => CompilerPlanar.nextTable d n j
  let H : ℕ → ℤ → ℝ := fun n j => if CompilerPlanar.haltTable d n j then 1 else 0
  have hF (n : ℕ) (j : ℤ) : |F n j| ≤ (Scales.capacity (CompilerPlanar.radix d) d.word.length (n + 1) : ℝ) := by
    simpa only [F, Nat.abs_cast] using
      (Nat.cast_le.mpr (CompilerPlanar.nextTable_bound d hd n j).le :
        (CompilerPlanar.nextTable d n j : ℝ) ≤ _)
  have hH (n : ℕ) (j : ℤ) : |H n j| ≤ 1 := by dsimp [H]; split_ifs <;> norm_num
  obtain ⟨C, hC⟩ := Planar.field_rapid (CompilerPlanar.radix_ge_two d) d.word.length
    (CompilerPlanar.loadingCode d) (w.count true) (w.count false) J F H hF hH
  refine ⟨C, fun t ht y => ?_⟩
  let V := Planar.coefficients (CompilerPlanar.radix d) d.word.length (CompilerPlanar.loadingCode d) F H
  have hV (n : ℕ) : ContDiff ℝ ∞ (V n) := by
    cases n with
    | zero => exact contDiff_const
    | succ n => exact Planar.slot_contDiff _ _ _ _ _
  change (1 + t) ^ J * ‖wordD w (schedule V) t y‖ ≤ (C : ℝ)
  rw [wordD_schedule V hV w ⌊t⌋₊ (Nat.floor_le ht) (Nat.lt_floor_add_one t).le]
  simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < (1 + t) ^ J)).mp (hC t ht y)

theorem a_rapid2 (d : Input) (hd : d.WellFormed) : Rapid2 (a d) := by
  refine ⟨a_contDiff d, fun w J => ?_⟩
  obtain ⟨C, hC⟩ := (v_rapid2 d hd).bound w J
  refine ⟨C, fun t ht y => ?_⟩
  have he : wordD w (v d) = fun t y => (wordD w (a d) t y, wordD w (b d) t y) :=
    wordD_pair _ _ (a_contDiff d) (b_contDiff d) w
  have hn : ‖wordD w (a d) t y‖ ≤ ‖wordD w (v d) t y‖ := by
    rw [he]; exact norm_fst_le (wordD w (a d) t y, wordD w (b d) t y)
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans (hC t ht y)

theorem b_rapid2 (d : Input) (hd : d.WellFormed) : Rapid2 (b d) := by
  refine ⟨b_contDiff d, fun w J => ?_⟩
  obtain ⟨C, hC⟩ := (v_rapid2 d hd).bound w J
  refine ⟨C, fun t ht y => ?_⟩
  have he : wordD w (v d) = fun t y => (wordD w (a d) t y, wordD w (b d) t y) :=
    wordD_pair _ _ (a_contDiff d) (b_contDiff d) w
  have hn : ‖wordD w (b d) t y‖ ≤ ‖wordD w (v d) t y‖ := by
    rw [he]; exact norm_snd_le (wordD w (a d) t y, wordD w (b d) t y)
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans (hC t ht y)

end FluidLift

end
end PeriodicLattice

end OAI
