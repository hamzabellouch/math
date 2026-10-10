import Mathlib

namespace OAI

/-! Degree exclusions, separated filtrations, kernel obstructions, and contraction of semilinear homogeneous cochains. -/

namespace NamedPrimeFiveSupport

theorem no_incoming_monomial
    (r : ℤ) (hr : 2 ≤ r) (a b : ℕ) (ha : a ≤ 1) (l : ℤ) :
    ¬ ((a : ℤ) + 2 * b = 32 - r ∧
       8 * (a : ℤ) + 40 * b + 160 * l = 641 - r) := by
  rintro ⟨hs, hq⟩
  have hab : (a : ℤ) ≤ 1 := by exact_mod_cast ha
  have ha0 : 0 ≤ (a : ℤ) := by omega
  have hb0 : 0 ≤ (b : ℤ) := by omega
  omega

theorem incoming_congruence (r l : ℤ) (h : 160 * l = 13 + 19 * r) :
    r % 160 = 33 := by
  omega

theorem no_incoming_odd_degree (r l : ℤ) (hr : 3 ≤ r) (hr' : r ≤ 31) :
    160 * l ≠ 13 + 19 * r := by
  intro h
  have := incoming_congruence r l h
  omega

theorem filtration_zero_source_is_odd : Odd (641 - 32 : ℤ) := by
  norm_num

theorem source_filtration_zero (r : ℤ) (h : 32 - r = 0) :
    r = 32 ∧ Odd (641 - r) := by
  have hr : r = 32 := by omega
  exact ⟨hr, hr ▸ filtration_zero_source_is_odd⟩

theorem power_degrees :
    (38 * 16 : ℕ) = 608 ∧ (40 * 16 : ℕ) = 640 ∧
      (2 * 16 : ℕ) = 32 ∧ (640 - 32 : ℤ) = 608 := by
  norm_num

section Filtration

variable {L : Type*} [CompleteLattice L]

theorem tail_eq_bot {F : ℕ → L} (hmono : Antitone F)
    (hsep : (⨅ s, F s) = ⊥) {N : ℕ}
    (hstable : ∀ s, N ≤ s → F s = F (s + 1)) :
    F N = ⊥ := by
  have hc (d : ℕ) : F (N + d) = F N := by
    induction d with
    | zero => simp
    | succ d ih =>
      exact (hstable (N + d) (by omega)).symm.trans ih
  apply le_antisymm _ bot_le
  rw [← hsep]
  apply le_iInf
  intro s
  rcases le_total s N with hs | hs
  · exact hmono hs
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
    exact (hc d).ge

theorem later_eq_bot {F : ℕ → L} (hmono : Antitone F)
    (hsep : (⨅ s, F s) = ⊥) {N : ℕ}
    (hstable : ∀ s, N ≤ s → F s = F (s + 1))
    {s : ℕ} (hs : N ≤ s) : F s = ⊥ := by
  apply le_antisymm _ bot_le
  calc
    F s ≤ F N := hmono hs
    _ = ⊥ := tail_eq_bot hmono hsep hstable

end Filtration

section FilteredPowers

variable {R : Type*} [Ring R]

theorem power_mem (F : ℕ → AddSubgroup R)
    (hone : (1 : R) ∈ F 0)
    (hmul : ∀ {i j : ℕ} {x y : R}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j))
    {s : ℕ} {x : R} (hx : x ∈ F s) (n : ℕ) :
    x ^ n ∈ F (s * n) := by
  induction n with
  | zero => simpa using hone
  | succ n ih => simpa only [pow_succ, Nat.mul_succ] using hmul ih hx

theorem sixteenth_power_zero_of_filtration
    (F : ℕ → AddSubgroup R) (hmono : Antitone F)
    (hsep : (⨅ s, F s) = ⊥)
    (hstable : ∀ s, 27 ≤ s → F s = F (s + 1))
    (hone : (1 : R) ∈ F 0)
    (hmul : ∀ {i j : ℕ} {x y : R}, x ∈ F i → y ∈ F j → x * y ∈ F (i + j))
    {x : R} (hx : x ∈ F 2) : x ^ 16 = 0 := by
  have hmem := power_mem F hone hmul hx 16
  have hbot : F (2 * 16) = ⊥ := later_eq_bot hmono hsep hstable (by norm_num)
  rw [hbot] at hmem
  exact hmem

end FilteredPowers

section Kernel

variable {A B : Type*} [AddGroup A] [AddGroup B]

theorem no_left_inverse (f : A →+ B) {x : A}
    (hx : x ≠ 0) (hfx : f x = 0) :
    ¬ ∃ r : B → A, Function.LeftInverse r f := by
  rintro ⟨r, hr⟩
  apply hx
  apply hr.injective
  exact hfx.trans (map_zero f).symm

variable {S D U T : Type*}
    [AddGroup S] [AddGroup D] [AddGroup U] [AddGroup T]

theorem kernel_from_factorization
    (c : S →+ A) (d : S →+ D) (v : A →+ D)
    (u : S →+ U) (j : U →+ T) (i : A →+ T)
    (hfactor : v.comp c = d) (hsquare : i.comp c = j.comp u)
    {z : S} (hd : d z ≠ 0) (hu : u z = 0) :
    c z ≠ 0 ∧ i (c z) = 0 ∧
      ¬ ∃ r : T → A, Function.LeftInverse r i := by
  have hcz : c z ≠ 0 := by
    intro hz
    apply hd
    have h := DFunLike.congr_fun hfactor z
    simpa [hz] using h.symm
  have hic : i (c z) = 0 := by
    have h := DFunLike.congr_fun hsquare z
    simpa [hu] using h
  exact ⟨hcz, hic, no_left_inverse i hcz hic⟩

end Kernel

open CategoryTheory

theorem no_retraction_of_detected_kernel
    {C : Type*} [Category C] (P : C ⥤ AddCommGrpCat)
    {A B : C} (f : A ⟶ B) {z : P.obj A}
    (hz : z ≠ 0) (hfz : P.map f z = 0) :
    ¬ ∃ r : B ⟶ A, f ≫ r = 𝟙 A := by
  rintro ⟨r, hr⟩
  apply hz
  have h := congrArg (fun k : A ⟶ A => P.map k z) hr
  simpa [hfz] using h.symm

end NamedPrimeFiveSupport

noncomputable section
namespace SemilinearTraceSupport

open Finset

variable {Q W P : Type*} [Group Q] [Fintype Q]
    [CommRing W] [AddCommGroup P] [Module W P]
    [MulSemiringAction Q W] [DistribMulAction Q P]
    [SMulDistribClass Q W P]

abbrev Cochain (Q P : Type*) (n : ℕ) := (Fin (n + 1) → Q) → P

def delta {n : ℕ} (f : Cochain Q P n) : Cochain Q P (n + 1) :=
  fun gs => ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • f (gs ∘ i.succAbove)

def Equivariant {n : ℕ} (f : Cochain Q P n) : Prop :=
  ∀ (g : Q) (gs : Fin (n + 1) → Q), f (fun i => g * gs i) = g • f gs

def contract (w : W) {n : ℕ} (f : Cochain Q P (n + 1)) : Cochain Q P n :=
  fun gs => ∑ g : Q, (g • w) • f (Fin.cons g gs)

omit [Group Q] [Fintype Q] [DistribMulAction Q P] in
lemma delta_cons {n : ℕ} (f : Cochain Q P (n + 1)) (g : Q)
    (gs : Fin (n + 2) → Q) :
    delta f (Fin.cons g gs) =
      f gs - ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • f (Fin.cons g (gs ∘ i.succAbove)) := by
  rw [delta, Fin.sum_univ_succ]
  have h₀ : Fin.cons g gs ∘ (0 : Fin (n + 3)).succAbove = gs := by
    funext i
    simp
  rw [h₀]
  simp only [Fin.val_zero, pow_zero, one_zsmul, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fin.val_succ, pow_succ, mul_neg_one, neg_smul]
  congr 2
  apply congrArg f
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp
  · simp

omit [Fintype Q] in

theorem delta_equivariant {n : ℕ} {f : Cochain Q P n} (hf : Equivariant f) :
    Equivariant (delta f) := by
  intro g gs
  simp only [delta, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change (-1 : ℤ) ^ i.val • f (fun j => g * gs (i.succAbove j)) = _
  rw [hf]
  exact smul_comm _ _ _

theorem contract_equivariant (w : W) {n : ℕ} {f : Cochain Q P (n + 1)}
    (hf : Equivariant f) : Equivariant (contract w f) := by
  intro q gs
  dsimp only [contract]
  rw [← Equiv.sum_comp (Equiv.mulLeft q)
    (fun g : Q => (g • w) • f (Fin.cons g (fun i => q * gs i)))]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  have he : (Fin.cons (q * g) (fun i => q * gs i) : Fin (n + 2) → Q) =
      fun i => q * (Fin.cons g gs : Fin (n + 2) → Q) i := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  change ((q * g) • w) • f (Fin.cons (q * g) (fun i => q * gs i)) = _
  rw [he, hf, mul_smul]
  exact (smul_distrib_smul q (g • w) (f (Fin.cons g gs))).symm

omit [SMulDistribClass Q W P] [DistribMulAction Q P] in

theorem contract_identity (w : W) (hw : ∑ g : Q, g • w = 1)
    {n : ℕ} (f : Cochain Q P (n + 1)) (gs : Fin (n + 2) → Q) :
    delta (contract w f) gs + contract w (delta f) gs = f gs := by
  have h : contract w (delta f) gs = f gs - delta (contract w f) gs := by
    simp only [contract, delta_cons, smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hw, one_smul]
    congr 1
    simp only [delta, contract, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro g hg
    exact smul_comm _ _ _
  rw [h]
  abel

theorem equivariant_cocycle_is_boundary (w : W) (hw : ∑ g : Q, g • w = 1)
    {n : ℕ} (f : Cochain Q P (n + 1)) (hf : Equivariant f)
    (hc : delta f = 0) :
    ∃ b : Cochain Q P n, Equivariant b ∧ delta b = f := by
  refine ⟨contract w f, contract_equivariant w hf, ?_⟩
  funext gs
  have h := contract_identity w hw f gs
  simpa [hc, contract] using h

end SemilinearTraceSupport

end

end OAI
