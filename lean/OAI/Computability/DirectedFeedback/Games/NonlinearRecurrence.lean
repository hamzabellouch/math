import Mathlib
import OAI.Computability.DirectedFeedback.Probability.DescentProbability

namespace OAI

namespace DFVSGames.Gadget.EmbeddedConditional

open scoped BigOperators

variable {k P R B Z M : Type*} [Ring k]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup B] [Module k B] [Fintype B]
variable [AddCommMonoid M] [Module ℚ≥0 M]

theorem expect_uniform_output_embedded (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (D : P → Z) (hD : ∀ u h, D (u + e h) = D u)
    (f : B → Z → M) :
    (𝔼 u, f (C u) (D u)) = 𝔼 u, 𝔼 b : B, f b (D u) := by
  classical
  have hs (b : B) :
      (𝔼 u, f (C u + b) (D u)) = 𝔼 u, f (C u) (D u) := by
    obtain ⟨h, rfl⟩ := hlam b
    apply Fintype.expect_equiv (Equiv.addRight (e h))
    intro u
    simp only [Equiv.coe_addRight, hC, hD]
  calc
    (𝔼 u, f (C u) (D u)) = 𝔼 b : B, 𝔼 u, f (C u + b) (D u) := by
      simp only [hs, Fintype.expect_const]
    _ = 𝔼 u, 𝔼 b : B, f (C u + b) (D u) := Finset.expect_comm _ _ _
    _ = 𝔼 u, 𝔼 b : B, f b (D u) := by
      apply Finset.expect_congr rfl
      intro u _
      apply Fintype.expect_equiv (Equiv.addLeft (C u))
      intro b
      rfl

theorem expect_equivariant_output (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h) (f : B → M) :
    (𝔼 u, f (C u)) = 𝔼 b : B, f b := by
  have he := expect_uniform_output_embedded e lam hlam C hC
    (fun _ => ()) (fun _ _ => rfl) (fun b _ => f b)
  simpa only [Fintype.expect_const] using he

theorem expect_linear_surjective (f : P →ₗ[k] B) (hf : Function.Surjective f)
    (test : B → M) : (𝔼 u, test (f u)) = 𝔼 b : B, test b := by
  apply expect_equivariant_output (LinearMap.id : P →ₗ[k] P) f hf f
  intro u h
  exact f.map_add u h

theorem expect_uniform_difference_embedded (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h) (a : P) (f : B → B → M) :
    (𝔼 u, f (C u) (C (u + a) - C u)) =
      𝔼 u, 𝔼 b : B, f b (C (u + a) - C u) := by
  apply expect_uniform_output_embedded e lam hlam C hC
  intro u h
  have he : u + e h + a = (u + a) + e h := by
    simp only [add_assoc, add_comm (e h) a]
  rw [he, hC, hC, add_sub_add_right_eq_sub]

end DFVSGames.Gadget.EmbeddedConditional

namespace DFVSGames.Gadget.NonlinearRecurrence

open scoped BigOperators

variable {k I P R X B : Type*} [CommRing k]
variable [Fintype I] [DecidableEq I]
variable [AddCommGroup P] [Module k P] [Fintype P]
variable [AddCommGroup R] [Module k R]
variable [AddCommGroup X] [Module k X] [Fintype X]
variable [AddCommGroup B] [Module k B] [Fintype B] [DecidableEq B]

def change (F : X × B → B) (p d : X × B) : ℚ :=
  if F (p + d) ≠ F p then 1 else 0

omit [Fintype X] [Fintype B] in
@[simp] theorem change_zero (F : X × B → B) (p : X × B) : change F p 0 = 0 := by
  simp [change]

omit [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] in
theorem compLeft_surjective (lam : R →ₗ[k] B) (hlam : Function.Surjective lam) :
    Function.Surjective (lam.compLeft I) := by
  intro b
  choose h hh using fun i => hlam (b i)
  exact ⟨h, funext hh⟩

omit [Fintype X] [Fintype B] [DecidableEq B] in
theorem aggregate_single (J : I → B →ₗ[k] X × B) (i : I) (b : B) :
    aggregate J (Pi.single i b) = J i b := by
  classical
  change (∑ j, J j ((Pi.single i b : I → B) j)) = J i b
  simp only [LinearMap.apply_single]
  simp

omit [Fintype I] [Fintype P] [Fintype B] [DecidableEq B] in
theorem child_outputs_perturb (C : P → B) (u : I → P) (i : I) (a : P) :
    (fun j => C ((u + (Pi.single i a : I → P)) j)) =
      (fun j => C (u j)) + (Pi.single i (C (u i + a) - C (u i)) : I → B) := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Pi.add_apply, Pi.single_eq_same]
    rw [add_comm (C (u i)), sub_add_cancel]
  · simp [Pi.single_eq_of_ne hj]

omit [Module k P] in
omit [Fintype P] [Fintype X] [Fintype B] [DecidableEq B] in
theorem parent_output_perturb (J : I → B →ₗ[k] X × B) (C : P → B)
    (F : X × B → B) (u : I → P) (i : I) (a : P) :
    F (aggregate J (fun j => C ((u + (Pi.single i a : I → P)) j))) =
      F (aggregate J (fun j => C (u j)) + J i (C (u i + a) - C (u i))) := by
  rw [child_outputs_perturb, map_add, aggregate_single]

theorem expect_change_at_index (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (e : R →ₗ[k] P) (lam : R →ₗ[k] B)
    (hlam : Function.Surjective lam) (C : P → B)
    (hC : ∀ u h, C (u + e h) = C u + lam h)
    (F : X × B → B) (i : I) (a : P) :
    (𝔼 u : I → P,
      change F (aggregate J (fun j => C (u j))) (J i (C (u i + a) - C (u i)))) =
      𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + a) - C x)) := by
  have hCt : ∀ (u : I → P) (h : I → R),
      (fun j => C ((u + (e.compLeft I) h) j)) =
        (fun j => C (u j)) + (lam.compLeft I) h := by
    intro u h
    funext j
    exact hC (u j) (h j)
  have hDt : ∀ (u : I → P) (h : I → R),
      C ((u + (e.compLeft I) h) i + a) - C ((u + (e.compLeft I) h) i) =
        C (u i + a) - C (u i) := by
    intro u h
    change C (u i + e (h i) + a) - C (u i + e (h i)) = _
    have he : u i + e (h i) + a = (u i + a) + e (h i) := by
      simp only [add_assoc, add_comm (e (h i)) a]
    rw [he, hC, hC, add_sub_add_right_eq_sub]
  calc
    _ = 𝔼 u : I → P, 𝔼 b : I → B,
        change F (aggregate J b) (J i (C (u i + a) - C (u i))) :=
      EmbeddedConditional.expect_uniform_output_embedded
        (e.compLeft I) (lam.compLeft I) (compLeft_surjective lam hlam)
        (fun u j => C (u j)) hCt (fun u => C (u i + a) - C (u i)) hDt
        (fun b d => change F (aggregate J b) (J i d))
    _ = 𝔼 u : I → P, 𝔼 z : X × B,
        change F z (J i (C (u i + a) - C (u i))) := by
      apply Finset.expect_congr rfl
      intro u _
      exact EmbeddedConditional.expect_linear_surjective (aggregate J) hJ
        (fun z => change F z (J i (C (u i + a) - C (u i))))
    _ = 𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + a) - C x)) := by
      exact EmbeddedConditional.expect_linear_surjective
        (LinearMap.proj i : (I → P) →ₗ[k] P)
        (fun x => ⟨fun _ => x, rfl⟩)
        (fun x : P => 𝔼 z : X × B, change F z (J i (C (x + a) - C x)))

omit [DecidableEq I] in

theorem kernel_all (J : I → B →ₗ[k] X × B) (F : X × B → B) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 → (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ)
    (d : B) :
    (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ * (if d ≠ 0 then 1 else 0) := by
  classical
  by_cases hd : d = 0
  · simp [hd]
  · simp only [ite_eq_left hd, mul_one]
    exact hk d hd

theorem parent_change_recurrence {N : Type*} [Fintype N]
    (J : I → B →ₗ[k] X × B) (hJ : Function.Surjective (aggregate J))
    (e : R →ₗ[k] P) (lam : R →ₗ[k] B) (hlam : Function.Surjective lam)
    (C : P → B) (hC : ∀ u h, C (u + e h) = C u + lam h)
    (F : X × B → B) (noise : N → P) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 → (𝔼 i, 𝔼 z : X × B, change F z (J i d)) = ρ) :
    (𝔼 i, 𝔼 n : N, 𝔼 u : I → P,
      if F (aggregate J (fun j => C ((u + (Pi.single i (noise n) : I → P)) j))) ≠
        F (aggregate J (fun j => C (u j))) then (1 : ℚ) else 0) =
      ρ * (𝔼 n : N, 𝔼 x : P, if C (x + noise n) ≠ C x then (1 : ℚ) else 0) := by
  classical
  have hpoint (i : I) (n : N) :
      (𝔼 u : I → P,
        if F (aggregate J (fun j => C ((u + (Pi.single i (noise n) : I → P)) j))) ≠
          F (aggregate J (fun j => C (u j))) then (1 : ℚ) else 0) =
        𝔼 x : P, 𝔼 z : X × B, change F z (J i (C (x + noise n) - C x)) := by
    simp_rw [parent_output_perturb]
    exact expect_change_at_index J hJ e lam hlam C hC F i (noise n)
  simp_rw [hpoint]
  rw [Finset.expect_comm]
  calc
    _ = 𝔼 n : N, 𝔼 x : P, 𝔼 i,
        𝔼 z : X × B, change F z (J i (C (x + noise n) - C x)) := by
      apply Finset.expect_congr rfl
      intro n _
      exact Finset.expect_comm _ _ _
    _ = 𝔼 n : N, 𝔼 x : P,
        ρ * (if C (x + noise n) ≠ C x then (1 : ℚ) else 0) := by
      apply Finset.expect_congr rfl
      intro n _
      apply Finset.expect_congr rfl
      intro x _
      simpa only [ne_eq, sub_eq_zero] using kernel_all J F ρ hk (C (x + noise n) - C x)
    _ = _ := by simp only [← Finset.mul_expect]

end DFVSGames.Gadget.NonlinearRecurrence

namespace DFVSGames.Gadget.StageNoiseRecurrence

open scoped BigOperators

noncomputable def average {A : Type*} [Finite A] (f : A → ℚ) : ℚ :=
  letI := Fintype.ofFinite A
  𝔼 a, f a

theorem average_eq_expect {A : Type*} [Fintype A] (f : A → ℚ) :
    average f = 𝔼 a, f a := by
  have he : Fintype.ofFinite A = ‹Fintype A› := Subsingleton.elim _ _
  unfold average
  rw [he]

universe u v

variable {k : Type u} {B : Type v} [CommRing k] [AddCommGroup B] [Module k B]

noncomputable def error (s : Stage k B) : ℚ := by
  classical
  exact average (fun n : s.Noise => average (fun u : s.Input =>
    if s.output (u + s.noise n) ≠ s.output u then 1 else 0))

theorem error_eq_expect [DecidableEq B] (s : Stage k B) [Fintype s.Input] [Fintype s.Noise] :
    error s = 𝔼 n : s.Noise, 𝔼 u : s.Input,
      if s.output (u + s.noise n) ≠ s.output u then (1 : ℚ) else 0 := by
  classical
  simp only [error, average_eq_expect]
  apply Finset.expect_congr rfl
  intro n _
  apply Finset.expect_congr rfl
  intro u _
  split_ifs <;> rfl

variable [Fintype B] [DecidableEq B]

theorem base_error : error (Stage.base (k := k) (B := B)) =
    1 - 1 / (Fintype.card B : ℚ) := by
  classical
  let : Fintype (Stage.base (k := k) (B := B)).Input := ‹Fintype B›
  let : Fintype (Stage.base (k := k) (B := B)).Noise := ‹Fintype B›
  rw [error_eq_expect]
  change (𝔼 a : B, 𝔼 u : B, if u + a ≠ u then (1 : ℚ) else 0) = _
  have hpoint (a u : B) : (u + a ≠ u) ↔ a ≠ 0 := by
    constructor
    · intro h ha
      exact h (by rw [ha, add_zero])
    · intro ha h
      apply ha
      exact add_left_cancel (show u + a = u + 0 by simpa only [add_zero] using h)
  simp_rw [hpoint, Fintype.expect_const]
  calc
    (𝔼 a : B, if a ≠ 0 then (1 : ℚ) else 0) =
        𝔼 a : B, (1 - if a = 0 then (1 : ℚ) else 0) := by
      apply Finset.expect_congr rfl
      intro a _
      by_cases ha : a = 0 <;> simp [ha]
    _ = 1 - (𝔼 a : B, if a = 0 then (1 : ℚ) else 0) := by
      rw [Finset.expect_sub_distrib, Fintype.expect_const]
    _ = _ := by simp []

variable {I X : Type v} [Fintype I] [DecidableEq I] [Nonempty I]
variable [AddCommGroup X] [Module k X] [Fintype X]

theorem next_error (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 →
      (𝔼 i, 𝔼 z : X × B,
        NonlinearRecurrence.change (fun p => p.2 + Q p.1) z (J i d)) = ρ)
    (s : Stage k B) : error (Stage.next J hJ Q s) = ρ * error s := by
  classical
  let := Fintype.ofFinite s.Input
  let := Fintype.ofFinite s.Noise
  let : Fintype (Stage.next J hJ Q s).Input := inferInstanceAs (Fintype (I → s.Input))
  let : Fintype (Stage.next J hJ Q s).Noise := inferInstanceAs (Fintype (I × s.Noise))
  simp only [error_eq_expect]
  change (𝔼 t : I × s.Noise, 𝔼 u : I → s.Input,
    if parentOutput J s.output Q (u + (Pi.single t.1 (s.noise t.2) : I → s.Input)) ≠
      parentOutput J s.output Q u then (1 : ℚ) else 0) =
    ρ * (𝔼 n : s.Noise, 𝔼 u : s.Input,
      if s.output (u + s.noise n) ≠ s.output u then (1 : ℚ) else 0)
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact NonlinearRecurrence.parent_change_recurrence J hJ s.embed s.logical
    s.logical_surjective s.output s.equivariant (fun p => p.2 + Q p.1) s.noise ρ hk

theorem iterate_error (J : I → B →ₗ[k] X × B)
    (hJ : Function.Surjective (aggregate J)) (Q : X → B) (ρ : ℚ)
    (hk : ∀ d : B, d ≠ 0 →
      (𝔼 i, 𝔼 z : X × B,
        NonlinearRecurrence.change (fun p => p.2 + Q p.1) z (J i d)) = ρ)
    (n : ℕ) : error (Stage.iterate J hJ Q n) =
      (1 - 1 / (Fintype.card B : ℚ)) * ρ ^ n := by
  induction n with
  | zero => simp [Stage.iterate_zero, base_error]
  | succ n ih =>
    rw [Stage.iterate_succ, next_error J hJ Q ρ hk, ih, pow_succ]
    ac_rfl

theorem quotient_error (s : Stage k B) : error (StageQuotient.toStage s) = error s := by
  classical
  let := Fintype.ofFinite s.Input
  let := Fintype.ofFinite s.Noise
  let := Fintype.ofFinite (StageQuotient.Space s)
  let : Fintype (StageQuotient.toStage s).Input := inferInstanceAs (Fintype (StageQuotient.Space s))
  let : Fintype (StageQuotient.toStage s).Noise := inferInstanceAs (Fintype s.Noise)
  simp only [error_eq_expect]
  change (𝔼 n : s.Noise, 𝔼 x : StageQuotient.Space s,
    if StageQuotient.output s (x + StageQuotient.noise s n) ≠
      StageQuotient.output s x then (1 : ℚ) else 0) =
    𝔼 n : s.Noise, 𝔼 u : s.Input,
      if s.output (u + s.noise n) ≠ s.output u then (1 : ℚ) else 0
  apply Finset.expect_congr rfl
  intro n _
  calc
    _ = 𝔼 u : s.Input,
      if StageQuotient.output s (StageQuotient.projection s u + StageQuotient.noise s n) ≠
        StageQuotient.output s (StageQuotient.projection s u) then (1 : ℚ) else 0 :=
      (EmbeddedConditional.expect_linear_surjective (StageQuotient.projection s)
        (StageQuotient.projection_surjective s)
        (fun x : StageQuotient.Space s =>
          if StageQuotient.output s (x + StageQuotient.noise s n) ≠
            StageQuotient.output s x then (1 : ℚ) else 0)).symm
    _ = _ := by simp only [StageQuotient.noise_change_iff]

end DFVSGames.Gadget.StageNoiseRecurrence

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F]

def basisCoord (i : Fin 3) : Vec F := Pi.single i 1

theorem basisCoord_ne_zero (i : Fin 3) : (basisCoord i : Vec F) ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [basisCoord] at hi

@[simp] theorem Q_smul_basisCoord (t : F) (i : Fin 3) :
    Q (t • (basisCoord i : Vec F)) = 0 := by
  ext k
  fin_cases i <;> fin_cases k <;> simp [Q, basisCoord]

theorem dot_smul_basisCoord_of_ne (t : F) (i j : Fin 3) (hij : i ≠ j) :
    dot (basisCoord j : Vec F) (t • (basisCoord i : Vec F)) = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [dot, basisCoord]

theorem basisCoord_decomposition (x : Vec F) :
    x = x 0 • basisCoord 0 + x 1 • basisCoord 1 + x 2 • basisCoord 2 := by
  ext i
  fin_cases i <;> simp [basisCoord]

variable [CharP F 2] [Algebra (ZMod 2) F]

theorem horizontal_mem_U_basisCoord (t : F) (i : Fin 3) :
    (t • basisCoord i, (0 : Vec F)) ∈ U (basisCoord i) := by
  refine ⟨(mem_line_iff _ _).mpr ⟨t, rfl⟩, ?_⟩
  change dot (basisCoord i) (0 + Q (t • basisCoord i)) = 0
  simp

theorem vertical_mem_U_basisCoord_of_ne (t : F) (i j : Fin 3) (hij : i ≠ j) :
    ((0 : Vec F), t • basisCoord i) ∈ U (basisCoord j) := by
  refine ⟨(line _).zero_mem, ?_⟩
  change dot (basisCoord j) (t • basisCoord i + Q 0) = 0
  simpa using dot_smul_basisCoord_of_ne t i j hij

def coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F) :=
  (U (basisCoord 0) ⊔ U (basisCoord 1)) ⊔ U (basisCoord 2)

theorem U_basisCoord_le_coordinateBlockSpan (i : Fin 3) :
    U (basisCoord i) ≤ (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  fin_cases i
  · exact le_trans le_sup_left le_sup_left
  · exact le_trans le_sup_right le_sup_left
  · exact le_sup_right

theorem horizontal_mem_coordinateBlockSpan (t : F) (i : Fin 3) :
    (t • basisCoord i, (0 : Vec F)) ∈
      (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) :=
  U_basisCoord_le_coordinateBlockSpan i (horizontal_mem_U_basisCoord t i)

theorem vertical_mem_coordinateBlockSpan (t : F) (i : Fin 3) :
    ((0 : Vec F), t • basisCoord i) ∈
      (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  have h (j : Fin 3) (hij : i ≠ j) :
      ((0 : Vec F), t • basisCoord i) ∈
        (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) :=
    U_basisCoord_le_coordinateBlockSpan j (vertical_mem_U_basisCoord_of_ne t i j hij)
  fin_cases i
  · exact h 1 (by decide)
  · exact h 0 (by decide)
  · exact h 0 (by decide)

theorem mem_coordinateBlockSpan (p : Vec F × Vec F) :
    p ∈ (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) := by
  let S : Submodule (ZMod 2) (Vec F × Vec F) := coordinateBlockSpan
  have hh : (p.1, (0 : Vec F)) ∈ S := by
    have h := S.add_mem
      (S.add_mem (horizontal_mem_coordinateBlockSpan (p.1 0) 0)
        (horizontal_mem_coordinateBlockSpan (p.1 1) 1))
      (horizontal_mem_coordinateBlockSpan (p.1 2) 2)
    convert h using 1 ; ext i <;> fin_cases i <;> simp [basisCoord]
  have hv : ((0 : Vec F), p.2) ∈ S := by
    have h := S.add_mem
      (S.add_mem (vertical_mem_coordinateBlockSpan (p.2 0) 0)
        (vertical_mem_coordinateBlockSpan (p.2 1) 1))
      (vertical_mem_coordinateBlockSpan (p.2 2) 2)
    convert h using 1 ; ext i <;> fin_cases i <;> simp [basisCoord]
  have h := S.add_mem hh hv
  simpa only [Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta] using h

theorem coordinateBlockSpan_eq_top :
    (coordinateBlockSpan : Submodule (ZMod 2) (Vec F × Vec F)) = ⊤ := by
  apply top_unique
  intro p _
  exact mem_coordinateBlockSpan p

theorem iSup_U_nonzero_eq_top :
    (⨆ v : {v : Vec F // v ≠ 0}, U v.1) = ⊤ := by
  apply top_unique
  rw [← coordinateBlockSpan_eq_top (F := F)]
  unfold coordinateBlockSpan
  refine sup_le (sup_le ?_ ?_) ?_
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 0, basisCoord_ne_zero 0⟩
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 1, basisCoord_ne_zero 1⟩
  · exact le_iSup (fun v : {v : Vec F // v ≠ 0} => U v.1)
      ⟨basisCoord 2, basisCoord_ne_zero 2⟩

end DFVSGames.Quadratic

noncomputable section

open scoped BigOperators

namespace DFVSGames.Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]
variable [Fintype (BlockOrientationIndex F)]

def blockEmbedding (i : BlockOrientationIndex F) :
    Vec F →ₗ[ZMod 2] Vec F × Vec F :=
  (U (lineGenerator i.1)).subtype.comp i.2.toLinearMap

def blockAggregate : (BlockOrientationIndex F → Vec F) →ₗ[ZMod 2] Vec F × Vec F :=
  Gadget.aggregate (blockEmbedding (F := F))

theorem blockAggregate_single [DecidableEq (BlockOrientationIndex F)]
    (i : BlockOrientationIndex F) (b : Vec F) :
    blockAggregate (Pi.single i b) = blockEmbedding i b := by
  classical
  change (∑ j : BlockOrientationIndex F,
    blockEmbedding j ((Pi.single i b : BlockOrientationIndex F → Vec F) j)) = _
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · intro h
    exact False.elim (h (Finset.mem_univ _))

theorem fieldLine_block_le_range_aggregate (A : FieldLine F) :
    U (lineGenerator A) ≤ LinearMap.range (blockAggregate (F := F)) := by
  classical
  intro p hp
  let J := chosenBlockOrientation A
  let i : BlockOrientationIndex F := ⟨A, J⟩
  obtain ⟨b, hb⟩ := J.surjective ⟨p, hp⟩
  refine ⟨Pi.single i b, ?_⟩
  rw [blockAggregate_single]
  change ((J b : U (lineGenerator A)) : Vec F × Vec F) = p
  exact congrArg Subtype.val hb

theorem blockAggregate_surjective : Function.Surjective (blockAggregate (F := F)) := by
  have hspan : (⨆ v : {v : Vec F // v ≠ 0}, U v.1) ≤
      LinearMap.range (blockAggregate (F := F)) := by
    apply iSup_le
    intro v
    let A : FieldLine F := Projectivization.mk F v.1 v.2
    have hl : line (lineGenerator A) = line v.1 := by
      simpa only [A, Projectivization.submodule_mk, line] using line_lineGenerator A
    have hm : lineGenerator A ∈ line v.1 := by
      rw [← hl]
      exact (mem_line_iff _ _).mpr ⟨1, one_smul _ _⟩
    have hu := U_eq_of_nonzero_mem_line (lineGenerator_ne_zero A) hm
    simpa only [hu] using fieldLine_block_le_range_aggregate A
  rw [iSup_U_nonzero_eq_top] at hspan
  exact LinearMap.range_eq_top.mp (top_unique hspan)

theorem aggregate_blockEmbedding_surjective :
    Function.Surjective (Gadget.aggregate (blockEmbedding (F := F))) :=
  blockAggregate_surjective

end DFVSGames.Quadratic
end

noncomputable section

namespace DFVSGames.Gadget.QuadraticStageNoise

open scoped BigOperators Classical
open Quadratic

variable {F : Type*} [Field F] [Fintype F] [CharP F 2] [Algebra (ZMod 2) F]

local instance indexDecidableEq : DecidableEq (BlockOrientationIndex F) := Classical.decEq _

local instance automorphismFinite : Finite (Vec F ≃ₗ[ZMod 2] Vec F) := DFunLike.finite _
noncomputable local instance automorphismFintype : Fintype (Vec F ≃ₗ[ZMod 2] Vec F) :=
  Fintype.ofFinite _

local instance indexNonempty : Nonempty (BlockOrientationIndex F) := by
  have hA : Nonempty (FieldLine F) := Fintype.card_pos_iff.mp (by
    simpa only [Nat.card_eq_fintype_card] using (card_FieldLine_pos (F := F)))
  obtain ⟨A⟩ := hA
  exact ⟨⟨A, chosenBlockOrientation A⟩⟩

def rate (F : Type*) [Fintype F] : ℚ :=
  1 - 1 / ((Nat.card F : ℚ) ^ 2 + (Nat.card F : ℚ) + 1)

theorem actual_kernel (d : Vec F) (hd : d ≠ 0) :
    (𝔼 i : BlockOrientationIndex F, 𝔼 p : Vec F × Vec F,
      NonlinearRecurrence.change (fun z => z.2 + Q z.1) p (blockEmbedding i d)) =
      rate F := by
  classical
  exact OrientedBlockKernel.mean_oriented_block_kernel d hd

noncomputable def stage (n : ℕ) : Stage (ZMod 2) (Vec F) :=
  Stage.iterate (blockEmbedding (F := F)) aggregate_blockEmbedding_surjective Q n

theorem stage_error (n : ℕ) :
    StageNoiseRecurrence.error (stage (F := F) n) =
      (1 - 1 / (Nat.card F : ℚ) ^ 3) * rate F ^ n := by
  have he := StageNoiseRecurrence.iterate_error (blockEmbedding (F := F))
    aggregate_blockEmbedding_surjective Q (rate F) actual_kernel n
  simpa only [stage, Vec, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    Nat.card_eq_fintype_card] using he

noncomputable def quotientStage (n : ℕ) : Stage (ZMod 2) (Vec F) :=
  StageQuotient.toStage (stage (F := F) n)

theorem quotientStage_error (n : ℕ) :
    StageNoiseRecurrence.error (quotientStage (F := F) n) =
      (1 - 1 / (Nat.card F : ℚ) ^ 3) * rate F ^ n := by
  rw [quotientStage, StageNoiseRecurrence.quotient_error, stage_error]

end DFVSGames.Gadget.QuadraticStageNoise
end

namespace DFVSGames.Gadget.Parameters

open Harmonic
open scoped BigOperators

theorem harmonic_double (n : ℕ) (hn : 0 < n) :
    DFVSGames.Gadget.Harmonic.harmonic n + 1 / 2 ≤ DFVSGames.Gadget.Harmonic.harmonic (2 * n) := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hsplit : DFVSGames.Gadget.Harmonic.harmonic (2 * n) = DFVSGames.Gadget.Harmonic.harmonic n +
      ∑ i ∈ Finset.range n, (↑(n + i + 1) : ℚ)⁻¹ := by
    rw [harmonic_eq_sum, show 2 * n = n + n by omega, Finset.sum_range_add]
    rw [← harmonic_eq_sum n]
  have hs : (∑ _i ∈ Finset.range n, (2 * (n : ℚ))⁻¹) ≤
      ∑ i ∈ Finset.range n, (↑(n + i + 1) : ℚ)⁻¹ := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    apply inv_anti₀ (by positivity)
    exact_mod_cast (show n + i + 1 ≤ 2 * n by omega)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs
  have he : (n : ℚ) * (2 * (n : ℚ))⁻¹ = 1 / 2 := by
    field_simp [ne_of_gt hnq]
  rw [he] at hs
  rw [hsplit]
  linarith

theorem harmonic_pow_two (k : ℕ) : (k : ℚ) / 2 ≤ DFVSGames.Gadget.Harmonic.harmonic (2 ^ k) := by
  induction k with
  | zero => simpa only [Nat.cast_zero, zero_div, pow_zero] using harmonic_nonneg 1
  | succ k ih =>
    have hd := harmonic_double (2 ^ k) (pow_pos (by decide) _)
    rw [pow_succ, Nat.mul_comm]
    push_cast
    linarith

def rankFor (level : ℚ) : ℕ := 2 ^ ⌈2 * level⌉₊

theorem rankFor_pos (level : ℚ) : 0 < rankFor level := by
  unfold rankFor
  positivity

theorem le_harmonic_rankFor (level : ℚ) : level ≤ DFVSGames.Gadget.Harmonic.harmonic (rankFor level) := by
  have hc := Nat.le_ceil (2 * level)
  have hh := harmonic_pow_two ⌈2 * level⌉₊
  change level ≤ DFVSGames.Gadget.Harmonic.harmonic (2 ^ ⌈2 * level⌉₊)
  linarith

theorem harmonic_unbounded (level : ℚ) :
    ∃ r₀ : ℕ, 0 < r₀ ∧ level ≤ DFVSGames.Gadget.Harmonic.harmonic r₀ :=
  ⟨rankFor level, rankFor_pos level, le_harmonic_rankFor level⟩

def genericityError (r₀ : ℕ) : ℚ := 1 / (2 * (badRankCoefficient r₀ + 1))

theorem genericityError_pos (r₀ : ℕ) : 0 < genericityError r₀ := by
  unfold genericityError
  have := badRankCoefficient_nonneg r₀
  positivity

theorem genericityError_lt_one (r₀ : ℕ) : genericityError r₀ < 1 := by
  have hc := badRankCoefficient_nonneg r₀
  unfold genericityError
  apply (div_lt_one (by positivity)).mpr
  linarith

theorem genericityError_budget (r₀ : ℕ) :
    badRankCoefficient r₀ * genericityError r₀ ≤ 1 := by
  have hc := badRankCoefficient_nonneg r₀
  unfold genericityError
  rw [← mul_div_assoc, mul_one]
  apply (div_le_one (by positivity)).mpr
  linarith

theorem geometric_reciprocal_bound (θ : ℚ) (_hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (n : ℕ) : (1 - θ) ^ n * (1 + (n : ℚ) * θ) ≤ 1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 0 ≤ (1 - θ) ^ n := pow_nonneg (sub_nonneg.mpr hθone) _
    have hn : (0 : ℚ) ≤ n := by positivity
    have hstep : (1 - θ) * (1 + ((n + 1 : ℕ) : ℚ) * θ) ≤
        1 + (n : ℚ) * θ := by
      push_cast
      nlinarith [sq_nonneg θ, mul_nonneg hn (sq_nonneg θ)]
    calc
      (1 - θ) ^ (n + 1) * (1 + ((n + 1 : ℕ) : ℚ) * θ) =
          (1 - θ) ^ n * ((1 - θ) * (1 + ((n + 1 : ℕ) : ℚ) * θ)) := by
        rw [pow_succ]
        ring
      _ ≤ (1 - θ) ^ n * (1 + (n : ℚ) * θ) :=
        mul_le_mul_of_nonneg_left hstep hp
      _ ≤ 1 := ih

theorem geometric_at_depth_le (p θ : ℚ) (r₀ : ℕ) (hp : 0 < p)
    (hθ : 0 < θ) (hθone : θ ≤ 1)
    (hlarge : 8 * (p⁻¹ + 1) ≤ DFVSGames.Gadget.Harmonic.harmonic r₀) :
    (1 - θ) ^ depth r₀ θ ≤ p := by
  have hden : (0 : ℚ) < 8 * θ := by positivity
  have hf := Nat.lt_floor_add_one (DFVSGames.Gadget.Harmonic.harmonic r₀ / (8 * θ))
  have hf' := (div_lt_iff₀ hden).mp hf
  change DFVSGames.Gadget.Harmonic.harmonic r₀ < ((depth r₀ θ : ℚ) + 1) * (8 * θ) at hf'
  have hnθ : p⁻¹ ≤ (depth r₀ θ : ℚ) * θ := by nlinarith
  have hpne : p ≠ 0 := ne_of_gt hp
  have hm := mul_le_mul_of_nonneg_left hnθ (le_of_lt hp)
  simp only [mul_inv_cancel₀ hpne] at hm
  have hr := geometric_reciprocal_bound θ (le_of_lt hθ) hθone (depth r₀ θ)
  have hb : 1 ≤ p * (1 + (depth r₀ θ : ℚ) * θ) := by nlinarith
  have hpositive : 0 < 1 + (depth r₀ θ : ℚ) * θ := by positivity
  exact (mul_le_mul_iff_left₀ hpositive).mp (by simpa only [mul_comm] using hr.trans hb)

def initialRank (p : ℚ) : ℕ := rankFor (8 * (p⁻¹ + 1))

theorem initialRank_pos (p : ℚ) : 0 < initialRank p := rankFor_pos _

theorem initialRank_large (p : ℚ) :
    8 * (p⁻¹ + 1) ≤ DFVSGames.Gadget.Harmonic.harmonic (initialRank p) := le_harmonic_rankFor _

theorem effective_parameters (p : ℚ) (hp : 0 < p) :
    ∃ r₀ : ℕ, ∃ ε : ℚ,
      0 < r₀ ∧ 0 < ε ∧ ε < 1 ∧ badRankCoefficient r₀ * ε ≤ 1 ∧
      ∀ θ : ℚ, 0 < θ → θ ≤ 1 → (1 - θ) ^ depth r₀ θ ≤ p := by
  refine ⟨initialRank p, genericityError (initialRank p), initialRank_pos p,
    genericityError_pos _, genericityError_lt_one _, genericityError_budget _, ?_⟩
  intro θ hθ hθone
  exact geometric_at_depth_le p θ (initialRank p) hp hθ hθone (initialRank_large p)

end DFVSGames.Gadget.Parameters

namespace DFVSGames.Quadratic

open MvPolynomial
open scoped BigOperators

variable {σ ι R : Type*} [CommSemiring R]

def SquarefreeExponent (a : σ →₀ ℕ) : Prop := ∀ k, a k < 2

theorem coeff_expand_mul_monomial_of_ne
    (p : MvPolynomial σ R) (a b n : σ →₀ ℕ)
    (ha : SquarefreeExponent a) (hb : SquarefreeExponent b) (hab : a ≠ b) :
    (expand 2 p * monomial b 1).coeff (2 • n + a) = 0 := by
  classical
  rw [coeff_mul_monomial']
  split_ifs with hle
  · obtain ⟨k, hk⟩ : ∃ k, a k ≠ b k := by
      by_contra h
      push Not at h
      exact hab (Finsupp.ext h)
    have hcoeff : (expand 2 p).coeff (2 • n + a - b) = 0 := by
      apply coeff_expand_of_not_dvd (i := k)
      intro hdiv
      obtain ⟨m, hm⟩ := hdiv
      have hle' := hle k
      have ha' := ha k
      have hb' := hb k
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.smul_apply,
        smul_eq_mul] at hm hle'
      omega
    simp [hcoeff]
  · rfl

theorem coeff_expand_mul_monomial_self
    (p : MvPolynomial σ R) (a n : σ →₀ ℕ) :
    (expand 2 p * monomial a 1).coeff (2 • n + a) = p.coeff n := by
  rw [coeff_mul_monomial, coeff_expand_smul 2 (by decide), mul_one]

theorem coeff_sum_expand_mul_monomial [Fintype ι]
    (e : ι → σ →₀ ℕ) (he : ∀ i, SquarefreeExponent (e i))
    (hinj : Function.Injective e) (p : ι → MvPolynomial σ R)
    (i : ι) (n : σ →₀ ℕ) :
    (∑ j, expand 2 (p j) * monomial (e j) 1).coeff (2 • n + e i) =
      (p i).coeff n := by
  classical
  rw [coeff_sum]
  rw [Finset.sum_eq_single i]
  · exact coeff_expand_mul_monomial_self _ _ _
  · intro j _ hji
    exact coeff_expand_mul_monomial_of_ne _ _ _ _ (he i) (he j)
      (fun h => hji (hinj h).symm)
  · simp

theorem sum_expand_mul_monomial_eq_zero_iff [Fintype ι]
    (e : ι → σ →₀ ℕ) (he : ∀ i, SquarefreeExponent (e i))
    (hinj : Function.Injective e) (p : ι → MvPolynomial σ R) :
    (∑ i, expand 2 (p i) * monomial (e i) 1) = 0 ↔ ∀ i, p i = 0 := by
  constructor
  · intro h i
    ext n
    have hc := congrArg (fun q : MvPolynomial σ R => q.coeff (2 • n + e i)) h
    simpa only [coeff_sum_expand_mul_monomial e he hinj, AddMonoidAlgebra.coeff_zero,
      Finsupp.zero_apply] using hc
  · intro h
    simp [h]

noncomputable def blockExponent {κ J : Type*} [Finite κ] [Finite J]
    (v : κ → J) : (κ × J) →₀ ℕ := by
  classical
  exact Finsupp.equivFunOnFinite.symm (fun x => if x.2 = v x.1 then 1 else 0)

@[simp] theorem blockExponent_apply {κ J : Type*} [Finite κ] [Finite J] [DecidableEq J]
    (v : κ → J) (x : κ × J) :
    blockExponent v x = if x.2 = v x.1 then 1 else 0 := by
  classical
  by_cases h : x.2 = v x.1 <;> simp [blockExponent, h]

theorem blockExponent_squarefree {κ J : Type*} [Finite κ] [Finite J]
    (v : κ → J) : SquarefreeExponent (blockExponent v) := by
  classical
  intro x
  simp only [blockExponent_apply]
  split_ifs <;> decide

theorem blockExponent_injective {κ J : Type*} [Finite κ] [Finite J] :
    Function.Injective (blockExponent (κ := κ) (J := J)) := by
  classical
  intro v w h
  funext i
  have hc := congrArg (fun e : (κ × J) →₀ ℕ => e (i, v i)) h
  by_contra hne
  simp [hne] at hc

theorem blockExponent_eq_sum {κ J : Type*} [Fintype κ] [Finite J]
    (v : κ → J) :
    blockExponent v = ∑ i, Finsupp.single (i, v i) 1 := by
  classical
  ext x
  rw [blockExponent_apply, Finsupp.finsetSum_apply]
  symm
  rw [Finset.sum_eq_single x.1]
  · simp [Finsupp.single_apply, Prod.ext_iff, eq_comm]
  · intro i _ hi
    have hix : (i, v i) ≠ x := fun h => hi (congrArg Prod.fst h)
    simp [hix]
  · simp

theorem monomial_blockExponent {κ J : Type*} [Fintype κ] [Finite J]
    (v : κ → J) :
    (monomial (blockExponent v) 1 : MvPolynomial (κ × J) R) =
      ∏ i, X (i, v i) := by
  rw [blockExponent_eq_sum, monomial_sum_one]
  rfl

theorem sum_expand_mul_blockMonomial_eq_zero_iff {J : Type*} [Fintype J]
    (p : (Fin 3 → J) → MvPolynomial (Fin 3 × J) R) :
    (∑ v, expand 2 (p v) * monomial (blockExponent v) 1) = 0 ↔
      ∀ v, p v = 0 :=
  sum_expand_mul_monomial_eq_zero_iff blockExponent blockExponent_squarefree
    blockExponent_injective p

end DFVSGames.Quadratic

end OAI
