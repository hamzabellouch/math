import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Ideal.Operations

namespace OAI

namespace ArExplicit

variable {R S : Type*} [Ring R] [Ring S]

theorem nilIdeal_le_jacobson (I : Ideal R)
    (hnil : ∀ x ∈ I, IsNilpotent x) : I ≤ Ring.jacobson R := by
  intro x hx
  rw [← Ideal.jacobson_bot]
  apply Ideal.mem_jacobson_iff.mpr
  intro y
  obtain ⟨u, hu⟩ := (hnil (y * x) (I.mul_mem_left y hx)).isUnit_add_one
  refine ⟨↑u⁻¹, ?_⟩
  change (↑u⁻¹ : R) * y * x + ↑u⁻¹ - 1 = 0
  calc
    (↑u⁻¹ : R) * y * x + ↑u⁻¹ - 1 = ↑u⁻¹ * (y * x + 1) - 1 := by
      rw [mul_add, mul_one, mul_assoc]
    _ = 0 := by rw [← hu]; simp

theorem nilpotentIdeal_le_jacobson (I : Ideal R) (hnil : IsNilpotent I) :
    I ≤ Ring.jacobson R := by
  apply nilIdeal_le_jacobson I
  intro x hx
  obtain ⟨n, hn⟩ := hnil
  refine ⟨n, ?_⟩
  have h := Ideal.pow_mem_pow hx n
  simpa only [hn, Ideal.zero_eq_bot, Ideal.mem_bot] using h

theorem jacobson_eq_kernel (f : R →+* S) (hf : Function.Surjective f)
    (hker : IsNilpotent (RingHom.ker f)) (hS : Ring.jacobson S = ⊥) :
    Ring.jacobson R = RingHom.ker f := by
  let : RingHomSurjective f := ⟨hf⟩
  apply le_antisymm
  · intro x hx
    have h := Ring.le_comap_jacobson f hx
    simpa only [hS, Ideal.mem_comap, Ideal.mem_bot, RingHom.mem_ker] using h
  · exact nilpotentIdeal_le_jacobson (RingHom.ker f) hker

theorem jacobson_eq_comap_of_nil_kernel (f : R →+* S)
    (hf : Function.Surjective f) (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    Ring.jacobson R = Ideal.comap f (Ring.jacobson S) := by
  let : RingHomSurjective f := ⟨hf⟩
  exact (Module.comap_jacobson_of_ker_le (f := f.toSemilinearMap) hf
    (nilIdeal_le_jacobson (RingHom.ker f) hker)).symm

theorem mem_jacobson_prod_iff (x : R × S) :
    x ∈ Ring.jacobson (R × S) ↔ x.1 ∈ Ring.jacobson R ∧ x.2 ∈ Ring.jacobson S := by
  constructor
  · intro hx
    have : RingHomSurjective (RingHom.fst R S) := ⟨fun r => ⟨(r, 0), rfl⟩⟩
    have : RingHomSurjective (RingHom.snd R S) := ⟨fun s => ⟨(0, s), rfl⟩⟩
    exact ⟨Ring.le_comap_jacobson (RingHom.fst R S) hx,
      Ring.le_comap_jacobson (RingHom.snd R S) hx⟩
  · rintro ⟨hr, hs⟩
    rw [← Ideal.jacobson_bot] at hr hs ⊢
    apply Ideal.mem_jacobson_iff.mpr
    intro y
    obtain ⟨r, hr⟩ := Ideal.mem_jacobson_iff.mp hr y.1
    obtain ⟨s, hs⟩ := Ideal.mem_jacobson_iff.mp hs y.2
    exact ⟨(r, s), Prod.ext hr hs⟩

theorem jacobson_prod_eq_bot (hR : Ring.jacobson R = ⊥) (hS : Ring.jacobson S = ⊥) :
    Ring.jacobson (R × S) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨hr, hs⟩ := (mem_jacobson_prod_iff x).mp hx
  rw [hR] at hr
  rw [hS] at hs
  exact Prod.ext hr hs

theorem jacobson_eq_bot_of_equiv (e : R ≃+* S) (hS : Ring.jacobson S = ⊥) :
    Ring.jacobson R = ⊥ := by
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  apply le_antisymm _ bot_le
  intro x hx
  have h := Ring.le_comap_jacobson e.toRingHom hx
  rw [hS] at h
  exact e.injective (by simpa using h)

theorem field_jacobson_eq_bot (k : Type*) [Field k] : Ring.jacobson k = ⊥ := by
  let : (⊥ : Ideal k).IsMaximal := Ideal.bot_isMaximal
  exact le_antisymm (Ring.jacobson_le_of_isMaximal ⊥) bot_le

theorem field_pi_jacobson_eq_bot (k ι : Type*) [Field k] : Ring.jacobson (ι → k) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  funext i
  let f : (ι → k) →+* k := Pi.evalRingHom (fun _ : ι => k) i
  let : RingHomSurjective f := ⟨fun c => ⟨fun _ => c, rfl⟩⟩
  have h := Ring.le_comap_jacobson f hx
  simpa [field_jacobson_eq_bot, Ideal.mem_comap, Ideal.mem_bot, f] using h

theorem map_mem_ideal_pow (f : R →+* S) (I : Ideal R) (J : Ideal S)
    (hf : ∀ x ∈ I, f x ∈ J) (n : ℕ) {x : R} (hx : x ∈ I ^ n) : f x ∈ J ^ n := by
  induction n generalizing x with
  | zero => simp only [Submodule.pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  | succ n hn =>
      rw [Submodule.pow_succ] at hx ⊢
      exact Submodule.mul_induction_on hx
        (fun a ha b hb => by rw [map_mul]; exact Ideal.mul_mem_mul (hn ha) (hf b hb))
        (fun a b ha hb => by rw [map_add]; exact Submodule.add_mem _ ha hb)

theorem radical_pow_ne_bot_of_injective (f : R →+* S) (hf : Function.Injective f)
    (hJ : ∀ x ∈ Ring.jacobson R, f x ∈ Ring.jacobson S) (n : ℕ)
    (hn : (Ring.jacobson R) ^ n ≠ ⊥) : (Ring.jacobson S) ^ n ≠ ⊥ := by
  intro hs
  apply hn
  apply le_antisymm _ bot_le
  intro x hx
  have hmem := map_mem_ideal_pow f _ _ hJ n hx
  rw [hs] at hmem
  apply hf
  simpa only [Ideal.mem_bot, map_zero] using hmem

end ArExplicit

end OAI
