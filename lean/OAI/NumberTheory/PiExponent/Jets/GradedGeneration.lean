import Mathlib
import OAI.NumberTheory.PiExponent.Jets.FilteredLength

namespace OAI

namespace PiExponentJets.W24

section RingHom

variable {A B : Type*} [CommRing A] [CommRing B]

theorem residue_corrections_of_surjective {K : Type*} [CommRing K]
    (f : A →+* B) (ρ : A →+* K) (π : B →+* K)
    (hρ : Function.Surjective ρ) (hcomm : π.comp f = ρ) :
    ∀ y : B, ∃ x : A, y - f x ∈ RingHom.ker π := by
  intro y
  obtain ⟨x, hx⟩ := hρ (π y)
  have hc : π (f x) = ρ x := congrArg (fun g : A →+* K => g x) hcomm
  refine ⟨x, ?_⟩
  rw [RingHom.mem_ker, map_sub, hc, hx, sub_self]

theorem ideal_power_corrections (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hf : I ≤ J.comap f)
    (hres : ∀ y : B, ∃ x : A, y - f x ∈ J)
    (hone : ∀ y ∈ J, ∃ x ∈ I, y - f x ∈ J ^ 2) :
    ∀ n : ℕ, ∀ y ∈ J ^ n, ∃ x ∈ I ^ n, y - f x ∈ J ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro y _
    obtain ⟨x, hx⟩ := hres y
    exact ⟨x, by simp, by simpa using hx⟩
  | succ n ih =>
    intro y hy
    rw [pow_succ'] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨x, hx, hex⟩ := hone a ha
      obtain ⟨z, hz, hez⟩ := ih b hb
      refine ⟨x * z, ?_, ?_⟩
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hx hz
      · have hleft : (a - f x) * b ∈ J ^ (n + 1 + 1) := by
          simpa only [← pow_add, Nat.add_comm 2 n, Nat.add_assoc] using
            (Ideal.mul_mem_mul hex hb)
        have hright : f x * (b - f z) ∈ J ^ (n + 1 + 1) := by
          rw [pow_succ']
          exact Ideal.mul_mem_mul (hf hx) hez
        have heq : a * b - f (x * z) = (a - f x) * b + f x * (b - f z) := by
          rw [map_mul]
          ring
        rw [heq]
        exact (J ^ (n + 1 + 1)).add_mem hleft hright
    · intro a b ha hb
      obtain ⟨x, hx, hex⟩ := ha
      obtain ⟨z, hz, hez⟩ := hb
      refine ⟨x + z, (I ^ (n + 1)).add_mem hx hz, ?_⟩
      have heq : a + b - f (x + z) = (a - f x) + (b - f z) := by
        rw [map_add]
        ring
      rw [heq]
      exact (J ^ (n + 1 + 1)).add_mem hex hez

end RingHom

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem ideal_power_preservation (I : Ideal A) (J : Ideal B)
    (hf : I ≤ J.comap (algebraMap A B)) :
    ∀ n, ∀ x ∈ (I ^ n : Ideal A), algebraMap A B x ∈ J ^ n := by
  intro n x hx
  exact Ideal.le_comap_pow (algebraMap A B) n (Ideal.pow_right_mono hf n hx)

def idealPowerLayerMap (I : Ideal A) (J : Ideal B)
    (hf : I ≤ J.comap (algebraMap A B)) (n : ℕ) :=
  filtrationLayerMap (Algebra.linearMap A B) (fun n => (I ^ n : Ideal A))
    (fun n => (J ^ n).restrictScalars A) (ideal_power_preservation I J hf) n

theorem layer_surjective_of_corrections
    {R M P : Type*} [Ring R] [AddCommGroup M] [AddCommGroup P]
    [Module R M] [Module R P] (f : M →ₗ[R] P)
    (F : ℕ → Submodule R M) (G : ℕ → Submodule R P)
    (hf : ∀ n, ∀ x ∈ F n, f x ∈ G n) (n : ℕ)
    (hc : ∀ y ∈ G n, ∃ x ∈ F n, y - f x ∈ G (n + 1)) :
    Function.Surjective (filtrationLayerMap f F G hf n) := by
  intro z
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
  obtain ⟨x, hx, he⟩ := hc y y.property
  refine ⟨Submodule.Quotient.mk (⟨x, hx⟩ : F n), ?_⟩
  apply (Submodule.Quotient.eq ((G (n + 1)).comap (G n).subtype)).mpr
  change f x - (y : P) ∈ G (n + 1)
  simpa only [neg_sub] using (G (n + 1)).neg_mem he

theorem idealPowerLayerMap_surjective (I : Ideal A) (J : Ideal B)
    (hf : I ≤ J.comap (algebraMap A B))
    (hzero : Function.Surjective (idealPowerLayerMap I J hf 0))
    (hone : Function.Surjective (idealPowerLayerMap I J hf 1)) (n : ℕ) :
    Function.Surjective (idealPowerLayerMap I J hf n) := by
  have hres : ∀ y : B, ∃ x : A, y - algebraMap A B x ∈ J := by
    intro y
    obtain ⟨x, _, hx⟩ := correction_of_layer_surjective (Algebra.linearMap A B)
      (fun n => (I ^ n : Ideal A)) (fun n => (J ^ n).restrictScalars A)
      (ideal_power_preservation I J hf) 0 hzero y (by simp)
    exact ⟨x, by simpa using hx⟩
  have hfirst : ∀ y ∈ J, ∃ x ∈ I, y - algebraMap A B x ∈ J ^ 2 := by
    intro y hy
    obtain ⟨x, hx, he⟩ := correction_of_layer_surjective (Algebra.linearMap A B)
      (fun n => (I ^ n : Ideal A)) (fun n => (J ^ n).restrictScalars A)
      (ideal_power_preservation I J hf) 1 hone y (by simpa using hy)
    exact ⟨x, by simpa using hx, by simpa using he⟩
  apply layer_surjective_of_corrections
  exact ideal_power_corrections (algebraMap A B) I J hf hres hfirst n

theorem algebraMap_surjective_of_nilpotent_ideal_layers (I : Ideal A) (J : Ideal B)
    (hf : I ≤ J.comap (algebraMap A B))
    (hzero : Function.Surjective (idealPowerLayerMap I J hf 0))
    (hone : Function.Surjective (idealPowerLayerMap I J hf 1))
    (d : ℕ) (hd : J ^ d = ⊥) : Function.Surjective (algebraMap A B) := by
  apply surjective_of_finite_layers (Algebra.linearMap A B)
    (fun n => (I ^ n : Ideal A)) (fun n => (J ^ n).restrictScalars A)
    (ideal_power_preservation I J hf) d
  · simp
  · simp [hd]
  · intro n _
    exact idealPowerLayerMap_surjective I J hf hzero hone n

theorem ring_length_le_of_residue_and_cotangent (I : Ideal A) (J : Ideal B)
    (hf : I ≤ J.comap (algebraMap A B))
    (hzero : Function.Surjective (idealPowerLayerMap I J hf 0))
    (hone : Function.Surjective (idealPowerLayerMap I J hf 1))
    (d : ℕ) (hd : J ^ d = ⊥) : Module.length B B ≤ Module.length A A := by
  have hsurj := algebraMap_surjective_of_nilpotent_ideal_layers I J hf hzero hone d hd
  rw [← Module.length_eq_of_surjective (M := B) hsurj]
  exact Module.length_le_of_surjective (Algebra.linearMap A B) hsurj

end PiExponentJets.W24

end OAI
