import Mathlib

namespace OAI

noncomputable section

namespace HeightThree.NilpotentTower
variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

def quotient (ρ : R →ₐ[K] K) (n : ℕ) := R ⧸ (RingHom.ker ρ)^(n+1)

instance (ρ : R →ₐ[K] K) (n : ℕ) : CommRing (quotient ρ n) := inferInstanceAs (CommRing (R ⧸ _))
instance (ρ : R →ₐ[K] K) (n : ℕ) : Algebra K (quotient ρ n) := inferInstanceAs (Algebra K (R ⧸ _))

def projection (ρ : R →ₐ[K] K) (n : ℕ) : R →ₐ[K] quotient ρ n :=
  Ideal.Quotient.mkₐ K _

def augmentation (ρ : R →ₐ[K] K) (n : ℕ) : quotient ρ n →ₐ[K] K :=
  Ideal.Quotient.liftₐ _ ρ (fun _ ha => Ideal.pow_le_self (Nat.succ_ne_zero _) ha)

@[simp] lemma augmentation_projection (ρ : R →ₐ[K] K) (n : ℕ) (a : R) :
    augmentation ρ n (projection ρ n a)=ρ a := rfl

lemma projection_surjective (ρ : R →ₐ[K] K) (n : ℕ) :
    Function.Surjective (projection ρ n) := Ideal.Quotient.mkₐ_surjective K _

lemma projection_eq_zero (ρ : R →ₐ[K] K) (n : ℕ) (a : R) :
    projection ρ n a=0 ↔ a∈(RingHom.ker ρ)^(n+1) := Ideal.Quotient.eq_zero_iff_mem

lemma augmentation_ker (ρ : R →ₐ[K] K) (n : ℕ) :
    RingHom.ker (augmentation ρ n)=Ideal.map (projection ρ n) (RingHom.ker ρ) := by
  ext a
  rw [Ideal.mem_map_iff_of_surjective _ (projection_surjective ρ n)]
  constructor
  · intro ha
    obtain ⟨b,rfl⟩ := projection_surjective ρ n a
    exact ⟨b,ha,rfl⟩
  · rintro ⟨b,hb,rfl⟩
    exact hb

lemma augmentation_nilpotent (ρ : R →ₐ[K] K) (n : ℕ) :
    (RingHom.ker (augmentation ρ n))^(n+1)=⊥ := by
  rw [augmentation_ker,←Ideal.map_pow,Ideal.map_eq_bot_iff_le_ker]
  intro a ha
  exact (projection_eq_zero ρ n a).mpr ha

lemma projection_ker_le (ρ : R →ₐ[K] K) (n : ℕ) (a : R)
    (ha : projection ρ n a=0) : ρ a=0 := by
  exact Ideal.pow_le_self (Nat.succ_ne_zero n) ((projection_eq_zero ρ n a).mp ha)

lemma projection_annihilate (ρ : R →ₐ[K] K) (n : ℕ)
    (h : (RingHom.ker ρ)^(n+2)=⊥) (a b : R)
    (ha : projection ρ n a=0) (hb : ρ b=0) : a*b=0 := by
  have hh := Ideal.mul_mem_mul ((projection_eq_zero ρ n a).mp ha) (show b∈RingHom.ker ρ from hb)
  rw [←pow_succ,show n+1+1=n+2 by omega,h] at hh
  exact hh

lemma nilpotent_of_mem_ker (ρ : R →ₐ[K] K) {n : ℕ}
    (h : (RingHom.ker ρ)^n=⊥) {a : R} (ha : ρ a=0) : IsNilpotent a := by
  refine ⟨n,?_⟩
  have hh := Ideal.pow_mem_pow (show a∈RingHom.ker ρ from ha) n
  rw [h] at hh
  exact hh

lemma augmentation_surjective (ρ : R →ₐ[K] K) : Function.Surjective ρ := by
  intro a; refine ⟨algebraMap K R a,?_⟩
  simp

lemma finite_local_nilpotent [IsLocalRing R] [FiniteDimensional K R] (ρ : R →ₐ[K] K) :
    ∃ n, (RingHom.ker ρ)^(n+1)=⊥ := by
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  have hj := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top,
    ←IsLocalRing.ker_eq_maximalIdeal ρ.toRingHom (augmentation_surjective ρ)] at hj
  obtain ⟨n,hn⟩ := hj
  change (RingHom.ker ρ)^n=0 at hn
  refine ⟨n,?_⟩
  rw [pow_succ,hn,zero_mul]
  rfl

end HeightThree.NilpotentTower

end

end OAI
