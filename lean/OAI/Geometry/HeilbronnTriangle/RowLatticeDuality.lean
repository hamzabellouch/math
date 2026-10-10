import OAI.Geometry.HeilbronnTriangle.RowLattice

namespace OAI


noncomputable section

namespace Problem355.RowLattice

open Matrix

variable {R S : Type*} [CommRing R] [CommRing S]

lemma mapped_rowImage_annihilator_iff (f : R →+* S)
    (C : Matrix (Fin 3) (Fin 3) R) (x : Fin 3 → S) :
    (∀ v, v ∈ rowImage C → (fun i => f (v i)) ⬝ᵥ x = 0) ↔
      (C.map f) *ᵥ x = 0 := by
  constructor
  · intro h
    funext i
    have hv : C.row i ∈ rowImage C :=
      ⟨Pi.single i 1, Matrix.single_one_vecMul i C⟩
    exact h (C.row i) hv
  · intro h v hv
    obtain ⟨w, hw⟩ := hv
    change w ᵥ* C = v at hw
    rw [← hw]
    have hm : (fun i => f ((w ᵥ* C) i)) = (f ∘ w) ᵥ* C.map f := by
      funext i
      exact f.map_vecMul C w i
    rw [hm, ← Matrix.dotProduct_mulVec, h]
    simp

lemma reduction_dotProduct (d : ℕ) (v x : Fin 3 → ℤ) :
    reduction d v ⬝ᵥ reduction d x = (v ⬝ᵥ x : ℤ) := by
  simpa [reduction, Function.comp_def] using ((Int.castRingHom (ZMod d)).map_dotProduct v x).symm

lemma dvd_dotProduct_iff (d : ℕ) (v x : Fin 3 → ℤ) :
    (d : ℤ) ∣ v ⬝ᵥ x ↔ reduction d v ⬝ᵥ reduction d x = 0 := by
  rw [reduction_dotProduct, ZMod.intCast_zmod_eq_zero_iff_dvd]

lemma map_reduction {h d : ℕ} (hd : d ∣ h) (v : Fin 3 → ℤ) :
    (fun i => ZMod.castHom hd (ZMod d) (reduction h v i)) = reduction d v := by
  funext i
  simp [reduction]

theorem forall_dvd_dotProduct_iff {h d : ℕ} (hd : d ∣ h)
    (C : Matrix (Fin 3) (Fin 3) (ZMod h)) (x : Fin 3 → ℤ) :
    (∀ v, v ∈ integerRowLattice h C → (d : ℤ) ∣ v ⬝ᵥ x) ↔
      (C.map (ZMod.castHom hd (ZMod d))) *ᵥ reduction d x = 0 := by
  constructor
  · intro H
    apply (mapped_rowImage_annihilator_iff (ZMod.castHom hd (ZMod d)) C
      (reduction d x)).mp
    intro w hw
    obtain ⟨v, hv⟩ := reduction_surjective h w
    have hmem : v ∈ integerRowLattice h C := by
      change reduction h v ∈ rowImage C
      rw [hv]
      exact hw
    have hzero := (dvd_dotProduct_iff d v x).mp (H v hmem)
    rw [← hv, map_reduction hd]
    exact hzero
  · intro H v hv
    apply (dvd_dotProduct_iff d v x).mpr
    have hm := (mapped_rowImage_annihilator_iff (ZMod.castHom hd (ZMod d)) C
      (reduction d x)).mpr H
    have hz := hm (reduction h v) hv
    simpa only [map_reduction hd] using hz

theorem dvd_dotGenerator_iff {h d : ℕ} (hd : d ∣ h)
    (C : Matrix (Fin 3) (Fin 3) (ZMod h)) (x : Fin 3 → ℤ) (g : ℤ)
    (hdiv : ∀ v, v ∈ integerRowLattice h C → g ∣ v ⬝ᵥ x)
    (hgen : ∃ v, v ∈ integerRowLattice h C ∧ v ⬝ᵥ x = g) :
    (d : ℤ) ∣ g ↔
      (C.map (ZMod.castHom hd (ZMod d))) *ᵥ reduction d x = 0 := by
  rw [← forall_dvd_dotProduct_iff hd C x]
  constructor
  · intro hg v hv
    exact hg.trans (hdiv v hv)
  · intro H
    obtain ⟨v, hv, hvg⟩ := hgen
    simpa only [hvg] using H v hv

theorem dotGenerator_dvd_larger_power
    (B k b e : ℕ) (hbe : b ≤ e)
    (C : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k)))
    (P Q : Matrix.GeneralLinearGroup (Fin 3) (ZMod (B ^ k)))
    (hC : C = (P : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))) *
      DiagonalStabilizer.diagonal3 (R := ZMod (B ^ k)) (B ^ b) (B ^ e) *
      (Q : Matrix (Fin 3) (Fin 3) (ZMod (B ^ k))))
    (x : Fin 3 → ℤ) (g : ℤ)
    (hdiv : ∀ v, v ∈ integerRowLattice (B ^ k) C → g ∣ v ⬝ᵥ x)
    (hprimitive : ∃ z : Fin 3 → ℤ, z ⬝ᵥ x = 1) :
    g ∣ (B ^ e : ℕ) := by
  obtain ⟨z, hz⟩ := hprimitive
  have hm := nsmul_mem_integerRowLattice_prime_power B k b e hbe C P Q hC z
  have hg := hdiv ((B ^ e) • z) hm
  have hs : ((B ^ e) • z) ⬝ᵥ x = (B ^ e : ℕ) * (z ⬝ᵥ x) := by
    simp [dotProduct, Finset.mul_sum, mul_assoc]
  simpa only [hs, hz, mul_one] using hg

end Problem355.RowLattice

end

end OAI
