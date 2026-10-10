import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.NonpRegradeFaithful
import OAI.Combinatorics.Chromatic.GradedAlgebra.LaurentRegrade

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries
noncomputable section
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (δ κ η : M →+ ℤ) (B : ℕ)
local instance rootLaurentCompletionRing : Ring (Torus v Ω) := Torus.instRing v Ω
local instance rootLaurentCompletionAddCommMonoid : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance rootLaurentCompletionAddGroup : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

lemma laurentRegrade_read {f : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hhom : FullHomogeneous v Ω η f)
    (n d : ℕ) (z : ℤ) (m : M) (hn : η m=(n:ℤ))
    (hd : δ m=(d:ℤ)) (hz : κ m=z) :
    (coeff d (laurentRegrade v Ω δ κ B f hf)).coeff z m=coeff n f m := by
  rw [laurentRegrade_coeff,nonp_torus_eval_sum]
  have H (j : ℕ) : (coeff d (laurentHomogenize v Ω δ κ (coeff j f))).coeff z m=coeff j f m := by
    rw [laurentHomogenize_coeff,hd,hz]
    simp
  simp_rw [H]
  apply Finset.sum_eq_single n
  · intro j hj hjn
    by_contra h
    have HH:=hhom j m h
    rw [hn] at HH
    exact hjn (by omega)
  · intro hn'
    by_contra h
    have HH:=(hf n m h).2.2
    rw [hd,hz] at HH
    simp only [Finset.mem_range,not_lt] at hn'
    omega

lemma laurentRegrade_injective {f g : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : LaurentBounded v Ω δ κ B g)
    (hfh : FullHomogeneous v Ω η f) (hgh : FullHomogeneous v Ω η g)
    (heq : laurentRegrade v Ω δ κ B f hf=laurentRegrade v Ω δ κ B g hg) : f=g := by
  apply PowerSeries.ext
  intro n
  ext m
  by_cases H : η m=(n:ℤ) ∧ 0≤δ m
  · rw [←laurentRegrade_read v Ω δ κ η B hf hfh n (δ m).toNat (κ m) m H.1
      (Int.toNat_of_nonneg H.2).symm rfl,heq,
      laurentRegrade_read v Ω δ κ η B hg hgh n (δ m).toNat (κ m) m H.1
        (Int.toNat_of_nonneg H.2).symm rfl]
  · have hF : coeff n f m=0 := by
      by_contra h
      exact H ⟨hfh n m h,(hf n m h).1⟩
    have hG : coeff n g m=0 := by
      by_contra h
      exact H ⟨hgh n m h,(hg n m h).1⟩
    rw [hF,hG]

lemma laurentRegrade_coeff_congr {f g : PowerSeries (Torus v Ω)}
    (hf : LaurentBounded v Ω δ κ B f) (hg : LaurentBounded v Ω δ κ B g)
    (d : ℕ) (z : ℤ)
    (H : ∀n≤(z+(B+1:ℤ)*(d:ℤ)).toNat,coeff n f=coeff n g) :
    (coeff d (laurentRegrade v Ω δ κ B f hf)).coeff z=
      (coeff d (laurentRegrade v Ω δ κ B g hg)).coeff z := by
  rw [laurentRegrade_coeff,laurentRegrade_coeff]
  apply Finset.sum_congr rfl
  intro n hn
  rw [H n (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hn)]
end
end ElementaryPositivity.QuantumTorus

end

end OAI
