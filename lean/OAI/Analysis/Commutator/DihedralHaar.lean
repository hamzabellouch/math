import Mathlib
import OAI.Analysis.Commutator.HankelAlgebra

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} (τ : A →ₗ[ℂ] ℂ)

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
  (hstar : ∀ a : A, τ (star a)=star (τ a)) (hfree : Free S τ)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d : A)∈S i) (hs : (s : A)∈S j)
  (hd0 : τ (d : A)=0) (hs0 : τ (s : A)=0)

lemma wave_nat (u : unitary A) (n : ℕ) : wave u (n:ℤ)=(u:A)^n := by
  simp only [wave,zpow_natCast,SubmonoidClass.coe_pow]

include hfree hij hd hs hd0 hs0 in
lemma wave_positive_trace (n : ℕ) : τ (wave (d*s) ((n+1:ℕ):ℤ))=0 := by
  let D : Letter S τ := ⟨i,d,hd,hd0⟩
  let F : Letter S τ := ⟨j,s,hs,hs0⟩
  have h := alternating_power_centered hfree D F hij n
  change τ (((d:A)*(s:A))^(n+1))=0 at h
  simpa only [wave_nat,Submonoid.coe_mul] using h

include hstar hfree hij hd hs hd0 hs0 in
lemma wave_trace_zero (n : ℤ) (hn : n≠0) : τ (wave (d*s) n)=0 := by
  cases n with
  | ofNat n =>
      cases n with
      | zero => exact (hn rfl).elim
      | succ n => exact wave_positive_trace τ hfree d s i j hij hd hs hd0 hs0 n
  | negSucc n =>
      change τ (wave (d*s) (-((n+1:ℕ):ℤ)))=0
      rw [←wave_star,hstar,wave_positive_trace τ hfree d s i j hij hd hs hd0 hs0,star_zero]

include h1 hstar hfree hij hd hs hd0 hs0 in
lemma wave_trace (n : ℤ) : τ (wave (d*s) n)=if n=0 then 1 else 0 := by
  split_ifs with h
  · simp [h,h1]
  · exact wave_trace_zero τ hstar hfree d s i j hij hd hs hd0 hs0 n h

include h1 hstar hfree hij hd hs hd0 hs0 in
theorem dihedral_haar (a b : ℕ) :
    τ (star (((d:A)*(s:A))^a)*((d:A)*(s:A))^b)=if a=b then 1 else 0 := by
  have hw (m : ℕ) : ((d:A)*(s:A))^m=wave (d*s) (m:ℤ) := (wave_nat (d*s) m).symm
  rw [hw a,hw b,wave_star,←wave_add,wave_trace τ h1 hstar hfree d s i j hij hd hs hd0 hs0]
  have he : (-(a:ℤ)+(b:ℤ)=0) ↔ a=b := by omega
  simp only [he]

include hfree hij hd hs hd0 hs0 in
lemma reflection_positive_trace (n : ℕ) : τ (wave (d*s) (n:ℤ)*(d:A))=0 := by
  let D : Letter S τ := ⟨i,d,hd,hd0⟩
  let F : Letter S τ := ⟨j,s,hs,hs0⟩
  have h := alternating_odd_centered hfree F D hij.symm n
  have hm : ((d:A)*(s:A))^n*(d:A)=(d:A)*((s:A)*(d:A))^n := by
    exact mul_pow_mul (d:A) (s:A) n
  rw [wave_nat]
  change τ (((d:A)*(s:A))^n*(d:A))=0
  rw [hm]
  exact h

lemma symmetry_star (u : unitary A) (hu : (u:A)*(u:A)=1) : star (u:A)=(u:A) := by
  have h := congrArg ((star (u:A)) * ·) hu
  simpa only [←mul_assoc,Unitary.coe_star_mul_self,one_mul,mul_one] using h.symm

include htr hstar hfree hij hd hs hd0 hs0 in
lemma reflection_trace (hd2 : (d:A)*(d:A)=1) (n : ℤ) :
    τ (wave (d*s) n*(d:A))=0 := by
  cases n with
  | ofNat n => exact reflection_positive_trace τ hfree d s i j hij hd hs hd0 hs0 n
  | negSucc n =>
    change τ (wave (d*s) (-((n+1:ℕ):ℤ))*(d:A))=0
    calc
      _ = τ ((d:A)*wave (d*s) (-((n+1:ℕ):ℤ))) := htr _ _
      _ = τ (star (wave (d*s) ((n+1:ℕ):ℤ)*(d:A))) := by
        rw [star_mul,symmetry_star d hd2,wave_star]
      _ = star (τ (wave (d*s) ((n+1:ℕ):ℤ)*(d:A))) := hstar _
      _ = 0 := by rw [reflection_positive_trace τ hfree d s i j hij hd hs hd0 hs0,star_zero]

end Kadison.DihedralCorner

end

end
end

end OAI
