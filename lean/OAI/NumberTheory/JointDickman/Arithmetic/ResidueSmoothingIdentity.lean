import OAI.NumberTheory.JointDickman.Arithmetic.PeriodicConvolutionSmoothing

namespace OAI

/-! # Identifying progression smoothing with the arithmetic residue average -/
namespace JointDickman
open Finset Classical

theorem sum_residue_integer_window {q : ℕ} (hq : 0 < q) (R v : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ Ioc v (v+q*R), if (n : ZMod q) = (v : ZMod q) then f n else 0) =
      ∑ h ∈ range R, f (v+q*(h+1)) := by
  have hs : (range R).image (fun h => v+q*(h+1)) =
      (Ioc v (v+q*R)).filter (fun n : ℕ => (n : ZMod q) = (v : ZMod q)) := by
    ext n
    simp only [mem_image,mem_filter,mem_Ioc,mem_range]
    constructor
    · rintro ⟨h,hh,rfl⟩
      refine ⟨⟨by nlinarith,by nlinarith⟩,?_⟩
      simp
    · rintro ⟨⟨hvn,hupper⟩,hr⟩
      have hm : n ≡ v [MOD q] := by rwa [ZMod.natCast_eq_natCast_iff] at hr
      have hd : q ∣ n-v := hm.symm.dvd'
      let k := (n-v)/q
      have hk : q*k = n-v := Nat.mul_div_cancel' hd
      have hnv : 0 < n-v := Nat.sub_pos_of_lt hvn
      have hk0 : 0 < k := by nlinarith
      have hnsub : n-v ≤ q*R := by omega
      have hkR : k ≤ R := by nlinarith
      refine ⟨k-1,by omega,?_⟩
      have hk1 : k-1+1=k := by omega
      rw [hk1,hk]
      omega
  rw [← sum_filter,← hs,sum_image]
  intro a _ b _ hab
  nlinarith

theorem residueSmoothed_eq_residueBinAverage {ι : Type*} [Fintype ι]
    (E : ι → Finset ℕ) (ζ : ι → ℂ) (μ : ℂ) (w : ArithmeticFunction ℝ)
    {q R : ℕ} (hq : 0 < q) (hR : 0 < R) (v : ℕ) :
    residueSmoothed (fun n => (binLabel E ζ n-μ)*(w n : ℂ)) q R v =
      (q : ℂ)*residueBinAverage E ζ μ w (v : ZMod q) (q*R : ℕ) v := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hRC : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold residueSmoothed residueBinAverage
  rw [← Nat.cast_add,Nat.floor_natCast,Nat.floor_natCast,sum_residue_integer_window hq]
  push_cast
  field_simp

end JointDickman

end OAI
