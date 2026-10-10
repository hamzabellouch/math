import OAI.MeasureTheory.Falconer.Radial.WeakRadialParameters
import OAI.MeasureTheory.Falconer.Radial.WeakRadialCapParameters

namespace OAI

/-! # Simultaneous fixed losses for the single-scale weak radial theorem -/

namespace Falconer

structure WeakRadialLosses (n : ℕ) (ℓ ζ : ℝ) where
  J : ℕ
  e : ℝ
  f : ℝ
  τ : ℝ
  η : ℝ
  lam : ℝ
  u : ℝ
  ε : ℝ
  c : ℝ
  J_pos : 0 < J
  e_pos : 0 < e
  f_pos : 0 < f
  η_pos : 0 < η
  η_le : η ≤ 1/2
  lam_pos : 0 < lam
  u_pos : 0 < u
  ε_pos : 0 < ε
  c_pos : 0 < c
  ε_lt_lam : ε < lam
  regularization_gap : 2*((n:ℝ)+2)*lam < τ
  count_gap : 0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u
  incidence_gap : c*((n:ℝ)+1) < u
  slab_gap : c*((n:ℝ)+1) < η*ζ-ε
  near_gap : ε < (n:ℝ)/((J:ℝ)+2)
  cap_gap : (J:ℝ)*(e+f)-((n:ℝ)/(n+1))*
    ((n:ℝ)-((n:ℝ)+5)*lam-2*((n:ℝ)+1)/((J:ℝ)+2)) < -ℓ

theorem exists_weak_radial_losses {n : ℕ} (hn : 1 ≤ n) {ℓ ζ : ℝ}
    (hζ : 0 < ζ) (hℓ : ℓ < ((n:ℝ)/(n+1))*(n:ℝ)) :
    Nonempty (WeakRadialLosses n ℓ ζ) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hd : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hβ : 0 < (n:ℝ)/(n+1) := div_pos hn0 hd
  obtain ⟨J,hJ,e,f,L,he,hf,hL,hcap⟩ := weak_radial_cap_parameters (n+1) hβ
    (by simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using hℓ)
  obtain ⟨η,τ,u,ε₀,hη,hηle,hτ,hu,hε₀,hcount,hslab⟩ := weak_radial_bounded_exponents hn he hζ
  let lam : ℝ := min (L/(4*((n:ℝ)+5))) (τ/(4*((n:ℝ)+2)))
  have hlam : 0 < lam := lt_min (by positivity) (by positivity)
  have hlamL : ((n:ℝ)+5)*lam < L := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 4*((n:ℝ)+5))).mp
      (min_le_left (L/(4*((n:ℝ)+5))) (τ/(4*((n:ℝ)+2))))
    change lam*(4*((n:ℝ)+5)) ≤ L at hh
    nlinarith
  have hlamτ : 2*((n:ℝ)+2)*lam < τ := by
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 4*((n:ℝ)+2))).mp
      (min_le_right (L/(4*((n:ℝ)+5))) (τ/(4*((n:ℝ)+2))))
    change lam*(4*((n:ℝ)+2)) ≤ τ at hh
    nlinarith
  let ε : ℝ := min (lam/2) (min ε₀ ((n:ℝ)/(4*((J:ℝ)+2))))
  have hε : 0 < ε := lt_min (by positivity) (lt_min hε₀ (by positivity))
  have hEpsLam : ε < lam := (min_le_left _ _).trans_lt (by linarith : lam/2 < lam)
  have hεold : ε ≤ ε₀ := (min_le_right _ _).trans (min_le_left _ _)
  have hεnear : ε < (n:ℝ)/((J:ℝ)+2) := by
    have hh : ε ≤ (n:ℝ)/(4*((J:ℝ)+2)) := (min_le_right _ _).trans (min_le_right _ _)
    have hq : 0 < (n:ℝ)/((J:ℝ)+2) := by positivity
    have heq : (n:ℝ)/(4*((J:ℝ)+2)) = ((n:ℝ)/((J:ℝ)+2))/4 := by
      field_simp
    rw [heq] at hh
    linarith
  let c : ℝ := u/(2*((n:ℝ)+1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcd : c*((n:ℝ)+1) = u/2 := by dsimp [c]; field_simp
  refine ⟨⟨J,e,f,τ,η,lam,u,ε,c,hJ,he,hf,hη,hηle,hlam,hu,hε,hc,hEpsLam,
    hlamτ,hcount,?_,?_,hεnear,?_⟩⟩
  · rw [hcd]
    linarith
  · rw [hcd]
    linarith
  · have hm := mul_lt_mul_of_pos_left hlamL hβ
    norm_num only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] at hcap
    nlinarith

end Falconer

end OAI
