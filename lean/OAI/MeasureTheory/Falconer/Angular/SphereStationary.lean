import OAI.MeasureTheory.Falconer.Angular.SphereStationaryAssembly

namespace OAI

/-! # Full-sphere stationary phase for the actual amplitude

The two pole expansions are combined with the proved off-pole estimate.
The only inputs are the recorded gnomonic surface formula and the precise
quadratic stationary-phase specialization. No spherical estimate is an
assumption.
-/

namespace Falconer
open Set
open scoped ContDiff

noncomputable def directStationarySum (m J : ℕ) (Λ : ℝ)
    (B : Space (m+3) → ℂ) (e : Sphere (m+3)) : ℂ :=
  ∑ j ∈ Finset.range J, ((Λ^(-(j : ℝ)) : ℝ) : ℂ)*actualStationaryCoefficient m j B e

/-- Full outgoing/incoming expansion, with the original symbol and
original sphere measure. The derivative budget is `2*J+d`. -/
theorem sphere_stationary_expansion
    (hgnomonic : PublishedGnomonicSurface) (hquadratic : PublishedQuadraticStationary)
    (m J : ℕ) (hJ : 1 ≤ J) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (e : Sphere (m+3)) (B : Space (m+3) → ℂ),
      ContDiff ℝ ∞ B → ∀ C D : ℝ, 0 ≤ C → 1 ≤ D →
      (∀ j ≤ 2*J+(m+2)+1, ∀ w : Sphere (m+3),
        ‖iteratedFDeriv ℝ j B w‖ ≤ C*D^j) →
      ∀ Λ : ℝ, 1 ≤ Λ →
      ‖((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)*sphereOscillation Λ e (fun w => B w) -
        (Complex.exp (Complex.I*(Λ : ℂ))*directStationarySum m J Λ B e +
          star (Complex.exp (Complex.I*(Λ : ℂ))*
            directStationarySum m J Λ (antipodalConjugate B) e))‖ ≤
        A*Λ^(-(J : ℝ))*C*D^(2*J+(m+2)+1) := by
  obtain ⟨A,hA,hpole⟩ := pole_stationary_remainder_of_ambient_bounds
    hgnomonic hquadratic m J hJ
  obtain ⟨O,hO,hoff⟩ := sphere_offPole_decay_of_ambient_bounds
    hgnomonic (m+1) (J+(m+2)+1) (by omega)
  refine ⟨2*A+O,by positivity,?_⟩
  intro e B hB C D hC hD hb Λ hΛ
  let p : ℂ := ((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ)
  let z := Complex.exp (Complex.I*(Λ : ℂ))
  let Ip := sphereOscillation Λ e (fun w => poleLocalizedAmbient e B w)
  let Im := sphereOscillation Λ e (fun w => poleLocalizedAmbient (oppositePole e) B w)
  let Io := sphereOscillation Λ e (fun w => offPoleLocalizedAmbient e B w)
  let Sp := z*directStationarySum m J Λ B e
  let Sm := star (z*directStationarySum m J Λ (antipodalConjugate B) e)
  let T := Λ^(-(J : ℝ))*C*D^(2*J+(m+2)+1)
  have hp : ‖p*Ip-Sp‖ ≤ A*T := by
    rw [show A*T = A*Λ^(-(J : ℝ))*C*D^(2*J+(m+2)+1) by dsimp [T]; ring]
    simpa only [p,Ip,Sp,z,directStationarySum,remove_outgoing_phase] using
      hpole e B hB C D hC hD hb Λ hΛ
  have hanti : ContDiff ℝ ∞ (antipodalConjugate B) := antipodalConjugate_contDiff hB
  have hab : ∀ j ≤ 2*J+(m+2)+1, ∀ w : Sphere (m+3),
      ‖iteratedFDeriv ℝ j (antipodalConjugate B) w‖ ≤ C*D^j := by
    intro j hj w
    rw [antipodalConjugate_derivative_norm]
    exact hb j hj (oppositePole w)
  have hpa : ‖p*sphereOscillation Λ e
      (fun w => poleLocalizedAmbient e (antipodalConjugate B) w)-
        z*directStationarySum m J Λ (antipodalConjugate B) e‖ ≤ A*T := by
    rw [show A*T = A*Λ^(-(J : ℝ))*C*D^(2*J+(m+2)+1) by dsimp [T]; ring]
    simpa only [p,z,directStationarySum,remove_outgoing_phase] using
      hpole e (antipodalConjugate B) hanti C D hC hD hab Λ hΛ
  have hm : ‖p*Im-Sm‖ ≤ A*T := by
    have hpstar : star p = p := by
      change (starRingEnd ℂ) ((Λ^(((m+2 : ℕ) : ℝ)/2) : ℝ) : ℂ) = _
      exact Complex.conj_ofReal _
    have he : p*Im-Sm = star (p*sphereOscillation Λ e
        (fun w => poleLocalizedAmbient e (antipodalConjugate B) w)-
          z*directStationarySum m J Λ (antipodalConjugate B) e) := by
      dsimp only [Im,Sm]
      simp only [poleLocalized_opposite_oscillation,star_sub,star_mul',hpstar]
      rfl
    rw [he,norm_star]
    exact hpa
  have hΛp : 0 < Λ := zero_lt_one.trans_le hΛ
  have hpr : 0 < Λ^(((m+2 : ℕ) : ℝ)/2) := Real.rpow_pos_of_pos hΛp _
  have ho : ‖p*Io‖ ≤ O*T := by
    have hod := hoff e B hB C D hC hD
      (fun j hj => hb j (by omega)) Λ hΛp
    rw [norm_mul,show ‖p‖ = Λ^(((m+2 : ℕ) : ℝ)/2) by
      simp only [p,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpr]]
    apply (mul_le_mul_of_nonneg_left hod hpr.le).trans
    calc
      _ = O*C*(Λ^(((m+2 : ℕ) : ℝ)/2)*(D/Λ)^(J+(m+2)+1)) := by ring
      _ ≤ O*C*(Λ^(-(J : ℝ))*D^(2*J+(m+2)+1)) :=
        mul_le_mul_of_nonneg_left (stationary_offPole_scale m J hD hΛ) (mul_nonneg hO hC)
      _ = O*T := by dsimp [T]; ring
  have hsplit : p*sphereOscillation Λ e (fun w => B w)-(Sp+Sm) =
      (p*Ip-Sp)+(p*Im-Sm)+p*Io := by
    rw [sphereOscillation_pole_partition Λ e hB]
    dsimp [Ip,Im,Io]
    ring
  change ‖p*sphereOscillation Λ e (fun w => B w)-(Sp+Sm)‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ (‖p*Ip-Sp‖+‖p*Im-Sm‖)+‖p*Io‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (A*T+A*T)+O*T := add_le_add (add_le_add hp hm) ho
    _ = _ := by dsimp [T]; ring

end Falconer

end OAI
