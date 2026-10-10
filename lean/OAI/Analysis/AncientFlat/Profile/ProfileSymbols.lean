import OAI.Analysis.AncientFlat.Profile.ProfileScaleMatch

namespace OAI
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace FlatSimilarity
open ProfileDecay ParabolicAnnular
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
omit [MeasurableSpace V] [BorelSpace V] in
theorem profile_symbols (G H : ℝ → ℝ) (c κ : ℝ) (hc : 0<c) (hκ : 0<κ)
    (hG : ContDiffOn ℝ ∞ G (Ici 0)) (hH : ContDiffOn ℝ ∞ H (Ici 0))
    (hH0 : H 0=c) (hmatch : ∀ u : ℝ, 0<u → H u=G (u^(-(1:ℝ)/2)))
    (hpos : ∀ y : ℝ, 0≤y → κ≤G y) :
    SymbolBounds c (profileAf (V := V) G) (profileBf G) := by
  obtain ⟨hA,hB⟩ := profile_smooth (V := V) G κ hκ hG hpos
  refine ⟨hc,⟨κ^2,sq_pos_of_pos hκ,?_⟩,hA,hB,?_⟩
  · intro x
    exact (sq_le_sq₀ hκ.le (hκ.le.trans (hpos _ (sq_nonneg _)))).mpr (hpos _ (sq_nonneg _))
  intro n
  have hn : (n:ℕ∞ω)≤(∞:ℕ∞ω) := ENat.natCast_le_of_coe_top_le_withTop le_rfl n
  let A := fun x : V => iteratedFDeriv ℝ n (fun y => profileAf G y-c^2) x
  let B := fun x : V => iteratedFDeriv ℝ n (profileBf G) x
  have hAc : Continuous A := (hA.sub contDiff_const).continuous_iteratedFDeriv hn
  have hBc : Continuous B := hB.continuous_iteratedFDeriv hn
  obtain ⟨C1,hC1⟩ := (isCompact_closedBall (0:V) 2).exists_bound_of_continuousOn hAc.continuousOn
  obtain ⟨C2,hC2⟩ := (isCompact_closedBall (0:V) 2).exists_bound_of_continuousOn hBc.continuousOn
  obtain ⟨C3,hC3,h3⟩ := families_decay (V := V) H c hH
    (fun u hu => compactification_pos G H c κ hc hκ hH0 hmatch hpos hu) hH0 n
  let C := max (C1+C2) C3
  have hC : 0≤C := hC3.trans (le_max_right _ _)
  have hweight (x : V) : (‖A x‖+‖B x‖)*(1+‖x‖)^(n+4)≤C*3^(n+4) := by
    by_cases hx : ‖x‖≤2
    · have haxb : x∈closedBall (0:V) 2 := by simpa [mem_closedBall,dist_zero_right] using hx
      have hj : ‖A x‖+‖B x‖≤C := (add_le_add (hC1 x haxb) (hC2 x haxb)).trans (le_max_left _ _)
      exact mul_le_mul hj (pow_le_pow_left₀ (by positivity) (by linarith : 1+‖x‖≤3) _)
        (by positivity) hC
    · have hx2 : 2<‖x‖ := lt_of_not_ge hx
      let r := ‖x‖/2
      have hr1 : 1≤r := by dsimp [r]; linarith
      have hr : 0<r := lt_of_lt_of_le zero_lt_one hr1
      let z : V := r⁻¹ • x
      have hxz : r • z=x := by simp [z,smul_smul,hr.ne']
      have hz : ‖z‖=2 := by
        dsimp [z,r]
        rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
        field_simp
        dsimp [r]
        ring
      have hs : r⁻¹^2∈Icc (0:ℝ) 1 := by
        refine ⟨sq_nonneg _,?_⟩
        exact pow_le_one₀ (inv_nonneg.mpr hr.le) (inv_le_one_of_one_le₀ hr1)
      have h3' := h3 (r⁻¹^2) hs z (by rw [hz]; norm_num)
      obtain ⟨heA,heB⟩ := family_jet_scale G H c κ hκ hG hpos hmatch n r hr z (by rw [hz]; norm_num)
      rw [heA,heB,hxz,norm_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hr.le n),←mul_add] at h3'
      change r^n*(‖A x‖+‖B x‖)≤C3*(r⁻¹^2)^2 at h3'
      have hscale : r^(n+4)*(‖A x‖+‖B x‖)≤C3 := by
        have hmul := mul_le_mul_of_nonneg_left h3' (pow_nonneg hr.le 4)
        have he : r^4*(C3*(r⁻¹^2)^2)=C3 := by field_simp
        rw [he] at hmul
        simpa only [pow_add,mul_assoc,mul_left_comm,mul_comm] using hmul
      have hw : 1+‖x‖≤3*r := by dsimp [r]; linarith
      calc
        _ ≤ (‖A x‖+‖B x‖)*(3*r)^(n+4) := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) hw _) (by positivity)
        _ = 3^(n+4)*(r^(n+4)*(‖A x‖+‖B x‖)) := by rw [mul_pow]; ring
        _ ≤ 3^(n+4)*C3 := mul_le_mul_of_nonneg_left hscale (by positivity)
        _ ≤ C*3^(n+4) := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  refine ⟨C*3^(n+4),by positivity,?_⟩
  intro x
  have hp : 0<1+‖x‖ := by positivity
  have he : (1+‖x‖)^(-(4:ℝ)-n)=((1+‖x‖)^(n+4))⁻¹ := by
    rw [show -(4:ℝ)-n=-((n+4:ℕ):ℝ) by push_cast; ring,
      Real.rpow_neg hp.le,Real.rpow_natCast]
  rw [he]
  exact (le_mul_inv_iff₀ (pow_pos hp _)).mpr (hweight x)
end FlatSimilarity

end

end OAI
