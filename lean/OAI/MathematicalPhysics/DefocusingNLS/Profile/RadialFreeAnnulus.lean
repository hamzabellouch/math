import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeModulus
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorExtendedTail

namespace OAI

/-! A genuine subunit annulus for the boundary-normalized free exterior. -/

open Set Filter
namespace DefocusingNLS

theorem radialFreeSlowValue_tendsto (q m : ℂ) (hq : -1 < q.re) :
    Tendsto (radialFreeSlowValue q m) atTop (nhds m) := by
  obtain ⟨C,_hC,hbound⟩ := radialFreeSlowValue_remainder q m hq 0
  have he : Tendsto (fun t : ℝ => C*Real.exp (-2*t)) atTop (nhds 0) := by
    have hh := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (show (0 : ℝ)<2 by norm_num))).const_mul C
    simpa only [mul_zero,neg_mul,Function.comp_def,id_eq] using hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) _ he
  filter_upwards [eventually_ge_atTop (Real.log 4/2)] with t ht
  simpa only [radialFreeExpansion,radialExteriorPolynomialFunction,Polynomial.eval_C,
    Nat.reduceAdd,Nat.cast_one,mul_one] using hbound t ht

theorem radialFreeSlow_annulus
    (w : Metric.closedBall (0 : ℂ) (ProfileCertificate.radius : ℝ)) (m : ℂ)
    (hm : m ≠ 0)
    (hsmall : ‖radialFreeSlowValue
      (-Complex.I*(((ProfileCertificate.centerB : ℝ)+w.val.re : ℝ) : ℂ)) m
        (Real.log innerBoundaryRadius)‖ < 1) :
    let q := -Complex.I*(((ProfileCertificate.centerB : ℝ)+w.val.re : ℝ) : ℂ)
    ∃ δ ρ : ℝ, 0 < δ ∧ δ < ‖m‖ ∧ ‖m‖+2*δ < 1 ∧ ρ < 1 ∧
      (∀ t, Real.log innerBoundaryRadius ≤ t →
        ‖(radialFreeSlowJet q m t).1‖+2*δ ≤ ρ) ∧
      ∀ t, Real.log innerBoundaryRadius ≤ t → δ < ‖(radialFreeSlowJet q m t).1‖ := by
  intro q
  let h := ‖radialFreeSlowValue q m (Real.log innerBoundaryRadius)‖
  have h0 : 0 ≤ h := norm_nonneg _
  have h1 : h < 1 := hsmall
  have hmono := radialFreeSlowValue_norm_antitone w m
  have hlim := (radialFreeSlowValue_tendsto q m (by simp [q])).norm
  have hupper (t : ℝ) (ht : Real.log innerBoundaryRadius ≤ t) :
      ‖radialFreeSlowValue q m t‖ ≤ h := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  have hlower (t : ℝ) (ht : Real.log innerBoundaryRadius ≤ t) :
      ‖m‖ ≤ ‖radialFreeSlowValue q m t‖ := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop t] with s hs
    exact hmono ht (ht.trans hs) hs
  have hmh : ‖m‖ ≤ h := hlower _ le_rfl
  let δ := min (‖m‖/4) ((1-h)/8)
  let ρ := (1+h)/2
  have hm0 : 0 < ‖m‖ := norm_pos_iff.mpr hm
  have hd0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hdm : δ ≤ ‖m‖/4 := min_le_left _ _
  have hdh : δ ≤ (1-h)/8 := min_le_right _ _
  refine ⟨δ,ρ,hd0,by linarith,by linarith,by dsimp [ρ]; linarith,?_,?_⟩
  · intro t ht
    change ‖radialFreeSlowValue q m t‖+2*δ ≤ ρ
    have hh := hupper t ht
    dsimp [ρ]
    linarith
  · intro t ht
    change δ < ‖radialFreeSlowValue q m t‖
    have hh := hlower t ht
    linarith

noncomputable def radialFreeBoundaryCoefficient (b h : ℝ) : ℂ :=
  (h : ℂ)/normalizedSlowSolution (-Complex.I*(b : ℂ)) 6
    (radialFreeSlowArgument (Real.log innerBoundaryRadius))

theorem radialFreeBoundaryCoefficient_spec
    (w : Metric.closedBall (0 : ℂ) (ProfileCertificate.radius : ℝ))
    (h : ℝ) (hh : 0 < h) :
    let b := (ProfileCertificate.centerB : ℝ)+w.val.re
    radialFreeBoundaryCoefficient b h ≠ 0 ∧
      radialFreeSlowValue (-Complex.I*(b : ℂ)) (radialFreeBoundaryCoefficient b h)
        (Real.log innerBoundaryRadius)=(h : ℂ) := by
  intro b
  let Z := (ProfileCertificate.centerZ : ℝ)+w.val.im
  have hz := (ProfileCertificate.disk_coordinates w).2
  have hZ : |Z-(ProfileCertificate.centerZ : ℝ)| ≤ (1/100000000 : ℝ) := by
    simpa [Z,ProfileCertificate.radius] using hz
  obtain ⟨hR,_,hshell⟩ := radial_boundary_shell_geometry Z hZ
  have hZ0 : 0 < Z := by
    have hb := (abs_le.mp hz).1
    dsimp [Z]
    norm_num [ProfileCertificate.centerZ,ProfileCertificate.radius] at hb ⊢
    linarith
  have hR2 : Z ≤ innerBoundaryRadius^2/4 := by
    have he := freeProfileRadius_sq hZ0.le
    dsimp [freeProfileRadius] at he
    nlinarith [hshell.1]
  have he : radialFreeSlowArgument (Real.log innerBoundaryRadius)=
      -Complex.I*((innerBoundaryRadius^2/4 : ℝ) : ℂ) := by
    dsimp [radialFreeSlowArgument]
    rw [show (2 : ℝ)*Real.log innerBoundaryRadius=
      Real.log innerBoundaryRadius+Real.log innerBoundaryRadius by ring,
      Real.exp_add,Real.exp_log (by linarith [innerBoundaryRadius_bounds.1])]
    congr 2
    ring
  have hN : normalizedSlowSolution (-Complex.I*(b : ℂ)) 6
      (radialFreeSlowArgument (Real.log innerBoundaryRadius)) ≠ 0 := by
    apply mul_ne_zero
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl (radialFreeSlowArgument_ne_zero _))
    · rw [he]
      exact (ProfileCertificate.disk_free_exterior w _ hR2).1
  refine ⟨div_ne_zero (Complex.ofReal_ne_zero.mpr hh.ne') hN,?_⟩
  exact div_mul_cancel₀ (h : ℂ) hN

theorem exists_radialExterior_boundary_free_limit
    (w : Metric.closedBall (0 : ℂ) (ProfileCertificate.radius : ℝ))
    (h : ℝ) (hh : 0 < h) (hh1 : h < 1) (ν m : ℕ → ℂ)
    (hν : Tendsto ν atTop
      (nhds (2*Complex.I*(((ProfileCertificate.centerB : ℝ)+w.val.re : ℝ) : ℂ))))
    (hm : Tendsto m atTop
      (nhds (radialFreeBoundaryCoefficient ((ProfileCertificate.centerB : ℝ)+w.val.re) h))) :
    let q := -Complex.I*(((ProfileCertificate.centerB : ℝ)+w.val.re : ℝ) : ℂ)
    let m₀ := radialFreeBoundaryCoefficient ((ProfileCertificate.centerB : ℝ)+w.val.re) h
    ∃ Z : ℕ → ℝ → ℂ × ℂ,
      TendstoUniformlyOn Z (radialFreeSlowJet q m₀) atTop
        (Ici (Real.log innerBoundaryRadius)) ∧
      (∀ n, Tendsto (Z n) atTop (nhds (m n,0))) ∧
      ∀ᶠ n in atTop, ∀ t, Real.log innerBoundaryRadius ≤ t →
        (Z n t).1 ≠ 0 ∧ HasDerivAt (Z n)
          ((Z n t).2,-(2*ν n+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*(Z n t).2-
            ν n*(ν n+10)*(Z n t).1+oddPowerNonlinearity n (Z n t).1) t := by
  intro q m₀
  obtain ⟨hn,hvalue⟩ := radialFreeBoundaryCoefficient_spec w h hh
  have hsmall : ‖radialFreeSlowValue q m₀ (Real.log innerBoundaryRadius)‖ < 1 := by
    rw [hvalue,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hh]
    exact hh1
  obtain ⟨δ,ρ,hd,hdm,hm1,hρ,hupper,hlower⟩ := radialFreeSlow_annulus w m₀ hn hsmall
  apply exists_radialExterior_extended_tail ν m q m₀ (by simp [q]) _ hm δ ρ
    (Real.log innerBoundaryRadius) hd hdm hm1 hρ hupper hlower
  convert hν using 1
  dsimp [q]
  congr 1
  ring

end DefocusingNLS

end OAI
