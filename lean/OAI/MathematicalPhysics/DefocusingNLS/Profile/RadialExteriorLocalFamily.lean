import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorContinuousTail
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorTailRemoval
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialExteriorUniformTail

namespace OAI

/-! A nonvanishing outgoing family on an open parameter neighborhood, at fixed power. -/

open Polynomial Set Filter
open scoped BoundedContinuousFunction
namespace DefocusingNLS

theorem boundedRadialPolynomialAfter_shift (T t : ℝ) (hT : 0 ≤ T) (P : ℂ[X]) :
    boundedRadialPolynomialAfter T P t=boundedRadialPolynomialAfter 0 P (max t T) := by
  simp only [boundedRadialPolynomialAfter_apply,radialExteriorTailVariable,
    max_eq_left (hT.trans (le_max_right t T))]

theorem boundedRadialResidualAfter_norm_le (T : ℝ) (hT : 0 ≤ T) (P : ℂ[X]) :
    ‖boundedRadialResidualAfter T P‖ ≤ ‖boundedRadialResidualAfter 0 P‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro t
  have he : boundedRadialResidualAfter T P t=boundedRadialResidualAfter 0 P (max t T) := by
    simp only [boundedRadialResidualAfter_apply,boundedRadialPolynomialAfter_shift T t hT P]
  rw [he]
  exact (boundedRadialResidualAfter 0 P).norm_coe_le_norm _

theorem exists_radialExterior_local_family_order (ν₀ m₀ : ℂ) (n : ℕ) (δ : ℝ) (J : ℕ)
    (hδ : 0 < δ) (hδm : δ < ‖m₀‖) :
    ∃ S : Set (ℂ × ℂ), IsOpen S ∧ (ν₀,m₀) ∈ S ∧
      ∃ T : ℝ, 0 ≤ T ∧ ∃ j : ℕ, J ≤ j ∧ ∃ v : S → ℝ →ᵇ ℂ × ℂ,
        Continuous v ∧
        (∀ z : S, radialExteriorMatrixBound z.val.1+
          radialExteriorCutoffRate n m₀ δ < 2*(j : ℝ)) ∧
        (∀ z : S, ‖z.val.2-m₀‖ ≤ δ/4) ∧
        let Z := fun (z : S) t => radialPolynomialJet
          (radialExteriorExpansion z.val.1 n z.val.2 j) t+
            radialExteriorUnweight (2*(j : ℝ)) (v z) t
        (∀ t, T ≤ t → Continuous (fun z => Z z t)) ∧
        (∀ z, Tendsto (Z z) atTop (nhds (z.val.2,0))) ∧
        ∀ z t, T ≤ t → (Z z t).1 ≠ 0 ∧
          HasDerivAt (fun s => (Z z s).1) (Z z t).2 t ∧
          HasDerivAt (fun s => (Z z s).2)
            (-(2*z.val.1+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*(Z z t).2-
              z.val.1*(z.val.1+10)*(Z z t).1+oddPowerNonlinearity n (Z z t).1) t := by
  let L := radialExteriorCutoffRate n m₀ δ
  obtain ⟨j,hj⟩ := exists_nat_gt (max ((radialExteriorMatrixBound ν₀+L+2)/2) (J : ℝ))
  have hjbound := lt_of_le_of_lt (le_max_left ((radialExteriorMatrixBound ν₀+L+2)/2) (J : ℝ)) hj
  have hJ : J ≤ j := by exact_mod_cast (le_max_right ((radialExteriorMatrixBound ν₀+L+2)/2) (J : ℝ)).trans hj.le
  let κ : ℝ := 2*(j : ℝ)
  have hκ : radialExteriorMatrixBound ν₀+L+2 < κ := by dsimp [κ]; linarith
  have hκ0 : 0 < κ := by
    have := radialExteriorMatrixBound_pos ν₀
    have := radialExteriorCutoffRate_nonneg n m₀ δ
    dsimp [L] at hκ
    linarith
  let P := fun z : ℂ × ℂ => radialExteriorExpansion z.1 n z.2 j
  let f := fun z : ℂ × ℂ => boundedRadialPolynomialAfter 0 (P z)
  let r := fun z : ℂ × ℂ => boundedRadialResidualAfter 0
    (radialExteriorResidualQuotient z.1 n z.2 j)
  let M : ℝ := ‖r (ν₀,m₀)‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hf : Continuous f := continuous_radialExteriorBase n j 0 le_rfl
  have hr : Continuous r := continuous_radialExteriorSource n j 0 le_rfl
  have hB : Continuous (fun z : ℂ × ℂ => radialExteriorMatrixBound z.1+L) := by
    unfold radialExteriorMatrixBound
    fun_prop
  let S : Set (ℂ × ℂ) := {z | radialExteriorMatrixBound z.1+L < κ-1 ∧
    ‖f z-f (ν₀,m₀)‖ < δ/8 ∧ ‖r z‖ < M}
  have hS : IsOpen S := (isOpen_lt hB continuous_const).inter
    ((isOpen_lt (hf.sub continuous_const).norm continuous_const).inter
      (isOpen_lt hr.norm continuous_const))
  have hp : (ν₀,m₀) ∈ S := by
    change radialExteriorMatrixBound ν₀+L < κ-1 ∧
      ‖f (ν₀,m₀)-f (ν₀,m₀)‖ < δ/8 ∧ ‖r (ν₀,m₀)‖ < M
    refine ⟨by linarith,?_,by dsimp [M]; linarith⟩
    simpa using (show 0 < δ/8 by positivity)
  have hPlim : Tendsto (radialExteriorPolynomialFunction (P (ν₀,m₀))) atTop (nhds m₀) := by
    simpa only [P,radialExteriorExpansion_constant] using
      radialExteriorPolynomialFunction_tendsto (P (ν₀,m₀))
  have hdec : Tendsto (fun t : ℝ => Real.exp (-κ*t)*M) atTop (nhds 0) := by
    have hh := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hκ0)).mul_const M
    simpa only [Function.comp_def,id_eq,neg_mul,zero_mul] using! hh
  obtain ⟨T,hT⟩ := eventually_atTop.mp ((eventually_ge_atTop (0 : ℝ)).and
    (((tendsto_iff_norm_sub_tendsto_zero.mp hPlim).eventually
      (gt_mem_nhds (show 0 < δ/8 by positivity))).and
      (hdec.eventually (gt_mem_nhds (show 0 < δ/4 by positivity)))))
  have hT0 : 0 ≤ T := (hT T le_rfl).1
  have hbase : ∀ (z : S) t, ‖boundedRadialPolynomialAfter T (P z.val) t-m₀‖ ≤ δ/4 := by
    intro z t
    let s := max t T
    have hs : T ≤ s := le_max_right _ _
    have hs0 : 0 ≤ s := hT0.trans hs
    have hpnear := (hT s hs).2.1
    have hz := ((z.property).2.1)
    have hdiff := (f z.val-f (ν₀,m₀)).norm_coe_le_norm s
    change ‖f z.val s-f (ν₀,m₀) s‖ ≤ ‖f z.val-f (ν₀,m₀)‖ at hdiff
    rw [boundedRadialPolynomialAfter_shift T t hT0]
    change ‖f z.val s-m₀‖ ≤ δ/4
    have he : f (ν₀,m₀) s=radialExteriorPolynomialFunction (P (ν₀,m₀)) s :=
      boundedRadialPolynomialAfter_eq 0 _ s hs0
    have htri := dist_triangle (f z.val s) (f (ν₀,m₀) s) m₀
    rw [dist_eq_norm,dist_eq_norm,dist_eq_norm,he] at htri
    rw [he] at hdiff
    linarith
  have hparam : ∀ z : S, ‖z.val.2-m₀‖ ≤ δ/4 := by
    intro z
    have hh : Tendsto (fun t => ‖radialExteriorPolynomialFunction (P z.val) t-m₀‖)
        atTop (nhds ‖z.val.2-m₀‖) := by
      simpa only [P,radialExteriorExpansion_constant] using
        ((radialExteriorPolynomialFunction_tendsto (P z.val)).sub_const m₀).norm
    apply le_of_tendsto hh
    filter_upwards [eventually_ge_atTop T] with t ht
    have hb := hbase z t
    rw [boundedRadialPolynomialAfter_eq T _ t ht] at hb
    exact hb
  obtain ⟨v,hvc,hv⟩ := exists_continuous_radialExterior_corrections S n j m₀ δ T hδ hT0
    (fun z => by have := z.property.1; dsimp [κ,L] at *; linarith) hbase
  let Z := fun (z : S) t => radialPolynomialJet (P z.val) t+radialExteriorUnweight κ (v z) t
  have hvM (z : S) : ‖v z‖ ≤ M := by
    have hden : 1 < κ-(radialExteriorMatrixBound z.val.1+L) := by
      have := z.property.1
      linarith
    have hrM : ‖boundedRadialResidualAfter T
        (radialExteriorResidualQuotient z.val.1 n z.val.2 j)‖ ≤ M :=
      (boundedRadialResidualAfter_norm_le T hT0 _).trans z.property.2.2.le
    apply (hv z).1.trans
    change ‖_‖/(κ-(radialExteriorMatrixBound z.val.1+L)) ≤ M
    apply (div_le_iff₀ (by linarith : 0 < κ-(radialExteriorMatrixBound z.val.1+L))).mpr
    nlinarith
  refine ⟨S,hS,hp,T,hT0,j,hJ,v,hvc,?_,hparam,?_,?_,?_⟩
  · intro z
    have := z.property.1
    change radialExteriorMatrixBound z.val.1+L < κ
    linarith
  · intro t ht
    exact continuous_radialExterior_corrected_boundary S n j t (hT0.trans ht) v hvc
  · intro z
    simpa only [P,κ,radialExteriorExpansion_constant] using
      radialExterior_corrected_jet_tendsto κ hκ0 (P z.val) (v z)
  · intro z t ht
    have hpnear : ‖radialExteriorPolynomialFunction (P z.val) t-m₀‖ ≤ δ/4 := by
      rw [← boundedRadialPolynomialAfter_eq T _ t ht]
      exact hbase z t
    have hynear : ‖radialExteriorUnweight κ (v z) t‖ ≤ δ/4 :=
      (radialExteriorUnweight_norm κ t (v z) M
        ((v z).norm_coe_le_norm t |>.trans (hvM z))).trans ((hT t ht).2.2.le)
    have hznear : ‖(Z z t).1-m₀‖ ≤ δ/2 := by
      have htri : ‖(Z z t).1-m₀‖ ≤
          ‖radialExteriorPolynomialFunction (P z.val) t-m₀‖+
            ‖(radialExteriorUnweight κ (v z) t).1‖ := by
        change ‖(radialExteriorPolynomialFunction (P z.val) t+
          (radialExteriorUnweight κ (v z) t).1)-m₀‖ ≤ _
        rw [add_sub_right_comm]
        exact norm_add_le _ _
      have hh := (norm_fst_le (radialExteriorUnweight κ (v z) t)).trans hynear
      linarith
    have hne : (Z z t).1 ≠ 0 := by
      intro he
      rw [he,zero_sub,norm_neg] at hznear
      linarith
    refine ⟨hne,?_⟩
    exact radialExterior_tail_cutoff_removal z.val.1 m₀ n j δ T (P z.val)
      (radialExteriorResidualQuotient z.val.1 n z.val.2 j)
      (radialExteriorResidualQuotient_spec _ _ _ _) (v z) t ht
      (hpnear.trans (by linarith)) (hznear.trans (by linarith)) ((hv z).2.2 t)

theorem exists_radialExterior_local_family (ν₀ m₀ : ℂ) (n : ℕ) (δ : ℝ)
    (hδ : 0 < δ) (hδm : δ < ‖m₀‖) :
    ∃ S : Set (ℂ × ℂ), IsOpen S ∧ (ν₀,m₀) ∈ S ∧
      ∃ T : ℝ, 0 ≤ T ∧ ∃ j : ℕ, ∃ v : S → ℝ →ᵇ ℂ × ℂ,
        Continuous v ∧
        (∀ z : S, radialExteriorMatrixBound z.val.1+
          radialExteriorCutoffRate n m₀ δ < 2*(j : ℝ)) ∧
        (∀ z : S, ‖z.val.2-m₀‖ ≤ δ/4) ∧
        let Z := fun (z : S) t => radialPolynomialJet
          (radialExteriorExpansion z.val.1 n z.val.2 j) t+
            radialExteriorUnweight (2*(j : ℝ)) (v z) t
        (∀ t, T ≤ t → Continuous (fun z => Z z t)) ∧
        (∀ z, Tendsto (Z z) atTop (nhds (z.val.2,0))) ∧
        ∀ z t, T ≤ t → (Z z t).1 ≠ 0 ∧
          HasDerivAt (fun s => (Z z s).1) (Z z t).2 t ∧
          HasDerivAt (fun s => (Z z s).2)
            (-(2*z.val.1+10+Complex.I*(Real.exp (2*t)/2 : ℝ))*(Z z t).2-
              z.val.1*(z.val.1+10)*(Z z t).1+oddPowerNonlinearity n (Z z t).1) t := by
  obtain ⟨S,hS,hm,T,hT,j,_hJ,v,hv,hbound,hparam,hrest⟩ :=
    exists_radialExterior_local_family_order ν₀ m₀ n δ 0 hδ hδm
  exact ⟨S,hS,hm,T,hT,j,v,hv,hbound,hparam,hrest⟩

end DefocusingNLS

end OAI
