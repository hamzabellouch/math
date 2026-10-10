import OAI.Analysis.LipschitzHilbert.Trees.SourceDensityModel
import OAI.Analysis.LipschitzHilbert.Trees.SourceLatticeScaleEnergy
import OAI.Analysis.LipschitzHilbert.Packets.PacketVectorDerivative

namespace OAI

/-! A single short-tree term is controlled by its actual density test.
Extra packet decay retains the distance to the horizontal strip. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable

private theorem taxicab_quadratic_le (x y : ℝ) :
    1+|x|+|y| ≤ 3*((1+x^2)*(1+y^2)) := by
  have hx : |x|≤1+x^2 := by nlinarith [sq_nonneg (|x|-1),sq_abs x]
  have hy : |y|≤1+y^2 := by nlinarith [sq_nonneg (|y|-1),sq_abs y]
  have ha : 1≤1+x^2 := le_add_of_nonneg_right (sq_nonneg x)
  have hb : 1≤1+y^2 := le_add_of_nonneg_right (sq_nonneg y)
  nlinarith [mul_le_mul_of_nonneg_right ha (show 0≤1+y^2 by positivity),
    mul_le_mul_of_nonneg_left hb (show 0≤1+x^2 by positivity)]

/-- The physical product envelope dominates the density kernel, while
leaving any prescribed number of horizontal decay powers. -/
theorem packet_envelope_density_decay (T : SlopeBox) (D r : ℕ) (z : ℝ×ℝ) :
    lineEnvelope T.x T.length (D+r) z.1 *
      lineEnvelope (T.y-T.slope*T.x) T.width (D+r) (z.2-T.slope*z.1) ≤
      3^D*T.densityKernel D z*lineEnvelope T.x T.length r z.1 := by
  let x := T.horizontal z
  let y := T.transverse z
  let A := 1+x^2
  let B := 1+y^2
  let R := 1+|x|+|y|
  have hA : 1≤A := le_add_of_nonneg_right (sq_nonneg x)
  have hB : 1≤B := le_add_of_nonneg_right (sq_nonneg y)
  have hR : 0<R := by dsimp [R]; positivity
  have hA0 : 0<A := zero_lt_one.trans_le hA
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hpow : R^D≤3^D*(A^D*B^D) := by
    simpa only [mul_pow,mul_assoc] using
      pow_le_pow_left₀ hR.le (taxicab_quadratic_le x y) D
  have hratio : (A^D*B^D)⁻¹≤3^D*(R^D)⁻¹ := by
    have hdiv : 1/(A^D*B^D)≤3^D/(R^D) := by
      rw [div_le_div_iff₀ (mul_pos (pow_pos hA0 D) (pow_pos hB0 D)) (pow_pos hR D)]
      simpa only [one_mul] using hpow
    simpa only [one_div,div_eq_mul_inv,one_mul] using hdiv
  have hBr : (B^r)⁻¹≤1 := (inv_le_one₀ (pow_pos hB0 r)).2 (one_le_pow₀ hB)
  have heX : lineEnvelope T.x T.length (D+r) z.1=(A^(D+r))⁻¹ := rfl
  have heY : lineEnvelope (T.y-T.slope*T.x) T.width (D+r) (z.2-T.slope*z.1)=
      (B^(D+r))⁻¹ := by
    dsimp [lineEnvelope,B,y,SlopeBox.transverse]
    congr 3
    ring
  have heD : T.densityKernel D z=(R^D)⁻¹ := by
    change (1+(|x|+|y|))^(-(D:ℝ))=(R^D)⁻¹
    rw [←add_assoc,Real.rpow_neg hR.le,Real.rpow_natCast]
  rw [heX,heY,heD]
  change (A^(D+r))⁻¹*(B^(D+r))⁻¹≤3^D*(R^D)⁻¹*(A^r)⁻¹
  calc
    _ = (A^D*B^D)⁻¹*(A^r)⁻¹*(B^r)⁻¹ := by
      rw [pow_add,pow_add,mul_inv_rev,mul_inv_rev,mul_inv_rev]
      ring
    _ ≤ (3^D*(R^D)⁻¹)*(A^r)⁻¹*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hratio (inv_nonneg.mpr (pow_nonneg hA0.le r)))
        hBr (inv_nonneg.mpr (pow_nonneg hB0.le r))
        (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity))
    _ = _ := mul_one _

theorem horizontal_envelope_le_distance (T : SlopeBox) (r : ℕ) {d : ℝ}
    (hd : 0≤d) (z : ℝ×ℝ) (hsep : d≤|z.1-T.x|) :
    lineEnvelope T.x T.length r z.1 ≤ (1+(d/T.length)^2)⁻¹^r := by
  have hrat : d/T.length≤|(z.1-T.x)/T.length| := by
    rw [abs_div,abs_of_pos T.length_pos]
    exact div_le_div_of_nonneg_right hsep T.length_pos.le
  have hs : (d/T.length)^2≤((z.1-T.x)/T.length)^2 := by
    have hh := pow_le_pow_left₀ (div_nonneg hd T.length_pos.le) hrat 2
    simpa only [sq_abs] using hh
  have hp : (1+(d/T.length)^2)^r≤(1+((z.1-T.x)/T.length)^2)^r :=
    pow_le_pow_left₀ (by positivity) (by linarith) r
  have hh := inv_anti₀ (show 0<(1+(d/T.length)^2)^r by positivity) hp
  simpa only [lineEnvelope,inv_pow] using hh

namespace OrdinaryDensityTile

/-- Every admissible test is bounded by the literal density supremum. -/
theorem test_integral_le_density (tile : OrdinaryDensityTile)
    (ell0 w W tau : ℝ) (grid : ℤ) (E : Set (ℝ×ℝ)) (v : ℝ×ℝ → ℝ)
    (test : OrdinaryDensityTest ell0 w W tau grid tile) :
    (∫ z in E ∩ v ⁻¹' scaledAngularCell (w/ell0) grid test.level test.cell,
      test.top.densityKernel 203 z ∂volume.prod volume) ≤
        tile.density ell0 w W tau grid E v*test.top.area := by
  have h := le_csSup (tile.densityValues_bddAbove ell0 w W tau grid E v)
    (show densityAverage test.top E v (scaledAngularCell (w/ell0) grid test.level test.cell) ∈
      tile.densityValues ell0 w W tau grid E v from Or.inr ⟨test,rfl⟩)
  exact (div_le_iff₀ test.top.area_pos).mp h

end OrdinaryDensityTile

/-- One literal physical packet term. Its selector may be complex and
coordinate-dependent; only its original support and norm bound are used. -/
theorem density_test_short_packet_term {κ : Type} [Fintype κ]
    (ell0 w W tau : ℝ) (grid : ℤ) (tile : OrdinaryDensityTile)
    (test : OrdinaryDensityTest ell0 w W tau grid tile)
    (r n : ℕ) (horder : 203+r≤n) (C M sigma eta d : ℝ)
    (hC : 0≤C) (hM : 0≤M) (hsigma : 0≤sigma) (hd : 0≤d)
    (profile : κ → SchwartzMap (ℝ×ℝ) ℂ) (frequency : κ → ℝ)
    (hprofile : ∀ k, planarProfileConstant (profile k) n≤C)
    (c : EuclideanSpace ℂ κ) (hc : ‖c‖≤sigma)
    (selector : κ → ℝ → ℂ) (hselector : ∀ k, Measurable (selector k))
    (hbound : ∀ k s, ‖selector k s‖≤M)
    (hsupport : ∀ k s, selector k s≠0 →
      s∈scaledAngularCell (w/ell0) grid test.level test.cell)
    (v : ℝ×ℝ → ℝ) (hv : Measurable v) (E : Set (ℝ×ℝ))
    (hE : MeasurableSet E) (I : Set ℝ) (hI : MeasurableSet I)
    (hsep : ∀ x∈I, d≤|x-test.top.x|)
    (hdensity : tile.density ell0 w W tau grid E v≤eta) :
    let F := fun z : ℝ×ℝ => WithLp.toLp 2 (fun k => c k*selector k (v z)*
      physicalPlanarPacket (profile k) test.top.x test.top.y test.top.length test.top.width
        test.top.slope (frequency k) test.top.length_pos.ne' test.top.width_pos.ne' z)
    IntegrableOn (fun z => ‖F z‖) (E∩Prod.fst ⁻¹' I) (volume.prod volume) ∧
    (∫ z in E∩Prod.fst ⁻¹' I, ‖F z‖ ∂volume.prod volume) ≤
      (3:ℝ)^203*C*M*sigma*((1+(d/test.top.length)^2)⁻¹^r)*eta*test.top.area := by
  let T := test.top
  let F := fun z : ℝ×ℝ => WithLp.toLp 2 (fun k => c k*selector k (v z)*
    physicalPlanarPacket (profile k) T.x T.y T.length T.width T.slope (frequency k)
      T.length_pos.ne' T.width_pos.ne' z)
  let omega := scaledAngularCell (w/ell0) grid test.level test.cell
  let A := E∩Prod.fst ⁻¹' I
  let tail := (1+(d/T.length)^2)⁻¹^r
  let B := (3:ℝ)^203*C*M*sigma*tail
  have htail : 0≤tail := by dsimp [tail]; positivity
  have hB : 0≤B := by dsimp [B]; positivity
  have homega : MeasurableSet (v ⁻¹' omega) :=
    (scaledAngularCell_measurable _ _ _ _).preimage hv
  have hA : MeasurableSet A := hE.inter (hI.preimage measurable_fst)
  have hF : Measurable (fun z => ‖F z‖) := by
    apply Measurable.norm
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_iff.mpr
    intro k
    exact
      (measurable_const.mul ((hselector k).comp hv)).mul
        (physicalPlanarPacket (profile k) T.x T.y T.length T.width T.slope
          (frequency k) T.length_pos.ne' T.width_pos.ne').continuous.measurable
  have hpacket (k : κ) (z : ℝ×ℝ) (hz : z∈A) :
      ‖physicalPlanarPacket (profile k) T.x T.y T.length T.width T.slope
        (frequency k) T.length_pos.ne' T.width_pos.ne' z‖ ≤
      (3:ℝ)^203*C*tail*T.densityKernel 203 z := by
    have hp := physicalPlanarPacket_profile_envelope (profile k) n T.x T.y T.length
      T.width T.slope (frequency k) T.length_pos.ne' T.width_pos.ne' z
    have he := packet_envelope_density_decay T 203 r z
    have hx := horizontal_envelope_le_distance T r hd z (hsep z.1 hz.2)
    calc
      _ ≤ C*(lineEnvelope T.x T.length (203+r) z.1 *
          lineEnvelope (T.y-T.slope*T.x) T.width (203+r) (z.2-T.slope*z.1)) :=
        hp.trans (mul_le_mul (hprofile k)
          (mul_le_mul (lineEnvelope_antitone _ _ _ horder) (lineEnvelope_antitone _ _ _ horder)
            (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _))
          (mul_nonneg (lineEnvelope_nonneg _ _ _ _) (lineEnvelope_nonneg _ _ _ _)) hC)
      _ ≤ C*((3:ℝ)^203*T.densityKernel 203 z*lineEnvelope T.x T.length r z.1) :=
        mul_le_mul_of_nonneg_left he hC
      _ ≤ C*((3:ℝ)^203*T.densityKernel 203 z*tail) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx
          (mul_nonneg (by positivity) (T.densityKernel_nonneg 203 z))) hC
      _ = _ := by ring
  have hpoint (z : ℝ×ℝ) (hz : z∈A) :
      ‖F z‖≤B*(v ⁻¹' omega).indicator (T.densityKernel 203) z := by
    by_cases hvz : v z∈omega
    · rw [Set.indicator_of_mem (show z∈v ⁻¹' omega from hvz)]
      let ker : ℝ := (3:ℝ)^203*C*tail*T.densityKernel 203 z
      have hker : 0≤ker :=
        mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hC) htail)
          (T.densityKernel_nonneg 203 z)
      let wave := fun k => selector k (v z)*
        physicalPlanarPacket (profile k) T.x T.y T.length T.width T.slope
          (frequency k) T.length_pos.ne' T.width_pos.ne' z
      have hwave (k : κ) : ‖wave k‖≤M*ker := by
        dsimp only [wave]
        rw [norm_mul]
        exact mul_le_mul (hbound k (v z)) (hpacket k z hz) (norm_nonneg _) hM
      have hp := diagonal_packet_norm c wave (mul_nonneg hM hker) hwave
      calc
        _ = ‖WithLp.toLp 2 (fun k => c k*(selector k (v z)*
            physicalPlanarPacket (profile k) T.x T.y T.length T.width T.slope
              (frequency k) T.length_pos.ne' T.width_pos.ne' z))‖ := by
          dsimp only [F]
          congr 1
          ext k
          simp only [mul_assoc]
        _ ≤ M*((3:ℝ)^203*C*tail*T.densityKernel 203 z)*sigma :=
          hp.trans (mul_le_mul_of_nonneg_left hc (mul_nonneg hM hker))
        _ = _ := by dsimp [B]; ring
    · have hs (k) : selector k (v z)=0 := by
        by_contra hn
        exact hvz (hsupport k (v z) hn)
      have hzero : F z=0 := by
        ext k
        simp only [F,hs,mul_zero,zero_mul,WithLp.ofLp_zero,Pi.zero_apply]
      rw [hzero,norm_zero,Set.indicator_of_notMem (show z∉v ⁻¹' omega from hvz),mul_zero]
  have hmajor : Integrable (fun z => B*(v ⁻¹' omega).indicator (T.densityKernel 203) z)
      (volume.prod volume) :=
    ((T.densityKernel_integrable (by norm_num : (2:ℝ)<203)).indicator homega).const_mul B
  have hfi : IntegrableOn (fun z => ‖F z‖) A (volume.prod volume) :=
    hmajor.integrableOn.mono' hF.aestronglyMeasurable (by
      filter_upwards [ae_restrict_mem hA] with z hz
      simpa only [Real.norm_eq_abs,abs_norm] using hpoint z hz)
  refine ⟨hfi,?_⟩
  calc
    _ ≤ ∫ z in A, B*(v ⁻¹' omega).indicator (T.densityKernel 203) z ∂volume.prod volume :=
      setIntegral_mono_on hfi hmajor.integrableOn hA hpoint
    _ = B*∫ z in A∩v ⁻¹' omega, T.densityKernel 203 z ∂volume.prod volume := by
      rw [integral_const_mul,setIntegral_indicator homega]
    _ ≤ B*∫ z in E∩v ⁻¹' omega, T.densityKernel 203 z ∂volume.prod volume := by
      apply mul_le_mul_of_nonneg_left _ hB
      apply setIntegral_mono_set (T.densityKernel_integrable (by norm_num : (2:ℝ)<203)).integrableOn
        (Filter.Eventually.of_forall (fun z => T.densityKernel_nonneg 203 z))
      exact Filter.Eventually.of_forall (fun z hz => ⟨hz.1.1,hz.2⟩)
    _ ≤ B*(eta*T.area) := mul_le_mul_of_nonneg_left
      ((tile.test_integral_le_density ell0 w W tau grid E v test).trans
        (mul_le_mul_of_nonneg_right hdensity T.area_pos.le)) hB
    _ = _ := by dsimp [B,T,tail]; ring

end LipschitzHilbert

end

end OAI
