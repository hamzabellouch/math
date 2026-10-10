import Mathlib
import OAI.Analysis.CoulombIonization.FormDomain.FourierMomentGradient
import OAI.Analysis.CoulombIonization.FieldAnalysis.LocalFieldScalarBoundBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpFreshPatch_barrier_scope

open MeasureTheory Set
open scoped BigOperators

namespace CoulombAtom
open CoulombAnalysis CoulombNeumann

 def sharpPatchRemainder (a b m : ℝ) : ℝ :=
    localizationIMSConstant/b^2*(Real.sqrt (8*b/a)*actualCellMomentConstant*m)+
    b⁻¹^2*neumannRemainderConstant*
      (actualCellMomentConstant^(2/3:ℝ)*m^(4/3:ℝ)+actualCellMomentConstant*m)+
    (((2*Real.pi+1)/2)/b)*(actualCellMomentConstant*m)+
    (sharpFreshFieldConstant*(m/a))*(Real.sqrt (8*b/a)*actualCellMomentConstant*m)+
    ((packetDirichlet canonicalRealPacket/2)*b⁻¹^2)*(768*sharpFreshFieldConstant*m)

lemma count_two_thirds_scale {B C m : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hBC : B ≤ C*m^2) : B^(2/3:ℝ) ≤ C^(2/3:ℝ)*m^(4/3:ℝ) := by
  have hh := Real.rpow_le_rpow hB hBC (by norm_num : (0:ℝ) ≤ 2/3)
  have he : (C*m^2)^(2/3:ℝ) = C^(2/3:ℝ)*m^(4/3:ℝ) := by
    rw [Real.mul_rpow hC (sq_nonneg m),←Real.rpow_natCast,←Real.rpow_mul hm]
    norm_num
  rwa [he] at hh

theorem sharp_selected_fresh_patch {N : ℕ} {ψ : FormVector N}
    (hψ : SobolevFermion ψ) (hm : formMass ψ = 1) {y : Space} (hy : y ≠ 0)
    {b Z lam : ℝ} (hb : 0 < b) (hba : 7*b < 5*localCellRadius y)
    (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    ∃ r ∈ Icc (5*localCellRadius y) (6*localCellRadius y), ∃ hr0 : 0 ≤ r,
      (∑ c : Fin N → Fin 2, ∑ s : Spins (cutOutNumber c), ∫ u,
        weightedPatchGap (orderedCutForm (coreFirstRadialCut y hr0 hb)
          (coreFirstRadialCut_partition y hr0 hb) ψ c) s Z lam y (r-4*b) hb
          (radialPatchRetention N y r b c s) u) ≤
        corePriceExcess Z lam ψ+sharpPatchRemainder (localCellRadius y) b
          (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) := by
  let a := localCellRadius y
  let D := max (corePriceExcess Z lam ψ) 0
  let m := localOffsetMass D y
  let B := rawCountMoment ψ y (7*a)
  have ha : 0 < a := localCellRadius_pos hy
  have hba' : b ≤ a := by linarith
  have hn : 6*a+2*b ≤ ‖y‖ := by dsimp [a,localCellRadius] at *; nlinarith [norm_nonneg y]
  obtain ⟨r,hr,hr0,hgap⟩ := selected_fresh_patch_budget hψ hm y ha hb hba hn hZ hlam
    canonicalRealPacket_smooth canonicalRealPacket_compact canonicalRealPacket_normalized
    canonicalRealPacket_radial canonicalRealPacket_support
  dsimp only at hgap
  rw [←rawCountMoment_eq_integral hψ.sobolevVector y (7*a)] at hgap
  obtain ⟨hr0',hfield,hmass⟩ := sharp_cell_fresh_field_mass hψ hm hy hb hba' hr hZ hlam hcollar
  have hBC : B ≤ actualCellMomentConstant*m^2 :=
    (rawCountMoment_le_of_radius hψ.sobolevVector y y (by simp only [sub_self,norm_zero,zero_add]; linarith : ‖y-y‖+7*a ≤ 32*a)).trans
      (priced_enlarged_cell_count hψ hm hZ hlam hy)
  have hB : 0 ≤ B := rawCountMoment_nonneg ψ y (7*a)
  have hC := actualCellMomentConstant_one_le
  have hC0 := le_trans zero_le_one hC
  have hm0 : 0 ≤ m := le_trans zero_le_one (localOffsetMass_one_le D y)
  have hroot : Real.sqrt B ≤ actualCellMomentConstant*m := by
    simpa using sqrt_count_scale hB hC (by norm_num : (0:ℝ) ≤ 1) hm0 (by simpa using hBC)
  have htwo := count_two_thirds_scale hB hC0 hm0 hBC
  have hsqrt : Real.sqrt ((8*b/a)*B) ≤ Real.sqrt (8*b/a)*actualCellMomentConstant*m := by
    rw [Real.sqrt_mul (show 0 ≤ 8*b/a by positivity)]
    exact (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)).trans_eq (by ring)
  have hF0 : 0 ≤ sharpFreshFieldConstant*(m/a) := by
    have := sharpFreshFieldConstant_one_le
    positivity
  have hfieldroot : Real.sqrt (freshOutMaximumSecondMoment (coreFirstRadialCut y hr0 hb)
      (coreFirstRadialCut_partition y hr0 hb) ψ Z lam) ≤ sharpFreshFieldConstant*(m/a) :=
    Real.sqrt_le_iff.mpr ⟨hF0,hfield⟩
  have hims : (3/2:ℝ)*(Real.pi*smoothTransitionBound/b)^2 = localizationIMSConstant/b^2 := by
    unfold localizationIMSConstant
    ring
  simp only [←Real.sqrt_eq_rpow,hims] at hgap
  have hI := localizationIMSConstant_nonneg
  have hN := neumannRemainderConstant_pos.le
  have hP := packetDirichlet_nonneg canonicalRealPacket
  refine ⟨r,hr,hr0,hgap.trans ?_⟩
  change _ ≤ corePriceExcess Z lam ψ+sharpPatchRemainder a b m
  unfold sharpPatchRemainder
  simp only [←add_assoc]
  gcongr

end CoulombAtom

end Work_SharpFreshPatch_barrier_scope

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace

namespace CoulombAtom

 def smoothMultiplyL2 (p : SmoothMultiplier spaceDirections)
    (f : Lp ℂ 2 (volume : Measure Space)) : Lp ℂ 2 (volume : Measure Space) :=
  (memLp_bounded_mul p.regular.continuous p.bound (Lp.memLp f)).toLp _

lemma smoothMultiplyL2_ae (p : SmoothMultiplier spaceDirections)
    (f : Lp ℂ 2 (volume : Measure Space)) :
    (smoothMultiplyL2 p f : Space → ℂ) =ᵐ[volume] fun x => (p.value x : ℂ)*f x :=
  (memLp_bounded_mul p.regular.continuous p.bound (Lp.memLp f)).coeFn_toLp

lemma smoothMultiplyL2_norm_le (p : SmoothMultiplier spaceDirections)
    (hp : ∀ x, |p.value x| ≤ 1) (f : Lp ℂ 2 (volume : Measure Space)) :
    ‖smoothMultiplyL2 p f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [smoothMultiplyL2_ae p f] with x hx
  rw [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  simpa using mul_le_mul_of_nonneg_right (hp x) (norm_nonneg (f x))

lemma smoothMultiplyL2_inner (p : SmoothMultiplier spaceDirections)
    (f g : Lp ℂ 2 (volume : Measure Space)) :
    inner ℂ f (smoothMultiplyL2 p g) = inner ℂ (smoothMultiplyL2 p f) g := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [smoothMultiplyL2_ae p f,smoothMultiplyL2_ae p g] with x hf hg
  rw [hf,hg]
  change (p.value x:ℂ)*g x*starRingEnd ℂ (f x) =
    g x*starRingEnd ℂ ((p.value x:ℂ)*f x)
  rw [map_mul,Complex.conj_ofReal]
  ring

 def smoothDerivativeProductL2 (p : SmoothMultiplier spaceDirections)
    (a : Fin 3) (f g : Lp ℂ 2 (volume : Measure Space)) : Lp ℂ 2 (volume : Measure Space) :=
  ((memLp_bounded_mul p.regular.continuous p.bound (Lp.memLp g)).add
    (memLp_bounded_mul (p.derivative_continuous a) (p.gradient_bound a) (Lp.memLp f))).toLp _

lemma smoothDerivativeProductL2_ae (p : SmoothMultiplier spaceDirections)
    (a : Fin 3) (f g : Lp ℂ 2 (volume : Measure Space)) :
    (smoothDerivativeProductL2 p a f g : Space → ℂ) =ᵐ[volume]
      fun x => (p.value x : ℂ)*g x + Complex.ofReal (lineDeriv ℝ p.value x (spaceDirections a))*f x :=
  ((memLp_bounded_mul p.regular.continuous p.bound (Lp.memLp g)).add
    (memLp_bounded_mul (p.derivative_continuous a) (p.gradient_bound a) (Lp.memLp f))).coeFn_toLp

lemma smoothMultiplyL2_weak (p : SmoothMultiplier spaceDirections)
    {a : Fin 3} {f g : Lp ℂ 2 (volume : Measure Space)}
    (hw : HasWeakDirectionalDerivative f g (spaceDirections a)) :
    HasWeakDirectionalDerivative (smoothMultiplyL2 p f)
      (smoothDerivativeProductL2 p a f g) (spaceDirections a) :=
  (IsWeakDerivative.mul_smooth hw (Lp.memLp f) (Lp.memLp g) p.regular).congr_ae
    (smoothMultiplyL2_ae p f).symm (smoothDerivativeProductL2_ae p a f g).symm

end CoulombAtom
namespace CoulombLT
open CoulombAtom

lemma BesselFamily.smoothMultiply {ι : Type*} [Fintype ι]
    {f : ι → Lp ℂ 2 (volume : Measure Space)} (hf : BesselFamily f)
    (p : SmoothMultiplier spaceDirections) (hp : ∀ x, |p.value x| ≤ 1) :
    BesselFamily (fun j => smoothMultiplyL2 p (f j)) := by
  intro u
  simp only [smoothMultiplyL2_inner]
  exact (hf (smoothMultiplyL2 p u)).trans
    (pow_le_pow_left₀ (norm_nonneg _) (smoothMultiplyL2_norm_le p hp u) 2)

lemma infiniteDensity_smoothMultiply {ι : Type*} [Countable ι]
    (f : ι → Lp ℂ 2 (volume : Measure Space)) (p : SmoothMultiplier spaceDirections) :
    ∀ᵐ x ∂volume, infiniteDensity (fun j => smoothMultiplyL2 p (f j)) x =
      ENNReal.ofReal (p.value x^2)*infiniteDensity f x := by
  filter_upwards [ae_all_iff.mpr (fun j => smoothMultiplyL2_ae p (f j))] with x hx
  unfold infiniteDensity
  simp only [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs,
    ENNReal.ofReal_mul (sq_nonneg _),ENNReal.tsum_mul_left]

theorem localized_family_lieb_thirring {ι : Type*} [Countable ι]
    {f : ι → Lp ℂ 2 (volume : Measure Space)}
    {g : Fin 3 → ι → Lp ℂ 2 (volume : Measure Space)}
    (hf : ∀ s : Finset ι, BesselFamily (fun j : s => f j))
    (hw : ∀ a j, HasWeakDirectionalDerivative (f j) (g a j) (spaceDirections a))
    (p : SmoothMultiplier spaceDirections) (hp : ∀ x, |p.value x| ≤ 1) :
    (∫⁻ x, (ENNReal.ofReal (p.value x^2)*infiniteDensity f x)^(5/3:ℝ)) ≤
      16*(∑' j, ENNReal.ofReal (‖smoothMultiplyL2 p (f j)‖^2))+
        ENNReal.ofReal (1024/3:ℝ)*(∑ a, ∑' j,
          ENNReal.ofReal (‖smoothDerivativeProductL2 p a (f j) (g a j)‖^2)) := by
  have hb (s : Finset ι) : BesselFamily (fun j : s => smoothMultiplyL2 p (f j)) :=
    (hf s).smoothMultiply p hp
  have hd (a : Fin 3) (j : ι) : HasWeakDirectionalDerivative (smoothMultiplyL2 p (f j))
      (smoothDerivativeProductL2 p a (f j) (g a j)) (EuclideanSpace.single a 1) :=
    smoothMultiplyL2_weak p (hw a j)
  have h := weak_family_lieb_thirring
    (f := fun j : ι => smoothMultiplyL2 p (f j))
    (g := fun a j => smoothDerivativeProductL2 p a (f j) (g a j)) hb hd
  calc
    _ = ∫⁻ x, infiniteDensity (fun j => smoothMultiplyL2 p (f j)) x^(5/3:ℝ) := by
      apply lintegral_congr_ae
      filter_upwards [infiniteDensity_smoothMultiply f p] with x hx
      rw [hx]
    _ ≤ _ := h

end CoulombLT

end

end OAI
