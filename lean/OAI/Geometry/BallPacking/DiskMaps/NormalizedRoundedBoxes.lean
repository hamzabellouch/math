import Mathlib
import OAI.Geometry.BallPacking.DiskMaps.CompactEmbeddingIsotopy

namespace OAI

noncomputable section
namespace PackingSufficiencySupport.Hamiltonian

section
open scoped ContDiff Topology
open Set Function MeasureTheory

def normalizedRoundedMap (k : ℝ) (c : Plane) (a b r : ℝ) : Plane → Plane :=
  roundedMap k c a b ∘ diagonalScale r⁻¹ r⁻¹

@[fun_prop] theorem normalizedRoundedMap_smooth (k : ℝ) (c : Plane) (a b r : ℝ) :
    ContDiff ℝ ∞ (normalizedRoundedMap k c a b r) :=
  (roundedMap_smooth k c a b).comp (diagonalScale r⁻¹ r⁻¹).contDiff

theorem normalizedRoundedMap_injective {k a b r : ℝ} (hk : 0 < k) (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (c : Plane) :
    Injective (normalizedRoundedMap k c a b r) :=
  (roundedMap_injective hk.ne' ha.ne' hb.ne' c).comp
    (diagonalScale_injective (inv_ne_zero hr.ne') (inv_ne_zero hr.ne'))

theorem normalizedRoundedMap_det_pos {k a b r : ℝ} (hk : 0 < k) (ha : 0 < a)
    (hb : 0 < b) (hr : 0 < r) (c : Plane) (x : Plane) :
    0 < (fderiv ℝ (normalizedRoundedMap k c a b r) x).det := by
  rw [normalizedRoundedMap,fderiv_comp x
    ((roundedMap_smooth k c a b).differentiable (by simp) _)
    ((diagonalScale r⁻¹ r⁻¹).differentiable _), (diagonalScale r⁻¹ r⁻¹).fderiv,
    ContinuousLinearMap.det,ContinuousLinearMap.toLinearMap_comp,LinearMap.det_comp]
  change 0 < (fderiv ℝ (roundedMap k c a b) _).det * (diagonalScale r⁻¹ r⁻¹).det
  rw [diagonalScale_det]
  exact mul_pos (roundedMap_det_pos hk ha hb c _) (mul_pos (inv_pos.mpr hr) (inv_pos.mpr hr))

theorem normalizedRoundedMap_image {r : ℝ} (hr : 0 < r) (k : ℝ) (c : Plane) (a b : ℝ) :
    normalizedRoundedMap k c a b r '' closedRoundDisk r = roundedBox k c a b := by
  rw [normalizedRoundedMap,image_comp,diagonalScale_inv_image_closedRoundDisk hr]
  rfl

theorem roundedBox_volume_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (k : ℝ) (c : Plane) :
    volume (roundedBox k c a b) = ENNReal.ofReal (a*b*squeezedArea k) := by
  exact (ENNReal.toReal_eq_toReal_iff' (roundedBox_compact k c a b).measure_ne_top
    ENNReal.ofReal_ne_top).mp (by
      rw [roundedBox_volume ha hb k c,ENNReal.toReal_ofReal
        (mul_nonneg (mul_nonneg ha hb) (squeezedArea_nonneg k))])


end

section
open scoped ContDiff Topology
open Set Function

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SupportedSmoothIsotopyFamily

def cutoff {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W)
    (ρ : P → ℝ) (hρ : ContDiff ℝ ∞ ρ) : SupportedSmoothIsotopyFamily P E W where
  map := fun y t => Φ.map y (ρ y*t)
  smooth := Φ.smooth.comp ((contDiff_fst.fst.prodMk
    (((hρ.comp contDiff_fst.fst).mul contDiff_fst.snd))).prodMk contDiff_snd)
  inverse_smooth := Φ.inverse_smooth.comp ((contDiff_fst.fst.prodMk
    (((hρ.comp contDiff_fst.fst).mul contDiff_fst.snd))).prodMk contDiff_snd)
  zero := fun y => by simp only [mul_zero,Φ.zero]
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset
  fixed := fun y t x hx => Φ.fixed y (ρ y*t) x hx

theorem endpoint_support {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W) :
    tsupport (fun p : P × E => Φ.map p.1 1 p.2-p.2) ⊆ univ ×ˢ Φ.support := by
  apply closure_minimal _ (isClosed_univ.prod Φ.compact_support.isClosed)
  intro p hp
  refine ⟨mem_univ _,?_⟩
  by_contra hn
  exact hp (sub_eq_zero.mpr (Φ.fixed p.1 1 p.2 hn))

theorem cutoff_compact {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W)
    (ρ : P → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    HasCompactSupport (fun p : P × E => (Φ.cutoff ρ hρ).map p.1 1 p.2-p.2) := by
  apply HasCompactSupport.intro (hρc.prod Φ.compact_support)
  intro p hp
  by_cases h : p.1 ∈ tsupport ρ
  · have hn : p.2 ∉ Φ.support := fun hx => hp ⟨h,hx⟩
    exact sub_eq_zero.mpr (Φ.fixed p.1 (ρ p.1*1) p.2 hn)
  · have hz := image_eq_zero_of_notMem_tsupport h
    simp only [cutoff,hz,zero_mul,Φ.zero,Homeomorph.refl_apply,id_eq,sub_self]

variable [FiniteDimensional ℝ P]

theorem exists_compact_parameterization {W : Set E}
    (Φ : SupportedSmoothIsotopyFamily P E W) (Y : Set P) (hY : IsCompact Y) :
    ∃ Ψ : SupportedSmoothIsotopyFamily P E W,
      HasCompactSupport (fun p : P × E => Ψ.map p.1 1 p.2-p.2) ∧
      (∀ y ∈ Y, ∀ t, Ψ.map y t = Φ.map y t) := by
  obtain ⟨ρ,hρ,hρc,_,hρ1,_⟩ := exists_smooth_cutoff hY isOpen_univ (subset_univ Y)
  refine ⟨Φ.cutoff ρ hρ,Φ.cutoff_compact ρ hρ hρc,?_⟩
  intro y hy t
  have hh : ρ y = 1 := (Filter.Eventually.self_of_nhdsSet hρ1) y hy
  change Φ.map y (ρ y*t) = Φ.map y t
  rw [hh,one_mul]

end SupportedSmoothIsotopyFamily


namespace SupportedSmoothIsotopyFamily

def timeCutoff {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W)
    (ρ : P × ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) : SupportedSmoothIsotopyFamily P E W where
  map := fun y t => Φ.map y (ρ (y,t)*t)
  smooth := Φ.smooth.comp ((contDiff_fst.fst.prodMk
    ((hρ.comp contDiff_fst).mul contDiff_fst.snd)).prodMk contDiff_snd)
  inverse_smooth := Φ.inverse_smooth.comp ((contDiff_fst.fst.prodMk
    ((hρ.comp contDiff_fst).mul contDiff_fst.snd)).prodMk contDiff_snd)
  zero := fun y => by simp only [mul_zero,Φ.zero]
  support := Φ.support
  compact_support := Φ.compact_support
  support_subset := Φ.support_subset
  fixed := fun y t x hx => Φ.fixed y (ρ (y,t)*t) x hx

theorem joint_support {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W) :
    tsupport (fun p : (P × ℝ) × E => Φ.map p.1.1 p.1.2 p.2-p.2) ⊆
      univ ×ˢ Φ.support := by
  apply closure_minimal _ (isClosed_univ.prod Φ.compact_support.isClosed)
  intro p hp
  refine ⟨mem_univ _,?_⟩
  by_contra hn
  exact hp (sub_eq_zero.mpr (Φ.fixed p.1.1 p.1.2 p.2 hn))

theorem timeCutoff_hasCompactSupport {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W)
    (ρ : P × ℝ → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    HasCompactSupport (fun p : (P × ℝ) × E =>
      (Φ.timeCutoff ρ hρ).map p.1.1 p.1.2 p.2-p.2) := by
  apply HasCompactSupport.intro (hρc.prod Φ.compact_support)
  intro p hp
  by_cases h : p.1 ∈ tsupport ρ
  · have hn : p.2 ∉ Φ.support := fun hx => hp ⟨h,hx⟩
    exact sub_eq_zero.mpr (Φ.fixed p.1.1 (ρ p.1*p.1.2) p.2 hn)
  · have hz := image_eq_zero_of_notMem_tsupport h
    simp only [timeCutoff,Prod.eta,hz,zero_mul,Φ.zero,Homeomorph.refl_apply,id_eq,sub_self]

variable [FiniteDimensional ℝ P]

theorem exists_joint_compact {W : Set E} (Φ : SupportedSmoothIsotopyFamily P E W)
    (Y : Set P) (hY : IsCompact Y) :
    ∃ Ψ : SupportedSmoothIsotopyFamily P E W,
      HasCompactSupport (fun p : (P × ℝ) × E => Ψ.map p.1.1 p.1.2 p.2-p.2) ∧
      (∀ y ∈ Y, ∀ t ∈ Icc (0:ℝ) 1, Ψ.map y t = Φ.map y t) := by
  obtain ⟨ρ,hρ,hρc,_,hρ1,_⟩ := exists_smooth_cutoff (hY.prod isCompact_Icc)
    isOpen_univ (subset_univ (Y ×ˢ Icc (0:ℝ) 1))
  refine ⟨Φ.timeCutoff ρ hρ,Φ.timeCutoff_hasCompactSupport ρ hρ hρc,?_⟩
  intro y hy t ht
  have hh : ρ (y,t) = 1 := (Filter.Eventually.self_of_nhdsSet hρ1) (y,t) ⟨hy,ht⟩
  change Φ.map y (ρ (y,t)*t) = Φ.map y t
  rw [hh,one_mul]

end SupportedSmoothIsotopyFamily

end

section
open scoped ContDiff Topology
open Set Function MeasureTheory

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parameter_relative_circle_primitive
    {alpha : P × Plane → Plane →L[ℝ] ℝ}
    (ha : ContDiff ℝ ∞ alpha) (hac : HasCompactSupport alpha) {R delta : ℝ}
    (hR : 0 < R) (hd : 0 < delta) (hdR : delta < R^2) (Y : Set P)
    (hz : ∀ y ∈ Y, (∫ p in roundDisk R, planarCurl (fun x => alpha (y,x)) p) = 0) :
    ∃ H : P × Plane → ℝ, ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      (∀ y p, delta ≤ |radiusSq p-R^2| → H (y,p) = 0) ∧
      (∀ y ∈ Y, ∀ t, fderiv ℝ (fun x => H (y,x)) (polarCoord.symm (R,t))
        (-R*Real.sin t,R*Real.cos t) = circlePullback (fun x => alpha (y,x)) R t) ∧
      ∀ y, (∀ x, alpha (y,x) = 0) → ∀ x, H (y,x) = 0 := by
  let a : P × ℝ → ℝ := fun p => circlePullback (fun x => alpha (p.1,x)) R p.2
  have has : ContDiff ℝ ∞ a := circlePullback_parameter_smooth ha R
  let m : P → ℝ := fun y => (∫ t in -Real.pi..Real.pi, a (y,t))/(2*Real.pi)
  have hms : ContDiff ℝ ∞ m :=
    ((contDiff_parameter_segment_integral has (-Real.pi)).comp
      (contDiff_id.prodMk contDiff_const)).div_const _
  let b : P × ℝ → ℝ := fun p => a p-m p.1
  have hbs : ContDiff ℝ ∞ b := has.sub (hms.comp contDiff_fst)
  have hby (y : P) : ContDiff ℝ ∞ (fun t => b (y,t)) :=
    hbs.comp (contDiff_const.prodMk contDiff_id)
  have hmY (y : P) (hy : y ∈ Y) : m y = 0 := by
    have hai : ContDiff ℝ ∞ (fun x : Plane => alpha (y,x)) :=
      ha.comp (contDiff_const.prodMk contDiff_id)
    have hz' := (integral_curl_roundDisk hai hR).symm.trans (hz y hy)
    change (∫ t in -Real.pi..Real.pi, circlePullback (fun x => alpha (y,x)) R t) / (2*Real.pi) = 0
    exact div_eq_zero_iff.mpr (Or.inl hz')
  have hb0 (y : P) : (∫ t in -Real.pi..Real.pi, b (y,t)) = 0 := by
    have hai : IntervalIntegrable (fun t => a (y,t)) volume (-Real.pi) Real.pi :=
      (has.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
    simp only [b]
    rw [intervalIntegral.integral_sub hai intervalIntegrable_const,intervalIntegral.integral_const]
    dsimp [m]
    field_simp
    ring
  have hbp (y : P) : Periodic (fun t => b (y,t)) (2*Real.pi) := by
    intro t
    dsimp [b,a]
    rw [circlePullback_periodic (fun x => alpha (y,x)) R t]
  have hp (y : P) := periodicPrimitive_periodic (hby y).continuous (hbp y) (hb0 y)
  let H : P × Plane → ℝ := fun p =>
    angularExtension R delta hd (periodicPrimitive (fun t => b (p.1,t))) p.2
  have hH : ContDiff ℝ ∞ H := angularExtension_parameter_smooth hd hdR
    (contDiff_parameter_segment_integral hbs (-Real.pi)) hp
  have hbzero (y : P) (hy : ∀ x, alpha (y,x) = 0) : (fun t => b (y,t)) = fun _ => (0:ℝ) := by
    have ha0 : (fun t => a (y,t)) = fun _ => (0:ℝ) := by
      funext t
      simp only [a,circlePullback,hy,zero_apply]
    funext t
    change a (y,t) - (∫ t in -Real.pi..Real.pi, a (y,t))/(2*Real.pi) = 0
    rw [ha0,congrFun ha0 t]
    simp only [intervalIntegral.integral_zero,zero_div,sub_self]
  have hHc : HasCompactSupport H := by
    have hK : IsCompact (Prod.fst '' tsupport alpha) := hac.image continuous_fst
    apply angularExtension_parameter_compact (h := fun p =>
      periodicPrimitive (fun t => b (p.1,t)) p.2) (K := Prod.fst '' tsupport alpha) hd hK
    intro y hy t
    have he := hbzero y (fun x => image_eq_zero_of_notMem_tsupport
      (fun h => hy ⟨(y,x),h,rfl⟩))
    change periodicPrimitive (fun t => b (y,t)) t = 0
    rw [he]
    simp only [periodicPrimitive,intervalIntegral.integral_zero]
  refine ⟨H,hH,hHc,fun _ p hp => angularExtension_zero hd _ p hp,?_,?_⟩
  · intro y hy t
    have hc : HasDerivAt (fun t => polarCoord.symm (R,t)) (-R*Real.sin t,R*Real.cos t) t := by
      change HasDerivAt (fun t => (R*Real.cos t,R*Real.sin t)) _ t
      exact (((Real.hasDerivAt_cos t).const_mul R).prodMk
        ((Real.hasDerivAt_sin t).const_mul R)).congr_deriv (by ext <;> simp [neg_mul])
    have hHy : ContDiff ℝ ∞ (fun x => H (y,x)) := hH.comp (contDiff_const.prodMk contDiff_id)
    have hdH := ((hHy.differentiable (by simp)) (polarCoord.symm (R,t))).hasFDerivAt.comp_hasDerivAt t hc
    have he : (fun t => H (y,polarCoord.symm (R,t))) = periodicPrimitive (fun t => b (y,t)) :=
      funext fun t => angularExtension_polar hR hd (hp y) t
    change HasDerivAt (fun t => H (y,polarCoord.symm (R,t))) _ t at hdH
    rw [he] at hdH
    simpa only [b,hmY y hy,sub_zero,a] using
      hdH.unique (periodicPrimitive_hasDerivAt (hby y).continuous t)
  · intro y hy x
    change angularExtension R delta hd (periodicPrimitive (fun t => b (y,t))) x = 0
    rw [hbzero y hy]
    simp only [angularExtension,periodicPrimitive,intervalIntegral.integral_zero,mul_zero]

omit [FiniteDimensional ℝ P] in
theorem parameter_relative_finite_potential_correction {ι : Type*} [Fintype ι]
    {alpha : P × Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha)
    (hac : HasCompactSupport alpha) (Y : Set P) (R : ι → ℝ)
    (H : ι → P × Plane → ℝ) (hHs : ∀ i, ContDiff ℝ ∞ (H i))
    (hHc : ∀ i, HasCompactSupport (H i))
    (hself : ∀ i y, y ∈ Y → ∀ p, radiusSq p = (R i)^2 →
      fderiv ℝ (fun x => H i (y,x)) p (-p.2,p.1) = alpha (y,p) (-p.2,p.1))
    (hother : ∀ i j, j ≠ i → ∀ y p, radiusSq p = (R i)^2 →
      fderiv ℝ (fun x => H j (y,x)) p = 0)
    (hHzero : ∀ i y, (∀ x, alpha (y,x) = 0) → ∀ x, H i (y,x) = 0) :
    ∃ beta : P × Plane → Plane →L[ℝ] ℝ, ContDiff ℝ ∞ beta ∧ HasCompactSupport beta ∧
      (∀ y p, planarCurl (fun x => beta (y,x)) p = planarCurl (fun x => alpha (y,x)) p) ∧
      (∀ i y, y ∈ Y → ∀ p, radiusSq p = (R i)^2 → beta (y,p) (-p.2,p.1) = 0) ∧
      ∀ y, (∀ x, alpha (y,x) = 0) → ∀ x, beta (y,x) = 0 := by
  classical
  let F : P × Plane → ℝ := fun p => ∑ i, H i p
  have hFs : ContDiff ℝ ∞ F := ContDiff.sum (fun i _ => hHs i)
  have hFc : HasCompactSupport F := by
    have he : (∑ i, H i) = F := by funext p; simp [F]
    rw [← he]
    exact HasCompactSupport.finset_sum (s := Finset.univ) (f := H) (fun i _ => hHc i)
  have hFd (y : P) (p v : Plane) :
      fderiv ℝ (fun x => F (y,x)) p v = ∑ i, fderiv ℝ (fun x => H i (y,x)) p v := by
    change fderiv ℝ (fun x => ∑ i, H i (y,x)) p v = _
    have hHyi (i : ι) : DifferentiableAt ℝ (fun x : Plane => H i (y,x)) p :=
      (((hHs i).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)) p
    rw [fderiv_fun_sum (fun i _ => hHyi i)]
    simp only [sum_apply]
  let beta : P × Plane → Plane →L[ℝ] ℝ := fun p => alpha p - fderiv ℝ (fun x => F (p.1,x)) p.2
  refine ⟨beta,ha.sub (fiber_fderiv_smooth hFs),hac.sub (fiber_fderiv_compact hFs hFc),?_,?_,?_⟩
  · intro y p
    exact planarCurl_sub_differential (ha.comp (contDiff_const.prodMk contDiff_id))
      (hFs.comp (contDiff_const.prodMk contDiff_id)) p
  · intro i y hy p hp
    change alpha (y,p) (-p.2,p.1) - fderiv ℝ (fun x => F (y,x)) p (-p.2,p.1) = 0
    rw [hFd,Finset.sum_eq_single i,hself i y hy p hp,sub_self]
    · intro j _ hj
      rw [hother i j hj y p hp]
      rfl
    · simp

  · intro y hy x
    have he : (fun x => F (y,x)) = fun _ => (0:ℝ) := by
      funext q
      exact Finset.sum_eq_zero (fun i _ => hHzero i y hy q)
    change alpha (y,x) - fderiv ℝ (fun x => F (y,x)) x = 0
    rw [hy x,he,fderiv_const_apply,sub_self]

theorem exists_parameter_relative_finite_circle_correction {ι : Type*} [Fintype ι]
    {alpha : P × Plane → Plane →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ alpha)
    (hac : HasCompactSupport alpha) (Y : Set P) (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (hRi : Injective R)
    (hz : ∀ i y, y ∈ Y → (∫ p in roundDisk (R i), planarCurl (fun x => alpha (y,x)) p) = 0) :
    ∃ beta : P × Plane → Plane →L[ℝ] ℝ, ContDiff ℝ ∞ beta ∧ HasCompactSupport beta ∧
      (∀ y p, planarCurl (fun x => beta (y,x)) p = planarCurl (fun x => alpha (y,x)) p) ∧
      (∀ i y, y ∈ Y → ∀ p, radiusSq p = (R i)^2 → beta (y,p) (-p.2,p.1) = 0) ∧
      ∀ y, (∀ x, alpha (y,x) = 0) → ∀ x, beta (y,x) = 0 := by
  classical
  choose d hd hdR hdsep using exists_disjoint_radial_collars R hR hRi
  choose H hHs hHc hHspt hHt hHzero using fun i =>
    exists_parameter_relative_circle_primitive ha hac (hR i) (hd i) (hdR i) Y (hz i)
  apply parameter_relative_finite_potential_correction ha hac Y R H hHs hHc
      (hHzero := hHzero)
  · intro i y hy p hp
    obtain ⟨t,rfl⟩ := polar_surjective_circle (hR i) hp
    simpa only [circlePullback,polarCoord_symm_apply,neg_mul] using hHt i y hy t
  · intro i j hj y p hp
    apply fderiv_zero_outside_collar (hHspt j y)
    rw [hp]
    exact hdsep j i hj.symm


end

open scoped ContDiff Topology NNReal
open Set Function MeasureTheory
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

theorem exists_parameter_relative_density_transport {ι : Type*} {L : ℝ≥0}
    (X : C(ℝ × (P × Plane),Plane)) (hX : LipschitzWith L X)
    (hXs : ContDiff ℝ ∞ X) (hXc : HasCompactSupport X)
    (ρ : P → ℝ × Plane → ℝ) (hρ : ∀ y, ContDiff ℝ ∞ (ρ y))
    (B : Plane →L[ℝ] Plane →L[ℝ] ℝ)
    (hPDE : ∀ y p v w, fderiv ℝ (ρ y) p (1,fiberField X y p) * B v w +
      ρ y p * (B (fderiv ℝ (fiberField X y) p (0,v)) w +
        B v (fderiv ℝ (fiberField X y) p (0,w))) = 0)
    (Y : Set P) (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (htan : ∀ i y, y ∈ Y → ∀ t x, radiusSq x = (R i)^2 → radialDrift (fiberField X y) (t,x) = 0)
    (t T : ℝ) : ∃ Φ : P → Plane ≃ₜ Plane,
      ContDiff ℝ ∞ (fun p : P × Plane => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × Plane => (Φ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × Plane => Φ p.1 p.2 - p.2) ∧
      (∀ y x v w, ρ y (t+T,Φ y x) * B (fderiv ℝ (Φ y) x v) (fderiv ℝ (Φ y) x w) =
        ρ y (t,x) * B v w) ∧
      (∀ i y, y ∈ Y → Φ y '' closedRoundDisk (R i) = closedRoundDisk (R i)) ∧
      ∀ y, (∀ t x, X (t,(y,x)) = 0) → ∀ x, Φ y x = x := by
  obtain ⟨N,hN⟩ := exists_nat_gt (‖T‖ * L)
  have hN0 : (0:ℝ) < N := (mul_nonneg (norm_nonneg _) L.coe_nonneg).trans_lt hN
  let h := T / N
  have hh : ‖h‖ * L < 1 := by
    change ‖T/(N:ℝ)‖ * L < 1
    rw [norm_div,Real.norm_of_nonneg hN0.le,div_mul_eq_mul_div]
    exact (div_lt_one hN0).mpr hN
  have he : (N:ℝ) * h = T := by dsimp [h]; field_simp
  let Φ (y : P) := timeSteps (fiberField X y) (fiberField_lipschitz X hX y)
    (fiberField_smooth X hXs y) hh t N
  have hK : IsCompact (Prod.snd '' tsupport X) := hXc.image continuous_snd
  have hfix (p : P × Plane) (hp : p ∉ Prod.snd '' tsupport X) : Φ p.1 p.2 = p.2 := by
    apply timeSteps_of_stationary
    intro s
    change X (s,p) = 0
    exact image_eq_zero_of_notMem_tsupport (fun h => hp ⟨(s,p),h,rfl⟩)
  refine ⟨Φ,(timeSteps_fiber_smooth X hX hXs hh t N).1,
    (timeSteps_fiber_smooth X hX hXs hh t N).2,
    HasCompactSupport.intro hK (fun p hp => sub_eq_zero.mpr (hfix p hp)),?_,?_,?_⟩
  · intro y x v w
    simpa only [he] using timeSteps_preserves_density (fiberField X y)
      (fiberField_lipschitz X hX y) (fiberField_smooth X hXs y)
      (ρ y) (hρ y) B (hPDE y) hh t N x v w
  · intro i y hy
    apply homeomorph_image_closedRoundDisk
    intro x
    exact timeSteps_preserves_circle_iff (fiberField X y) (fiberField_lipschitz X hX y)
      (fiberField_smooth X hXs y) (fiberField_compact X hXc y) (hR i) (htan i y hy) hh t N x

  · intro y hy x
    apply timeSteps_of_stationary
    intro s
    exact hy s x

theorem exists_parameter_relative_primitive {ι : Type*} [Fintype ι]
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hf0 : ∀ y, (∫ p, f (y,p)) = 0)
    (Y : Set P) (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRi : Injective R)
    (hz : ∀ i y, y ∈ Y → (∫ p in roundDisk (R i), f (y,p)) = 0) :
    ∃ U V : P × Plane → ℝ, ContDiff ℝ ∞ U ∧ ContDiff ℝ ∞ V ∧
      HasCompactSupport U ∧ HasCompactSupport V ∧
      (∀ y p, deriv (fun x => V (y,(x,p.2))) p.1 -
        deriv (fun t => U (y,(p.1,t))) p.2 = f (y,p)) ∧
      (∀ i y, y ∈ Y → ∀ p, radiusSq p = (R i)^2 → -p.2*U (y,p)+p.1*V (y,p) = 0) ∧
      ∀ y, (∀ x, f (y,x) = 0) → ∀ x, U (y,x) = 0 ∧ V (y,x) = 0 := by
  obtain ⟨U,V,hU,hV,hUc,hVc,hcurl,huvzero⟩ := exists_parametric_compact_primitive hf hfc hf0
  let alpha : P × Plane → Plane →L[ℝ] ℝ := fun p =>
    coordinateForm (fun x => U (p.1,x)) (fun x => V (p.1,x)) p.2
  have has : ContDiff ℝ ∞ alpha :=
    (hU.smul contDiff_const).add (hV.smul contDiff_const)
  have hac : HasCompactSupport alpha := by
    apply HasCompactSupport.intro (hUc.union hVc)
    intro p hp
    have hu : U p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inl h))
    have hv : V p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (Or.inr h))
    change U p • _ + V p • _ = 0
    rw [hu,hv,zero_smul,zero_smul,zero_add]
  have hc (y : P) (p : Plane) : planarCurl (fun x => alpha (y,x)) p = f (y,p) :=
    (coordinateForm_curl (hU.comp (contDiff_const.prodMk contDiff_id))
      (hV.comp (contDiff_const.prodMk contDiff_id)) p).trans (hcurl y p)
  have hz' (i : ι) (y : P) (hy : y ∈ Y) : (∫ p in roundDisk (R i), planarCurl (fun x => alpha (y,x)) p) = 0 := by
    simp_rw [hc]
    exact hz i y hy
  obtain ⟨beta,hbs,hbc,hcurlb,hbt,hbzero⟩ :=
    exists_parameter_relative_finite_circle_correction has hac Y R hR hRi hz'
  let U' : P × Plane → ℝ := fun p => beta p (1,0)
  let V' : P × Plane → ℝ := fun p => beta p (0,1)
  have hUs : ContDiff ℝ ∞ U' := hbs.clm_apply contDiff_const
  have hVs : ContDiff ℝ ∞ V' := hbs.clm_apply contDiff_const
  have hU'c : HasCompactSupport U' := by
    apply HasCompactSupport.intro hbc
    intro p hp
    simp only [U',image_eq_zero_of_notMem_tsupport hp,zero_apply]
  have hV'c : HasCompactSupport V' := by
    apply HasCompactSupport.intro hbc
    intro p hp
    simp only [V',image_eq_zero_of_notMem_tsupport hp,zero_apply]
  have hUy (y : P) : ContDiff ℝ ∞ (fun x => U' (y,x)) := hUs.comp (contDiff_const.prodMk contDiff_id)
  have hVy (y : P) : ContDiff ℝ ∞ (fun x => V' (y,x)) := hVs.comp (contDiff_const.prodMk contDiff_id)
  have hby (y : P) : ContDiff ℝ ∞ (fun x => beta (y,x)) := hbs.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨U',V',hUs,hVs,hU'c,hV'c,?_,?_,?_⟩
  · intro y p
    rw [plane_deriv_first ((hVy y).differentiable (by simp)),
      plane_deriv_second ((hUy y).differentiable (by simp))]
    change fderiv ℝ (fun q => beta (y,q) (0,1)) p (1,0) -
      fderiv ℝ (fun q => beta (y,q) (1,0)) p (0,1) = f (y,p)
    rw [form_eval_fderiv (hby y),form_eval_fderiv (hby y)]
    exact (hcurlb y p).trans (hc y p)
  · intro i y hy p hp
    have he : (-p.2,p.1) = (-p.2) • ((1:ℝ),(0:ℝ)) + p.1 • ((0:ℝ),(1:ℝ)) := by
      ext <;> simp
    have ht := hbt i y hy p hp
    rw [he,map_add,map_smul,map_smul] at ht
    exact ht

  · intro y hy x
    have ha0 (q : Plane) : alpha (y,q) = 0 := by
      obtain ⟨hu,hv⟩ := huvzero y hy q
      simp only [alpha,coordinateForm,hu,hv,zero_smul,zero_add]
    have hb0 := hbzero y ha0 x
    simp only [U',V',hb0,zero_apply,and_self]

theorem exists_parameter_relative_background_moser {ι : Type*} [Fintype ι]
    {g f : P × Plane → ℝ} (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hf0 : ∀ y, (∫ p, f (y,p)) = 0)
    (hgpos : ∀ p, 0 < g p) (hpos : ∀ p, 0 < g p+f p)
    (Y : Set P) (R : ι → ℝ) (hR : ∀ i, 0 < R i) (hRi : Injective R)
    (hz : ∀ i y, y ∈ Y → (∫ p in roundDisk (R i), f (y,p)) = 0) :
    ∃ Φ : P → Plane ≃ₜ Plane,
      ContDiff ℝ ∞ (fun p : P × Plane => Φ p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : P × Plane => (Φ p.1).symm p.2) ∧
      HasCompactSupport (fun p : P × Plane => Φ p.1 p.2-p.2) ∧
      (∀ y x v w, (g (y,Φ y x)+f (y,Φ y x)) *
        planarArea (fderiv ℝ (Φ y) x v) (fderiv ℝ (Φ y) x w) = g (y,x)*planarArea v w) ∧
      (∀ i y, y ∈ Y → Φ y '' closedRoundDisk (R i) = closedRoundDisk (R i)) ∧
      ∀ y, (∀ x, f (y,x) = 0) → ∀ x, Φ y x = x := by
  obtain ⟨U,V,hU,hV,hUc,hVc,hcurl,htan,huvzero⟩ :=
    exists_parameter_relative_primitive hf hfc hf0 Y R hR hRi hz
  let field : ℝ × (P × Plane) → Plane := fun p =>
    backgroundField (fun x => g (p.2.1,x)) (fun x => f (p.2.1,x))
      (fun x => U (p.2.1,x)) (fun x => V (p.2.1,x)) (p.1,p.2.2)
  have hXs : ContDiff ℝ ∞ field := parametric_backgroundField_smooth hg hf hU hV hgpos hpos
  have hXc : HasCompactSupport field := parametric_backgroundField_compact hUc hVc
  obtain ⟨L,hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hXc hXs (by simp)
  let X : C(ℝ × (P × Plane),Plane) := ⟨field,hXs.continuous⟩
  have hgy (y : P) : ContDiff ℝ ∞ (fun x => g (y,x)) := hg.comp (contDiff_const.prodMk contDiff_id)
  have hfy (y : P) : ContDiff ℝ ∞ (fun x => f (y,x)) := hf.comp (contDiff_const.prodMk contDiff_id)
  have hUy (y : P) : ContDiff ℝ ∞ (fun x => U (y,x)) := hU.comp (contDiff_const.prodMk contDiff_id)
  have hVy (y : P) : ContDiff ℝ ∞ (fun x => V (y,x)) := hV.comp (contDiff_const.prodMk contDiff_id)
  obtain ⟨Φ,hΦ,hΦi,hΦc,hΦarea,hΦdisk,hΦfix⟩ := exists_parameter_relative_density_transport X hL hXs hXc
    (fun y => backgroundDensity (fun x => g (y,x)) (fun x => f (y,x)))
    (fun y => backgroundDensity_smooth (hgy y) (hfy y)) planarArea
    (fun y => backgroundField_transport (hgy y) (hfy y) (hUy y) (hVy y)
      (fun x => hgpos (y,x)) (fun x => hpos (y,x)) (hcurl y)) Y R hR
    (fun i y hy => backgroundField_tangent (g := fun x => g (y,x))
      (f := fun x => f (y,x)) (htan i y hy)) 0 1
  refine ⟨Φ,hΦ,hΦi,hΦc,?_,hΦdisk,?_⟩
  · intro y x v w
    simpa only [zero_add,backgroundDensity,Real.smoothTransition.one,Real.smoothTransition.zero,
      one_mul,zero_mul,add_zero] using hΦarea y x v w
  · intro y hy x
    apply hΦfix y _ x
    intro t q
    obtain ⟨hu,hv⟩ := huvzero y hy q
    change backgroundField (fun x => g (y,x)) (fun x => f (y,x))
      (fun x => U (y,x)) (fun x => V (y,x)) (t,q) = 0
    simp only [backgroundField,hu,hv,mul_zero,zero_div]
    rfl



end PackingSufficiencySupport.Hamiltonian
end

end OAI
