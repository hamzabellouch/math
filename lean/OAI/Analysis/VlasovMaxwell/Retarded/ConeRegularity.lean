import Mathlib
import OAI.Analysis.VlasovMaxwell.Regularity.IntegralBallPolarFlip
import OAI.Analysis.VlasovMaxwell.Geometry.ParticleTame

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

section

def smoothReciprocal (δ x : ℝ) : ℝ := Real.smoothTransition (2*x/δ-1)/x

lemma smoothReciprocal_smooth {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ ∞ (smoothReciprocal δ) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq (f:=fun _ : ℝ => (0:ℝ))
    have hne : ∀ᶠ y : ℝ in 𝓝 0, y<δ/2 := Iio_mem_nhds (by positivity)
    filter_upwards [hne] with y hy
    dsimp only [smoothReciprocal]
    rw [Real.smoothTransition.zero_of_nonpos,zero_div]
    apply sub_nonpos.mpr
    exact (div_le_iff₀ hδ).2 (by linarith)
  · exact (Real.smoothTransition.contDiff.contDiffAt.comp x
      ((contDiffAt_const.mul contDiffAt_id).div_const δ |>.sub contDiffAt_const)).div contDiffAt_id hx

lemma smoothReciprocal_eq {δ x : ℝ} (hδ : 0 < δ) (hx : δ ≤ x) :
    smoothReciprocal δ x=x⁻¹ := by
  unfold smoothReciprocal
  rw [Real.smoothTransition.one_of_one_le,one_div]
  apply le_sub_iff_add_le.mpr
  exact (le_div_iff₀ hδ).2 (by linarith)

lemma uniform_cone_denominator (P : ℝ) : ∃ δ : ℝ, 0 < δ ∧ ∀ n v : Vec,
    ‖n‖=1 → ‖v‖ ≤ P → δ ≤ 1-dot n (velocity v) := by
  let K : Set (Vec × Vec) := sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_closedBall _ _)
  let D : Vec × Vec → ℝ := fun p => 1-dot p.1 (velocity p.2)
  have hD : Continuous D := continuous_const.sub
    ((contDiff_dot_pair (k:=∞)).continuous.comp (continuous_fst.prodMk ((contDiff_velocity (k:=∞)).continuous.comp continuous_snd)))
  have hp (p : Vec × Vec) (hp : p∈K) : 0<D p :=
    cone_denom_pos p.2 p.1 (by simpa only [mem_sphere,dist_zero_right] using hp.1)
  have hi : ContinuousOn (fun p => (D p)⁻¹) K := hD.continuousOn.inv₀ (fun p hp' => (hp p hp').ne')
  obtain ⟨C,hC⟩ := (hK.image_of_continuousOn hi).isBounded.exists_norm_le
  refine ⟨(1+max C 0)⁻¹,by positivity,?_⟩
  intro n v hn hv
  have hm : (n,v)∈K := ⟨by simpa only [mem_sphere,dist_zero_right] using hn,
    by simpa only [mem_closedBall_zero_iff] using hv⟩
  have hpos := hp (n,v) hm
  have hb := hC _ ⟨(n,v),hm,rfl⟩
  rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos)] at hb
  exact (inv_le_comm₀ (by positivity) hpos).2 (hb.trans (by linarith [le_max_left C 0]))

def smoothNormalisedPhysical (δ : ℝ) (p : (ℝ × Vec × Vec) × (ℝ × Vec × Vec)) : Vec :=
  let r := p.1.1
  let n := p.1.2.1
  let u := velocity p.1.2.2
  let b := fderiv ℝ velocity p.1.2.2 (p.2.2.1+cross u p.2.2.2)
  let D := 1-dot n u
  let R := (smoothReciprocal δ D)^3
  (p.2.1*D) • (((1-dot u u)*R) • (n-u)+(r*R) • ((dot n b) • (n-u)-D • b))

lemma smoothNormalisedPhysical_smooth {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (smoothNormalisedPhysical δ) := by
  let v : ((ℝ × Vec × Vec) × (ℝ × Vec × Vec)) → Vec := fun p => p.1.2.2
  have hv : ContDiff ℝ ∞ v := contDiff_fst.snd.snd
  have hu : ContDiff ℝ ∞ (fun p => velocity (v p)) := contDiff_velocity.comp hv
  have hn : ContDiff ℝ ∞ (fun p : (ℝ × Vec × Vec) × (ℝ × Vec × Vec) => p.1.2.1) := contDiff_fst.snd.fst
  have hb : ContDiff ℝ ∞ (fun p => fderiv ℝ velocity (v p)
      (p.2.2.1+cross (velocity (v p)) p.2.2.2)) :=
    (((contDiff_velocity (k:=∞)).fderiv_right (by simp)).comp hv).clm_apply
      (contDiff_snd.snd.fst.add (contDiff_cross.comp (hu.prodMk contDiff_snd.snd.snd)))
  have hD : ContDiff ℝ ∞ (fun p => 1-dot p.1.2.1 (velocity (v p))) :=
    contDiff_const.sub (contDiff_dot_pair.comp (hn.prodMk hu))
  have hR := ((smoothReciprocal_smooth hδ).comp hD).pow 3
  exact (contDiff_snd.fst.mul hD).smul
    ((((contDiff_const.sub (contDiff_dot_pair.comp (hu.prodMk hu))).mul hR).smul (hn.sub hu)).add
      ((contDiff_fst.fst.mul hR).smul
        (((contDiff_dot_pair.comp (hn.prodMk hb)).smul (hn.sub hu)).sub (hD.smul hb))))

lemma smoothNormalisedPhysical_eq {δ : ℝ} (hδ : 0 < δ)
    (p : (ℝ × Vec × Vec) × (ℝ × Vec × Vec)) (hp : δ ≤ 1-dot p.1.2.1 (velocity p.1.2.2)) :
    smoothNormalisedPhysical δ p=normalisedPhysicalIntegrand p := by
  simp only [smoothNormalisedPhysical,smoothReciprocal_eq hδ hp,normalisedPhysicalIntegrand,
    normalisedElectricKernel,div_eq_mul_inv,inv_pow]

lemma uniform_normalised_integrand_tame (k : ℕ) (hk : 1 ≤ k) (P A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r∈Icc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 → ∀ v : Vec, ‖v‖ ≤ P →
      ∀ (f : Vec → ℝ) (E B : Vec → Vec), ContDiff ℝ ∞ f → ContDiff ℝ ∞ E → ContDiff ℝ ∞ B →
      ∀ x, (∀ i : ℕ, i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ A ∧
        ‖iteratedFDeriv ℝ i E x‖ ≤ A ∧ ‖iteratedFDeriv ℝ i B x‖ ≤ A) →
      ∀ H : ℝ, 0 ≤ H → ‖iteratedFDeriv ℝ (k+1) f x‖ ≤ H →
        ‖iteratedFDeriv ℝ (k+1) E x‖ ≤ H → ‖iteratedFDeriv ℝ (k+1) B x‖ ≤ H →
      ‖iteratedFDeriv ℝ (k+1) (fun y => normalisedPhysicalIntegrand ((r,n,v),(f y,E y,B y))) x‖ ≤ C*(1+H) := by
  obtain ⟨δ,hδ,hden⟩ := uniform_cone_denominator P
  let K : Set ((ℝ × Vec × Vec) × (ℝ × Vec × Vec)) :=
    (Icc (0:ℝ) 1 ×ˢ sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P) ×ˢ closedBall 0 A
  have hK : IsCompact K := (isCompact_Icc.prod ((isCompact_sphere _ _).prod
    (isCompact_closedBall _ _))).prod (isCompact_closedBall _ _)
  obtain ⟨C,hC,hcomp⟩ := tame_comp_on_compact (U:=Vec) (smoothNormalisedPhysical_smooth hδ) hK k hk A hA
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv f E B hf hE hB x hlow H hH hft hEt hBt
  let a : Vec → (ℝ × Vec × Vec) × (ℝ × Vec × Vec) := fun y => ((r,n,v),(f y,E y,B y))
  have ha : ContDiff ℝ ∞ a := contDiff_const.prodMk (hf.prodMk (hE.prodMk hB))
  have harg (i : ℕ) (hi : 1 ≤ i) {D : ℝ} (hD : 0 ≤ D)
      (hfD : ‖iteratedFDeriv ℝ i f x‖ ≤ D) (hED : ‖iteratedFDeriv ℝ i E x‖ ≤ D)
      (hBD : ‖iteratedFDeriv ℝ i B x‖ ≤ D) : ‖iteratedFDeriv ℝ i a x‖ ≤ D := by
    apply norm_iteratedFDeriv_pair_le contDiff_const (hf.prodMk (hE.prodMk hB))
    · simpa only [iteratedFDeriv_const_of_ne (by omega : i≠0),Pi.zero_apply,norm_zero] using hD
    · exact norm_iteratedFDeriv_pair_le hf (hE.prodMk hB) i x hfD
        (norm_iteratedFDeriv_pair_le hE hB i x hED hBD)
  have hx : a x∈K := by
    refine ⟨⟨hr,by simpa only [mem_sphere,dist_zero_right] using hn,
      by simpa only [mem_closedBall_zero_iff] using hv⟩,?_⟩
    rw [mem_closedBall_zero_iff]
    exact max_le (by simpa only [norm_iteratedFDeriv_zero] using (hlow 0 (Nat.zero_le _)).1)
      (max_le (by simpa only [norm_iteratedFDeriv_zero] using (hlow 0 (Nat.zero_le _)).2.1)
        (by simpa only [norm_iteratedFDeriv_zero] using (hlow 0 (Nat.zero_le _)).2.2))
  have hh := hcomp a ha x hx (fun i hi hi' =>
    harg i hi (zero_le_one.trans hA) (hlow i hi').1 (hlow i hi').2.1 (hlow i hi').2.2)
  have he : smoothNormalisedPhysical δ ∘ a =
      (fun y => normalisedPhysicalIntegrand ((r,n,v),(f y,E y,B y))) := by
    funext y
    exact smoothNormalisedPhysical_eq hδ (a y) (hden n v hn hv)
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by linarith [harg (k+1) (by omega) hH hft hEt hBt]) hC)

lemma compact_parameter_taylor
    {U W Z : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {K : Set U} {S : Set W} {g : U × W → Z}
    (hK : IsCompact K) (hS : IsCompact S) (hconv : Convex ℝ S)
    (hg : ∀ q∈K ×ˢ S, ContDiffAt ℝ ∞ g q) :
    ∃ C : ℝ, 0≤C ∧ ∀ p∈K, ∀ x∈S,
      ‖fderiv ℝ (fun z => g (p,z)) x‖≤C ∧ ∀ y∈S,
      ‖g (p,y)-g (p,x)-fderiv ℝ (fun z => g (p,z)) x (y-x)‖≤C*‖y-x‖^2 := by
  obtain ⟨H,hH,hDl⟩ := compact_parameter_lipschitz hK hS hconv
    (g:=fderiv ℝ g) (fun q hq => (hg q hq).fderiv_right (by decide))
  have hd : ContinuousOn (fderiv ℝ g) (K ×ˢ S) :=
    fun q hq => ((hg q hq).continuousAt_fderiv (by simp)).continuousWithinAt
  obtain ⟨M,hM⟩ := ((hK.prod hS).image_of_continuousOn hd).isBounded.exists_norm_le
  let C := max H (max M 0)
  have hC : 0≤C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro p hp x hx
  have hder (z : W) (hz : z∈S) : HasFDerivAt (fun z => g (p,z))
      ((fderiv ℝ g (p,z)).comp (ContinuousLinearMap.inr ℝ U W)) z := by
    exact ((hg (p,z) ⟨hp,hz⟩).differentiableAt (by simp)).hasFDerivAt.comp z
      ((hasFDerivAt_const p z).prodMk (hasFDerivAt_id z))
  have hds (a b : W) (ha : a∈S) (hb : b∈S) :
      ‖fderiv ℝ (fun z => g (p,z)) b-fderiv ℝ (fun z => g (p,z)) a‖≤H*‖b-a‖ := by
    rw [(hder b hb).fderiv,(hder a ha).fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hH (norm_nonneg _))
    intro v
    change ‖(fderiv ℝ g (p,b)-fderiv ℝ g (p,a)) (0,v)‖≤(H*‖b-a‖)*‖v‖
    have hh := (fderiv ℝ g (p,b)-fderiv ℝ g (p,a)).le_opNorm (0,v)
    simp only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg v)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hDl p hp a ha b hb) (norm_nonneg v))
  constructor
  · rw [(hder x hx).fderiv]
    apply ContinuousLinearMap.opNorm_le_bound _ hC
    intro v
    change ‖fderiv ℝ g (p,x) (0,v)‖≤C*‖v‖
    have hh := (fderiv ℝ g (p,x)).le_opNorm (0,v)
    simp only [Prod.norm_mk,norm_zero,max_eq_right (norm_nonneg v)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      ((hM _ ⟨(p,x),⟨hp,hx⟩,rfl⟩).trans (le_trans (le_max_left _ _) (le_max_right _ _))) (norm_nonneg v))
  · intro y hy
    have ht := (hconv.inter (convex_closedBall x ‖y-x‖)).norm_image_sub_le_of_norm_fderiv_le'
      (f:=fun z => g (p,z)) (φ:=fderiv ℝ (fun z => g (p,z)) x) (C:=H*‖y-x‖)
      (fun z hz => (hder z hz.1).differentiableAt)
      (fun z hz => (hds x z hx hz.1).trans (mul_le_mul_of_nonneg_left
        (by simpa only [mem_closedBall,dist_eq_norm] using hz.2) hH))
      (show x∈S ∩ closedBall x ‖y-x‖ by simp [hx])
      (show y∈S ∩ closedBall x ‖y-x‖ by simpa only [mem_inter_iff,mem_closedBall,dist_eq_norm,le_refl,and_true] using hy)
    exact ht.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (le_max_left H (max M 0)) (norm_nonneg _)) (norm_nonneg _)).trans_eq (by ring))

lemma compact_parameter_curvature
    {U W Z X : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {K : Set U} {S : Set W} {g : U × W → Z}
    (hK : IsCompact K) (hS : IsCompact S) (hconv : Convex ℝ S)
    (hg : ∀ q∈K ×ˢ S, ContDiffAt ℝ ∞ g q) :
    ∃ C : ℝ, 0≤C ∧ ∀ p∈K, ∀ f : X → W, (∀ x, f x∈S) →
      ∀ H M : ℝ, 0≤M → CurvatureBound f H →
      (∀ x y, ‖f y-f x‖≤M*‖y-x‖) →
      CurvatureBound (fun x => g (p,f x)) (C*(H+2*M^2)) := by
  obtain ⟨C,hC,hb⟩ := compact_parameter_taylor hK hS hconv hg
  refine ⟨C,hC,?_⟩
  intro p hp f hf H M hM hc hl x v
  let D := fderiv ℝ (fun z => g (p,z)) (f x)
  have h₁ := (hb p hp (f x) (hf x)).2 (f (x+v)) (hf _)
  have h₂ := (hb p hp (f x) (hf x)).2 (f (x-v)) (hf _)
  have hpdist : ‖f (x+v)-f x‖≤M*‖v‖ := by simpa only [add_sub_cancel_left] using hl x (x+v)
  have hmdist : ‖f (x-v)-f x‖≤M*‖v‖ := by simpa only [sub_sub_cancel_left,norm_neg] using hl x (x-v)
  have h₁' := h₁.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mpr hpdist) hC)
  have h₂' := h₂.trans (mul_le_mul_of_nonneg_left
    ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))).mpr hmdist) hC)
  have hlin : ‖D (f (x+v)+f (x-v)-(2:ℝ) • f x)‖≤C*(H*‖v‖^2) :=
    (D.le_opNorm _).trans ((mul_le_mul_of_nonneg_right (hb p hp (f x) (hf x)).1 (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (hc x v) hC))
  have he : g (p,f (x+v))+g (p,f (x-v))-(2:ℝ) • g (p,f x) =
      (g (p,f (x+v))-g (p,f x)-D (f (x+v)-f x))+
      (g (p,f (x-v))-g (p,f x)-D (f (x-v)-f x))+
      D (f (x+v)+f (x-v)-(2:ℝ) • f x) := by
    simp only [map_add,map_sub,map_smul]; module
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h₁' h₂')) hlin)).trans_eq (by ring)

lemma uniform_normalised_integrand_curvature (A P L : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ r∈Icc (0:ℝ) 1, ∀ n : Vec, ‖n‖=1 →
      ∀ v : Vec, ‖v‖≤P → ∀ a : Vec → ℝ, ∀ E B : Vec → Vec,
      (∀ x, |a x|≤A ∧ ‖E x‖≤L ∧ ‖B x‖≤L) →
      ∀ Hf H M N : ℝ, 0≤Hf → 0≤H → 0≤M → 0≤N →
      CurvatureBound a Hf → CurvatureBound E H → CurvatureBound B H →
      (∀ x y, |a y-a x|≤M*‖y-x‖) →
      (∀ x y, ‖E y-E x‖≤N*‖y-x‖ ∧ ‖B y-B x‖≤N*‖y-x‖) →
      CurvatureBound (fun x => normalisedPhysicalIntegrand ((r,n,v),(a x,E x,B x)))
        (C*(Hf+H+2*(M+N)^2)) := by
  let K : Set (ℝ × Vec × Vec) := Icc (0:ℝ) 1 ×ˢ sphere (0:Vec) 1 ×ˢ closedBall (0:Vec) P
  let S : Set (ℝ × Vec × Vec) := closedBall (0:ℝ) A ×ˢ closedBall (0:Vec) L ×ˢ closedBall (0:Vec) L
  have hK : IsCompact K := isCompact_Icc.prod ((isCompact_sphere _ _).prod (isCompact_closedBall _ _))
  have hS : IsCompact S := (isCompact_closedBall _ _).prod
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hc : Convex ℝ S := (convex_closedBall _ _).prod ((convex_closedBall _ _).prod (convex_closedBall _ _))
  obtain ⟨C,hC,hb⟩ := compact_parameter_curvature (X:=Vec) hK hS hc
    (g:=normalisedPhysicalIntegrand) (fun q hq => normalisedPhysicalIntegrand_smoothAt
      ((cone_denom_pos q.1.2.2 q.1.2.1 (mem_sphere_zero_iff_norm.mp hq.1.2.1)).ne'))
  refine ⟨C,hC,?_⟩
  intro r hr n hn v hv a E B hbnd Hf H M N hHf hH hM hN ha hE hB haL hEBL
  apply hb (r,n,v) ⟨hr,mem_sphere_zero_iff_norm.mpr hn,mem_closedBall_zero_iff.mpr hv⟩
    (fun x => (a x,E x,B x))
    (fun x => ⟨by simpa only [mem_closedBall_zero_iff,Real.norm_eq_abs] using (hbnd x).1,
      mem_closedBall_zero_iff.mpr (hbnd x).2.1,mem_closedBall_zero_iff.mpr (hbnd x).2.2⟩)
    (Hf+H) (M+N) (add_nonneg hM hN)
  · exact (ha.mono (le_add_of_nonneg_right hH)).prodMk
      ((hE.mono (le_add_of_nonneg_left hHf)).prodMk (hB.mono (le_add_of_nonneg_left hHf)))
  · intro x y
    apply max_le
    · exact (haL x y).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hN) (norm_nonneg _))
    · exact max_le (((hEBL x y).1).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM) (norm_nonneg _)))
        ((hEBL x y).2.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM) (norm_nonneg _)))

attribute [local instance] Measure.Subtype.measureSpace

variable (t P : ℝ)
local instance : CompactSpace Sphere := isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
local instance : CompactSpace (Icc (0:ℝ) t) := isCompact_iff_compactSpace.mp isCompact_Icc
local instance : CompactSpace (closedBall (0:Vec) P) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
local instance : IsFiniteMeasure (volume : Measure (Icc (0:ℝ) t)) := ⟨by
  rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
  exact isCompact_Icc.measure_lt_top⟩
local instance : IsFiniteMeasure (volume : Measure (closedBall (0:Vec) P)) := ⟨by
  rw [Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet]
  exact (isCompact_closedBall _ _).measure_lt_top⟩

abbrev ConeParameters := Sphere × Icc (0:ℝ) t × closedBall (0:Vec) P
abbrev coneParameterMeasure : Measure (ConeParameters t P) := sphereMeasure.prod (volume.prod volume)

def compactPolarIntegral (G : (ℝ × Vec × Vec) × Vec → Vec) (x : Vec) : Vec :=
  ∫ p : ConeParameters t P, G (((p.2.1:ℝ),(p.1:Vec),(p.2.2:Vec)),x) ∂coneParameterMeasure t P

lemma compactPolarIntegral_eq (G : (ℝ × Vec × Vec) × Vec → Vec)
    (hG : Continuous G) (x : Vec) :
    compactPolarIntegral t P G x = ∫ n : Sphere, ∫ r in Icc (0:ℝ) t,
      ∫ v in closedBall (0:Vec) P, G ((r,n.1,v),x) ∂volume ∂volume ∂sphereMeasure := by
  have hcont : Continuous (fun p : ConeParameters t P => G (((p.2.1:ℝ),(p.1:Vec),(p.2.2:Vec)),x)) :=
    hG.comp (((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))).prodMk continuous_const)
  unfold compactPolarIntegral coneParameterMeasure
  rw [integral_prod _ (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  apply integral_congr_ae
  exact ae_of_all _ (fun n => by
    have hc : Continuous (fun p : Icc (0:ℝ) t × closedBall (0:Vec) P => G (((p.1:ℝ),n.1,(p.2:Vec)),x)) :=
      hG.comp (((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_const.prodMk (continuous_subtype_val.comp continuous_snd))).prodMk continuous_const)
    try dsimp only at *
    rw [integral_prod _ (μ:=volume) (ν:=volume) (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    dsimp only
    have hv (r : ℝ) : (∫ v : closedBall (0:Vec) P, G ((r,n.1,(v:Vec)),x)) =
        ∫ v in closedBall (0:Vec) P, G ((r,n.1,v),x) :=
      integral_subtype measurableSet_closedBall (fun v => G ((r,n.1,v),x))
    simp_rw [hv]
    exact integral_subtype measurableSet_Icc (fun r => ∫ v in closedBall (0:Vec) P, G ((r,n.1,v),x)))

lemma compactPolarIntegral_smooth (G : (ℝ × Vec × Vec) × Vec → Vec)
    (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (compactPolarIntegral t P G) := by
  apply contDiff_integral_smoothFamily
  exact SmoothCompactFamily.ofJoint hG
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))

lemma compactPolarIntegral_derivative_bound (G : (ℝ × Vec × Vec) × Vec → Vec)
    (hG : ContDiff ℝ ∞ G) (n : ℕ) (H : ℝ → ℝ) (hH : Continuous H)
    (hb : ∀ r∈Icc (0:ℝ) t, ∀ a : Vec, ‖a‖=1 → ∀ v : Vec, ‖v‖≤P →
      ∀ x, ‖iteratedFDeriv ℝ n (fun y => G ((r,a,v),y)) x‖ ≤ H r) (x : Vec) :
    ‖iteratedFDeriv ℝ n (compactPolarIntegral t P G) x‖ ≤
      (4*Real.pi)*volume.real (closedBall (0:Vec) P)*(∫ r in Icc (0:ℝ) t, H r) := by
  have hfamily : SmoothCompactFamily (fun p : ConeParameters t P => fun x =>
      G (((p.2.1:ℝ),(p.1:Vec),(p.2.2:Vec)),x)) :=
    SmoothCompactFamily.ofJoint hG
      ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).prodMk
        ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))))
  have hj := norm_iteratedFDeriv_integral_le (coneParameterMeasure t P) n hfamily x
  have hD : Continuous (fun p : ConeParameters t P =>
      ‖iteratedFDeriv ℝ n (fun y => G (((p.2.1:ℝ),(p.1:Vec),(p.2.2:Vec)),y)) x‖) :=
    ((hfamily.2 n).comp (continuous_const.prodMk continuous_id)).norm
  have hhc : Continuous (fun p : ConeParameters t P => H (p.2.1:ℝ)) :=
    hH.comp (continuous_subtype_val.comp (continuous_fst.comp continuous_snd))
  refine hj.trans ((integral_mono (hD.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hhc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (fun p =>
      hb _ p.2.1.2 _ (sphere_norm p.1) _ (mem_closedBall_zero_iff.mp p.2.2.2) x)).trans_eq ?_)
  unfold coneParameterMeasure
  rw [integral_prod _ (hhc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  have he : (∫ p : Icc (0:ℝ) t × closedBall (0:Vec) P, H (p.1:ℝ) ∂volume.prod volume) =
      volume.real (closedBall (0:Vec) P)*(∫ r in Icc (0:ℝ) t, H r) := by
    have hc : Continuous (fun p : Icc (0:ℝ) t × closedBall (0:Vec) P => H (p.1:ℝ)) :=
      hH.comp (continuous_subtype_val.comp continuous_fst)
    try dsimp only at *
    rw [integral_prod _ (μ:=volume) (ν:=volume) (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    dsimp only
    simp_rw [integral_const,smul_eq_mul]
    rw [integral_const_mul,integral_subtype measurableSet_Icc H]
    congr 1
    exact congrArg ENNReal.toReal (Measure.Subtype.volume_univ measurableSet_closedBall.nullMeasurableSet)
  dsimp only
  simp_rw [he,integral_const,smul_eq_mul,sphere_area]
  ring

end

def normalisedRetardedExtension (δ : ℝ) (s : Solution) (t : ℝ)
    (p : (ℝ × Vec × Vec) × Vec) : Vec :=
  smoothNormalisedPhysical δ (p.1,
    (s.f (t-p.1.1,(p.2-p.1.1 • p.1.2.1,p.1.2.2)),
      s.E (t-p.1.1,p.2-p.1.1 • p.1.2.1),s.B (t-p.1.1,p.2-p.1.1 • p.1.2.1)))

lemma normalisedRetardedExtension_smooth {δ : ℝ} (hδ : 0<δ) {s : Solution}
    (hf : ContDiff ℝ ∞ s.f) (hE : ContDiff ℝ ∞ s.E) (hB : ContDiff ℝ ∞ s.B) (t : ℝ) :
    ContDiff ℝ ∞ (normalisedRetardedExtension δ s t) := by
  have hr : ContDiff ℝ ∞ (fun p : (ℝ × Vec × Vec) × Vec => p.1.1) := contDiff_fst.fst
  have hn : ContDiff ℝ ∞ (fun p : (ℝ × Vec × Vec) × Vec => p.1.2.1) := contDiff_fst.snd.fst
  have hv : ContDiff ℝ ∞ (fun p : (ℝ × Vec × Vec) × Vec => p.1.2.2) := contDiff_fst.snd.snd
  have hx := contDiff_snd.sub (hr.smul hn)
  have htime := (contDiff_const (c:=t)).sub hr
  exact (smoothNormalisedPhysical_smooth hδ).comp (contDiff_fst.prodMk
    ((hf.comp (htime.prodMk (hx.prodMk hv))).prodMk
      ((hE.comp (htime.prodMk hx)).prodMk (hB.comp (htime.prodMk hx)))))

lemma retardedElectricDensity_polar_integral {s : Solution} {t P δ r : ℝ}
    (hδ : 0<δ) (hr : 0<r) (hrt : r≤t)
    (hden : ∀ a v : Vec, ‖a‖=1 → ‖v‖≤P → δ≤1-dot a (velocity v))
    (hsupport : ∀ u∈Icc (0:ℝ) t, ∀ y v, P<‖v‖ → s.f (u,(y,v))=0)
    (x : Vec) (n : Sphere) :
    r^2 • retardedElectricDensity s t x (x-r • n.1) =
      ∫ v in closedBall (0:Vec) P, normalisedRetardedExtension δ s t ((r,n.1,v),x) := by
  rw [retardedElectricDensity,coneRadius_sub_smul x n hr,coneDirection_sub_smul x n hr,
    ← integral_smul]
  have hrest : (∫ v in closedBall (0:Vec) P,
      r^2 • ((s.f (t-r,(x-r • n.1,v))*(1-dot n.1 (velocity v))) •
        physicalElectricKernel r n.1 (velocity v)
          (fderiv ℝ velocity v (s.E (t-r,x-r • n.1)+cross (velocity v) (s.B (t-r,x-r • n.1)))))) =
      ∫ v : Vec, r^2 • ((s.f (t-r,(x-r • n.1,v))*(1-dot n.1 (velocity v))) •
        physicalElectricKernel r n.1 (velocity v)
          (fderiv ℝ velocity v (s.E (t-r,x-r • n.1)+cross (velocity v) (s.B (t-r,x-r • n.1))))) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [hsupport (t-r) ⟨by linarith,by linarith⟩ _ v
      (by simpa only [mem_closedBall_zero_iff,not_le] using hv),zero_mul,zero_smul,smul_zero]
  rw [← hrest]
  apply setIntegral_congr_fun measurableSet_closedBall
  intro v hv
  dsimp only [normalisedRetardedExtension]
  rw [smoothNormalisedPhysical_eq hδ _ (hden n.1 v (sphere_norm n) (mem_closedBall_zero_iff.mp hv)),
    normalisedPhysicalIntegrand_eq hr.ne']

lemma retardedElectricDensity_polar_compact {s : Solution} (hf : ContDiff ℝ ∞ s.f)
    (hE : ContDiff ℝ ∞ s.E) (hB : ContDiff ℝ ∞ s.B) (hc : CompactOnFiniteHorizons s)
    {t P δ : ℝ} (ht : 0≤t) (hδ : 0<δ)
    (hden : ∀ a v : Vec, ‖a‖=1 → ‖v‖≤P → δ≤1-dot a (velocity v))
    (hsupport : ∀ r∈Icc (0:ℝ) t, ∀ x v, P<‖v‖ → s.f (r,(x,v))=0) :
    (fun x => ∫ z in ball (0:Vec) t, retardedElectricDensity s t x (x+z)) =
      compactPolarIntegral t P (normalisedRetardedExtension δ s t) := by
  funext x
  rw [integral_ball_polar_flip (integrableOn_retardedElectricDensity_le
    (hf.of_le (by simp)).contDiffOn (hE.of_le (by simp)).contDiffOn
    (hB.of_le (by simp)).contDiffOn hc ht le_rfl x),
    compactPolarIntegral_eq t P _ (normalisedRetardedExtension_smooth hδ hf hE hB t).continuous]
  apply integral_congr_ae
  exact ae_of_all _ (fun n => by
    dsimp only
    rw [integral_Icc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have he : x+-(r • n.1)=x-r • n.1 := by module
    dsimp only
    rw [he]
    exact retardedElectricDensity_polar_integral hδ hr.1 hr.2.le hden hsupport x n)

lemma crossCLM_norm_le (a : Vec) : ‖crossCLM a‖≤‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
  exact norm_cross_le a

lemma retardedMagneticDensity_polar_compact {s : Solution} (hf : ContDiff ℝ ∞ s.f)
    (hE : ContDiff ℝ ∞ s.E) (hB : ContDiff ℝ ∞ s.B) (hc : CompactOnFiniteHorizons s)
    {t P δ : ℝ} (ht : 0≤t) (hδ : 0<δ)
    (hden : ∀ a v : Vec, ‖a‖=1 → ‖v‖≤P → δ≤1-dot a (velocity v))
    (hsupport : ∀ r∈Icc (0:ℝ) t, ∀ x v, P<‖v‖ → s.f (r,(x,v))=0) :
    (fun x => ∫ z in ball (0:Vec) t, retardedMagneticDensity s t x (x+z)) =
      compactPolarIntegral t P (fun p => cross p.1.2.1 (normalisedRetardedExtension δ s t p)) := by
  have hG := normalisedRetardedExtension_smooth hδ hf hE hB t
  have hGB : ContDiff ℝ ∞ (fun p : (ℝ × Vec × Vec) × Vec =>
      cross p.1.2.1 (normalisedRetardedExtension δ s t p)) := contDiff_cross.comp (contDiff_fst.snd.fst.prodMk hG)
  funext x
  rw [integral_ball_polar_flip (integrableOn_retardedMagneticDensity_le
    (hf.of_le (by simp)).contDiffOn (hE.of_le (by simp)).contDiffOn
    (hB.of_le (by simp)).contDiffOn hc ht le_rfl x),compactPolarIntegral_eq t P _ hGB.continuous]
  apply integral_congr_ae
  exact ae_of_all _ (fun n => by
    dsimp only
    rw [integral_Icc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    have he : x+-(r • n.1)=x-r • n.1 := by module
    dsimp only
    rw [he,retardedMagneticDensity,coneDirection_sub_smul x n hr.1,←cross_smul_right,
      retardedElectricDensity_polar_integral hδ hr.1 hr.2.le hden hsupport x n]
    have hint : IntegrableOn (fun v : Vec => normalisedRetardedExtension δ s t ((r,n.1,v),x))
        (closedBall (0:Vec) P) :=
      (hG.continuous.comp ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).prodMk
        continuous_const)).continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    exact ((crossCLM n.1).integral_comp_comm hint).symm)

def ParticleJetBound (n : ℕ) (T A : ℝ) (f : Particle) : Prop :=
  ∀ t∈Icc (0:ℝ) T, ∀ i : ℕ, i≤n → ∀ z, ‖iteratedFDeriv ℝ i (fun w => f (t,w)) z‖≤A

lemma uniform_retarded_extension_tame (k : ℕ) (hk : 1≤k) (P A : ℝ) (hA : 1≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution), ContDiff ℝ ∞ s.f → ContDiff ℝ ∞ s.E → ContDiff ℝ ∞ s.B →
      ∀ δ : ℝ, 0<δ → (∀ a v : Vec, ‖a‖=1 → ‖v‖≤P → δ≤1-dot a (velocity v)) →
      ∀ T : ℝ, T≤1 → ParticleJetBound k T A s.f → SpatialJetBound k T A s.E s.B →
      ∀ H : ℝ → ℝ, (∀ u∈Icc (0:ℝ) T, 0≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ z, ‖iteratedFDeriv ℝ (k+1) (fun w => s.f (u,w)) z‖≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ x, ‖iteratedFDeriv ℝ (k+1) (fun y => s.E (u,y)) x‖≤H u ∧
        ‖iteratedFDeriv ℝ (k+1) (fun y => s.B (u,y)) x‖≤H u) →
      ∀ t∈Icc (0:ℝ) T, ∀ r∈Icc (0:ℝ) t, ∀ a : Vec, ‖a‖=1 → ∀ v : Vec, ‖v‖≤P →
      ∀ x, ‖iteratedFDeriv ℝ (k+1) (fun y => normalisedRetardedExtension δ s t ((r,a,v),y)) x‖ ≤
          C*(1+H (t-r)) := by
  obtain ⟨C,hC,hkernel⟩ := uniform_normalised_integrand_tame k hk P A hA
  refine ⟨C,hC,?_⟩
  intro s hf hE hB δ hδ hden T hT hfj hEBj H hH hft hEBt t ht r hr a ha v hv x
  have htr : t-r∈Icc (0:ℝ) T := ⟨by linarith [hr.2],by linarith [ht.2,hr.1]⟩
  have hfs : ContDiff ℝ ∞ (fun y => s.f (t-r,(y,v))) :=
    hf.comp (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))
  have hEs := hE.comp ((contDiff_const (c:=t-r)).prodMk contDiff_id)
  have hBs := hB.comp ((contDiff_const (c:=t-r)).prodMk contDiff_id)
  have he : (fun y => normalisedRetardedExtension δ s t ((r,a,v),y)) =
      (fun y => normalisedPhysicalIntegrand ((r,a,v),(s.f (t-r,(y-r • a,v)),
        s.E (t-r,y-r • a),s.B (t-r,y-r • a)))) := by
    funext y
    exact smoothNormalisedPhysical_eq hδ _ (hden a v ha hv)
  rw [he]
  change ‖iteratedFDeriv ℝ (k+1) (fun y => (fun z => normalisedPhysicalIntegrand
    ((r,a,v),(s.f (t-r,(z,v)),s.E (t-r,z),s.B (t-r,z)))) (y-r • a)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub (f:=fun z => normalisedPhysicalIntegrand
    ((r,a,v),(s.f (t-r,(z,v)),s.E (t-r,z),s.B (t-r,z)))) (k+1) (r • a) x]
  apply hkernel r ⟨hr.1,hr.2.trans (ht.2.trans hT)⟩ a ha v hv _ _ _ hfs hEs hBs (x-r • a)
  · intro i hi
    refine ⟨(norm_iteratedFDeriv_phase_slice (hf.comp (contDiff_const.prodMk contDiff_id)) i _ v).trans
      (hfj _ htr i hi _),(hEBj _ htr _ i hi).1,(hEBj _ htr _ i hi).2⟩
  · exact hH _ htr
  · exact (norm_iteratedFDeriv_phase_slice (hf.comp (contDiff_const.prodMk contDiff_id)) (k+1) _ v).trans
      (hft _ htr _)
  · exact (hEBt _ htr _).1
  · exact (hEBt _ htr _).2

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma integral_Icc_sub (H : ℝ → ℝ) {t : ℝ} (ht : 0≤t) :
    (∫ r in Icc (0:ℝ) t, H (t-r))=∫ r in Icc (0:ℝ) t, H r := by
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le ht,← intervalIntegral.integral_of_le ht,
    intervalIntegral.integral_comp_sub_left]
  simp only [sub_self,sub_zero]

lemma physical_cone_derivative_tame (k : ℕ) (hk : 1≤k) (P A : ℝ) (hA : 1≤A) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution), ContDiff ℝ ∞ s.f → ContDiff ℝ ∞ s.E → ContDiff ℝ ∞ s.B →
      CompactOnFiniteHorizons s → ∀ T : ℝ, T≤1 →
      (∀ u∈Icc (0:ℝ) T, ∀ y v, P<‖v‖ → s.f (u,(y,v))=0) →
      ParticleJetBound k T A s.f → SpatialJetBound k T A s.E s.B →
      ∀ H : ℝ → ℝ, Continuous H → (∀ u∈Icc (0:ℝ) T, 0≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ z, ‖iteratedFDeriv ℝ (k+1) (fun w => s.f (u,w)) z‖≤H u) →
      (∀ u∈Icc (0:ℝ) T, ∀ x, ‖iteratedFDeriv ℝ (k+1) (fun y => s.E (u,y)) x‖≤H u ∧
        ‖iteratedFDeriv ℝ (k+1) (fun y => s.B (u,y)) x‖≤H u) →
      ∀ t∈Icc (0:ℝ) T, ∀ x,
        ‖iteratedFDeriv ℝ (k+1) (fun y => ∫ z in ball (0:Vec) t,
          retardedElectricDensity s t y (y+z)) x‖ ≤ C*(∫ u in Icc (0:ℝ) t, 1+H u) ∧
        ‖iteratedFDeriv ℝ (k+1) (fun y => ∫ z in ball (0:Vec) t,
          retardedMagneticDensity s t y (y+z)) x‖ ≤ C*(∫ u in Icc (0:ℝ) t, 1+H u) := by
  obtain ⟨K,hK,hkernel⟩ := uniform_retarded_extension_tame k hk P A hA
  obtain ⟨δ,hδ,hden⟩ := uniform_cone_denominator P
  refine ⟨(4*Real.pi)*volume.real (closedBall (0:Vec) P)*K,by positivity,?_⟩
  intro s hf hE hB hc T hT hsupport hfj hEBj H hH hHpos hft hEBt t ht x
  let G := normalisedRetardedExtension δ s t
  have hG : ContDiff ℝ ∞ G := normalisedRetardedExtension_smooth hδ hf hE hB t
  have hsupport' : ∀ u∈Icc (0:ℝ) t, ∀ y v, P<‖v‖ → s.f (u,(y,v))=0 :=
    fun u hu => hsupport u ⟨hu.1,hu.2.trans ht.2⟩
  have hGb : ∀ r∈Icc (0:ℝ) t, ∀ a : Vec, ‖a‖=1 → ∀ v : Vec, ‖v‖≤P →
      ∀ y, ‖iteratedFDeriv ℝ (k+1) (fun w => G ((r,a,v),w)) y‖≤K*(1+H (t-r)) :=
    hkernel s hf hE hB δ hδ hden T hT hfj hEBj H hHpos hft hEBt t ht
  have hHc : Continuous (fun r => K*(1+H (t-r))) :=
    continuous_const.mul (continuous_const.add (hH.comp (continuous_const.sub continuous_id)))
  have hint : (4*Real.pi)*volume.real (closedBall (0:Vec) P)*
      (∫ r in Icc (0:ℝ) t, K*(1+H (t-r))) =
      (4*Real.pi)*volume.real (closedBall (0:Vec) P)*K*(∫ u in Icc (0:ℝ) t, 1+H u) := by
    rw [integral_const_mul,integral_Icc_sub (fun r => 1+H r) ht.1]
    ring
  constructor
  · rw [retardedElectricDensity_polar_compact hf hE hB hc ht.1 hδ hden hsupport']
    exact (compactPolarIntegral_derivative_bound t P G hG (k+1) _ hHc hGb x).trans_eq hint
  · rw [retardedMagneticDensity_polar_compact hf hE hB hc ht.1 hδ hden hsupport']
    have hGB : ContDiff ℝ ∞ (fun p : (ℝ × Vec × Vec) × Vec => cross p.1.2.1 (G p)) :=
      contDiff_cross.comp (contDiff_fst.snd.fst.prodMk hG)
    apply (compactPolarIntegral_derivative_bound t P _ hGB (k+1) _ hHc ?_ x).trans_eq hint
    intro r hr a ha v hv y
    have hs : ContDiff ℝ ∞ (fun w => G ((r,a,v),w)) := hG.comp (contDiff_const.prodMk contDiff_id)
    have hb := (crossCLM a).norm_iteratedFDeriv_comp_left (x:=y) hs.contDiffAt (by exact_mod_cast le_top : ((k+1:ℕ):ℕ∞ω)≤∞)
    change ‖iteratedFDeriv ℝ (k+1) ((crossCLM a) ∘ (fun w => G ((r,a,v),w))) y‖ ≤ _
    refine hb.trans ((mul_le_mul_of_nonneg_right (crossCLM_norm_le a) (norm_nonneg _)).trans ?_)
    rw [ha,one_mul]
    exact hGb r hr a ha v hv y

end RVM

end

end OAI
