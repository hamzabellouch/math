import Mathlib
import OAI.Geometry.BallPacking.Models.CubicPhysicalLocality

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

 theorem linearLiouville_variable_smul (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    (hΩ : ∀ z,Ω z z=0) {s : E → ℝ} {w : E → V} {x : E}
    (hs : DifferentiableAt ℝ s x) (hw : DifferentiableAt ℝ w x) (u : E) :
    linearLiouville Ω (s x • w x) (fderiv ℝ (fun y => s y • w y) x u)=
      (s x)^2*linearLiouville Ω (w x) (fderiv ℝ w x u) := by
  change linearLiouville Ω (s x • w x) (fderiv ℝ (s • w) x u)=_
  rw [fderiv_smul hs hw]
  simp only [linearLiouville,smul_apply,smul_eq_mul,add_apply,
    ContinuousLinearMap.smulRight_apply,map_smul,map_add,hΩ,mul_zero,add_zero]
  ring

variable {ι : Type*} [Fintype ι]
 theorem fsBallMap_primitive {c : ℝ} (hc : 0≤c) (z v : PlanePhase ι) :
    standardLiouville (fsBallMap c z) (fderiv ℝ (fsBallMap c) z v)=affineFSPrimitive c z v := by
  rw [fsBallMap_fderiv]
  simp only [standardLiouville,affineFSPrimitive,fsBallMap,smul_apply,smul_eq_mul,
    map_smul,map_sub,phaseArea_self,mul_zero,sub_zero]
  have he : (Real.sqrt c/Real.sqrt (1+phaseSq z))^2=c/(1+phaseSq z) := by
    rw [div_pow,Real.sq_sqrt hc,Real.sq_sqrt (fs_den_pos z).le]
  calc
    _=(Real.sqrt c/Real.sqrt (1+phaseSq z))^2/2*phaseArea z v := by ring
    _=_ := by rw [he]; field_simp

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport
open scoped BigOperators
open MeasureTheory Set
open scoped Pointwise
open MomentPolytope

def largeMomentDomain (q : ℕ) (h₁ h₂ : ℝ) : Set (ℝ × (Fin q → ℝ)) :=
  {x | x.1 ∈ Icc 0 h₁ ∧ x.2 ∈ momentSimplex q (h₂*(1-x.1))}

theorem largeMomentDomain_isClosed (q : ℕ) (h₁ h₂ : ℝ) :
    IsClosed (largeMomentDomain q h₁ h₂) := by
  have hn : IsClosed {x : ℝ × (Fin q → ℝ) | ∀ i,0≤x.2 i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const ((continuous_apply i).comp continuous_snd)
  exact (isClosed_Icc.preimage continuous_fst).inter (hn.inter
    (isClosed_le (continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_snd)
      (continuous_const.mul (continuous_const.sub continuous_fst))))

theorem largeMomentDomain_isCompact (q : ℕ) (h₁ : ℝ) {h₂ : ℝ} (hh₂ : 0 ≤ h₂) :
    IsCompact (largeMomentDomain q h₁ h₂) := by
  refine (isCompact_Icc (a := (0,fun _ : Fin q => (0:ℝ)))
    (b := (h₁,fun _ => h₂))).of_isClosed_subset (largeMomentDomain_isClosed q h₁ h₂) ?_
  intro x hx
  refine ⟨⟨hx.1.1,hx.2.1⟩,hx.1.2,fun i => ?_⟩
  have hi := (Finset.single_le_sum (fun j _ => hx.2.1 j) (Finset.mem_univ i)).trans hx.2.2
  have hu : h₂*(1-x.1)≤h₂ := by nlinarith [hx.1.1]
  exact hi.trans hu

theorem integral_scaled_small_model (q : ℕ) {h A : ℝ} (hh : 0≤h) (hA : 0≤A) :
    (∫ p in momentSimplex q (h*A), (2:ℝ)^q*(A-2*∑ i,p i)) =
      smallModelMean q h * A^(q+1) := by
  have ht : IntegrableOn (fun p : Fin q → ℝ => h*A-∑ i,p i) (momentSimplex q (h*A)) :=
    ((continuous_const.sub (continuous_finsetSum _ fun i _ => continuous_apply i)).continuousOn).integrableOn_compact (momentSimplex_isCompact q (h*A))
  have hc : IntegrableOn (fun _ : Fin q → ℝ => A-2*(h*A)) (momentSimplex q (h*A)) :=
    continuousOn_const.integrableOn_compact (momentSimplex_isCompact q (h*A))
  have heq (p : Fin q → ℝ) : A-2*∑ i,p i = (A-2*(h*A))+2*(h*A-∑ i,p i) := by ring
  simp_rw [heq]
  rw [integral_const_mul,integral_add hc (ht.const_mul 2),integral_const_mul,
    setIntegral_const,integral_simplex_tent q (mul_nonneg hh hA)]
  simp only [smul_eq_mul,volumeReal_momentSimplex q (mul_nonneg hh hA)]
  dsimp [smallModelMean]
  rw [Nat.factorial_succ,Nat.cast_mul]
  simp only [Nat.cast_add,Nat.cast_one,pow_succ,mul_pow]
  have hf : (q.factorial : ℝ) ≠ 0 := by positivity
  have hq : (q:ℝ)+1 ≠ 0 := by positivity
  field_simp
  ring

def largeModelMean (q : ℕ) (h₁ h₂ : ℝ) : ℝ :=
  smallModelMean q h₂ * (1-(1-h₁)^(q+2))/(q+2)

theorem integral_large_model (q : ℕ) {h₁ h₂ : ℝ}
    (hh₁ : 0≤h₁) (hh₁' : h₁≤1) (hh₂ : 0≤h₂) :
    (∫ x in largeMomentDomain q h₁ h₂, (2:ℝ)^q*(1-x.1-2*∑ i,x.2 i)) =
      largeModelMean q h₁ h₂ := by
  let D := largeMomentDomain q h₁ h₂
  let f : ℝ × (Fin q → ℝ) → ℝ := fun x => (2:ℝ)^q*(1-x.1-2*∑ i,x.2 i)
  have hD := (largeMomentDomain_isClosed q h₁ h₂).measurableSet
  have hf : IntegrableOn f D := ContinuousOn.integrableOn_compact
    (largeMomentDomain_isCompact q h₁ hh₂) (by dsimp [f]; fun_prop)
  have hi : Integrable (D.indicator f) := (integrable_indicator_iff hD).2 hf
  rw [←integral_indicator hD]
  change (∫ x, D.indicator f x ∂(volume.prod volume)) = _
  rw [integral_prod _ hi]
  have slice (u : ℝ) : (∫ p, D.indicator f (u,p)) =
      (Icc 0 h₁).indicator (fun u => ∫ p in momentSimplex q (h₂*(1-u)),
        (2:ℝ)^q*(1-u-2*∑ i,p i)) u := by
    by_cases hu : u ∈ Icc 0 h₁
    · rw [indicator_of_mem hu,←integral_indicator (momentSimplex_isClosed q (h₂*(1-u))).measurableSet]
      congr 1
      funext p
      by_cases hp : p∈momentSimplex q (h₂*(1-u))
      · rw [indicator_of_mem (show (u,p)∈D from ⟨hu,hp⟩),indicator_of_mem hp]
      · rw [indicator_of_notMem (show (u,p)∉D from fun hx => hp hx.2),indicator_of_notMem hp]
    · rw [indicator_of_notMem hu]
      have hz (p : Fin q → ℝ) : D.indicator f (u,p)=0 :=
        indicator_of_notMem (show (u,p)∉D from fun hx => hu hx.1) f
      simp_rw [hz]
      exact integral_zero _ _
  simp_rw [slice]
  rw [integral_indicator measurableSet_Icc]
  have heq : (∫ u in Icc 0 h₁, ∫ p in momentSimplex q (h₂*(1-u)),
      (2:ℝ)^q*(1-u-2*∑ i,p i)) =
      ∫ u in Icc 0 h₁, smallModelMean q h₂*(1-u)^(q+1) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    exact integral_scaled_small_model q hh₂ (by linarith [hu.2])
  rw [heq,integral_const_mul,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le hh₁,
    intervalIntegral.integral_comp_sub_left (fun u : ℝ => u^(q+1)) 1,
    sub_zero,integral_pow]
  simp only [one_pow]
  simp only [largeModelMean,Nat.cast_add,Nat.cast_one]
  rw [show q+1+1=q+2 by omega,show (q:ℝ)+1+1=(q:ℝ)+2 by ring]
  ring

theorem continuous_largeModelMean (q : ℕ) :
    Continuous (fun h : ℝ×ℝ => largeModelMean q h.1 h.2) := by
  unfold largeModelMean
  exact ((continuous_smallModelMean q).comp continuous_snd).mul
    (continuous_const.sub ((continuous_const.sub continuous_fst).pow (q+2))) |>.div_const _

theorem largeModelMean_limit_value (q : ℕ) (a : ℝ) :
    largeModelMean q (1-a) (1/2) = (1-a^(q+2))/((q+2).factorial : ℝ) := by
  unfold largeModelMean
  rw [smallModelMean_half]
  have ha : 1-(1-a)=a := by ring
  rw [ha]
  have hf : ((q+2).factorial : ℝ)=((q:ℝ)+2)*((q+1).factorial : ℝ) := by
    rw [show q+2=(q+1)+1 by omega,Nat.factorial_succ,Nat.cast_mul]
    push_cast
    ring
  rw [hf]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

def largeModelBounds (q : ℕ) (h₂ : ℝ) : Fin 2 → Moments (q+1) :=
  ![Fin.cons 1 (fun _ => 0),Fin.cons h₂ (fun _ => 1)]

theorem largeModelBounds_nonneg (q : ℕ) {h₂ : ℝ} (hh₂ : 0 ≤ h₂) :
    ∀ ν i,0 ≤ largeModelBounds q h₂ ν i := by
  intro ν i
  fin_cases ν <;> refine Fin.cases ?_ (fun j => ?_) i <;> simp [largeModelBounds,hh₂]

theorem largeModelRegion_eq (q : ℕ) (h₁ h₂ : ℝ) :
    region (largeModelBounds q h₂) ![h₁,h₂] =
      (momentHeadTail q) ⁻¹' largeMomentDomain q h₁ h₂ := by
  ext p
  have hrow0 : (∑ j,largeModelBounds q h₂ 0 j*p j)=p 0 := by
    simp [largeModelBounds,Fin.sum_univ_succ]
  have hrow1 : (∑ j,largeModelBounds q h₂ 1 j*p j)=h₂*p 0+∑ j : Fin q,p j.succ := by
    simp [largeModelBounds,Fin.sum_univ_succ]
  change ((∀ j,0≤p j) ∧ ∀ ν,∑ j,largeModelBounds q h₂ ν j*p j ≤ ![h₁,h₂] ν) ↔
    (p 0∈Icc 0 h₁ ∧ (fun j : Fin q => p j.succ)∈momentSimplex q (h₂*(1-p 0)))
  constructor
  · rintro ⟨hp,hbound⟩
    have h0 := hbound 0
    have h1 := hbound 1
    rw [hrow0] at h0
    rw [hrow1] at h1
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at h0 h1
    exact ⟨⟨hp 0,h0⟩,fun j => hp j.succ,by linarith⟩
  · rintro ⟨⟨hp,hh₁⟩,hp',hh₂⟩
    refine ⟨fun j => Fin.cases hp hp' j,fun ν => ?_⟩
    fin_cases ν
    · change (∑ j,largeModelBounds q h₂ 0 j*p j) ≤ h₁
      rw [hrow0]
      exact hh₁
    · change (∑ j,largeModelBounds q h₂ 1 j*p j) ≤ h₂
      rw [hrow1]
      linarith

theorem largeModelRegion_isCompact (q : ℕ) (h₁ : ℝ) {h₂ : ℝ} (hh₂ : 0 ≤ h₂) :
    IsCompact (region (largeModelBounds q h₂) ![h₁,h₂]) := by
  rw [largeModelRegion_eq]
  exact isCompact_preimage_momentHeadTail q (largeMomentDomain_isCompact q h₁ hh₂)

theorem largeModelRegion_contains_cap (q : ℕ) {r h₁ h₂ : ℝ}
    (hr₁ : r ≤ h₁) (hr₂ : r ≤ h₂) (hh₂ : h₂ ≤ 1) :
    momentSimplex (q+1) r ⊆ region (largeModelBounds q h₂) ![h₁,h₂] := by
  rw [largeModelRegion_eq]
  intro p hp
  change p 0∈Icc 0 h₁ ∧ (fun j : Fin q => p j.succ)∈momentSimplex q (h₂*(1-p 0))
  have hsum : p 0+∑ j : Fin q,p j.succ ≤ r := by simpa only [Fin.sum_univ_succ] using hp.2
  have htail : 0 ≤ ∑ j : Fin q,p j.succ := Finset.sum_nonneg fun j _ => hp.1 j.succ
  refine ⟨⟨hp.1 0,by linarith⟩,fun j => hp.1 j.succ,?_⟩
  have hu := mul_le_mul_of_nonneg_right hh₂ (hp.1 0)
  dsimp
  linarith

def largeModelDensity (q : ℕ) (p : Moments (q+1)) : ℝ :=
  (2:ℝ)^q*(1-p 0-2*∑ j : Fin q,p j.succ)

def largeModelGap {q : ℕ} {ι : Type*} [Fintype ι] (r : ι → ℝ) (p : Moments (q+1)) : ℝ :=
  largeModelDensity q p-∑ i,max (r i-∑ j,p j) 0

theorem integral_largeModelDensity (q : ℕ) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁' : h₁ ≤ 1) (hh₂ : 0 ≤ h₂) :
    (∫ p in region (largeModelBounds q h₂) ![h₁,h₂], largeModelDensity q p) =
      largeModelMean q h₁ h₂ := by
  rw [largeModelRegion_eq]
  have heq : largeModelDensity q =
      (fun x : ℝ×(Fin q→ℝ) => (2:ℝ)^q*(1-x.1-2*∑ j,x.2 j)) ∘ momentHeadTail q := rfl
  rw [heq]
  simp only [Function.comp_apply]
  rw [integral_momentHeadTail q (largeMomentDomain_isClosed q h₁ h₂).measurableSet
    (fun x : ℝ×(Fin q→ℝ) => (2:ℝ)^q*(1-x.1-2*∑ j,x.2 j))]
  exact integral_large_model q hh₁ hh₁' hh₂

theorem integral_largeModelGap {q : ℕ} {ι : Type*} [Fintype ι]
    (r : ι → ℝ) (hr : ∀ i,0 ≤ r i) {h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hh₁' : h₁ ≤ 1) (hh₂ : 0 ≤ h₂) (hh₂' : h₂ ≤ 1)
    (hr₁ : ∀ i,r i ≤ h₁) (hr₂ : ∀ i,r i ≤ h₂) :
    (∫ p in region (largeModelBounds q h₂) ![h₁,h₂], largeModelGap r p) =
      largeModelMean q h₁ h₂-(∑ i,r i^(q+2))/((q+2).factorial : ℝ) := by
  have hC := largeModelRegion_isCompact q h₁ hh₂
  have hcap (i : ι) := largeModelRegion_contains_cap q (hr₁ i) (hr₂ i) hh₂'
  unfold largeModelGap
  rw [integral_sub]
  · rw [integral_largeModelDensity q hh₁ hh₁' hh₂,
      integral_sum_tents r hr hC.measurableSet (fun _ hp => hp.1) hcap]
  · apply ContinuousOn.integrableOn_compact hC
    unfold largeModelDensity
    fun_prop
  · apply ContinuousOn.integrableOn_compact hC
    fun_prop

theorem largeModelGap_eq_cappedAffine {q : ℕ} {ι : Type*} [Fintype ι]
    (r : ι → ℝ) : @largeModelGap q ι _ r =
      cappedAffine ((2:ℝ)^q) (Fin.cons ((2:ℝ)^q) (fun _ => (2:ℝ)^q*2)) r (fun _ => 1) := by
  funext p
  simp only [largeModelGap,largeModelDensity,cappedAffine,Fin.sum_univ_succ,
    Fin.cons_zero,Fin.cons_succ,one_mul,←Finset.mul_sum]
  ring

theorem continuous_largeModelGap {q : ℕ} {ι : Type*} [Fintype ι] (r : ι → ℝ) :
    Continuous (@largeModelGap q ι _ r) := by
  rw [largeModelGap_eq_cappedAffine]
  exact continuous_cappedAffine _ _ _ _

theorem largeModelDensity_lower (q : ℕ) {h₁ h₂ : ℝ} (hh₂ : h₂ ≤ 1/2)
    {p : Moments (q+1)} (hp : p ∈ region (largeModelBounds q h₂) ![h₁,h₂]) :
    (2:ℝ)^q*(1-h₁)*(1-2*h₂) ≤ largeModelDensity q p := by
  rw [largeModelRegion_eq] at hp
  change p 0∈Icc 0 h₁ ∧ (fun j => p j.succ)∈momentSimplex q (h₂*(1-p 0)) at hp
  have he : (1-h₁)*(1-2*h₂) ≤ 1-p 0-2*∑ j : Fin q,p j.succ := by
    have hm := mul_le_mul_of_nonneg_right (show 1-h₁ ≤ 1-p 0 by linarith [hp.1.2])
      (show 0 ≤ 1-2*h₂ by linarith)
    nlinarith [hp.2.2]
  unfold largeModelDensity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (by positivity : (0:ℝ) ≤ 2^q)

theorem exists_large_model_comparison_data {q : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ι → ℝ) (hr : ∀ i,0 < r i) {a : ℝ} (ha : 0<a) (_ha1 : a<1)
    (hrs : ∀ i,r i<1-a) (hrhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(q+2)<1-a^(q+2)) :
    ∃ h₁ h₂ d₁ d₂ : ℚ, ∃ τ ε : ℝ,
      (∀ i,r i<h₁) ∧ h₁<d₁ ∧ (d₁:ℝ)<1-a ∧
      (∀ i,r i<h₂) ∧ h₂<d₂ ∧ (d₂:ℝ)<1/2 ∧
      0<(h₁:ℝ) ∧ 0<(h₂:ℝ) ∧ 0<τ ∧ τ<1 ∧ 0<ε ∧
      (∀ i,momentSimplex (q+1) (r i) ⊆ τ • region (largeModelBounds q h₂) ![h₁,h₂]) ∧
      ConcaveOn ℝ (region (largeModelBounds q h₂) ![h₁,h₂]) (largeModelGap r) ∧
      (0 < ∫ p in region (largeModelBounds q h₂) ![h₁,h₂], largeModelGap r p) ∧
      ∀ p ∈ region (largeModelBounds q h₂) ![h₁,h₂],
        p ∉ τ • region (largeModelBounds q h₂) ![h₁,h₂] → ε ≤ largeModelGap r p := by
  classical
  let S := Finset.univ.image r
  have hS : S.Nonempty := Finset.image_nonempty.2 Finset.univ_nonempty
  let R := S.max' hS
  have hR (i : ι) : r i ≤ R := Finset.le_max' S (r i) (Finset.mem_image_of_mem r (Finset.mem_univ i))
  have hRs : R<1-a := (Finset.max'_lt_iff S hS).2 (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.1 hx
    exact hrs i)
  have hRhalf : R<1/2 := (Finset.max'_lt_iff S hS).2 (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.1 hx
    exact hrhalf i)
  have hRpos : 0<R := (hr (Classical.arbitrary ι)).trans_le (hR _)
  have hfac : (0:ℝ)<((q+2).factorial : ℝ) := by positivity
  have hlim : (∑ i,r i^(q+2))/((q+2).factorial : ℝ)<largeModelMean q (1-a) (1/2) := by
    rw [largeModelMean_limit_value]
    exact div_lt_div_of_pos_right hvol hfac
  obtain ⟨h₁,h₂,d₁,d₂,hRh₁,hhd₁,hd₁,hRh₂,hhd₂,hd₂,hmean⟩ :=
    rational_truncation_2d (fun h => largeModelMean q h.1 h.2)
      (continuous_largeModelMean q) hRs hRhalf hlim
  have hh₁ : (0:ℝ)<h₁ := hRpos.trans hRh₁
  have hh₂ : (0:ℝ)<h₂ := hRpos.trans hRh₂
  have hh₁s : (h₁:ℝ)<1-a := (by exact_mod_cast hhd₁ : (h₁:ℝ)<d₁).trans hd₁
  have hh₂half : (h₂:ℝ)<1/2 := (by exact_mod_cast hhd₂ : (h₂:ℝ)<d₂).trans hd₂
  have hratio : max (R/(h₁:ℝ)) (R/(h₂:ℝ))<1 := max_lt
    ((div_lt_one hh₁).2 hRh₁) ((div_lt_one hh₂).2 hRh₂)
  obtain ⟨τ,hτlo,hτhi⟩ := exists_between hratio
  have hτlo₁ : R/(h₁:ℝ)<τ := (le_max_left _ _).trans_lt hτlo
  have hτlo₂ : R/(h₂:ℝ)<τ := (le_max_right _ _).trans_lt hτlo
  have hτ : 0<τ := (div_pos hRpos hh₁).trans hτlo₁
  have hRτ₁ : R<τ*(h₁:ℝ) := (div_lt_iff₀ hh₁).1 hτlo₁
  have hRτ₂ : R<τ*(h₂:ℝ) := (div_lt_iff₀ hh₂).1 hτlo₂
  let ε := (2:ℝ)^q*(1-(h₁:ℝ))*(1-2*(h₂:ℝ))
  have hε : 0<ε := mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)
  have hb : ∀ ν j,largeModelBounds q (h₂:ℝ) ν j ≤ 1 := by
    intro ν j
    fin_cases ν
    · change (@Fin.cons q (fun _ => ℝ) 1 (fun _ => 0)) j ≤ 1
      exact Fin.cases (by norm_num) (fun _ => by norm_num) j
    · change (@Fin.cons q (fun _ => ℝ) (h₂:ℝ) (fun _ => 1)) j ≤ 1
      exact Fin.cases (by simpa using (show (h₂:ℝ) ≤ 1 by linarith)) (fun _ => le_rfl) j
  have hcap (i : ι) : momentSimplex (q+1) (r i) ⊆
      τ • region (largeModelBounds q h₂) ![h₁,h₂] := by
    apply cap_into_scaled_region _ _ hb hτ
    intro ν
    fin_cases ν
    · exact (hR i).trans hRτ₁.le
    · exact (hR i).trans hRτ₂.le
  refine ⟨h₁,h₂,d₁,d₂,τ,ε,fun i => (hR i).trans_lt hRh₁,hhd₁,hd₁,
    fun i => (hR i).trans_lt hRh₂,hhd₂,hd₂,hh₁,hh₂,hτ,hτhi,hε,hcap,?_,?_,?_⟩
  · rw [largeModelGap_eq_cappedAffine]
    exact concaveOn_cappedAffine _ _ _ _ (fun _ => by norm_num) (convex_region _ _)
  · rw [integral_largeModelGap r (fun i => (hr i).le) hh₁.le (by linarith) hh₂.le
      (by linarith) (fun i => (hR i).trans hRh₁.le) (fun i => (hR i).trans hRh₂.le)]
    linarith
  · intro p hp hout
    have hz := sum_caps_zero_outside r (fun _ hp => hp.1) hcap hp hout
    simp only [largeModelGap,hz,sub_zero]
    exact largeModelDensity_lower q hh₂half.le hp

end PackingSufficiencySupport

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open Hamiltonian MomentPolytope

 def largeNormalCoefficient (q : ℕ) (p : Fin (q+1) → ℝ) : ℝ :=
  1-p 0-2*∑ j : Fin q,p j.succ

 theorem largeNormalCoefficient_smooth (q : ℕ) : ContDiff ℝ ∞ (largeNormalCoefficient q) := by
  unfold largeNormalCoefficient
  fun_prop

 theorem largeNormalCoefficient_pos {q : ℕ} {h₁ h₂ : ℝ} (hh₁ : h₁<1) (hh₂ : h₂<1/2)
    {p : Fin (q+1) → ℝ} (hp : p∈region (largeModelBounds q h₂) ![h₁,h₂]) :
    0<largeNormalCoefficient q p := by
  have he := largeModelDensity_lower q hh₂.le hp
  have hpos : 0<(2:ℝ)^q*(1-h₁)*(1-2*h₂) :=
    mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)
  have hh : 0 < (2:ℝ)^q * largeNormalCoefficient q p := hpos.trans_le he
  exact (mul_pos_iff_of_pos_left (by positivity)).mp hh

 theorem largeNormalCoefficient_le_one {q : ℕ} {p : Fin (q+1) → ℝ}
    (hp : ∀ j,0≤p j) : largeNormalCoefficient q p≤1 := by
  have hs := Finset.sum_nonneg (fun j (_ : j∈(Finset.univ : Finset (Fin q))) => hp j.succ)
  unfold largeNormalCoefficient
  linarith [hp 0]

 variable {m q : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]
local instance liouvilleRadialSigmaCompact : SigmaCompactSpace (locus a) := curveSigmaCompact a

 def largeHorizontalPrimitive (p : Fin (q+1) → ℝ) : ManifoldOneForm Plane (locus a) :=
  largeNormalCoefficient q p • curveFSPrimitive a (1/Real.pi)

 theorem largeHorizontalPrimitive_smooth : SmoothOneFormFamily (largeHorizontalPrimitive (q := q) a) :=
  ((curveFSPrimitive_smooth a (1/Real.pi)).comp
    (f := fun _ : Fin (q+1) → ℝ => (0:ℝ)) contDiff_const).smul (largeNormalCoefficient_smooth q)

 theorem largeHorizontalPrimitive_exterior (p : Fin (q+1) → ℝ) (x : locus a) :
    manifoldExteriorOneForm (largeHorizontalPrimitive a p) x=
      largeNormalCoefficient q p • curveFSForm a (1/Real.pi) x := by
  have hx := (extChartAt 𝓘(ℝ,Plane) x).map_source (mem_extChartAt_source x)
  rw [largeHorizontalPrimitive,manifoldExteriorOneForm_smul_at _
    ((curveFSPrimitive_smooth a (1/Real.pi)).spatial_smooth 0 x hx),curveFSPrimitive_exterior]

 theorem largeHorizontalPrimitive_area_limit {h₁ h₂ : ℝ} (hh₁ : h₁<1) (hh₂ : h₂<1/2) :
    TendstoUniformlyOn (fun ℓ p => compactSurfaceFormIntegral
      (projectionDomain_compact a (exhaustionRadius a ℓ))
      (fun x => largeNormalCoefficient q p • curveFSForm a (1/Real.pi) x))
      (fun p => (2:ℝ)^m*largeNormalCoefficient q p) atTop
      (region (largeModelBounds q h₂) ![h₁,h₂]) := by
  simp_rw [show (fun x => largeNormalCoefficient q _ • curveFSForm a (1/Real.pi) x)=
    largeNormalCoefficient q _ • curveFSForm a (1/Real.pi) from rfl,
    compactSurfaceFormIntegral_smul]
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hm := (tendsto_normalized_exhaustion_area a).eventually
    (Metric.ball_mem_nhds _ hε)
  filter_upwards [hm] with ℓ hℓ p hp
  have hc0 := largeNormalCoefficient_pos hh₁ hh₂ hp
  have hc1 := largeNormalCoefficient_le_one hp.1
  rw [Real.dist_eq,show (2:ℝ)^m*largeNormalCoefficient q p-
    largeNormalCoefficient q p*compactSurfaceFormIntegral
      (projectionDomain_compact a (exhaustionRadius a ℓ)) (curveFSForm a (1/Real.pi)) =
    largeNormalCoefficient q p*((2:ℝ)^m-compactSurfaceFormIntegral
      (projectionDomain_compact a (exhaustionRadius a ℓ)) (curveFSForm a (1/Real.pi))) by ring,
    abs_mul,abs_of_pos hc0]
  exact (mul_le_of_le_one_left (abs_nonneg _) hc1).trans_lt
    (by simpa only [Metric.mem_ball,Real.dist_eq,abs_sub_comm] using hℓ)

namespace Explicit

 theorem actual_large_normal_packing (m : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) {a₀ : ℝ} (ha₀ : 0<a₀) (ha₁ : a₀<1)
    (hrs : ∀ i,r i<1-a₀) (hhalf : ∀ i,r i<1/2)
    (hvol : ∑ i,r i^(m+4)<1-a₀^(m+4)) :
    ∃ h₁ h₂ d₁ d₂ : ℚ, (∀ i,r i<h₁) ∧ h₁<d₁ ∧ (d₁:ℝ)<1-a₀ ∧
      (∀ i,r i<h₂) ∧ h₂<d₂ ∧ (d₂:ℝ)<1/2 ∧
      ∃ ℓ,∃ φ : Fin N → Ambient (m+4) → Surface m × PlanePhase (Fin (m+3)),
        (∀ i,FormNeighborhoodEmbedding (closedBall (m+4) (r' i))
          (fun _ => successorStandardForm (m+3))
          (globalHorizontalCoupling phaseArea
            (largeHorizontalPrimitive (q := m+2) (parameters m) ∘ planeMoments)) (φ i)) ∧
        (∀ i,MapsTo (φ i) (closedBall (m+4) (r' i))
          (interior (projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ) ×ˢ
            planeRegion (largeModelBounds (m+2) h₂) ![h₁,h₂]))) ∧
        Pairwise (fun i j => Disjoint (φ i '' closedBall (m+4) (r' i))
          (φ j '' closedBall (m+4) (r' j))) := by
  classical
  obtain ⟨h₁,h₂,d₁,d₂,τ,ε,hr₁,hhd₁,hd₁,hr₂,hhd₂,hd₂,hh₁,hh₂,hτ,hτ1,hε,
    _hcap,hconc,hmean,houter⟩ := exists_large_model_comparison_data r hr ha₀ ha₁ hrs hhalf hvol
  have hh₁1 : (h₁:ℝ)<1 := lt_trans (show (h₁:ℝ)<(d₁:ℝ) by exact_mod_cast hhd₁) (by linarith)
  have hh₂half : (h₂:ℝ)<1/2 := (show (h₂:ℝ)<d₂ by exact_mod_cast hhd₂).trans hd₂
  let bF := largeModelBounds (m+2) (h₂:ℝ)
  let cF : Fin 2 → ℝ := ![h₁,h₂]
  have hcomp : IsCompact (region bF cF) := largeModelRegion_isCompact (m+2) h₁ hh₂.le
  let K := fun ℓ => projectionDomain (parameters m) (exhaustionRadius (parameters m) ℓ)
  have hK ℓ : IsCompact (K ℓ) := projectionDomain_compact (parameters m) _
  have hKn ℓ : K ℓ⊆interior (K (ℓ+1)) := by
    apply projectionDomain_nested
    simp only [exhaustionRadius,Nat.cast_add,Nat.cast_one]
    linarith
  have hKc ℓ : IsConnected (interior (K ℓ)) :=
    projectionDomain_interior_connected (exhaustionRadius_pos (parameters m) ℓ)
      (exhaustionRadius_branch (parameters m) ℓ)
  obtain ⟨H,_hw,hclock,hpos⟩ := exists_positive_fixed_annularHandleData m
  have hsimp i p (hp : ∀ j,0≤p j) (ht : (∑ j,p j)≤r i) : p∈region bF cF :=
    largeModelRegion_contains_cap (m+2) (hr₁ i).le (hr₂ i).le (by linarith) ⟨hp,ht⟩
  have hbLe : ∀ ν j,bF ν j≤1 := by
    intro ν j
    fin_cases ν
    · exact Fin.cases (by norm_num [bF,largeModelBounds])
        (fun _ => by norm_num [bF,largeModelBounds]) j
    · exact Fin.cases (by simpa [bF,largeModelBounds] using (show (h₂:ℝ)≤1 by linarith))
        (fun _ => by norm_num [bF,largeModelBounds]) j
  have hface (i : Fin N) (p : Moments (m+3)) (hp : ∀ j,0≤p j) (ht : (∑ j,p j)≤r i) ν :
      (∑ j,bF ν j*p j)≠cF ν := by
    have hb : (∑ j,bF ν j*p j)≤r i :=
      (Finset.sum_le_sum (fun j _ => mul_le_of_le_one_left (hp j) (hbLe ν j))).trans ht
    apply ne_of_lt (hb.trans_lt ?_)
    fin_cases ν
    · exact hr₁ i
    · exact hr₂ i
  obtain ⟨ℓ,φ,hφ,hφK,hdisj⟩ := Annular.exhausted_surface_packing bF cF
    (largeModelBounds_nonneg _ hh₂.le)
    (fun ν => Fin.cases hh₁ (fun j => by fin_cases j; exact hh₂) ν) hcomp
    (largeModelDensity (m+2))
    ((continuous_const.mul (largeNormalCoefficient_smooth (m+2)).continuous).continuousOn)
    (fun p hp => mul_pos (by positivity) (largeNormalCoefficient_pos hh₁1 hh₂half hp))
    r r' hr' hrr hsimp hface hconc hmean hτ hτ1 hε houter
    K hK hKn (projectionDomain_cover (parameters m) (2+∑ j,‖parameters m j‖))
    (fun ℓ => (hKc ℓ).isPreconnected) (fun ℓ => (hKc ℓ).nonempty)
    (fun ℓ => projectionDomain_smoothBoundary (exhaustionRadius_pos (parameters m) ℓ)
      (exhaustionRadius_branch (parameters m) ℓ)) (positivePlaneTransitions (parameters m))
    H (half_pos H.width_pos) (by linarith [H.width_pos]) (by norm_num : (0:ℝ)<1/4)
    (by norm_num : (1:ℝ)/4<1/2) hpos hclock
    (curveFSForm_smooth (parameters m) (1/Real.pi)) (curveFSForm_skew (parameters m) (1/Real.pi))
    (fun c y hy => curveFSForm_positive (parameters m) (one_div_pos.mpr Real.pi_pos) c hy)
    (fun _ p => largeNormalCoefficient (m+2) p.1)
    (fun _ => (largeNormalCoefficient_smooth (m+2)).contMDiff.comp contMDiff_fst)
    (fun _ p hp _ _ => largeNormalCoefficient_pos hh₁1 hh₂half hp)
    (fun _ => largeHorizontalPrimitive (q := m+2) (parameters m))
    (fun _ => largeHorizontalPrimitive_smooth (q := m+2) (parameters m))
    (fun _ => largeHorizontalPrimitive_exterior (parameters m))
    (largeHorizontalPrimitive_area_limit (parameters m) hh₁1 hh₂half)
  exact ⟨h₁,h₂,d₁,d₂,hr₁,hhd₁,hd₁,hr₂,hhd₂,hd₂,ℓ,φ,hφ,hφK,hdisj⟩

end Explicit

end PackingSufficiencySupport.DiagonalQuadrics
end

end OAI
