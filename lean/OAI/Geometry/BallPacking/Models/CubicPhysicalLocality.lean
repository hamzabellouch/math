import Mathlib
import OAI.Geometry.BallPacking.Models.RationalSlack

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]

theorem globalHorizontalCoupling_congr_germs (Ω : V →L[ℝ] V →L[ℝ] ℝ)
    {Γ Γ' : V → ManifoldOneForm E M} {K : Set (M × V)}
    (h : ∀ z∈K,∀ᶠ q in 𝓝 z,Γ q.2 q.1=Γ' q.2 q.1) :
    globalHorizontalCoupling Ω Γ=ᶠ[𝓝ˢ K] globalHorizontalCoupling Ω Γ' := by
  apply mem_nhdsSet_iff_forall.mpr
  intro z hz
  filter_upwards [(h z hz).eventually_nhds] with q hq
  exact globalHorizontalCoupling_congr_joint Ω hq

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope

theorem physicalParameter_fiber_lower_near {A B : ℕ} {L : ℝ} (hL : 0≤L)
    {z : BaseCurve × PlanePhase (Fin 2)}
    (hz : physicalParameter L (planeMoments z.2)∈Radial.lowerTrapezoid A B) :
    ∀ᶠ q in 𝓝 z,physicalParameter L (planeMoments q.2)∈Radial.lowerTrapezoid A B := by
  have hc : Continuous (fun q : BaseCurve × PlanePhase (Fin 2) => physicalParameter L (planeMoments q.2)) :=
    (physicalParameter_smooth L).continuous.comp (planeMoments_smooth.continuous.comp continuous_snd)
  have h0 := (hc.fst.continuousAt.eventually_lt continuousAt_const hz.2.1)
  have h1 := ((hc.fst.add hc.snd).continuousAt.eventually_lt continuousAt_const hz.2.2.2)
  filter_upwards [h0,h1] with q hq0 hq1
  exact ⟨mul_nonneg hL (planeMoments_nonneg _ 0),hq0,
    mul_nonneg hL (planeMoments_nonneg _ 1),hq1⟩

theorem physicalPrimitive_representative_fiber_germ {A B D S q : ℕ} {c L : ℝ} (hL : 0≤L)
    {bF : Fin q → Moments 2} {cF : Fin q → ℝ}
    (hPS : MapsTo (physicalParameter L) (region bF cF) (Radial.lowerTrapezoid A B))
    {ℓ : ℕ} {Γ : Moments 2 → ManifoldOneForm RealModel BaseCurve}
    (he : ∀ᶠ q in 𝓝ˢ (region bF cF ×ˢ cubicExhaustion ℓ),
      physicalParameter L q.1∈Radial.lowerTrapezoid A B →
      Γ q.1 q.2=physicalPrimitive (A := A) (B := B) D S c L q.1 q.2) :
    ∀ z∈cubicExhaustion ℓ ×ˢ planeRegion bF cF,∀ᶠ q in 𝓝 z,
      Γ (planeMoments q.2) q.1=physicalPrimitive (A := A) (B := B) D S c L (planeMoments q.2) q.1 := by
  intro z hz
  have hn := mem_nhdsSet_iff_forall.mp he (planeMoments z.2,z.1) ⟨hz.2,hz.1⟩
  have hc : Continuous (fun q : BaseCurve × PlanePhase (Fin 2) => (planeMoments q.2,q.1)) :=
    (planeMoments_smooth.continuous.comp continuous_snd).prodMk continuous_fst
  have hi := physicalParameter_fiber_lower_near (A := A) (B := B) (z := z) hL (hPS hz.2)
  filter_upwards [hc.continuousAt.eventually hn,hi] with q hq hqp
  exact hq hqp

attribute [local irreducible] physicalPrimitive

theorem physicalCoupling_representative_near {A B D S q : ℕ} {c L : ℝ} (hL : 0≤L)
    {bF : Fin q → Moments 2} {cF : Fin q → ℝ}
    (hPS : MapsTo (physicalParameter L) (region bF cF) (Radial.lowerTrapezoid A B))
    {ℓ : ℕ} {Γ : Moments 2 → ManifoldOneForm RealModel BaseCurve}
    (he : ∀ᶠ q in 𝓝ˢ (region bF cF ×ˢ cubicExhaustion ℓ),
      physicalParameter L q.1∈Radial.lowerTrapezoid A B →
      Γ q.1 q.2=physicalPrimitive (A := A) (B := B) D S c L q.1 q.2) :
    globalHorizontalCoupling (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2)) phaseArea (Γ ∘ planeMoments)=ᶠ[𝓝ˢ (cubicExhaustion ℓ ×ˢ planeRegion bF cF)]
      globalHorizontalCoupling (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2)) phaseArea (physicalPrimitive (A := A) (B := B) D S c L ∘ planeMoments) := by
  have hg : ∀ z∈cubicExhaustion ℓ ×ˢ planeRegion bF cF,∀ᶠ q in 𝓝 z,
      Γ (planeMoments q.2) q.1=physicalPrimitive (A := A) (B := B) D S c L (planeMoments q.2) q.1 :=
    physicalPrimitive_representative_fiber_germ hL hPS he
  exact globalHorizontalCoupling_congr_germs (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2)) phaseArea (Γ := Γ ∘ planeMoments)
    (Γ' := physicalPrimitive (A := A) (B := B) D S c L ∘ planeMoments) hg

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport
open scoped BigOperators
open MeasureTheory Set
open scoped Pointwise
open MomentPolytope

 theorem exists_positive_common_denominator {ι : Type*} [Fintype ι]
    (q : ι → ℚ) (hq : ∀ i,0≤q i) :
    ∃ L : ℕ,0<L ∧ ∃ k : ι → ℕ,∀ i,(k i:ℝ)=(L:ℝ)*(q i:ℝ) := by
  classical
  let L := ∏ i,(q i).den
  have hL : 0<L := Finset.prod_pos (fun i _ => (q i).den_pos)
  have hd i : (q i).den∣L := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hn i : 0≤(q i).num := Rat.num_nonneg.mpr (hq i)
  let k := fun i => (q i).num.toNat*(L/(q i).den)
  refine ⟨L,hL,k,fun i => ?_⟩
  have hc : ((q i).num.toNat:ℝ)=((q i).num:ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (hn i)
  have hmul : ((L/(q i).den:ℕ):ℝ)*((q i).den:ℝ)=(L:ℝ) := by
    exact_mod_cast Nat.div_mul_cancel (hd i)
  have hd0 : ((q i).den:ℝ)≠0 := by exact_mod_cast (q i).den_ne_zero
  dsimp only [k]
  rw [Nat.cast_mul,hc,Rat.cast_def]
  field_simp
  nlinarith [hmul]

def truncatedSimplex (q : ℕ) (h b : ℝ) : Set (ℝ × (Fin q → ℝ)) :=
  {x | x.1 ∈ Icc 0 h ∧ x.2 ∈ momentSimplex q (b-x.1)}

theorem truncatedSimplex_isClosed (q : ℕ) (h b : ℝ) :
    IsClosed (truncatedSimplex q h b) := by
  have hn : IsClosed {x : ℝ × (Fin q → ℝ) | ∀ i,0≤x.2 i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const ((continuous_apply i).comp continuous_snd)
  exact (isClosed_Icc.preimage continuous_fst).inter (hn.inter
    (isClosed_le (continuous_finsetSum _ fun i _ => (continuous_apply i).comp continuous_snd)
      (continuous_const.sub continuous_fst)))

theorem truncatedSimplex_isCompact (q : ℕ) (h b : ℝ) :
    IsCompact (truncatedSimplex q h b) := by
  refine (isCompact_Icc (a := (0,fun _ : Fin q => (0:ℝ)))
    (b := (h,fun _ => b))).of_isClosed_subset (truncatedSimplex_isClosed q h b) ?_
  intro x hx
  refine ⟨⟨hx.1.1,hx.2.1⟩,hx.1.2,fun i => ?_⟩
  have hi := (Finset.single_le_sum (fun j _ => hx.2.1 j) (Finset.mem_univ i)).trans hx.2.2
  linarith [hx.1.1]

theorem truncatedSimplex_fubini (q : ℕ) (h b : ℝ)
    (f : ℝ×(Fin q → ℝ) → ℝ) (hf : ContinuousOn f (truncatedSimplex q h b)) :
    (∫ x in truncatedSimplex q h b, f x) =
      ∫ u in Icc 0 h, ∫ p in momentSimplex q (b-u), f (u,p) := by
  let D := truncatedSimplex q h b
  have hD := (truncatedSimplex_isClosed q h b).measurableSet
  have hi : Integrable (D.indicator f) := (integrable_indicator_iff hD).2
    (hf.integrableOn_compact (truncatedSimplex_isCompact q h b))
  rw [←integral_indicator hD]
  change (∫ x, D.indicator f x ∂(volume.prod volume)) = _
  rw [integral_prod _ hi,←integral_indicator measurableSet_Icc]
  congr 1
  funext u
  by_cases hu : u∈Icc 0 h
  · rw [indicator_of_mem hu,←integral_indicator (momentSimplex_isClosed q (b-u)).measurableSet]
    congr 1
    funext p
    by_cases hp : p∈momentSimplex q (b-u)
    · rw [indicator_of_mem (show (u,p)∈D from ⟨hu,hp⟩),indicator_of_mem hp]
    · rw [indicator_of_notMem (show (u,p)∉D from fun hx => hp hx.2),indicator_of_notMem hp]
  · rw [indicator_of_notMem hu]
    have hz (p : Fin q → ℝ) : D.indicator f (u,p)=0 :=
      indicator_of_notMem (show (u,p)∉D from fun hx => hu hx.1) f
    simp_rw [hz]
    exact integral_zero _ _

theorem integral_truncated_simplex_power (q k : ℕ) {h b : ℝ} (hh : 0≤h) (hhb : h≤b) :
    (∫ x in truncatedSimplex q h b, (b-x.1-∑ i,x.2 i)^k) =
      (k.factorial : ℝ)/((q+k+1).factorial : ℝ)*
        (b^(q+k+1)-(b-h)^(q+k+1)) := by
  rw [truncatedSimplex_fubini q h b _ (by fun_prop)]
  have heq : (∫ u in Icc 0 h, ∫ p in momentSimplex q (b-u), (b-u-∑ i,p i)^k) =
      ∫ u in Icc 0 h, (k.factorial : ℝ)/((q+k).factorial : ℝ)*(b-u)^(q+k) := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    exact integral_simplex_power q k (by linarith [hu.2])
  rw [heq,integral_const_mul,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le hh,
    intervalIntegral.integral_comp_sub_left (fun u : ℝ => u^(q+k)) b,
    sub_zero,integral_pow]
  rw [Nat.factorial_succ (q+k),Nat.cast_mul]
  simp only [Nat.cast_add,Nat.cast_one,div_eq_mul_inv,mul_inv_rev]
  ring

theorem volumeReal_truncatedSimplex (q : ℕ) {h b : ℝ} (hh : 0≤h) (hhb : h≤b) :
    volume.real (truncatedSimplex q h b) =
      (b^(q+1)-(b-h)^(q+1))/((q+1).factorial : ℝ) := by
  simpa [div_eq_mul_inv,mul_comm] using integral_truncated_simplex_power q 0 hh hhb

theorem integral_truncated_tent (q : ℕ) {h b : ℝ} (hh : 0≤h) (hhb : h≤b) :
    (∫ x in truncatedSimplex q h b, b-x.1-∑ i,x.2 i) =
      (b^(q+2)-(b-h)^(q+2))/((q+2).factorial : ℝ) := by
  simpa [div_eq_mul_inv,mul_comm] using integral_truncated_simplex_power q 1 hh hhb

theorem integral_truncated_cap (q : ℕ) {h s b : ℝ}
    (hh : 0 ≤ h) (hhs : h ≤ s) (hsb : s ≤ b) :
    (∫ x in truncatedSimplex q h b, max (s-x.1-∑ i,x.2 i) 0) =
      (s^(q+2)-(s-h)^(q+2))/((q+2).factorial : ℝ) := by
  rw [←integral_truncated_tent q hh hhs,
    ←integral_indicator (truncatedSimplex_isClosed q h b).measurableSet,
    ←integral_indicator (truncatedSimplex_isClosed q h s).measurableSet]
  congr 1
  funext x
  by_cases hb : x∈truncatedSimplex q h b
  · rw [indicator_of_mem hb]
    by_cases hs : x∈truncatedSimplex q h s
    · rw [indicator_of_mem hs,max_eq_left]
      linarith [hs.2.2]
    · rw [indicator_of_notMem hs,max_eq_right]
      have hn : ¬ (∑ i,x.2 i) ≤ s-x.1 := fun he => hs ⟨hb.1,hb.2.1,he⟩
      linarith [not_le.1 hn]
  · rw [indicator_of_notMem hb,indicator_of_notMem]
    intro hs
    apply hb
    exact ⟨hs.1,hs.2.1,hs.2.2.trans (by linarith)⟩

theorem integral_truncated_affine {h b d : ℝ} (hh : 0 ≤ h) (hhd : h ≤ d) :
    (∫ x in truncatedSimplex 1 h d, b-x.1-∑ i,x.2 i) =
      (b-d)*(d^2-(d-h)^2)/2+(d^3-(d-h)^3)/6 := by
  have ht : IntegrableOn (fun x : ℝ×(Fin 1→ℝ) => d-x.1-∑ i,x.2 i)
      (truncatedSimplex 1 h d) := by
    apply ContinuousOn.integrableOn_compact (truncatedSimplex_isCompact 1 h d)
    fun_prop
  have hc : IntegrableOn (fun _ : ℝ×(Fin 1→ℝ) => b-d) (truncatedSimplex 1 h d) :=
    continuousOn_const.integrableOn_compact (truncatedSimplex_isCompact 1 h d)
  have heq (x : ℝ×(Fin 1→ℝ)) : b-x.1-∑ i,x.2 i = (b-d)+(d-x.1-∑ i,x.2 i) := by ring
  simp_rw [heq]
  rw [integral_add hc ht,setIntegral_const,integral_truncated_tent 1 hh hhd]
  simp only [smul_eq_mul,volumeReal_truncatedSimplex 1 hh hhd]
  norm_num
  ring

def sixModelMean (s b h₁ h₂ : ℝ) : ℝ :=
  (3/2)*(b^3-(b-h₁)^3) -(9/2)*h₁*(b-h₂)^2 -(1/3)*(s^3-(s-h₁)^3)

theorem integral_six_model {s b h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hhs : h₁ ≤ s) (hsh : s ≤ h₂) :
    (∫ x in truncatedSimplex 1 h₁ h₂,
      9*(b-x.1-∑ i,x.2 i)-2*max (s-x.1-∑ i,x.2 i) 0) =
      sixModelMean s b h₁ h₂ := by
  have hi (f : ℝ×(Fin 1→ℝ) → ℝ) (hf : Continuous f) :
      IntegrableOn f (truncatedSimplex 1 h₁ h₂) :=
    hf.continuousOn.integrableOn_compact (truncatedSimplex_isCompact 1 h₁ h₂)
  rw [integral_sub (hi _ (by fun_prop)) (hi _ (by fun_prop)),
    integral_const_mul,integral_const_mul,
    integral_truncated_affine hh₁ (hhs.trans hsh),
    integral_truncated_cap 1 hh₁ hhs hsh]
  norm_num [sixModelMean]
  ring

theorem continuous_sixModelMean (s b : ℝ) :
    Continuous (fun h : ℝ×ℝ => sixModelMean s b h.1 h.2) := by
  unfold sixModelMean
  fun_prop

theorem sixModelMean_limit_value (a : ℝ) :
    sixModelMean (1-a) ((2-a)/3) (1-a) ((2-a)/3) = (1-a^3)/6 := by
  unfold sixModelMean
  ring

def momentHeadTail (q : ℕ) : (Fin (q+1) → ℝ) ≃ᵐ (ℝ×(Fin q → ℝ)) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (q+1) => ℝ) 0

@[simp] theorem momentHeadTail_apply (q : ℕ) (p : Fin (q+1) → ℝ) :
    momentHeadTail q p=(p 0,fun i => p i.succ) := by
  rfl

@[simp] theorem momentHeadTail_symm_apply (q : ℕ) (x : ℝ×(Fin q → ℝ)) :
    (momentHeadTail q).symm x=Fin.cons x.1 x.2 := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [momentHeadTail,MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]

theorem continuous_momentHeadTail (q : ℕ) : Continuous (momentHeadTail q) := by
  change Continuous (fun p : Fin (q+1) → ℝ => (p 0,fun i : Fin q => p i.succ))
  fun_prop

theorem continuous_momentHeadTail_symm (q : ℕ) : Continuous (momentHeadTail q).symm := by
  change Continuous (fun x : ℝ×(Fin q → ℝ) => (momentHeadTail q).symm x)
  simp_rw [momentHeadTail_symm_apply]
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Fin.cons_zero,Fin.cons_succ] <;> fun_prop

theorem isCompact_preimage_momentHeadTail (q : ℕ) {D : Set (ℝ×(Fin q → ℝ))}
    (hD : IsCompact D) : IsCompact ((momentHeadTail q) ⁻¹' D) := by
  have he : (momentHeadTail q) ⁻¹' D = (momentHeadTail q).symm '' D := by
    ext p
    constructor
    · intro hp
      exact ⟨momentHeadTail q p,hp,(momentHeadTail q).symm_apply_apply p⟩
    · rintro ⟨x,hx,rfl⟩
      simpa using hx
  rw [he]
  exact hD.image (continuous_momentHeadTail_symm q)

theorem integral_momentHeadTail (q : ℕ) {D : Set (ℝ×(Fin q → ℝ))}
    (hD : MeasurableSet D) (f : ℝ×(Fin q → ℝ) → ℝ) :
    (∫ p in (momentHeadTail q) ⁻¹' D, f (momentHeadTail q p)) = ∫ x in D,f x := by
  let e := momentHeadTail q
  have he : MeasurePreserving e := volume_preserving_piFinSuccAbove (fun _ : Fin (q+1) => ℝ) 0
  rw [←integral_indicator (hD.preimage e.measurable),←integral_indicator hD]
  have hf : (e ⁻¹' D).indicator (fun p => f (e p)) = (D.indicator f) ∘ e := by
    funext p
    by_cases hp : e p∈D <;> simp [hp]
  rw [hf]
  exact he.integral_comp e.measurableEmbedding _

def sixModelBounds : Fin 2 → Moments 2 := ![![1,0],![1,1]]

theorem sixModelBounds_nonneg : ∀ ν j,0 ≤ sixModelBounds ν j := by
  intro ν j
  fin_cases ν <;> fin_cases j <;> norm_num [sixModelBounds]

theorem sixModelBounds_le_one : ∀ ν j,sixModelBounds ν j ≤ 1 := by
  intro ν j
  fin_cases ν <;> fin_cases j <;> norm_num [sixModelBounds]

theorem sixModelRegion_eq (h₁ h₂ : ℝ) :
    region sixModelBounds ![h₁,h₂] = (momentHeadTail 1) ⁻¹' truncatedSimplex 1 h₁ h₂ := by
  ext p
  change ((∀ j,0≤p j) ∧ ∀ ν,∑ j,sixModelBounds ν j*p j ≤ ![h₁,h₂] ν) ↔
    (p 0∈Icc 0 h₁ ∧ (fun j : Fin 1 => p j.succ)∈momentSimplex 1 (h₂-p 0))
  simp only [Fin.forall_fin_two,Fin.sum_univ_two,Fin.sum_univ_one,
    sixModelBounds,Matrix.cons_val_zero,Matrix.cons_val_one,momentSimplex,
    mem_ofPred_eq,Fin.forall_fin_one,mem_Icc,one_mul,zero_mul,add_zero]
  norm_num only [Fin.succ_zero_eq_one]
  constructor
  · rintro ⟨⟨h0,h1⟩,hh₁,hh₂⟩
    exact ⟨⟨h0,hh₁⟩,h1,by linarith⟩
  · rintro ⟨⟨h0,hh₁⟩,h1,hh₂⟩
    exact ⟨⟨h0,h1⟩,hh₁,by linarith⟩

theorem sixModelRegion_isCompact (h₁ h₂ : ℝ) :
    IsCompact (region sixModelBounds ![h₁,h₂]) := by
  rw [sixModelRegion_eq]
  exact isCompact_preimage_momentHeadTail 1 (truncatedSimplex_isCompact 1 h₁ h₂)

theorem sixModelRegion_contains_cap {r h₁ h₂ : ℝ} (hr₁ : r ≤ h₁) (hr₂ : r ≤ h₂) :
    momentSimplex 2 r ⊆ region sixModelBounds ![h₁,h₂] := by
  intro p hp
  refine ⟨hp.1,fun ν => ?_⟩
  fin_cases ν
  · change (∑ j,(![1,0] : Fin 2→ℝ) j*p j) ≤ h₁
    simp only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,one_mul,zero_mul,add_zero]
    have hs : p 0+p 1 ≤ r := by simpa only [Fin.sum_univ_two] using hp.2
    linarith [hp.1 1]
  · change (∑ j,(![1,1] : Fin 2→ℝ) j*p j) ≤ h₂
    simpa only [Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,one_mul] using hp.2.trans hr₂

def sixModelDensity (s b : ℝ) (p : Moments 2) : ℝ :=
  9*(b-∑ j,p j)-2*max (s-∑ j,p j) 0

def sixModelGap {ι : Type*} [Fintype ι] (s b : ℝ) (r : ι → ℝ) (p : Moments 2) : ℝ :=
  sixModelDensity s b p-∑ i,max (r i-∑ j,p j) 0

theorem continuous_sixModelGap {ι : Type*} [Fintype ι] (s b : ℝ) (r : ι → ℝ) :
    Continuous (sixModelGap s b r) := by
  unfold sixModelGap sixModelDensity
  fun_prop

theorem sixModelGap_eq_cappedAffine {ι : Type*} [Fintype ι] (s b : ℝ) (r : ι → ℝ) :
    sixModelGap s b r = cappedAffine (9*b) (fun _ => 9)
      (Sum.elim (fun _ : Unit => s) r) (Sum.elim (fun _ : Unit => 2) (fun _ => 1)) := by
  funext p
  simp only [sixModelGap,sixModelDensity,cappedAffine,Fintype.sum_sum_type,
    Sum.elim_inl,Sum.elim_inr,Fintype.sum_unique,one_mul,←Finset.mul_sum]
  ring

theorem integral_sixModelDensity {s b h₁ h₂ : ℝ}
    (hh₁ : 0 ≤ h₁) (hhs : h₁ ≤ s) (hsh : s ≤ h₂) :
    (∫ p in region sixModelBounds ![h₁,h₂],sixModelDensity s b p) = sixModelMean s b h₁ h₂ := by
  rw [sixModelRegion_eq]
  have he : sixModelDensity s b = (fun x : ℝ×(Fin 1→ℝ) =>
      9*(b-x.1-∑ j,x.2 j)-2*max (s-x.1-∑ j,x.2 j) 0) ∘ momentHeadTail 1 := by
    funext p
    simp only [sixModelDensity,Fin.sum_univ_succ,Function.comp_apply,momentHeadTail_apply]
    congr 2 <;> ring_nf
  rw [he]
  simp only [Function.comp_apply]
  rw [integral_momentHeadTail 1 (truncatedSimplex_isClosed 1 h₁ h₂).measurableSet
    (fun x : ℝ×(Fin 1→ℝ) => 9*(b-x.1-∑ j,x.2 j)-2*max (s-x.1-∑ j,x.2 j) 0)]
  exact integral_six_model hh₁ hhs hsh

theorem integral_sixModelGap {ι : Type*} [Fintype ι] (r : ι → ℝ) (hr : ∀ i,0 ≤ r i)
    {s b h₁ h₂ : ℝ} (hh₁ : 0 ≤ h₁) (hhs : h₁ ≤ s) (hsh : s ≤ h₂)
    (hr₁ : ∀ i,r i ≤ h₁) (hr₂ : ∀ i,r i ≤ h₂) :
    (∫ p in region sixModelBounds ![h₁,h₂],sixModelGap s b r p) =
      sixModelMean s b h₁ h₂-(∑ i,r i^3)/6 := by
  have hC := sixModelRegion_isCompact h₁ h₂
  have hcap (i : ι) := sixModelRegion_contains_cap (hr₁ i) (hr₂ i)
  unfold sixModelGap
  rw [integral_sub]
  · rw [integral_sixModelDensity hh₁ hhs hsh,
      integral_sum_tents r hr hC.measurableSet (fun _ hp => hp.1) hcap]
    norm_num
  · apply ContinuousOn.integrableOn_compact hC
    unfold sixModelDensity
    fun_prop
  · apply ContinuousOn.integrableOn_compact hC
    fun_prop

theorem sixModelDensity_lower {s b h₁ h₂ : ℝ} (hsh : s ≤ h₂)
    {p : Moments 2} (hp : p ∈ region sixModelBounds ![h₁,h₂]) :
    9*(b-h₂) ≤ sixModelDensity s b p := by
  have hs : (∑ j,p j) ≤ h₂ := by
    have ht := hp.2 1
    simpa [sixModelBounds,Fin.sum_univ_two] using ht
  have hm : max (s-∑ j,p j) 0 ≤ h₂-∑ j,p j := max_le (by linarith) (by linarith)
  unfold sixModelDensity
  linarith

end PackingSufficiencySupport

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators
open Set Function
open MomentPolytope FiniteMoment

 theorem physicalArea_eq_sixModelDensity {L D S : ℕ} (hL : 0<L) {a : ℝ}
    (hD : (D:ℝ)=(L:ℝ)*(2-a)) (hS : (S:ℝ)=(L:ℝ)*(1-a)) :
    physicalArea D S (1/((L:ℝ)*Real.pi)) L=sixModelDensity (1-a) ((2-a)/3) := by
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  funext p
  unfold physicalArea sixModelDensity
  rw [hD,hS,Fin.sum_univ_two]
  have he : (L:ℝ)*(1-a)-((L:ℝ)*p 0+(L:ℝ)*p 1)=(L:ℝ)*((1-a)-(p 0+p 1)) := by ring
  rw [he]
  have hm : max ((L:ℝ)*((1-a)-(p 0+p 1))) 0 = (L:ℝ)*max ((1-a)-(p 0+p 1)) 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg ((1-a)-(p 0+p 1)) 0 hLr.le).symm
  rw [hm]
  field_simp [hLr.ne',Real.pi_ne_zero]
  ring

 theorem exists_six_cubic_weights {a d₁ d₂ : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hd₁ : 1-a<d₁) (hdd : d₁<d₂) (hd₂ : d₂<(2-a)/3) :
    ∃ L A B D S : ℕ,0<L ∧ 0<A ∧ 0<S ∧ A≤B ∧ S≤B ∧ 3*B<D ∧ 3*S<D ∧
      (A:ℝ)=(L:ℝ)*(d₁:ℝ) ∧ (B:ℝ)=(L:ℝ)*(d₂:ℝ) ∧
      (D:ℝ)=(L:ℝ)*(2-(a:ℝ)) ∧ (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) := by
  let q : Fin 4 → ℚ := ![1-a,2-a,d₁,d₂]
  have hq : ∀ i,0≤q i := by
    intro i
    fin_cases i <;> dsimp [q] <;> linarith
  obtain ⟨L,hL,k,hk⟩ := exists_positive_common_denominator q hq
  have hS : (k 0:ℝ)=(L:ℝ)*(1-(a:ℝ)) := by simpa [q] using hk 0
  have hD : (k 1:ℝ)=(L:ℝ)*(2-(a:ℝ)) := by simpa [q] using hk 1
  have hA : (k 2:ℝ)=(L:ℝ)*(d₁:ℝ) := by simpa [q] using hk 2
  have hB : (k 3:ℝ)=(L:ℝ)*(d₂:ℝ) := by simpa [q] using hk 3
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  have ha' : (1:ℝ)/2<(a:ℝ) := by
    have hh : (((1:ℚ)/2:ℚ):ℝ)<(a:ℝ) := Rat.cast_lt.mpr ha
    norm_num at hh ⊢
    exact hh
  have ha1' : (a:ℝ)<1 := by exact_mod_cast ha1
  have hd₁' : 1-(a:ℝ)<d₁ := by exact_mod_cast hd₁
  have hdd' : (d₁:ℝ)<d₂ := by exact_mod_cast hdd
  have hd₂' : (d₂:ℝ)<(2-(a:ℝ))/3 := by exact_mod_cast hd₂
  refine ⟨L,k 2,k 3,k 1,k 0,hL,?_,?_,?_,?_,?_,?_,hA,hB,hD,hS⟩
  · apply (Nat.cast_pos (α := ℝ)).mp
    rw [hA]
    exact mul_pos hLr (by linarith)
  · apply (Nat.cast_pos (α := ℝ)).mp
    rw [hS]
    exact mul_pos hLr (by linarith)
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [hA,hB]
    exact mul_le_mul_of_nonneg_left hdd'.le hLr.le
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [hS,hB]
    exact mul_le_mul_of_nonneg_left (by linarith) hLr.le
  · have hm := mul_lt_mul_of_pos_left (show 3*(d₂:ℝ)<2-(a:ℝ) by linarith) hLr
    have hp : 3*(k 3:ℝ)<(k 1:ℝ) := by rw [hB,hD]; nlinarith
    exact_mod_cast hp
  · have hm := mul_lt_mul_of_pos_left (show 3*(1-(a:ℝ))<2-(a:ℝ) by linarith) hLr
    have hp : 3*(k 0:ℝ)<(k 1:ℝ) := by rw [hS,hD]; nlinarith
    exact_mod_cast hp

 theorem physicalParameter_maps_six_region {L A B : ℕ} (hL : 0<L)
    {h₁ h₂ d₁ d₂ : ℝ} (hhd₁ : h₁<d₁) (hhd₂ : h₂<d₂)
    (hA : (A:ℝ)=(L:ℝ)*d₁) (hB : (B:ℝ)=(L:ℝ)*d₂) :
    MapsTo (physicalParameter L) (region sixModelBounds ![h₁,h₂]) (Radial.lowerTrapezoid A B) := by
  intro p hp
  have hn := hp.1
  have hp0 : p 0≤h₁ := by
    simpa [sixModelBounds,Fin.sum_univ_two] using hp.2 0
  have hpt : p 0+p 1≤h₂ := by
    simpa [sixModelBounds,Fin.sum_univ_two] using hp.2 1
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  refine ⟨mul_nonneg hLr.le (hn 0),?_,mul_nonneg hLr.le (hn 1),?_⟩
  · change (L:ℝ)*p 0<(A:ℝ)
    rw [hA]
    exact mul_lt_mul_of_pos_left (hp0.trans_lt hhd₁) hLr
  · change (L:ℝ)*p 0+(L:ℝ)*p 1<(B:ℝ)
    rw [hB,← mul_add]
    exact mul_lt_mul_of_pos_left (hpt.trans_lt hhd₂) hLr

 theorem exists_six_cubic_inner_weights {a d₁ d₂ : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hd₁0 : 0<d₁) (hd₁ : d₁<1-a) (hd₂s : 1-a<d₂) (hd₂ : d₂<(2-a)/3) :
    ∃ L A B D S : ℕ,0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<D ∧ 3*S<D ∧
      (A:ℝ)=(L:ℝ)*(d₁:ℝ) ∧ (B:ℝ)=(L:ℝ)*(d₂:ℝ) ∧
      (D:ℝ)=(L:ℝ)*(2-(a:ℝ)) ∧ (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) := by
  let q : Fin 4 → ℚ := ![1-a,2-a,d₁,d₂]
  have hq : ∀ i,0≤q i := by
    intro i
    fin_cases i <;> dsimp [q] <;> linarith
  obtain ⟨L,hL,k,hk⟩ := exists_positive_common_denominator q hq
  have hS : (k 0:ℝ)=(L:ℝ)*(1-(a:ℝ)) := by simpa [q] using hk 0
  have hD : (k 1:ℝ)=(L:ℝ)*(2-(a:ℝ)) := by simpa [q] using hk 1
  have hA : (k 2:ℝ)=(L:ℝ)*(d₁:ℝ) := by simpa [q] using hk 2
  have hB : (k 3:ℝ)=(L:ℝ)*(d₂:ℝ) := by simpa [q] using hk 3
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  have ha' : (1:ℝ)/2<(a:ℝ) := by
    have hh : (((1:ℚ)/2:ℚ):ℝ)<(a:ℝ) := Rat.cast_lt.mpr ha
    norm_num at hh ⊢
    exact hh
  have ha1' : (a:ℝ)<1 := by exact_mod_cast ha1
  have hd₁0' : 0<(d₁:ℝ) := by exact_mod_cast hd₁0
  have hd₁' : (d₁:ℝ)<1-(a:ℝ) := by exact_mod_cast hd₁
  have hd₂s' : 1-(a:ℝ)<d₂ := by exact_mod_cast hd₂s
  have hdd' : (d₁:ℝ)<d₂ := hd₁'.trans hd₂s'
  have hd₂' : (d₂:ℝ)<(2-(a:ℝ))/3 := by exact_mod_cast hd₂
  refine ⟨L,k 2,k 3,k 1,k 0,hL,?_,?_,?_,?_,?_,?_,?_,hA,hB,hD,hS⟩
  · apply (Nat.cast_pos (α := ℝ)).mp
    rw [hA]
    exact mul_pos hLr (by linarith)
  · apply (Nat.cast_pos (α := ℝ)).mp
    rw [hS]
    exact mul_pos hLr (by linarith)
  · apply (Nat.cast_lt (α := ℝ)).mp
    rw [hA,hS]
    exact mul_lt_mul_of_pos_left hd₁' hLr
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [hA,hB]
    exact mul_le_mul_of_nonneg_left hdd'.le hLr.le
  · apply (Nat.cast_le (α := ℝ)).mp
    rw [hS,hB]
    exact mul_le_mul_of_nonneg_left (by linarith) hLr.le
  · have hm := mul_lt_mul_of_pos_left (show 3*(d₂:ℝ)<2-(a:ℝ) by linarith) hLr
    have hp : 3*(k 3:ℝ)<(k 1:ℝ) := by rw [hB,hD]; nlinarith
    exact_mod_cast hp
  · have hm := mul_lt_mul_of_pos_left (show 3*(1-(a:ℝ))<2-(a:ℝ) by linarith) hLr
    have hp : 3*(k 0:ℝ)<(k 1:ℝ) := by rw [hS,hD]; nlinarith
    exact_mod_cast hp

 theorem exists_six_cubic_inner_weights_large (Q : ℕ) {a d₁ d₂ : ℚ}
    (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hd₁0 : 0<d₁) (hd₁ : d₁<1-a) (hd₂s : 1-a<d₂) (hd₂ : d₂<(2-a)/3) :
    ∃ L A B D S : ℕ,Q<L ∧ 0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<D ∧ 3*S<D ∧
      (A:ℝ)=(L:ℝ)*(d₁:ℝ) ∧ (B:ℝ)=(L:ℝ)*(d₂:ℝ) ∧
      (D:ℝ)=(L:ℝ)*(2-(a:ℝ)) ∧ (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) := by
   obtain ⟨L,A,B,D,S,hL,hA,hS,hAS,hAB,hSB,hBD,hSD,heA,heB,heD,heS⟩ :=
     exists_six_cubic_inner_weights ha ha1 hd₁0 hd₁ hd₂s hd₂
   let M := Q+1
   have hM : 0<M := by dsimp [M]; omega
   refine ⟨M*L,M*A,M*B,M*D,M*S,?_,Nat.mul_pos hM hL,Nat.mul_pos hM hA,
     Nat.mul_pos hM hS,Nat.mul_lt_mul_of_pos_left hAS hM,
     Nat.mul_le_mul_left M hAB,Nat.mul_le_mul_left M hSB,?_,?_,?_,?_,?_,?_⟩
   · have hh := Nat.mul_le_mul_left M (show 1≤L by omega)
     dsimp [M] at hh ⊢
     nlinarith
   · nlinarith [Nat.mul_lt_mul_of_pos_left hBD hM]
   · nlinarith [Nat.mul_lt_mul_of_pos_left hSD hM]
   · push_cast
     rw [heA]
     ring
   · push_cast
     rw [heB]
     ring
   · push_cast
     rw [heD]
     ring
   · push_cast
     rw [heS]
     ring
end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport
open Set
open scoped BigOperators Pointwise
open MomentPolytope

theorem rational_truncation_pair (F : ℝ×ℝ → ℝ) (hF : Continuous F)
    {s₁ s₂ l₁ l₂ c : ℝ} (hl₁ : l₁<s₁) (hl₂ : l₂<s₂) (hc : c<F (s₁,s₂)) :
    ∃ h₁ h₂ d₁ d₂ : ℚ,
      l₁<h₁ ∧ h₁<d₁ ∧ (d₁:ℝ)<s₁ ∧
      l₂<h₂ ∧ h₂<d₂ ∧ (d₂:ℝ)<s₂ ∧ c<F (h₁,h₂) := by
  let U : Set (Fin 2 → ℝ) := {p | l₁<p 0 ∧ l₂<p 1 ∧ c<F (p 0,p 1)}
  have hU : IsOpen U := (isOpen_lt continuous_const (continuous_apply 0)).inter
    ((isOpen_lt continuous_const (continuous_apply 1)).inter
      (isOpen_lt continuous_const (hF.comp ((continuous_apply 0).prodMk (continuous_apply 1)))))
  let r : Fin 2 → ℝ := ![s₁,s₂]
  have hr : r∈U := ⟨hl₁,hl₂,hc⟩
  obtain ⟨h,hh,hU⟩ := exists_rational_below_in_open hU hr
  obtain ⟨d₁,hd₁,hd₁s⟩ := exists_rat_btwn (hh 0)
  obtain ⟨d₂,hd₂,hd₂s⟩ := exists_rat_btwn (hh 1)
  exact ⟨h 0,h 1,d₁,d₂,hU.1,by exact_mod_cast hd₁,hd₁s,
    hU.2.1,by exact_mod_cast hd₂,hd₂s,hU.2.2⟩

theorem cap_into_scaled_region {m N : ℕ} (b : Fin N → Moments m) (c : Fin N → ℝ)
    (hb : ∀ ν j,b ν j ≤ 1) {τ r : ℝ} (hτ : 0 < τ)
    (hr : ∀ ν,r ≤ τ*c ν) : momentSimplex m r ⊆ τ • region b c := by
  intro p hp
  let q := τ⁻¹ • p
  have hq (j : Fin m) : 0 ≤ q j := mul_nonneg (inv_nonneg.2 hτ.le) (hp.1 j)
  have hsum : (∑ j,q j) ≤ τ⁻¹*r := by
    simpa only [q,Pi.smul_apply,smul_eq_mul,←Finset.mul_sum] using
      mul_le_mul_of_nonneg_left hp.2 (inv_nonneg.2 hτ.le)
  refine ⟨q,⟨hq,fun ν => ?_⟩,?_⟩
  · have hweighted : (∑ j,b ν j*q j) ≤ ∑ j,q j := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb ν j) (hq j)
    have hc : τ⁻¹*r ≤ c ν := by
      have ht := mul_le_mul_of_nonneg_left (hr ν) (inv_nonneg.2 hτ.le)
      simpa only [←mul_assoc,inv_mul_cancel₀ hτ.ne',one_mul] using ht
    exact hweighted.trans (hsum.trans hc)
  · simp [q,smul_smul,hτ.ne']

theorem sum_caps_zero_outside {m : ℕ} {ι : Type*} [Fintype ι]
    (r : ι → ℝ) {D A : Set (Fin m → ℝ)}
    (hD : ∀ p ∈ D,∀ j,0 ≤ p j) (hcap : ∀ i,momentSimplex m (r i) ⊆ A)
    {p : Fin m → ℝ} (hp : p ∈ D) (hout : p ∉ A) :
    (∑ i,max (r i-∑ j,p j) 0)=0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply max_eq_right
  have hn : ¬ (∑ j,p j) ≤ r i := fun he => hout (hcap i ⟨hD p hp,he⟩)
  linarith [not_le.1 hn]

end PackingSufficiencySupport
end

end OAI
