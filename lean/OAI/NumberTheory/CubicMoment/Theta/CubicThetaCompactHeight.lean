import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspStrip

namespace OAI

/-! Heights of all representatives above a compact quotient set are
uniformly bounded. The arithmetic denominator bound is essential here:
a nonparabolic transformation sends height v to at most 1/v. -/
noncomputable section
open Set Filter Topology
open scoped MatrixGroups
namespace CubicFirstMoment

def cubicThetaPointHeight (p : CubicThetaPoint) : ℝ := (cubicThetaPointCoordinates p).2

lemma cubicThetaPointHeight_pos (p : CubicThetaPoint) : 0<cubicThetaPointHeight p := p.property

lemma cubicThetaPointHeight_continuous : Continuous cubicThetaPointHeight := by
  have h : Continuous cubicThetaPointCoordinates := continuous_subtype_val
  exact continuous_snd.comp h

lemma cubicThetaPointHeight_full_smul_le (g : SL(2,Eisenstein)) (p : CubicThetaPoint) :
    cubicThetaPointHeight (g • p) ≤ max (cubicThetaPointHeight p) (1/cubicThetaPointHeight p) := by
  by_cases hc : g 1 0=0
  · have hdet : g 0 0*g 1 1=1 := by
      simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using g.property
    have hu : IsUnit (g 1 1) := isUnit_iff_exists_inv'.mpr ⟨g 0 0,hdet⟩
    have hc' : cubicThetaFullComplex g 1 0=0 := congrArg (fun z : Eisenstein => (z:ℂ)) hc
    have hd' : Complex.normSq (cubicThetaFullComplex g 1 1)=1 := norm_of_isUnit hu
    change p.val.2/cubicThetaMobiusDenominator (cubicThetaFullComplex g) p.val≤_
    simp only [cubicThetaMobiusDenominator,hc',zero_mul,zero_add,hd',
      Complex.normSq_zero,add_zero,div_one]
    exact le_max_left _ _
  · have hb := cubicThetaMobius_height_product_le g hc p.property
    have hb' : cubicThetaPointHeight (g • p)≤1/cubicThetaPointHeight p :=
      (le_div_iff₀ (cubicThetaPointHeight_pos p)).mpr hb
    exact hb'.trans (le_max_right _ _)

lemma cubicThetaPointHeight_local_bound (q : CubicThetaQuotient) :
    ∃ U∈𝓝 q, ∃ C : ℝ, ∀ p : CubicThetaPoint,
      cubicThetaQuotientMap p∈U → ∀ δ : SL(2,Eisenstein), cubicThetaPointHeight (δ • p)≤C := by
  let p := cubicThetaQuotientLift q
  let e := cubicThetaCoveringChart p
  have hp : p∈e.source := cubicThetaCoveringChart_source p
  have he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap :=
    cubicThetaCoveringChart_coe p
  have heq : e p=q := by rw [he]; exact cubicThetaQuotientLift_map q
  have hq : q∈e.target := heq ▸ e.map_source hp
  have hinv : e.symm q=p := by rw [← heq]; exact e.left_inv hp
  let v := cubicThetaPointHeight p
  have hv : 0<v := cubicThetaPointHeight_pos p
  have hcont : ContinuousAt (fun r => cubicThetaPointHeight (e.symm r)) q :=
    cubicThetaPointHeight_continuous.continuousAt.comp
      (e.symm.continuousOn.continuousAt (e.open_target.mem_nhds hq))
  have hI : ∀ᶠ r in 𝓝 q, cubicThetaPointHeight (e.symm r)∈Ioo (v/2) (2*v) := by
    apply hcont.eventually
    apply Ioo_mem_nhds
    · change v/2<cubicThetaPointHeight (e.symm q)
      rw [hinv]
      change v/2<v
      linarith
    · change cubicThetaPointHeight (e.symm q)<2*v
      rw [hinv]
      change v<2*v
      linarith
  let U := {r | r∈e.target ∧ cubicThetaPointHeight (e.symm r)∈Ioo (v/2) (2*v)}
  refine ⟨U,inter_mem (e.open_target.mem_nhds hq) hI,max (2*v) (2/v),?_⟩
  intro x hx δ
  let y := e.symm (cubicThetaQuotientMap x)
  have hy : cubicThetaQuotientMap y=cubicThetaQuotientMap x := by
    have h := e.right_inv hx.1
    change e y=cubicThetaQuotientMap x at h
    rwa [he] at h
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp hy.symm
  change g.val • y=x at hg
  have hb := cubicThetaPointHeight_full_smul_le (δ*g.val) y
  rw [mul_smul,hg] at hb
  apply hb.trans
  apply max_le
  · exact hx.2.2.le.trans (le_max_left _ _)
  · have hdiv : 1/cubicThetaPointHeight y≤2/v := by
      apply (div_le_div_iff₀ (cubicThetaPointHeight_pos y) hv).mpr
      have hylow : v/2<cubicThetaPointHeight y := hx.2.1
      linarith
    exact hdiv.trans (le_max_right _ _)

theorem cubicThetaCompact_all_cusp_height_bound {K : Set CubicThetaQuotient} (hK : IsCompact K) :
    ∃ C≥0, ∀ p : CubicThetaPoint, cubicThetaQuotientMap p∈K →
      ∀ δ : SL(2,Eisenstein), cubicThetaPointHeight (δ • p)≤C := by
  classical
  choose U hU C hC using cubicThetaPointHeight_local_bound
  obtain ⟨A,_,hA⟩ := hK.elim_nhds_subcover U (fun q _ => hU q)
  refine ⟨∑ q∈A, max (C q) 0,Finset.sum_nonneg (fun q _ => le_max_right _ _),?_⟩
  intro p hp δ
  obtain ⟨q,hq,hpq⟩ := mem_iUnion₂.mp (hA hp)
  exact (hC q p hpq δ).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun r _ => le_max_right (C r) 0) hq))

theorem cubicThetaCompact_height_bound {K : Set CubicThetaQuotient} (hK : IsCompact K) :
    ∃ C≥0, ∀ p : CubicThetaPoint, cubicThetaQuotientMap p∈K → cubicThetaPointHeight p≤C := by
  obtain ⟨C,hC,h⟩ := cubicThetaCompact_all_cusp_height_bound hK
  refine ⟨C,hC,fun p hp => ?_⟩
  simpa only [one_smul] using h p hp (1:SL(2,Eisenstein))

end CubicFirstMoment

end

end OAI
