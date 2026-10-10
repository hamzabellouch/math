import Mathlib
import OAI.Analysis.HardSphere.Allocation.CertificateSupply

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener PathCutoff CellOrbital BathSlice HardSphere.Lattice

theorem ground_certificate_supply_ge_two :
    ∃ α₀ ell : ℝ, 2≤α₀ ∧ 0<ell ∧ ∀ θ : ℝ, 0<θ →
    ∃ b H t₀ : ℝ, 0<b ∧ b≤1/4 ∧ 0<H ∧ 0<t₀ ∧
    ∀ p : ℝ, 0<p → p≤1 → ∀ t : ℝ, 0<t → t≤t₀ →
    ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] [NeZero K] (L : Length), L.val=(K:ℝ) →
    ∀ D α : ℝ, 100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → α₀/2≤α → α≤2*α₀ →
    ∃ (hD : 0<D) (hh : D⁻¹<2*t), ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ A : Finset (Fin 3→Fin K),
      groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈A,
        ¬Certificate (sourceMesh t (α/D)) (α/D) (D^(1/12:ℝ)) (meanCost+1)
          (spatialCloseScale D b/8) (spatialCloseScale D b) ell θ H D
          (splitTime D⁻¹ (2*t-D⁻¹) (inv_pos.mpr hD) (sub_pos.mpr hh)) v ω}≤
        (6*ENNReal.ofReal p)^A.card := by
  classical
  obtain ⟨αE,hαE,hex⟩ := ShiftVisits.ground_excessVisitors_tail
  obtain ⟨αL,hαL,hlong⟩ := ShiftVisits.ground_longVisitors_tail
  obtain ⟨αR,hαR,hreg⟩ := ShiftVisits.ground_regularVisitors_uniform
  let Amin := 2*max 1 (max αE (max αL αR))
  obtain ⟨α₀,ell,Dlow,Qlow,hA,hα₀,hell,hDlow,hQlow,hlow⟩ := grid_stationary_low_above Amin
  have htwo : 2≤α₀ := le_trans (by dsimp [Amin]; linarith [le_max_left (1:ℝ) (max αE (max αL αR))]) hA
  refine ⟨α₀,ell,htwo,hell,?_⟩
  intro θ hθ
  obtain ⟨Qc,hQc,hclose⟩ := grid_close_tail
  obtain ⟨b,Gc,hb,hb1,hGc,hclim,hclose⟩ := hclose θ hθ
  obtain ⟨Dc,hDc,hclose⟩ := hclose (2*α₀)
  obtain ⟨H,hH,hex⟩ := hex (2*α₀) (by positivity)
  obtain ⟨tL,htL,hlong⟩ := hlong (2*α₀) θ (by positivity) hθ
  let t₀ := min 1 (tL/2)
  have ht₀ : 0<t₀ := lt_min zero_lt_one (by positivity)
  refine ⟨b,H,t₀,hb,hb1,hH,ht₀,?_⟩
  intro p hp hp1 t ht htt
  have ht1 : t≤1 := htt.trans (min_le_left _ _)
  have htl : 2*t≤ min 2 tL := le_min (by linarith) (by have hh := htt.trans (min_le_right 1 (tL/2)); linarith)
  obtain ⟨η,hη,hηp⟩ := exp_parameter hp
  let C := 2*t/(α₀/2)^2+2
  let a := 2*t/(2*α₀)^2
  have hC : 0<C := by dsimp [C]; positivity
  have ha : 0<a := by dsimp [a]; positivity
  obtain ⟨Dr,hDr,hreg⟩ := hreg η hη (2*α₀) C a b (by positivity) hC ha hb
  have hllim : Tendsto (fun D : ℝ ↦ Qlow/D^2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0))
  have hexlim : Tendsto (fun D : ℝ ↦ Real.exp (-D)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have hlonglim : Tendsto (fun D : ℝ ↦ Real.exp (-(θ*D/2))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by positivity : 0<θ/2))
    convert h using 1
    funext D
    simp only [Function.comp_apply,id_eq]
    congr 1
    ring
  have hinvlim : Tendsto (fun D : ℝ ↦ D⁻¹) atTop (𝓝 (0:ℝ)) := tendsto_inv_atTop_zero
  have hp6 : 0<p^6 := pow_pos hp _
  have hev : ∀ᶠ D : ℝ in atTop,
      1≤D ∧ Dlow≤D ∧ Dc≤D ∧ Dr≤D ∧ 2*(2*Real.pi*(2*α₀))^3≤D ∧
      Qlow/D^2≤p^6 ∧ (((Gc/b^2)*D^(-(4/3):ℝ))^(1/(Qc:ℝ)))≤p^6 ∧
      Real.exp (-D)≤p^6 ∧ Real.exp (-(θ*D/2))≤p^6 ∧ D⁻¹<2*t := by
    filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop Dlow,eventually_ge_atTop Dc,
      eventually_ge_atTop Dr,eventually_ge_atTop (2*(2*Real.pi*(2*α₀))^3),
      hllim.eventually (gt_mem_nhds hp6),hclim.eventually (gt_mem_nhds hp6),
      hexlim.eventually (gt_mem_nhds hp6),hlonglim.eventually (gt_mem_nhds hp6),
      hinvlim.eventually (gt_mem_nhds (by positivity : (0:ℝ)<2*t))] with D h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    exact ⟨h1,h2,h3,h4,h5,h6.le,h7.le,h8.le,h9.le,h10⟩
  obtain ⟨D₀,hD₀⟩ := eventually_atTop.1 hev
  refine ⟨max 1 D₀,le_max_left _ _,?_⟩
  intro n K inst instK L hLK D α hL hDeq hDD hαlo hαup
  obtain ⟨hD1,hDlow',hDc',hDr',hsmall',hlp,hcp,hep,hlgp,hinv⟩ := hD₀ D ((le_max_right _ _).trans hDD)
  have hD : 0<D := zero_lt_one.trans_le hD1
  have hα1 : 1≤α := by
    have hh := le_max_left 1 (max αE (max αL αR))
    dsimp [Amin] at hA
    linarith
  have hαe : αE≤α := by
    have hh := (le_max_left αE (max αL αR)).trans (le_max_right 1 (max αE (max αL αR)))
    dsimp [Amin] at hA
    linarith
  have hαl : αL≤α := by
    have hh := (le_max_left αL αR).trans ((le_max_right αE (max αL αR)).trans (le_max_right 1 (max αE (max αL αR))))
    dsimp [Amin] at hA
    linarith
  have hαr : αR≤α := by
    have hh := (le_max_right αL αR).trans ((le_max_right αE (max αL αR)).trans (le_max_right 1 (max αE (max αL αR))))
    dsimp [Amin] at hA
    linarith
  have hr : 0<α/D := div_pos (zero_lt_one.trans_le hα1) hD
  have hαeq : D*(α/D)=α := by field_simp
  have hsmall := smallness_of_large_density L hDeq hD1 (zero_le_one.trans hα1) hαup hsmall'
  have hK : 1≤K := Nat.one_le_iff_ne_zero.mpr (NeZero.ne K)
  obtain ⟨hm,hτ,hτr,hspan⟩ := sourceMesh_properties ht hr
  obtain ⟨hmlo,hmhi⟩ := sourceMesh_bounds (αmax:=2*α₀) ht hr hD1 (by positivity : 0<α₀/2)
    (by rw [hαeq]; exact hαlo) (by rw [hαeq]; exact hαup)
  refine ⟨hD,hinv,?_⟩
  intro g hg A
  let u := splitTime D⁻¹ (2*t-D⁻¹) (inv_pos.mpr hD) (sub_pos.mpr hinv)
  apply certificate_joint (sourceMesh t (α/D)) (α/D) (D^(1/12:ℝ)) (meanCost+1)
    (spatialCloseScale D b/8) (spatialCloseScale D b) ell θ H D u
    (groundPathLaw n L (α/D) (2*t) g) (ENNReal.ofReal_le_one.mpr hp1)
  intro i B
  fin_cases i
  · change groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈B,(centeredCount L (gridCenter L v) (ω 0):ℝ)<ell*D}≤_
    exact (hlow K n L D α hK hLK hDeq hDlow' hαlo hαup g hg (2*t) (by positivity) 0 B).trans
      (ofReal_power_tail (by positivity) hp.le hlp B.card)
  · change groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈B,θ*D≤((localCloseLabels L (spatialCloseScale D b) (gridCenter L v) (ω 0)).card:ℝ)}≤_
    exact (hclose n K L hLK D α hL hDeq hDc' hα1 hαup g hg (2*t) (by positivity) 0 B).trans
      (ofReal_power_tail (Real.rpow_nonneg (by positivity) _) hp.le hcp B.card)
  · change groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈B,θ*D≤((localCloseLabels L (spatialCloseScale D b) (gridCenter L v) (ω 1)).card:ℝ)}≤_
    exact (hclose n K L hLK D α hL hDeq hDc' hα1 hαup g hg (2*t) (by positivity) 1 B).trans
      (ofReal_power_tail (Real.rpow_nonneg (by positivity) _) hp.le hcp B.card)
  · change groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈B,H*D<((visitors (gridCenter L v) ω).card:ℝ)}≤_
    have he := hex n K L hLK (α/D) D hDeq hD1 (by rwa [hαeq]) (by rwa [hαeq]) hr hsmall g hg
      (gridShift L) (B.image gridSite) (by positivity : 0<2*t) (by linarith : 2*t≤2)
    rw [Finset.card_image_of_injective _ gridSite_injective,←joint_event_image] at he
    simp only [grid_visitors_eq] at he
    apply (measure_mono (fun ω hω v hv ↦ (hω v hv).le)).trans
    exact he.trans (by simpa only [neg_mul] using exp_power_tail hp.le hep B.card)
  · change groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈B,¬∀j,pathVisitsBall L 12 (gridCenter L v) j ω→
      Regular (sourceMesh t (α/D)) (α/D) (D^(1/12:ℝ)) (meanCost+1) u (spatialCloseScale D b/8) (onePathAt j ω)}≤_
    have he := hreg n K L hLK (α/D) D hDeq hDr' (by rwa [hαeq]) (by rwa [hαeq]) hr hsmall g hg
      (gridShift L) (B.image gridSite) (sourceMesh t (α/D)) (sourceStep t (α/D)) hm hτ hτr
      hmlo hmhi (by rw [hspan]; linarith) hD (by rwa [hspan])
    rw [Finset.card_image_of_injective _ gridSite_injective,←joint_event_image] at he
    simp only [hspan,←grid_nonregular_iff] at he
    exact he.trans (by simpa only [neg_div] using exp_power_tail hp.le hηp B.card)
  · change groundPathLaw n L (α/D) (2*t) g {ω | ∀v∈B,θ*D≤((longVisitors (gridCenter L v) ω).card:ℝ)}≤_
    have he := hlong n K L hLK (α/D) D hDeq hD1 (by rwa [hαeq]) (by rwa [hαeq]) hr hsmall g hg
      (gridShift L) (B.image gridSite) (by positivity : 0<2*t) htl
    rw [Finset.card_image_of_injective _ gridSite_injective,←joint_event_image] at he
    simp only [grid_longVisitors_eq] at he
    exact he.trans (exp_power_tail hp.le hlgp B.card)

end HardSphere.Groups
end
end

end OAI
