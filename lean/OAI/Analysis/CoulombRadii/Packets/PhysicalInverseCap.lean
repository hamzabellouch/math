import Mathlib
import OAI.Analysis.CoulombRadii.RandomFields.ObservationAnnulusTail
import OAI.Analysis.CoulombRadii.Screening.PhysicalSpatialCap
import OAI.Analysis.CoulombRadii.RandomFields.PosteriorBandOscillation
import OAI.Analysis.CoulombRadii.Packets.NormalizedInversePoint
import OAI.Analysis.CoulombRadii.Packets.MeshInverseDeterministic
import OAI.Analysis.CoulombRadii.RandomFields.FiniteInverseEvent
import OAI.Analysis.CoulombRadii.Packets.SimultaneousInverseScale
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalBandEvent

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_simultaneous_inverse_cap (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z,1 < ‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {c L hl hh ξ : ℝ} (hc : 0 < c) (hL : 1 ≤ L)
    (hξ : 0 < ξ) (hξl : ξ < hl) (hlh : hl ≤ hh) :
    ∃ C : ℝ,0 < C ∧ ∀ D : ℝ,0 ≤ D → ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1 ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ},0 < r₀ → 0 < s → s < s₀ →
    ∀ (j : Fin J),r₀*2^j.val ≤ s →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let r := fun k : Fin J => r₀*2^k.val
    ∃ G : Set (ObservationSample (N+1) J),
      (MeasurableSet G ∧ MeasurableSet[observationSigma r j.val] G) ∧
      P.real Gᶜ ≤ C*(r j)^25 ∧ ∀ a∈G,∀ y : Position,r j ≤ ‖y‖ → ‖y‖ ≤ 4*L*(r j) →
      let μ := conditionalPacketDensity P Prod.fst (tailObservation r j.val) g₀ c r₀ s
          (tailObservation r j.val a)
      let F := (Z:ℝ)*coulombKernel y-potentialOf μ y
      ‖y‖^4*F ≤ physicalSpatialCap ∧ ∀ h∈Icc hl hh,
        (Coulomb.tfScalarDensity h ≤ ‖y‖^6*μ y → h-ξ ≤ ‖y‖^4*F) ∧
        (‖y‖^6*μ y ≤ Coulomb.tfScalarDensity h → ‖y‖^4*F ≤ h+ξ) := by
  obtain ⟨K,hK,Hcount⟩ := physical_observed_small_annular_count_tail
    (by norm_num : (0:ℝ) < 1/8) (by norm_num : (1/8:ℝ) < 1/4)
    (by linarith : (1/4:ℝ) < 12*L) (by linarith : 12*L < 13*L)
  obtain ⟨B,T,hB,hT,Hreg⟩ := physical_posterior_band_event g₀ hg
  obtain ⟨Co,hCo,Hosc⟩ := posterior_count_cap_oscillation hB hK.le
  obtain ⟨heights,hhband,hheights⟩ := exists_height_brackets hξ hξl hlh
  obtain ⟨ε,hε,hmargin⟩ := exists_density_mesh_margin hξ hξl hlh
  obtain ⟨Cp,hCp,Hcap⟩ := physical_retained_spatial_cap hL
  let A := (4*L)^4*Co+4*(4*L)^3*max physicalSpatialCap 1
  let B' := (4*L)^6*(T*K)+6*(4*L)^5*(B*K)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB' : 0 ≤ B' := by dsimp [B']; positivity
  let C := 1+Cp+2*(12*L+1)^3*(heights.card:ℝ)
  have hC : 0 < C := by
    change 0 < 1+Cp+2*(12*L+1)^3*(heights.card:ℝ)
    have hlast : 0 ≤ 2*(12*L+1)^3*(heights.card:ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by linarith) _)) (Nat.cast_nonneg _)
    linarith
  refine ⟨C,hC,?_⟩
  intro D hD
  obtain ⟨sc,hsc,Hc⟩ := Hcount D hD
  obtain ⟨sp,hsp,hsp1,Hp⟩ := physical_normalized_inverse_point g₀ hg hm hrad hD hc hL hK.le
    (by positivity : 0 < ξ/2) (show ξ/2 < hl/2 by linarith)
    (show hl/2 ≤ 2*hh by linarith)
  obtain ⟨sn,hsn,hsn16,Hn⟩ := exists_simultaneous_inverse_scale (L:=L) (D:=D) (A:=A) (B:=B') hc hξ hε
  let s₀ := min sc (min sp sn)
  have hs₀sc : s₀ ≤ sc := min_le_left _ _
  have hs₀sp : s₀ ≤ sp := (min_le_right _ _).trans (min_le_left _ _)
  have hs₀sn : s₀ ≤ sn := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨s₀,lt_min hsc (lt_min hsp hsn),(hs₀sn.trans hsn16).trans (by norm_num),?_⟩
  intro N J Z hZ ψ g hd hn hmin E hE hbase r₀ s hr₀ hs hss j hrs
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let r : Fin J → ℝ := fun k => r₀*2^k.val
  let R := r j
  have hR : 0 < R := by dsimp [R,r]; positivity
  have hR₀ : r₀ ≤ R := le_mul_of_one_le_right hr₀.le (one_le_pow₀ (by norm_num))
  have hRs : R ≤ s := hrs
  have hsns : s < sn := hss.trans_le hs₀sn
  have hRn : R < sn := hRs.trans_lt hsns
  have hR16 : R ≤ 1/16 := hRn.le.trans hsn16
  have hR1 : R ≤ 1 := hR16.trans (by norm_num)
  obtain ⟨hscale,hwidth,hsA,hsD,_,_,_,_,_⟩ := Hn hs hsns
  obtain ⟨_,_,_,_,hnoise,hτr,hAr,hAl,hBD⟩ := Hn hR hRn
  have hw100 : c*s^packetExponent ≤ 1/100 := by linarith
  have hgs : HasCompactSupport (g₀ : Position → ℝ) := HasCompactSupport.intro
    (isCompact_closedBall (0:Position) 1) (fun z hz => hg z
      (by simpa only [Metric.mem_closedBall,dist_zero_right,not_le] using hz))
  let obs := tailObservation (n:=N+1) r j.val
  let μ := fun a => conditionalPacketDensity P Prod.fst obs g₀ c r₀ s (obs a)
  let d := fun a y => ‖y‖^6*μ a y
  let u := fun a y => ‖y‖^4*((Z:ℝ)*coulombKernel y-potentialOf (μ a) y)
  let O := {x : Position | R/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 12*L*R}
  let cnt : ObservationSample (N+1) J → ℝ := fun a => rawCount O (observedOrdered r j a)
  have hO : MeasurableSet O := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hcnt : Measurable[observationSigma r j.val] cnt := measurable_observed_count_tail r j le_rfl hO
  have hdmeas : ∀ y,Measurable[observationSigma r j.val] (fun a => d a y) :=
    measurable_normalized_posterior_density_tail P r j.val g₀.continuous hc hr₀ hs
  have humeas : ∀ y,Measurable[observationSigma r j.val] (fun a => u a y) :=
    measurable_normalized_posterior_field_tail P r j.val g₀.continuous hgs hm hc hr₀ hs (Z:ℝ)
  obtain ⟨t,ht,hcover,hcard⟩ := exists_atomic_band_mesh hL hR hR1
  have hp (y : Position) (hy : y∈t) (h : ℝ) (hh' : h∈heights) :
      P.real {a | cnt a ≤ K/R^3 ∧ Coulomb.tfScalarDensity h ≤ d a y ∧ u a y ≤ h-(ξ/2)/4} ≤ R^42 ∧
      P.real {a | cnt a ≤ K/R^3 ∧ d a y ≤ Coulomb.tfScalarDensity h ∧ h+(ξ/2)/4 ≤ u a y} ≤ R^42 := by
    exact Hp Z hZ hd hn hmin hE hbase hr₀ hs (hss.trans_le hs₀sp) hscale hw100
      (by nlinarith only [hsA,hL,hs] : (4*L/100000)*s ≤ 1) j hrs hnoise y (ht y hy).1 (ht y hy).2 h (hhband h hh')
  obtain ⟨Gm,hGm,hmp,Hm⟩ := finite_inverse_mesh_event (observationSigma r j.val)
    (observationSigma_le r j.val) P t heights cnt d u hcnt hdmeas humeas hp
  obtain ⟨Gr,hGr,hrp,Hr⟩ := Hreg (rawLaw ψ) hc hr₀ hs hR hL hR₀ hRs hscale hw100
    r (fun k => by dsimp [r]; positivity) j le_rfl hnoise
  obtain ⟨Gp,hGp,hpp,Hp'⟩ := Hcap g₀ hg hm hrad Z hZ hd hn hmin hE hbase hD hc hr₀ hs
    (by linarith only [hscale]) (by nlinarith only [hwidth]) hsA hsD j.val hrs
  let Gc := {a | cnt a ≤ K/R^3}
  have hGct : MeasurableSet[observationSigma r j.val] Gc := measurableSet_le hcnt measurable_const
  have hGc : MeasurableSet Gc := (observationSigma_le r j.val) _ hGct
  have hcp : P.real Gcᶜ ≤ R^40 := by
    have H := Hc Z hZ hd hn hmin hE hbase r j hR (hRs.trans_lt (hss.trans_le hs₀sc))
    simpa only [Gc,Set.compl_ofPred,not_le,cnt,O,R,P,one_div_mul_eq_div] using H
  let G := Gc ∩ (Gp ∩ (Gr ∩ Gm))
  refine ⟨G,⟨hGc.inter (hGp.1.inter (hGr.1.inter hGm.1)),
    hGct.inter (hGp.2.inter (hGr.2.inter hGm.2))⟩,?_,?_⟩
  · have hrp' : P.real Grᶜ=0 := by
      change ((observationLaw J (rawLaw ψ)) Grᶜ).toReal=0
      rw [hrp,ENNReal.toReal_zero]
    have HU (A B : Set (ObservationSample (N+1) J)) :
        P.real (A∩B)ᶜ ≤ P.real Aᶜ+P.real Bᶜ := by
      rw [compl_inter]
      exact measureReal_union_le _ _
    have H := (HU Gc (Gp ∩ (Gr ∩ Gm))).trans
      (add_le_add hcp ((HU Gp (Gr ∩ Gm)).trans
        (add_le_add hpp ((HU Gr Gm).trans (add_le_add (le_of_eq hrp') hmp)))))
    have H' : P.real Gᶜ ≤ R^40+Cp*R^249+2*(t.card:ℝ)*(heights.card:ℝ)*R^42 := by
      simpa only [zero_add,←add_assoc] using H
    exact H'.trans (mesh_exception_probability_scale hR hR1 hL hCp.le
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hcard)
  · intro a ha y hy0 hy1
    refine ⟨Hp' a ha.2.1 y (by linarith) (by
      have hpos : 0 ≤ L*R := mul_nonneg (by linarith) hR.le
      dsimp only [r,R] at hy1 hpos ⊢
      linarith only [hy1,hpos]),?_⟩
    intro h hh'
    have hcnta : cnt a ≤ K/R^3 := ha.1
    have hrega := Hr a ha.2.2.1
    let τ := c*(R/3)*(R/3)^packetExponent
    have hτ : 0 < τ := by dsimp [τ]; positivity
    have hden : ∀ y,R/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*R → μ a y ≤ (B/τ^3)*(K/R^3) := by
      intro y hy0 hy1
      exact (hrega.1 y hy0 hy1).trans (mul_le_mul_of_nonneg_left hcnta (by positivity))
    have hlip : ∀ y z,R/2 ≤ ‖y‖ → ‖y‖ ≤ 8*L*R → R/2 ≤ ‖z‖ → ‖z‖ ≤ 8*L*R →
        |μ a z-μ a y| ≤ (T/τ^4)*‖z-y‖*(K/R^3) := by
      intro y z hy0 hy1 hz0 hz1
      exact (hrega.2 z y hz0 hz1 hy0 hy1).trans (mul_le_mul_of_nonneg_left hcnta (by positivity))
    have hcapa := Hp' a ha.2.1
    have hosca := Hosc P Prod.fst obs g₀ g₀.continuous hgs hm hc hr₀ hs (obs a) (Z:ℝ) R L τ
      hR hL hτ hτr hden hcapa
    have hmesh (y : Position) (hy : y∈{y : Position | R ≤ ‖y‖ ∧ ‖y‖ ≤ 4*L*R}) :
        ∃ z∈t,|d a z-d a y| ≤ ε ∧ |u a z-u a y| ≤ (A*R)*((R/τ)^3+max (-u a y) 0) := by
      obtain ⟨z,hz,hdist⟩ := hcover y hy.1 hy.2
      have hdist' : ‖z-y‖ ≤ R^2 := by simpa only [norm_sub_rev] using hdist
      have HH := posterior_mesh_modulus P Prod.fst obs g₀ hc hr₀ hs (obs a) (Z:ℝ)
        hR hL hτ hτr hR16 hB hT hK.le hCo.le hden hlip hcapa hosca
        hy.1 hy.2 (ht z hz).1 (ht z hz).2 hdist'
      exact ⟨z,hz,HH.1.trans hBD,HH.2⟩
    exact inverse_of_space_height_mesh hξ hξl hε (mul_nonneg hA hR.le) hAr hAl
      (by positivity : 0 < (ξ/2)/4) (by linarith) hheights hmargin hmesh
      (Hm a ha.2.2.2 hcnta) y ⟨hy0,hy1⟩ h hh'
end NeutralAtom
end

end

end OAI
