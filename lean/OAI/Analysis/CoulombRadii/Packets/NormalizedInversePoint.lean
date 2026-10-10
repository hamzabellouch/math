import Mathlib
import OAI.Analysis.CoulombRadii.Packets.InverseGeometry
import OAI.Analysis.CoulombRadii.RandomFields.PhysicalPosteriorInverse
import OAI.Analysis.CoulombRadii.Packets.NormalizedBandModulus

namespace OAI

section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma atomic_response_normalization (h : ℝ) {y : Position} (hy : y≠0) :
    Coulomb.tfScalarDensity (h/100000^4)/(Coulomb.atomicCellScale y)^6 =
      Coulomb.tfScalarDensity h/‖y‖^6 := by
  rw [Coulomb.tfScalarDensity_scale _ (by norm_num : (0:ℝ) < 100000)]
  dsimp [Coulomb.atomicCellScale]
  field_simp [norm_ne_zero_iff.mpr hy]

lemma atomic_field_normalization (h η : ℝ) {y : Position} :
    (h/100000^4-2*(η/(8*100000^4)))/(Coulomb.atomicCellScale y)^4=(h-η/4)/‖y‖^4 ∧
    (h/100000^4+2*(η/(8*100000^4)))/(Coulomb.atomicCellScale y)^4=(h+η/4)/‖y‖^4 := by
  dsimp [Coulomb.atomicCellScale]
  constructor <;> ring

theorem physical_normalized_inverse_point (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z,1 < ‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {D c L K hl hh ξ : ℝ} (hD : 0 ≤ D) (hc : 0 < c) (hL : 1 ≤ L)
    (hK : 0 ≤ K) (hξ : 0 < ξ) (hξl : ξ < hl) (hlh : hl ≤ hh) :
    ∃ s₀ : ℝ,0 < s₀ ∧ s₀ ≤ 1 ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ},0 < r₀ → 0 < s → s < s₀ →
    c*(1+packetExponent)*s^packetExponent ≤ 1/4 → c*s^packetExponent ≤ 1/100 →
    (4*L/100000)*s ≤ 1 → ∀ (j : Fin J),r₀*2^j.val ≤ s →
    Real.sqrt 3*(r₀*2^j.val)^(101/100:ℝ) ≤ (r₀*2^j.val)/12 →
    ∀ (y : Position),r₀*2^j.val ≤ ‖y‖ → ‖y‖ ≤ 4*L*(r₀*2^j.val) →
    ∀ h∈Icc hl hh,
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let r := fun l : Fin J => r₀*2^l.val
    let μ := fun z => conditionalPacketDensity P Prod.fst (tailObservation r j.val) g₀ c r₀ s
      (tailObservation r j.val z)
    let cnt := fun z => rawCount {x : Position | (r j)/4 ≤ ‖x‖ ∧ ‖x‖ ≤ 12*L*(r j)} (observedOrdered r j z)
    let f := fun z => (Z:ℝ)*coulombKernel y-potentialOf (μ z) y
    P.real {z | cnt z ≤ K/(r j)^3 ∧ Coulomb.tfScalarDensity h ≤ ‖y‖^6*μ z y ∧ ‖y‖^4*f z ≤ h-ξ/4}
        ≤ (r j)^42 ∧
    P.real {z | cnt z ≤ K/(r j)^3 ∧ ‖y‖^6*μ z y ≤ Coulomb.tfScalarDensity h ∧ h+ξ/4 ≤ ‖y‖^4*f z}
        ≤ (r j)^42 := by
  let A := 4*L/100000
  let κ := c*100000/(max 1 A)^packetExponent
  let Λ := (100000:ℝ)^(101/100:ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨s₀,hs₀,hs₀1,H⟩ := physical_posterior_inverse_point g₀ hg hm hrad hD hc hA hκ
    (show 0 ≤ Λ by dsimp [Λ]; positivity) (by positivity : 0 ≤ K*A^3)
    (by positivity : 0 ≤ 100000*c) (by positivity : 0 < ξ/(8*100000^4))
    (show ξ/(8*100000^4) < hl/100000^4 by linarith)
    (show hl/100000^4 ≤ hh/100000^4 by gcongr)
  refine ⟨s₀,hs₀,hs₀1,?_⟩
  intro N J Z hZ ψ g hd hn hmin E hE hbase r₀ s hr₀ hs hss hscale hwidth hsA j hrj hnoise y hy0 hy1 h hh'
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let r : Fin J → ℝ := fun l => r₀*2^l.val
  have hr : 0 < r j := by dsimp [r]; positivity
  have hr₀r : r₀ ≤ r j := le_mul_of_one_le_right hr₀.le (one_le_pow₀ (by norm_num))
  have hy : y≠0 := norm_pos_iff.mp (hr.trans_le hy0)
  have ha : 0 < Coulomb.atomicCellScale y := Coulomb.atomicCellScale_pos hy
  have hya : Coulomb.atomicCellScale y ≤ A*(r j) := by dsimp [A,Coulomb.atomicCellScale]; linarith
  obtain ⟨hw,hwa,hell⟩ := physical_inverse_width_geometry hc hr₀ hr hs hA
    (hr₀r.trans hy0) hy0 hya hrj
  have ha1 : Coulomb.atomicCellScale y ≤ 1 :=
    (hya.trans (mul_le_mul_of_nonneg_left hrj hA.le)).trans hsA
  have hball := inverse_count_ball_subset hc hr₀ hs hr hL hr₀r hy0 hy1 hwidth
    (Real.rpow_le_self_of_le_one ha.le ha1 (by norm_num : (1:ℝ) ≤ 6/5)) hnoise
  have H' := H Z hZ hd hn hmin hE hbase hr₀ hs hss hscale j.val hrj
    ⟨j,le_rfl⟩ y hy (hr₀r.trans hy0) hya hw hwa hell
    (show h/100000^4∈Icc (hl/100000^4) (hh/100000^4) by
      constructor
      · exact div_le_div_of_nonneg_right hh'.1 (by norm_num)
      · exact div_le_div_of_nonneg_right hh'.2 (by norm_num))
  dsimp only at H'
  rw [atomic_response_normalization h hy,(atomic_field_normalization h ξ).1,
    (atomic_field_normalization h ξ).2] at H'
  have h6 := pow_pos (hr.trans_le hy0) 6
  have h4 := pow_pos (hr.trans_le hy0) 4
  constructor
  · apply le_trans (measureReal_mono (μ:=P) ?_) H'.1
    intro z hz
    refine ⟨(rawCount_mono (observedOrdered r j z) hball).trans
      (hz.1.trans (physical_inverse_count_rescale hK hA hr ha hya)),?_,?_⟩
    · exact (div_le_iff₀ h6).mpr (by simpa only [mul_comm] using hz.2.1)
    · exact (le_div_iff₀ h4).mpr (by simpa only [mul_comm] using hz.2.2)
  · apply le_trans (measureReal_mono (μ:=P) ?_) H'.2
    intro z hz
    refine ⟨(rawCount_mono (observedOrdered r j z) hball).trans
      (hz.1.trans (physical_inverse_count_rescale hK hA hr ha hya)),?_,?_⟩
    · exact (le_div_iff₀ h6).mpr (by simpa only [mul_comm] using hz.2.1)
    · exact (div_le_iff₀ h4).mpr (by simpa only [mul_comm] using hz.2.2)
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace NeutralAtom

lemma separated_mesh_volume_bound (t : Finset Position) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hball : ∀ x∈t,‖x‖ ≤ R)
    (hsep : ∀ x∈t,∀ y∈t,x≠y → ε < ‖x-y‖) :
    (t.card:ℝ)*(ε/3)^3 ≤ (R+ε/3)^3 := by
  have hdis : Set.PairwiseDisjoint (t:Set Position) (fun x => Metric.closedBall x (ε/3)) := by
    intro x hx y hy hxy
    apply Metric.closedBall_disjoint_closedBall
    rw [dist_eq_norm]
    linarith [hsep x hx y hy hxy]
  have hsub : (⋃ x∈t,Metric.closedBall x (ε/3)) ⊆ Metric.closedBall (0:Position) (R+ε/3) := by
    apply iUnion₂_subset
    intro x hx y hy
    rw [Metric.mem_closedBall,dist_zero_right]
    have hh : ‖y-x‖ ≤ ε/3 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hy
    have ht := norm_le_norm_add_norm_sub x y
    rw [norm_sub_rev x y] at ht
    linarith [hball x hx]
  have H := measureReal_mono (μ:=volume) hsub (isCompact_closedBall (0:Position) (R+ε/3)).measure_ne_top
  rw [measureReal_biUnion_finset hdis (fun _ _ => measurableSet_closedBall)
    (fun x _ => (isCompact_closedBall x (ε/3)).measure_ne_top),
    Coulomb.volume_closedBall_three _ (by positivity : 0 ≤ R+ε/3)] at H
  simp_rw [Coulomb.volume_closedBall_three _ (by positivity : 0 ≤ ε/3)] at H
  simp only [Finset.sum_const,nsmul_eq_mul] at H
  have he : (t.card:ℝ)*(4*Real.pi/3*(ε/3)^3)=(4*Real.pi/3)*((t.card:ℝ)*(ε/3)^3) := by ring
  rw [he] at H
  exact (mul_le_mul_iff_right₀ (by positivity : 0 < 4*Real.pi/3)).mp H

theorem exists_quantitative_mesh (S : Set Position) {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) (hball : ∀ x∈S,‖x‖ ≤ R) :
    ∃ t : Finset Position,(↑t:Set Position) ⊆ S ∧
      (∀ y∈S,∃ x∈t,‖y-x‖ ≤ ε) ∧
      (t.card:ℝ)*(ε/3)^3 ≤ (R+ε/3)^3 := by
  let P := fun t : Finset Position => (↑t:Set Position) ⊆ S ∧
    (∀ x∈t,∀ y∈t,x≠y → ε < ‖x-y‖)
  let A := {k : ℕ | ∃ t : Finset Position,t.card=k ∧ P t}
  have hb (k : ℕ) (hk : k∈A) : k ≤ ⌈(R+ε/3)^3/(ε/3)^3⌉₊ := by
    obtain ⟨t,rfl,ht⟩ := hk
    have H := separated_mesh_volume_bound t hR hε (fun x hx => hball x (ht.1 hx)) ht.2
    have hh : (t.card:ℝ) ≤ (R+ε/3)^3/(ε/3)^3 := (le_div_iff₀ (by positivity)).mpr H
    exact_mod_cast hh.trans (Nat.le_ceil _)
  have hAf : A.Finite := (Set.finite_Iic ⌈(R+ε/3)^3/(ε/3)^3⌉₊).subset hb
  have hAn : A.Nonempty := ⟨0,∅,by simp,by simp [P]⟩
  obtain ⟨k,hkf,hmaxf⟩ := hAf.toFinset.exists_max_image (fun k : ℕ => k)
    (by simpa only [Set.Finite.toFinset_nonempty] using hAn)
  have hk : k∈A := hAf.mem_toFinset.mp hkf
  have hmax (l : ℕ) (hl : l∈A) : l ≤ k := hmaxf l (hAf.mem_toFinset.mpr hl)
  obtain ⟨t,htk,ht⟩ := hk
  refine ⟨t,ht.1,?_,separated_mesh_volume_bound t hR hε (fun x hx => hball x (ht.1 hx)) ht.2⟩
  intro y hy
  by_contra hh
  push Not at hh
  have hyn : y∉t := by
    intro hyt
    have H := hh y hyt
    simp only [sub_self,norm_zero] at H
    linarith
  have hP : P (insert y t) := by
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl|hx
      · exact hy
      · exact ht.1 hx
    · intro x hx z hz hxz
      by_cases hxy : x=y
      · subst x
        have hz' : z∈t := (Finset.mem_insert.mp hz).resolve_left (Ne.symm hxz)
        exact hh z hz'
      · have hx' : x∈t := (Finset.mem_insert.mp hx).resolve_left hxy
        by_cases hzy : z=y
        · subst z
          simpa only [norm_sub_rev] using hh x hx'
        · have hz' : z∈t := (Finset.mem_insert.mp hz).resolve_left hzy
          exact ht.2 x hx' z hz' hxz
  have HM := hmax (insert y t).card ⟨insert y t,rfl,hP⟩
  simp only [Finset.card_insert_of_notMem hyn,←htk] at HM
  omega

theorem exists_atomic_band_mesh {L r : ℝ} (hL : 1 ≤ L) (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ t : Finset Position,(∀ y∈t,r ≤ ‖y‖ ∧ ‖y‖ ≤ 4*L*r) ∧
      (∀ y : Position,r ≤ ‖y‖ → ‖y‖ ≤ 4*L*r → ∃ z∈t,‖y-z‖ ≤ r^2) ∧
      (t.card:ℝ) ≤ (12*L+1)^3/r^3 := by
  let S := {y : Position | r ≤ ‖y‖ ∧ ‖y‖ ≤ 4*L*r}
  obtain ⟨t,ht,hcover,hcard⟩ := exists_quantitative_mesh S (R:=4*L*r) (ε:=r^2)
    (by positivity) (by positivity) (fun _ h => h.2)
  refine ⟨t,fun y hy => ht hy,fun y hy0 hy1 => hcover y ⟨hy0,hy1⟩,?_⟩
  have hroot : 4*L*r+r^2/3 ≤ r*(4*L+1/3) := by nlinarith
  have Hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 4*L*r+r^2/3) hroot 3
  have H : (t.card:ℝ)*(r^2/3)^3 ≤ (r*(4*L+1/3))^3 := hcard.trans Hpow
  apply (le_div_iff₀ (pow_pos hr 3)).mpr
  nlinarith [pow_pos hr 3]
end NeutralAtom
end

end

end OAI
