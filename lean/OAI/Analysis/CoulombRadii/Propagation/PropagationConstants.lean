import Mathlib
import OAI.Analysis.CoulombRadii.Packets.PhysicalSimultaneousInverse
import OAI.Analysis.CoulombRadii.Propagation.PropagationBarrierBounds

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

structure PropagationConstants (B C : ℝ) where
  L : ℝ
  l1 : ℝ
  l2 : ℝ
  e : ℝ
  ξ : ℝ
  L_large : 2<L
  l2_pos : 0<l2
  l2_le_l1 : l2≤l1
  l1_le_gamma : l1≤propagationGamma B
  upper_overlap : C≤l2*L^4
  e_pos : 0<e
  xi_pos : 0<ξ
  xi_lt_l2 : ξ<l2
  xi_lt_height : ξ<B/2
  gain_gap : 16*ξ+2*e<l1-l2
  height_lower : B/2≤(7/8:ℝ)*B-2*e*(2*L)^4

lemma propagation_constants_exist {B C : ℝ} (hB : 0<B) (hC : B≤C) :
    Nonempty (PropagationConstants B C) := by
  let l1 := propagationGamma B/2
  let l2 := l1/4
  have h1 : 0<l1 := by dsimp [l1]; exact div_pos (propagationGamma_pos hB) (by norm_num)
  have h2 : 0<l2 := by dsimp [l2]; positivity
  have hgap : 0<l1-l2 := by dsimp [l2]; linarith only [h1]
  let L := max 3 (C/l2)
  have hL : 2<L := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hL1 : 1≤L := by linarith only [hL]
  have hCL : C≤l2*L := by
    have H := (div_le_iff₀ h2).mp (le_max_right 3 (C/l2))
    simpa only [mul_comm] using H
  have hCL4 : C≤l2*L^4 := by
    calc
      C≤C*L^3 := le_mul_of_one_le_right (hB.le.trans hC) (one_le_pow₀ hL1)
      _≤(l2*L)*L^3 := mul_le_mul_of_nonneg_right hCL (pow_nonneg (zero_le_one.trans hL1) 3)
      _=l2*L^4 := by ring
  let e := min ((l1-l2)/16) (3*B/(16*(2*L)^4))
  have he : 0<e := lt_min (by positivity) (by positivity)
  have he1 : e≤(l1-l2)/16 := min_le_left _ _
  have he2 : e*(2*L)^4≤3*B/16 := by
    have H := min_le_right ((l1-l2)/16) (3*B/(16*(2*L)^4))
    have HD : 0<(2*L)^4 := by positivity
    exact (le_div_iff₀ HD).mp (by convert H using 1; ring)
  let ξ := min (l2/2) (min ((l1-l2)/64) (B/4))
  have hξ : 0<ξ := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hξ1 : ξ≤l2/2 := min_le_left _ _
  have hξ2 : ξ≤(l1-l2)/64 := (min_le_right _ _).trans (min_le_left _ _)
  have hξ3 : ξ≤B/4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨⟨L,l1,l2,e,ξ,hL,h2,?_,?_,hCL4,he,hξ,?_,?_,?_,?_⟩⟩
  · dsimp [l2]; linarith only [h1]
  · dsimp [l1]; linarith only [propagationGamma_pos hB]
  · linarith only [hξ1,h2]
  · linarith only [hξ3,hB]
  · linarith only [hξ2,he1,hgap]
  · nlinarith only [he2]

lemma tfReaction_posFactor {v : ℝ} (hv : 0<v) :
    tfReaction v=(4*Real.pi*kTF*Real.sqrt v)*v := by
  have he : v^(3/2:ℝ)=v*Real.sqrt v := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,Real.rpow_add hv,Real.rpow_one,Real.sqrt_eq_rpow]
  unfold tfReaction
  rw [max_eq_left hv.le,he]
  ring

lemma initial_constants_exist {εmax : ℝ} (hεmax : 0<εmax) :
    ∃ ε B : ℝ,0<ε ∧ ε≤εmax ∧ 0<B ∧ B≤ε^3/10 ∧
      tfReaction (2*ε^3)≤(3/40:ℝ)*ε^3 ∧
      4*Real.pi*kTF*Real.sqrt B≤19/2 := by
  have hcont : Continuous (fun ε : ℝ => 8*Real.pi*kTF*Real.sqrt (2*ε^3)) := by fun_prop
  have hcontB : Continuous (fun ε : ℝ => 4*Real.pi*kTF*Real.sqrt (ε^3/10)) := by fun_prop
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0,ε<εmax ∧
      8*Real.pi*kTF*Real.sqrt (2*ε^3)<3/40 ∧
      4*Real.pi*kTF*Real.sqrt (ε^3/10)<19/2 := by
    have ht1 : Tendsto (fun ε : ℝ => 8*Real.pi*kTF*Real.sqrt (2*ε^3)) (𝓝 0) (𝓝 0) := by
      simpa using hcont.tendsto 0
    have ht2 : Tendsto (fun ε : ℝ => 4*Real.pi*kTF*Real.sqrt (ε^3/10)) (𝓝 0) (𝓝 0) := by
      simpa using hcontB.tendsto 0
    have h1 := ht1.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<3/40))
    have h2 := ht2.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<19/2))
    exact ((gt_mem_nhds hεmax).and (h1.and h2)).filter_mono nhdsWithin_le_nhds
  have hpositive : ∀ᶠ ε : ℝ in 𝓝[>] 0,0<ε := self_mem_nhdsWithin
  obtain ⟨ε,hε,hεm,hR,hB⟩ := (hpositive.and hsmall).exists
  have hεp : 0<ε := hε
  refine ⟨ε,ε^3/10,hεp,hεm.le,by positivity,le_rfl,?_,hB.le⟩
  rw [tfReaction_posFactor (by positivity)]
  have H := mul_le_mul_of_nonneg_right hR.le (pow_nonneg hεp.le 3)
  nlinarith only [H]

lemma initial_scaled_gates {ε B Z r : ℝ} (hZ : 0<Z) (hr : 0<r)
    (hc : Z*r^3=ε^3) (hR : tfReaction (2*ε^3)≤(3/40:ℝ)*ε^3) :
    4*(Z/(80*r^3))*r^2≤(1/20:ℝ)*Z/r ∧
    tfReaction (2*Z/r)≤6*(Z/(80*r^3)) := by
  constructor
  · apply (add_le_add_iff_left B).mp
    exact le_of_eq (by field_simp; ring)
  · have he : 2*Z/r=(2*ε^3)/r^4 := by rw [←hc]; field_simp
    rw [he,tfReaction_div_fourth _ hr]
    calc
      _≤((3/40:ℝ)*ε^3)/r^6 := div_le_div_of_nonneg_right hR (pow_pos hr 6).le
      _=6*(Z/(80*r^3)) := by rw [←hc]; field_simp; ring
end NeutralAtom
end

end
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

theorem physical_propagation_good_events (g₀ : 𝓢(Position,ℝ))
    (hg : ∀ z,1<‖z‖ → g₀ z=0) (hm : (∫ z,g₀ z^2)=1)
    (hrad : ∀ z,g₀ z=g₀ (EuclideanSpace.single 0 ‖z‖))
    {c B C : ℝ} (hc : 0<c) (hB : 0<B) (hBC : B ≤ C) (hcapC : physicalSpatialCap ≤ C)
    (k : PropagationConstants B C) :
    ∃ K : ℝ,0<K ∧ ∀ D : ℝ,0 ≤ D → ∃ s₀ : ℝ,0<s₀ ∧ s₀ ≤ 1 ∧
      (∀ {s : ℝ},0<s → s<s₀ → c*(1+packetExponent)*s^packetExponent ≤ 1/2 ∧
        c*s^packetExponent ≤ 1/4 ∧ D*s^7 ≤ 1) ∧
    ∀ {N J : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (hn : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → ∀ {r₀ s : ℝ},0<r₀ → 0<s → s<s₀ →
    ∀ (j : Fin J),r₀*2^j.val  ≤  s →
    letI := rawLaw_isProbability hd.2.2.1 hn
    let P := observationLaw J (rawLaw ψ)
    let rs := fun l : Fin J => r₀*2^l.val
    ∃ G : Set (ObservationSample (N+1) J),
      (MeasurableSet G ∧ MeasurableSet[observationSigma rs j.val] G) ∧
      P.real Gᶜ ≤ K*(rs j)^24 ∧
      ∀ o∈G,∀ x : Position,rs j ≤ ‖x‖ → ‖x‖ ≤ 4*k.L*(rs j) →
        let μ := conditionalPacketDensity P Prod.fst (tailObservation rs j.val) g₀ c r₀ s (tailObservation rs j.val o)
        let F := (Z:ℝ)*coulombKernel x-potentialOf μ x
        F ≤ C/‖x‖^4 ∧ ∀ h∈Icc (B/2) C,
          (Coulomb.tfScalarDensity h ≤ ‖x‖^6*μ x → h-k.ξ ≤ ‖x‖^4*F) ∧
          (‖x‖^6*μ x ≤ Coulomb.tfScalarDensity h → ‖x‖^4*F ≤ h+k.ξ) := by
  have hL : 1 ≤ k.L := by linarith [k.L_large]
  obtain ⟨Ki,hKi,Hi⟩ := physical_simultaneous_inverse g₀ hg hm hrad hc hL k.xi_pos k.xi_lt_height
    (show B/2 ≤ C by linarith)
  obtain ⟨Kc,hKc,Hc⟩ := physical_retained_spatial_cap hL
  refine ⟨Ki+Kc,add_pos hKi hKc,?_⟩
  intro D hD
  obtain ⟨si,hsi,hsi1,Hi⟩ := Hi D hD
  obtain ⟨sn,hsn,hsn16,Hn⟩ := exists_simultaneous_inverse_scale (L:=k.L) (D:=D) (A:=0) (B:=0)
    hc k.xi_pos (by norm_num : (0:ℝ)<1)
  have ht : Tendsto (fun s : ℝ => D*s^7) (𝓝[>] 0) (𝓝 0) := by
    convert ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).pow 7).const_mul D using 1 <;> simp
  obtain ⟨sd,hsd,Hd⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1)))
  let s₀ := min si (min sn sd)
  have hsi' : s₀ ≤ si := min_le_left _ _
  have hsn' : s₀ ≤ sn := (min_le_right _ _).trans (min_le_left _ _)
  have hsd' : s₀ ≤ sd := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨s₀,lt_min hsi (lt_min hsn hsd),hsi'.trans hsi1,?_,?_⟩
  · intro s hs hss
    obtain ⟨h1,h2,-⟩ := Hn hs (hss.trans_le hsn')
    exact ⟨h1.trans (by norm_num),h2.trans (by norm_num),(Hd ⟨hs,hss.trans_le hsd'⟩).le⟩
  intro N J Z hZ ψ g hd hn hmin E hE he r₀ s hr₀ hs hss j hrjs
  have := rawLaw_isProbability hd.2.2.1 hn
  dsimp only
  let P := observationLaw J (rawLaw ψ)
  let rs := fun l : Fin J => r₀*2^l.val
  have hrj : 0<rs j := by dsimp [rs]; positivity
  have hrj1 : rs j ≤ 1 := hrjs.trans (hss.le.trans (hsi'.trans hsi1))
  obtain ⟨h1,h2,h3,h4,-⟩ := Hn hs (hss.trans_le hsn')
  obtain ⟨Gi,hGi,hPi,HI⟩ := Hi Z hZ hd hn hmin hE he hr₀ hs (hss.trans_le hsi') j hrjs
  obtain ⟨Gc,hGc,hPc,HC⟩ := Hc g₀ hg hm hrad Z hZ hd hn hmin hE he hD hc hr₀ hs
    (h1.trans (by norm_num)) (by linarith only [h2]) h3 h4 j.val hrjs
  refine ⟨Gi∩Gc,⟨hGi.1.inter hGc.1,hGi.2.inter hGc.2⟩,?_,?_⟩
  · rw [compl_inter]
    calc
      _ ≤ P.real Giᶜ+P.real Gcᶜ := measureReal_union_le _ _
      _ ≤ Ki*(rs j)^25+Kc*(rs j)^249 := add_le_add hPi hPc
      _ ≤ Ki*(rs j)^24+Kc*(rs j)^24 := add_le_add
        (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hrj.le hrj1 (by decide)) hKi.le)
        (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hrj.le hrj1 (by decide)) hKc.le)
      _=(Ki+Kc)*(rs j)^24 := by ring
  · intro o ho x hx hx'
    refine ⟨?_,HI o ho.1 x hx hx'⟩
    have H := HC o ho.2 x (by linarith) (by
      have hpos : 0 ≤ k.L*(rs j) := mul_nonneg (by linarith [k.L_large]) hrj.le
      dsimp only [rs] at hx' hpos ⊢; linarith only [hx',hpos])
    apply (le_div_iff₀ (pow_pos (hrj.trans_le hx) 4)).mpr
    simpa only [mul_comm] using H.trans hcapC
end NeutralAtom
end

end

end OAI
