import Mathlib
import OAI.Analysis.CoulombRadii.RadialBounds.PhysicalShellError
import OAI.Analysis.CoulombRadii.Propagation.InitialMesh
import OAI.Analysis.CoulombRadii.Propagation.PhysicalFinitePropagation

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical Topology SchwartzMap
noncomputable section
namespace NeutralAtom

lemma dyadic_endpoint {r s : ℝ} (hr : 0<r) (hrs : r ≤ s) :
    ∃ J : ℕ,r*2^J ≤ s ∧ s<2*(r*2^J) ∧ ∀ j ≤ J,r*2^j ≤ s := by
  obtain ⟨J,hJ,hJ'⟩ := exists_nat_pow_near ((le_div_iff₀ hr).mpr (by simpa using hrs)) (by norm_num : (1:ℝ)<2)
  have H : r*2^J ≤ s := by simpa only [mul_comm] using (le_div_iff₀ hr).mp hJ
  refine ⟨J,H,?_,fun j hj => (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hj) hr.le).trans H⟩
  have HH := (div_lt_iff₀ hr).mp hJ'
  rw [pow_succ] at HH
  nlinarith only [HH]

theorem physical_propagated_core_mean : ∃ a M : ℝ,0<a ∧ 0 ≤ M ∧
    ∀ D : ℝ,0 ≤ D → ∃ s₀ : ℝ,0<s₀ ∧ ∀ s : ℝ,0<s → s<s₀ →
    ∃ Zmin : ℕ,∀ Z : ℕ,Zmin ≤ Z → ∀ (hZ : 1 ≤ Z) {N : ℕ}
      {ψ : Wavefunction (N+1)} {g : Gradient (N+1)},
    ∀ (hd : FormDomain ψ g) (_ : normSquared ψ=1),
    (∀ (χ : Wavefunction (N+1)) (h : Gradient (N+1)),FormDomain χ h → normSquared χ=1 →
      energy Z ψ g ≤ energy Z χ h) →
    ∀ {E : ℝ},(E:EReal) ≤ Coulomb.unrestrictedFormBottom (Coulomb.atom Z hZ) →
    energy Z ψ g ≤ E+D → (N+1:ℝ) ≤ 3*(Z:ℝ) →
    Coulomb.expectedPopulation (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1)
      (Metric.ball (0:Position) (s/4)) ≤ (Z:ℝ)-a/s^3+M*s^9 := by
  obtain ⟨εmax,hεmax,HI⟩ := physical_initial_event
  obtain ⟨ε,B,hε,hεceil,hB,hBe,hR,hbar⟩ := initial_constants_exist hεmax
  let C := max physicalSpatialCap (max B (32*ε^3))
  have hBC : B ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hcapC : physicalSpatialCap ≤ C := le_max_left _ _
  have heC : 32*ε^3 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨k⟩ := propagation_constants_exist hB hBC
  obtain ⟨K,hK,HG⟩ := physical_propagation_good_events Coulomb.unitWindow Coulomb.unitWindow_support
    Coulomb.unitWindow_mass Coulomb.unitWindow_radial (by norm_num : (0:ℝ)<1) hB hBC hcapC k
  obtain ⟨M,hM,HC⟩ := physical_bad_shell_error
  let A := tfReaction (7*B/128)*(28*Real.pi/3)/(4*Real.pi)
  have hA : 0<A := by
    dsimp [A]
    rw [tfReaction_posFactor (by positivity)]
    have hk := kTF_pos
    positivity
  let T := 1029*ε^3+M*Real.sqrt K
  have hT : 0 ≤ T := by dsimp [T]; positivity
  refine ⟨A,T,hA,hT,?_⟩
  intro D hD
  obtain ⟨s₀,hs₀,hs₀1,hgates,HG⟩ := HG D hD
  refine ⟨s₀,hs₀,?_⟩
  intro s hs hss
  have hs1 : s ≤ 1 := hss.le.trans hs₀1
  obtain ⟨hq1,hq2,hDs⟩ := hgates hs hss
  obtain ⟨Zi,Hi⟩ := HI hε hεceil D Coulomb.unitWindow Coulomb.unitWindow_mass
    Coulomb.unitWindow_radial Coulomb.unitWindow_support (by norm_num : (0:ℝ)<1) hs hq1
  have hsmall : ∀ᶠ Z : ℕ in atTop,initialAtomicRadius ε (Z:ℝ) ≤ s :=
    (tendsto_natCast_atTop_atTop.eventually ((initialAtomicRadius_tendsto hε).mono_right nhdsWithin_le_nhds |>.eventually (gt_mem_nhds hs))).mono
      (fun _ h => h.le)
  obtain ⟨Zr,Hr⟩ := eventually_atTop.mp hsmall
  refine ⟨max Zi Zr,?_⟩
  intro Z hZm hZ N ψ g hd hn hmin E hE he hnum
  have hZi : Zi ≤ Z := (le_max_left _ _).trans hZm
  have hZr : Zr ≤ Z := (le_max_right _ _).trans hZm
  have hZpos : 0<(Z:ℝ) := by exact_mod_cast (zero_lt_one.trans_le hZ)
  let r₀ := initialAtomicRadius ε (Z:ℝ)
  have hr : 0<r₀ := initialAtomicRadius_pos hε hZpos
  have hrs : r₀ ≤ s := Hr Z hZr
  have hr1 : r₀ ≤ 1 := hrs.trans hs1
  obtain ⟨J,hJs,hJs',hjr⟩ := dyadic_endpoint hr hrs
  have := rawLaw_isProbability hd.2.2.1 hn
  let P := observationLaw J (rawLaw ψ)
  let rs := fun j : Fin J => r₀*2^j.val
  have hscale (j : Fin J) : rs j ≤ s := hjr j.val j.isLt.le
  have hge (j : Fin J) : r₀ ≤ rs j := le_mul_of_one_le_right hr.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
  obtain ⟨G₀,hG₀,hp₀,hlo⟩ := Hi Z hZi hZ (J:=J) hd hn hmin hE he hnum
  have HG' := fun j : Fin J => HG Z hZ hd hn hmin hE he hr hs hss j (hscale j)
  choose G hG hp HGood using HG'
  have hcost (j : Fin J) :
      (∫ o in (G j)ᶜ,∫ y in {y : Position | rs j ≤ ‖y‖ ∧ ‖y‖<2*(rs j)},
        conditionalPacketDensity P Prod.fst (tailObservation rs j.val) Coulomb.unitWindow 1 r₀ s
          (tailObservation rs j.val o) y ∂volume ∂P) ≤ M*Real.sqrt K*(rs j)^9 := by
    exact HC Z hZ hd hn hE he hD Coulomb.unitWindow.continuous Coulomb.unitWindow_mass
      Coulomb.unitWindow_support (by norm_num : (0:ℝ)<1) hr hs (hge j) ((hscale j).trans hs1)
      ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hr.trans_le (hge j)).le (hscale j) 7) hD).trans hDs)
      hq2 hK.le rs j.val (hG j).2.compl (hp j)
  have HF := physical_finite_propagation Z hZ hd hn Coulomb.unitWindow_support Coulomb.unitWindow_mass
    (by norm_num : (0:ℝ)<1) hε hB hBC hr hr1 hs (mul_nonneg hM (Real.sqrt_nonneg K)) hq2
    (initialAtomicRadius_cubic hZpos) hnum hBe heC hR hbar k hG₀ hp₀ hlo G
    (fun j => (hG j).1) HGood hcost
  rw [raw_population_asH1 hd measurableSet_ball] at HF
  have hmono := Coulomb.expectedPopulation_mono (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1)
    measurableSet_ball measurableSet_ball (Metric.ball_subset_ball (x:=(0:Position)) (show s/4 ≤ (r₀*2^J)/2 by linarith only [hJs']))
  apply hmono.trans (HF.trans ?_)
  have hn : 0<r₀*2^J := by positivity
  have hflux : A/s^3 ≤ (tfReaction (7*B/128)*(28*Real.pi/3))/(4*Real.pi*(r₀*2^J)^3) := by
    have HH := div_le_div_of_nonneg_left hA.le (pow_pos hn 3) (pow_le_pow_left₀ hn.le hJs 3)
    change A/s^3 ≤ A/(r₀*2^J)^3 at HH
    simpa only [A,div_div,mul_assoc] using HH
  have herr : T*(r₀*2^J)^9 ≤ T*s^9 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn.le hJs 9) hT
  exact add_le_add (sub_le_sub_left hflux _) herr
end NeutralAtom
end

end

end OAI
